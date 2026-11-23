using HTTP
using JSON
using PowerModels

PowerModels.silence()

const CURRENT_NET = Ref{Dict{String,Any}}(Dict{String,Any}())
const BASE_DIR = isempty(@__DIR__) ? pwd() : @__DIR__

function capacity_share(total, lower, upper)
    total <= sum(lower) && return copy(lower)
    total >= sum(upper) && return copy(upper)

    baseline = sum(clamp.(0.0, lower, upper))
    direction = total >= baseline ? 1.0 : -1.0
    capacity = direction > 0 ? max.(upper, 0.0) : min.(lower, 0.0)

    left, right = 0.0, 1.0
    for _ in 1:50
        factor = (left + right) / 2
        trial = clamp.(factor .* capacity, lower, upper)
        if direction * (sum(trial) - total) < 0
            left = factor
        else
            right = factor
        end
    end

    return clamp.(((left + right) / 2) .* capacity, lower, upper)
end

function allocate_bus_total!(unit_solutions, solver_units, ids,
                             field, lower, upper, total; fixed_id = nothing, preserve_total = false)
    lo = Float64[solver_units[id][lower] for id in ids]
    hi = Float64[solver_units[id][upper] for id in ids]

    # The slack-bus POI's MW is modeled through a signed load. Its generator
    # entry stays fixed at the solver setpoint until the caller restores its MW.
    if fixed_id !== nothing
        position = findfirst(==(fixed_id), ids)
        if position !== nothing
            fixed_output = solver_units[fixed_id][field]
            lo[position] = fixed_output
            hi[position] = fixed_output
        end
    end

    outputs = capacity_share(total, lo, hi)
    # A conventional PV/slack power flow solves for the bus's aggregate Q
    # without enforcing individual generator Q limits. Preserve that total.
    # If the limits cannot accommodate it, allocate the unmet Q in proportion
    # to each unit's capability (rather than placing it all on the last unit).
    # Individual q_violation flags then identify infeasible dispatches.
    if preserve_total && !isempty(outputs)
        residual = total - sum(outputs)
        if abs(residual) > 1e-12
            # Positive residual: weight by capacitive/injection capability.
            # Negative residual: weight by inductive/absorption capability.
            weights = residual > 0 ? max.(hi, 0.0) : max.(-lo, 0.0)
            # Fallback when none have capability in the required direction.
            if sum(weights) <= 0.0
                weights = max.(hi .- lo, 0.0)
            end
            if sum(weights) <= 0.0
                weights = ones(length(outputs))
            end
            outputs .+= residual .* (weights ./ sum(weights))
        end
    end
    for (id, output) in zip(ids, outputs)
        unit_solutions[id][field] = output
    end

    return total - sum(outputs)
end

function allocate_generator_outputs!(solution, original, solver_net;
                                     slack_poi = nothing, tol_pu = 1e-6)
    solver_units = solver_net["gen"]
    unit_solutions = solution["gen"]
    base_mva = original["baseMVA"]

    groups = Dict{Int,Vector{String}}()
    for (id, gen) in solver_units
        gen["gen_status"] == 0 && continue
        push!(get!(groups, gen["gen_bus"], String[]), id)
    end

    mismatches = Dict{Int,NamedTuple{(:mw, :mvar),Tuple{Float64,Float64}}}()

    for bus_id in sort!(collect(keys(groups)))
        ids = groups[bus_id]
        sort!(ids; by = id -> solver_units[id]["index"])
        bus_type = solver_net["bus"][string(bus_id)]["bus_type"]
        bus_type in (1, 2, 3) || continue

        if bus_type == 3
            p_total = sum(unit_solutions[id]["pg"] for id in ids)
        else
            p_total = sum(solver_units[id]["pg"] for id in ids)
        end

        p_mismatch = allocate_bus_total!(
            unit_solutions, solver_units, ids, "pg", "pmin", "pmax", p_total;
            fixed_id = bus_type == 3 ? slack_poi : nothing,
        )

        q_mismatch = 0.0
        if bus_type in (2, 3)
            q_total = sum(unit_solutions[id]["qg"] for id in ids)
            q_mismatch = allocate_bus_total!(
                unit_solutions, solver_units, ids, "qg", "qmin", "qmax", q_total;
                preserve_total = true,
            )
            if any(unit_solutions[id]["qg"] < solver_units[id]["qmin"] - tol_pu ||
                   unit_solutions[id]["qg"] > solver_units[id]["qmax"] + tol_pu for id in ids)
                @warn "PV/reference bus requires Q outside generator capability; voltage is not feasible with these limits" bus=bus_id required_q_mvar=q_total * base_mva
            end
        end

        if abs(p_mismatch) > tol_pu || abs(q_mismatch) > tol_pu
            mismatch = (mw = base_mva * p_mismatch,
                        mvar = base_mva * q_mismatch)
            mismatches[bus_id] = mismatch
            @warn "Generator capacity leaves a bus power mismatch" bus=bus_id mismatch_mw=mismatch.mw mismatch_mvar=mismatch.mvar
        end
    end

    return mismatches
end

function solve_pf_newton(net_in::Dict{String,Any}; fixed_poi = nothing, slack_poi = nothing)
    net = deepcopy(net_in)
    fixed_gens = Dict{String,Float64}()

    try
        # In the Newton solver, a PQ bus cannot retain an active generator:
        # PowerModels.compute_ac_pf asserts that PQ buses have no generators.
        # Replace each fixed-P/Q generator at a PQ bus by an equivalent signed
        # load in the SOLVER COPY ONLY.  Keep the original generator record so
        # its specified P and Q appear unchanged in the GUI/report.
        next_load_index = maximum((l["index"] for l in values(net["load"])); init=0)
        for (gid, gen) in collect(net["gen"])
            if gen["gen_status"] == 1 && net["bus"][string(gen["gen_bus"])]["bus_type"] == 1
                next_load_index += 1
                net["load"][string(next_load_index)] = Dict{String,Any}(
                    "index" => next_load_index, "load_bus" => gen["gen_bus"],
                    "status" => 1, "pd" => -gen["pg"], "qd" => -gen["qg"]
                )
                delete!(net["gen"], gid)
            end
        end

        # Represent fixed injections as signed demands in the solver copy.
        # A fixed PQ POI on a PQ bus has ALREADY been converted above, along
        # with every other fixed-P/Q generator at that bus. Do not convert it
        # twice or attempt to retrieve its now-deleted solver generator record.
        poi_id = fixed_poi === nothing ? slack_poi : fixed_poi
        if poi_id !== nothing && haskey(net["gen"], poi_id)
            gen = net["gen"][poi_id]
            load_id = maximum((l["index"] for l in values(net["load"])); init=0) + 1
            net["load"][string(load_id)] = Dict{String,Any}(
                "index" => load_id, "load_bus" => gen["gen_bus"], "status" => 1,
                "pd" => -gen["pg"], "qd" => fixed_poi === nothing ? 0.0 : -gen["qg"]
            )
            if fixed_poi !== nothing
                delete!(net["gen"], poi_id)
            else
                # The new PV facility has fixed MW even at the slack bus.
                # Existing slack units balance the system and share reactive output.
                gen["pg"] = gen["pmin"] = gen["pmax"] = 0.0
            end
        end

        println("--- Calling PowerModels.compute_ac_pf(net; method = :newton) ---")
        res = PowerModels.compute_ac_pf(net; method = :newton, show_trace = true)
        if res["termination_status"] !== true
            return Dict("termination_status" => "NOT_CONVERGED"), fixed_gens
        end

        sol = res["solution"]
        allocate_generator_outputs!(sol, net_in, net; slack_poi)
        # Sanity check: display the generator reactive power actually implied
        # by this PF solution, including any limit violations.
        for (bid, bus) in net["bus"]
            if bus["bus_type"] in (2, 3)
                gids = [gid for (gid, gen) in net["gen"] if
                        gen["gen_status"] == 1 && gen["gen_bus"] == bus["bus_i"] &&
                        haskey(sol["gen"], gid)]
                isempty(gids) && continue
                q_mvar = sum(sol["gen"][gid]["qg"] for gid in gids) * net["baseMVA"]
                println("PF bus $(bid): V=$(round(sol["bus"][bid]["vm"], digits=5)) pu, total Qg=$(round(q_mvar, digits=3)) MVAr")
            end
        end
        PowerModels.update_data!(net, sol)
        sol["branch"] = PowerModels.calc_branch_flow_ac(net)["branch"]
        if slack_poi !== nothing
            sol["gen"][slack_poi]["pg"] += net_in["gen"][slack_poi]["pg"]
        end
        println("--- PowerFlow converged successfully ---")
        result = Dict("termination_status" => "LOCALLY_SOLVED", "solution" => sol)
        return result, fixed_gens
    catch e
        println("=== CAUGHT SOLVER ERROR ===")
        Base.display(e)
        st = stacktrace(catch_backtrace())
        for line in st
            println(line)
        end
        result = Dict(
            "termination_status" => "SOLVER_ERROR: $(string(e))",
            "solution" => Dict("bus" => Dict(), "gen" => Dict(), "branch" => Dict())
        )
        return result, fixed_gens
    end
end

function build_response_payload(net::Dict{String,Any}, result, fixed_gens)
    baseMVA = get(net, "baseMVA", 100.0)
    status = string(get(result, "termination_status", "UNKNOWN"))
    converged = startswith(status, "LOCALLY_SOLVED")

    buses_out = Dict{String,Any}()
    sol_buses = get(get(result, "solution", Dict()), "bus", Dict())

    for (bid, bus) in net["bus"]
        bsol = get(sol_buses, bid, get(sol_buses, parse(Int, bid), get(sol_buses, string(bus["bus_i"]), Dict())))
        vm = get(bsol, "vm", bus["vm"])
        va_rad = get(bsol, "va", bus["va"])
        va = va_rad * 180.0 / pi
        v_viol = bus["bus_type"] != 4 && (vm < 0.95 - 1e-5 || vm > 1.05 + 1e-5)

        pd = sum((l["pd"] * baseMVA for (_, l) in net["load"] if l["load_bus"] == bus["bus_i"] && l["status"] == 1); init=0.0)
        qd = sum((l["qd"] * baseMVA for (_, l) in net["load"] if l["load_bus"] == bus["bus_i"] && l["status"] == 1); init=0.0)
        bs = sum((s["bs"] * baseMVA for (_, s) in net["shunt"] if s["shunt_bus"] == bus["bus_i"] && s["status"] == 1); init=0.0)

        sol_gens_here = get(get(result, "solution", Dict()), "gen", Dict())
        qg_total = converged ? sum((get(get(sol_gens_here, gid, Dict()), "qg", g["qg"]) * baseMVA
                                    for (gid, g) in net["gen"]
                                    if g["gen_bus"] == bus["bus_i"] && g["gen_status"] == 1); init=0.0) : nothing
        buses_out[bid] = Dict(
            "qg_total" => qg_total,
            "bus_i" => bus["bus_i"],
            "name" => get(bus, "name", "BUS_$(bus["bus_i"])"),
            "bus_type" => bus["bus_type"],
            "base_kv" => bus["base_kv"],
            "vm" => vm,
            "vm_setpoint" => bus["vm"],
            "va_deg" => va,
            "pd" => pd,
            "qd" => qd,
            "bs" => bs,
            "v_violation" => v_viol
        )
    end

    gens_out = Dict{String,Any}()
    sol_gens = get(get(result, "solution", Dict()), "gen", Dict())

    for (gid, gen) in net["gen"]
        gsol = get(sol_gens, gid, get(sol_gens, parse(Int, gid), Dict()))
        pg = gen["gen_status"] == 1 ? get(gsol, "pg", gen["pg"]) * baseMVA : 0.0
        qg = gen["gen_status"] == 1 ? get(gsol, "qg", gen["qg"]) * baseMVA : 0.0
        pmax = gen["pmax"] * baseMVA
        pmin = gen["pmin"] * baseMVA
        qmax = gen["qmax"] * baseMVA
        qmin = gen["qmin"] * baseMVA

        p_viol = gen["gen_status"] == 1 && (pg > pmax + 0.05 || pg < pmin - 0.05)
        q_viol = gen["gen_status"] == 1 && (qg > qmax + 0.05 || qg < qmin - 0.05)

        gens_out[gid] = Dict(
            "index" => parse(Int, gid),
            "gen_bus" => gen["gen_bus"],
            "status" => gen["gen_status"],
            "pg" => pg,
            "qg" => qg,
            "pmax" => pmax,
            "pmin" => pmin,
            "qmax" => qmax,
            "qmin" => qmin,
            "vg" => gen["vg"],
            "q_limited" => haskey(fixed_gens, gid),
            "p_violation" => p_viol,
            "q_violation" => q_viol
        )
    end

    branches_out = Dict{String,Any}()
    sol_branches = get(get(result, "solution", Dict()), "branch", Dict())

    for (brid, br) in net["branch"]
        in_service = br["br_status"] == 1
        brsol = get(sol_branches, brid, nothing)
        if !in_service
            pf = qf = pt = qt = s_max = 0.0
        elseif brsol === nothing || !all(isfinite(brsol[key]) for key in ("pf", "qf", "pt", "qt"))
            pf = qf = pt = qt = s_max = nothing
        else
            pf = brsol["pf"] * baseMVA
            qf = brsol["qf"] * baseMVA
            pt = brsol["pt"] * baseMVA
            qt = brsol["qt"] * baseMVA
            s_max = max(hypot(pf, qf), hypot(pt, qt))
        end

        rate_mva = get(br, "rate_a", 0.0) * baseMVA
        rate_a = 0 < rate_mva < 9900 ? rate_mva : nothing
        can_check_loading = in_service && s_max !== nothing && rate_a !== nothing
        loading_pct = can_check_loading ? 100.0 * s_max / rate_a : nothing
        overload = can_check_loading && s_max > rate_a + 0.05

        branches_out[brid] = Dict(
            "index" => parse(Int, brid),
            "f_bus" => br["f_bus"],
            "t_bus" => br["t_bus"],
            "status" => br["br_status"],
            "pf" => pf,
            "qf" => qf,
            "pt" => pt,
            "qt" => qt,
            "s_max" => s_max,
            "rate_a" => rate_a,
            "loading_pct" => loading_pct,
            "overload" => overload,
            "is_xfmr" => br["transformer"]
        )
    end

    return Dict(
        "converged" => converged,
        "termination_status" => status,
        "baseMVA" => baseMVA,
        "buses" => buses_out,
        "gens" => gens_out,
        "branches" => branches_out
    )
end

const ROUTER = HTTP.Router()

HTTP.register!(ROUTER, "GET", "/health", req -> HTTP.Response(200, "OK"))

HTTP.register!(ROUTER, "GET", "/", function(req)
    for fname in ["index.html", "hawaii_powermodels_visualizer.html"]
        fpath = joinpath(BASE_DIR, fname)
        if isfile(fpath)
            return HTTP.Response(200, ["Content-Type" => "text/html"], read(fpath, String))
        end
    end
    return HTTP.Response(404, "Place index.html in $(BASE_DIR)")
end)

HTTP.register!(ROUTER, "POST", "/load", function(req)
    body = JSON.parse(String(req.body))
    tmp = tempname() * ".m"
    write(tmp, body["m_content"])
    # PowerModels.parse_file() validates and silently changes PQ buses with
    # online generators into PV buses.  Capture the actual MATPOWER BUS_TYPE
    # values before that correction, then restore them in the normalized model.
    # parse_matpower(validate=false) still parses the MATPOWER bus matrix but
    # skips automatic bus-type correction.
    source = PowerModels.parse_matpower(tmp; validate=false)
    source_types = Dict(string(bus["bus_i"]) => Int(bus["bus_type"])
                        for bus in values(source["bus"]))
    net = PowerModels.parse_file(tmp)
    rm(tmp; force=true)
    for (bid, bus) in net["bus"]
        bus["bus_type"] = source_types[string(bus["bus_i"])]
    end
    println("MATPOWER bus types (from file): ",
            join(["$(b["bus_i"])=$(b["bus_type"])" for b in
                  sort!(collect(values(net["bus"])); by = b -> b["bus_i"])], ", "))
    CURRENT_NET[] = net
    res, fixed = solve_pf_newton(net)
    return HTTP.Response(200, ["Content-Type" => "application/json"], JSON.json(build_response_payload(net, res, fixed)))
end)

HTTP.register!(ROUTER, "POST", "/solve", function(req)
    body = JSON.parse(String(req.body))
    net = deepcopy(CURRENT_NET[])
    baseMVA = get(net, "baseMVA", 100.0)

    for (gid, gedit) in get(body, "gens", Dict())
        if haskey(net["gen"], gid)
            net["gen"][gid]["pg"] = Float64(gedit["pg"]) / baseMVA
            net["gen"][gid]["vg"] = Float64(gedit["vg"])
            net["gen"][gid]["gen_status"] = Int(gedit["status"])
        end
    end

    for (brid, bredit) in get(body, "branches", Dict())
        if haskey(net["branch"], brid)
            net["branch"][brid]["br_status"] = Int(bredit["status"])
        end
    end

    for (bid, ldedit) in get(body, "loads", Dict())
        b_int = parse(Int, bid)
        matching = [lid for (lid, l) in net["load"] if l["load_bus"] == b_int]
        if !isempty(matching)
            net["load"][matching[1]]["pd"] = Float64(ldedit["pd"]) / baseMVA
            net["load"][matching[1]]["qd"] = Float64(ldedit["qd"]) / baseMVA
            for extra in matching[2:end]
                net["load"][extra]["pd"] = 0.0
                net["load"][extra]["qd"] = 0.0
            end
        elseif Float64(ldedit["pd"]) != 0.0 || Float64(ldedit["qd"]) != 0.0
            new_id = string(length(net["load"]) + 1)
            net["load"][new_id] = Dict{String,Any}(
                "index" => parse(Int, new_id), "load_bus" => b_int, "status" => 1,
                "pd" => Float64(ldedit["pd"]) / baseMVA, "qd" => Float64(ldedit["qd"]) / baseMVA
            )
        end
    end

    # Bus types are taken exclusively from the MATPOWER file parsed by
    # PowerModels.parse_file at /load. A PQ bus remains PQ even with generators.
    if !isempty(get(body, "bus_types", Dict()))
        return HTTP.Response(400, "Bus types are defined in the MATPOWER .m file. Edit the file and reload it to change PQ/PV classification.")
    end

    # Bus-level controls are applied afresh to the originally loaded case
    # on each solve, so removing an edit returns that bus to its base value.
    for (bid, vedit) in get(body, "voltages", Dict())
        bus = get(net["bus"], string(bid), nothing)
        if bus === nothing || !(bus["bus_type"] in (2, 3))
            return HTTP.Response(400, "Voltage setpoints may only be edited at existing PV or reference buses.")
        end
        vm = Float64(vedit)
        if !isfinite(vm) || !(0.5 <= vm <= 1.5)
            return HTTP.Response(400, "Invalid voltage setpoint at bus $(bid).")
        end
        bus["vm"] = vm
        for gen in values(net["gen"])
            if gen["gen_bus"] == bus["bus_i"] && gen["gen_status"] == 1
                gen["vg"] = vm
            end
        end
    end

    # Shunt setting is the total shunt susceptance at a bus, reported as
    # MVAr injected at 1 p.u. voltage. Positive = capacitive; negative = inductive.
    for (bid, q_nominal) in get(body, "shunts", Dict())
        bus = get(net["bus"], string(bid), nothing)
        if bus === nothing || bus["bus_type"] == 4
            return HTTP.Response(400, "Shunt compensation requires an in-service bus.")
        end
        q = Float64(q_nominal)
        if !isfinite(q)
            return HTTP.Response(400, "Invalid shunt value at bus $(bid).")
        end
        matches = sort!([sid for (sid, s) in net["shunt"]
                         if s["shunt_bus"] == bus["bus_i"] && s["status"] == 1];
                        by = sid -> net["shunt"][sid]["index"])
        if !isempty(matches)
            net["shunt"][first(matches)]["bs"] = q / baseMVA
            for sid in matches[2:end]
                net["shunt"][sid]["bs"] = 0.0
            end
        elseif q != 0.0
            new_index = maximum((s["index"] for s in values(net["shunt"])); init=0) + 1
            sid = string(new_index)
            net["shunt"][sid] = Dict{String,Any}(
                "index" => new_index, "shunt_bus" => bus["bus_i"],
                "status" => 1, "gs" => 0.0, "bs" => q / baseMVA
            )
        end
    end

    fixed_poi = slack_poi = nothing
    poi = get(body, "poi", nothing)
    if poi !== nothing && get(poi, "enabled", false)
        p_bus = Int(poi["bus"])
        bus = get(net["bus"], string(p_bus), nothing)
        if bus === nothing || bus["bus_type"] == 4
            return HTTP.Response(400, "The POI must be an in-service bus in the loaded case.")
        end
        mode = get(poi, "mode", "PQ")
        if !(mode in ("PV", "PQ", "LOAD"))
            return HTTP.Response(400, "Unknown POI control mode.")
        end
        pd = Float64(get(poi, "demand_mw", 0.0))
        qd = Float64(get(poi, "demand_mvar", 0.0))
        if !isfinite(pd) || pd < 0 || !isfinite(qd)
            return HTTP.Response(400, "Enter finite POI demand and nonnegative MW.")
        end
        if pd != 0 || qd != 0
            load_id = maximum((l["index"] for l in values(net["load"])); init=0) + 1
            net["load"][string(load_id)] = Dict{String,Any}(
                "index" => load_id, "load_bus" => p_bus, "status" => 1,
                "pd" => pd / baseMVA, "qd" => qd / baseMVA
            )
        end
        if mode != "LOAD"
            new_gid = string(maximum(g["index"] for g in values(net["gen"]); init=0) + 1)
            is_pv = mode == "PV"
            net["gen"][new_gid] = Dict{String,Any}(
                "index" => parse(Int, new_gid),
                "gen_bus" => p_bus,
                "gen_status" => 1,
                "pg" => Float64(poi["pg"]) / baseMVA,
                "qg" => Float64(poi["qg"]) / baseMVA,
                "vg" => Float64(poi["vg"]),
                "pmax" => Float64(poi["pmax"]) / baseMVA,
                "pmin" => Float64(poi["pmin"]) / baseMVA,
                "qmax" => Float64(poi["qmax"]) / baseMVA,
                "qmin" => Float64(poi["qmin"]) / baseMVA,
                "mbase" => baseMVA
            )
            if is_pv
                if bus["bus_type"] == 3
                    slack_poi = new_gid
                else
                    bus["bus_type"] = 2
                end
                bus["vm"] = net["gen"][new_gid]["vg"]
            else
                fixed_poi = new_gid
            end
        end
    end

    res, fixed = solve_pf_newton(net; fixed_poi, slack_poi)
    return HTTP.Response(200, ["Content-Type" => "application/json"], JSON.json(build_response_payload(net, res, fixed)))
end)

println("ECEN 5417 PowerModels.jl Newton-Raphson Server running at http://localhost:8080")
HTTP.serve(ROUTER, "127.0.0.1", 8080)