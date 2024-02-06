# Integer Linear Programming Formulations for the "Capacitated Vehicle Routing problem"
# Assumptions: Directed Graph, One Depot, Homogeneous Vehicle Fleet, Each vehicle must be used
#                    Juan-Jose Salazar-Gonzalez     jjsalaza@ull.es     15 December 2023.

using JuMP, Coluna, BlockDecomposition, Gurobi, CVRPLIB, Graphs, GraphPlot, LightGraphs, LightGraphsFlows, Compose, Cairo, Printf

env = Gurobi.Env()

function SolveCVRP(instance)
    cvrp, vrp_file, sol_file = readCVRPLIB(instance)

    n = cvrp.dimension
    c = cvrp.weights
    q = cvrp.demand
    Q = cvrp.capacity
    m = parse(Int64, split(cvrp.name, "-k")[2])
    println("Solving CVRP $(cvrp.name) with $(n-1) customers and m=$m vehicles of capacity Q=$Q")
    depot = cvrp.depot
    if q[depot] != 0
        println("Warning: the depot has demand = ", q[depot], " ; we fix it to zero to continue!!!")
        q[depot] = 0
    end
    V = 1:n
    Vc = setdiff(V, [depot])
    coord = cvrp.coordinates

    function PlotRoutes(xval)
        G = Graphs.SimpleDiGraph(Graphs.Edge.([(i, j) for i in V, j in V if i != j && xval[i, j] > EPS]))
        p = gplot(G, [coord[i, 1] for i in V], [coord[i, 2] for i in V], nodelabel=V)
        display(p)   #    draw(PNG( cvrp.name*".png", 18cm, 18cm), p )
    end

    EPS = 1e-5
    VIOLA = 1e-4

    function Index3Model(model, x, y)
        function kSEC_callback_function(cb_data)
            xval = callback_value.(Ref(cb_data), x)
            yval = callback_value.(Ref(cb_data), y)
            weight = zeros(Float64, n, n)
            for k in K
                G = LightGraphs.SimpleDiGraph(n)
                for i in V, j in V
                    if i != j && xval[i, j, k] > EPS
                        LightGraphs.add_edge!(G, i, j)
                        weight[i, j] = xval[i, j, k]
                    end
                end
                for i in Vc
                    if yval[i, k] > VIOLA
                        fval, fsol, labels = LightGraphsFlows.maximum_flow(G, depot, i, weight, algorithm=BoykovKolmogorovAlgorithm())
                        if fval < yval[i, k] - VIOLA
                            S = Set()
                            T = Set()
                            for j in V
                                push!((labels[j] == labels[i] ? S : T), j)
                            end
                            cut = @build_constraint(sum(x[u, v, k] for u in S for v in T) ≥ y[i, k])
                            MOI.submit(model, MOI.LazyConstraint(cb_data), cut)
                        end
                    end
                end
            end
        end

        @objective(model, Min, sum(c[i, j] * sum(x[i, j, :]) for i in V for j in V if i != j))
        @constraint(model, [i in Vc], sum(y[i, :]) == 1)
        @constraint(model, [i in Vc, k in K], sum(x[i, :, k]) == y[i, k])
        @constraint(model, [i in Vc, k in K], sum(x[:, i, k]) == y[i, k])
        @constraint(model, [k in K], sum(x[:, depot, k]) == 1)
        @constraint(model, [k in K], sum(x[depot, :, k]) == 1)
        @constraint(model, [k in K], sum(q[i] * y[i, k] for i in Vc) ≤ Q)
        MOI.set(model, MOI.LazyConstraintCallback(), kSEC_callback_function)
    end

    function Index2Model(model, x, variant)
        function FCC_callback_function(cb_data)   # exact separation for Fractional Capacity Cuts
            xval = callback_value.(Ref(cb_data), x)
            weight = zeros(Float64, n + 1, n + 1)
            G = LightGraphs.SimpleDiGraph(n + 1)
            for i in V, j in V
                if i != j && xval[i, j] > EPS
                    LightGraphs.add_edge!(G, i, j)
                    weight[i, j] = xval[i, j]
                end
            end
            for i in Vc
                LightGraphs.add_edge!(G, i, n + 1)
                weight[i, n+1] = q[i] / Q
            end
            fval, fsol, labels = LightGraphsFlows.maximum_flow(G, depot, n + 1, weight, algorithm=BoykovKolmogorovAlgorithm())
            if fval < sum(q[:]) / Q - VIOLA
                S = []
                T = []
                for j in V
                    push!((labels[j] == labels[n+1] ? S : T), j)
                end
                cut = @build_constraint(sum(x[u, v] for u in S for v in T) ≥ ceil(sum(q[S]) / Q))
                MOI.submit(model, MOI.LazyConstraint(cb_data), cut)
            end
        end

        @objective(model, Min, sum(c[i, j] * x[i, j] for i in V for j in V if i != j))
        @constraint(model, [i in Vc], sum(x[i, :]) == 1)
        @constraint(model, [i in Vc], sum(x[:, i]) == 1)
        @constraint(model, sum(x[depot, :]) == m)
        @constraint(model, sum(x[:, depot]) == m)
        if occursin("MTZ", variant)
            @variable(model, q[i] ≤ u[i in V] ≤ Q)
            @constraint(model, [i in Vc], u[i] ≥ q[i] + sum(q[j] * x[j, i] for j in V if i != j))
            @constraint(model, [i in Vc], u[i] ≤ Q - sum(q[j] * x[i, j] for j in V if i != j))
            if variant == "MTZ1"
                @constraint(model, [i in Vc, j in Vc; i != j], u[j] ≥ u[i] + q[j] * x[i, j] - (Q - q[j]) * (1 - x[i, j]))
            elseif variant == "MTZ2"
                @constraint(model, [i in Vc, j in Vc; i != j], u[j] ≥ u[i] + q[j] * x[i, j] - (Q - q[j]) * (1 - x[i, j]) + (Q - q[i] - q[j]) * x[j, i])
            end
        elseif variant == "SCF1"
            @variable(model, f[i in V, j in V; i != j] ≥ 0)
            @constraint(model, [i in Vc], sum(f[:, i]) - sum(f[i, :]) == q[i])
            @constraint(model, [i in V, j in V; i != j], f[i, j] ≤ Q * x[i, j])
        elseif variant == "SCF2"
            @variable(model, f[i in V, j in V; i != j] ≥ 0)
            @constraint(model, [i in Vc], sum(f[:, i]) - sum(f[i, :]) == q[i])
            @constraint(model, [i in V, j in V; i != j], f[i, j] ≤ (Q - q[i]) * x[i, j])
            @constraint(model, [i in V, j in V; i != j], f[i, j] ≥ q[j] * x[i, j])
        elseif occursin("MCF", variant)
            @variable(model, f[i in V, j in V, k in Vc; i != j] ≥ 0)
            @constraint(model, [k in Vc], sum(f[depot, :, k]) == 1)
            @constraint(model, [k in Vc], sum(f[:, depot, k]) == 0)
            @constraint(model, [k in Vc], sum(f[:, k, k]) == 1)
            @constraint(model, [k in Vc], sum(f[k, :, k]) == 0)
            @constraint(model, [i in Vc, k in Vc; i != k], sum(f[i, :, k]) == sum(f[:, i, k]))
            #@constraint(model, [i in Vc,j in Vc,k in Vc ; i!=j && i!=k && j!=k], sum(f[i,:,j])+sum(f[j,:,k]) ≤ 1+sum(f[j,:,k]))
            if occursin("MCF1", variant)
                @constraint(model, [i in V, j in V, k in Vc; i != j], f[i, j, k] ≤ x[i, j])
                if variant == "MCF1a"
                    @constraint(model, [i in V, j in V; i != j], sum(q[k] * f[i, j, k] for k in Vc if k != j) ≤ (Q - q[j]) * x[i, j])
                elseif variant == "MCF1b"
                    @constraint(model, [i in Vc], sum(q[k] * sum(f[i, :, k]) for k in Vc if k != i) ≤ Q - q[i])
                elseif variant == "MCF1c"
                    @constraint(model, [i in V, j in V; i != j], sum(q[k] * f[i, j, k] for k in Vc if k != i && k != j) ≤ (Q - q[i] - q[j]) * x[i, j])
                elseif variant == "MCF1d"
                    @constraint(model, [i in V, j in V; i != j], sum(q[k] * f[i, j, k] for k in Vc if k != i && k != j) ≤ (Q - q[i] - q[j]) * x[i, j])
                    @constraint(model, [i in Vc], sum(q[k] * (sum(f[i, :, k]) + sum(f[k, :, i])) for k in Vc if k != i) ≤ Q - q[i])
                end
            elseif occursin("MCF2", variant)
                @variable(model, g[i in V, j in V, k in Vc; i != j] ≥ 0)
                @constraint(model, [k in Vc], sum(g[depot, :, k]) == 0)
                @constraint(model, [k in Vc], sum(g[:, depot, k]) == 1)
                @constraint(model, [k in Vc], sum(g[:, k, k]) == 0)
                @constraint(model, [k in Vc], sum(g[k, :, k]) == 1)
                @constraint(model, [i in Vc, k in Vc; i != k], sum(g[i, :, k]) == sum(g[:, i, k]))

                @constraint(model, [i in V, j in V, k in Vc; i != j], f[i, j, k] + g[i, j, k] ≤ x[i, j])
                if variant == "MCF2a"
                    @constraint(model, [i in Vc], sum(q[k] * (sum(f[k, :, i]) + sum(g[:, k, i])) for k in Vc if k != i) ≤ Q - q[i])
                elseif variant == "MCF2b"
                    @constraint(model, [i in V, j in V; i != j], sum(q[k] * (f[i, j, k] + g[i, j, k]) for k in Vc if k != i && k != j) ≤ (Q - q[i] - q[j]) * x[i, j])
                    @constraint(model, [i in Vc, k in Vc; i != k], sum(f[i, :, k]) == sum(g[k, :, i]))
                elseif variant == "MCF2c"
                    @constraint(model, [i in V, j in V; i != j], sum(q[k] * (f[i, j, k] + g[i, j, k]) for k in Vc if k != i && k != j) ≤ (Q - q[i] - q[j]) * x[i, j])
                elseif variant == "MCF2d"
                    @constraint(model, [i in Vc], sum(q[k] * (sum(f[k, :, i]) + sum(g[:, k, i])) for k in Vc if k != i) ≤ Q - q[i])
                    @constraint(model, [i in Vc, k in Vc; i != k], sum(f[i, :, k]) == sum(g[k, :, i]))
                elseif variant == "MCF2e"
                    @constraint(model, [i in V, j in V; i != j], sum(q[k] * (f[i, j, k] + g[i, j, k]) for k in Vc if k != i && k != j) ≤ (Q - q[i] - q[j]) * x[i, j])
                    @constraint(model, [i in Vc], sum(q[k] * (sum(f[k, :, i]) + sum(g[:, k, i])) for k in Vc if k != i) ≤ Q - q[i])
                    @constraint(model, [i in Vc, k in Vc; i != k], sum(f[i, :, k]) == sum(g[k, :, i]))
                end
            elseif variant == "MCF3"
                @constraint(model, [i in V, j in V, k in Vc; i < j], f[i, j, k] + f[j, i, k] ≤ (x[i, j] + x[j, i]) / 2)

                @constraint(model, [i in V, j in V; i < j], sum(q[k] * (f[i, j, k] + f[j, i, k]) for k in Vc if k != i && k != j) ≤ (Q - q[i] - q[j]) * (x[i, j] + x[j, i]) / 2)
                @constraint(model, [i in Vc, k in Vc; i < k], sum(f[i, :, k]) == sum(f[k, :, i]))
            else
                println("model of type $(variant) is not implemented yet!")
            end
        elseif variant == "B&C"
            MOI.set(model, MOI.LazyConstraintCallback(), FCC_callback_function)
        else
            println("model of type $(variant) is not implemented yet!")
        end
    end

    function CVRPModel(variant, relaxation)
        model = Model(() -> Gurobi.Optimizer(env))
        set_silent(model)
        #set_time_limit_sec(model, 10.0)
        if variant == "3index"
            K = 1:m
            @variable(model, x[i in V, j in V, k in K; i != j], Bin)
            @variable(model, y[i in Vc, k in K], Bin)
            Index3Model(model, x, y)
        else
            @variable(model, x[i in V, j in V; i != j], Bin)
            Index2Model(model, x, variant)
        end
        #write_to_file(model,"model.lp")
        if relaxation == "LP"
            relax_integrality(model)
        end
        optimize!(model)
        @printf "CVRP %s %7s solved:  status=%s  ObjVal=%10.4f  Time=%5.2f\n" relaxation variant termination_status(model) objective_value(model) solve_time(model)
        @printf io " %s %s %12.4f %12.2f" relaxation variant objective_value(model) solve_time(model)
        return objective_value(model)
    end

    function CVRPModelCutAndBranch()
        model = Model(() -> Gurobi.Optimizer(env))
        set_silent(model)
        #set_time_limit_sec(model, 10.0)
        tcuts = 0
        iterations = 0
        @variable(model, x[i in V, j in V; i != j], Bin)
        @objective(model, Min, sum(c[i, j] * x[i, j] for i in V for j in V if i != j))
        @constraint(model, [i in Vc], sum(x[i, :]) == 1)
        @constraint(model, [i in Vc], sum(x[:, i]) == 1)
        @constraint(model, sum(x[depot, :]) == m)
        @constraint(model, sum(x[:, depot]) == m)
        newcut = true
        while newcut
            newcut = false
            optimize!(model)
            xval = value.(x)
            G = LightGraphs.SimpleDiGraph(LightGraphs.Edge.([(i, j) for i in V, j in V if i != j && xval[i, j] > 0.5]))
            Components = LightGraphs.connected_components(G)
            if length(Components) == 1
                for i in Vc
                    if xval[depot, i] > 0.5
                        LightGraphs.rem_edge!(G, depot, i)
                    end
                    if xval[i, depot] > 0.5
                        LightGraphs.rem_edge!(G, i, depot)
                    end
                end
                Components = LightGraphs.connected_components(G)
            end
            for S in Components
                if depot ∉ S && sum(xval[S, setdiff(V, S)]) < sum(q[S]) / Q - EPS
                    @constraint(model, sum(x[S, setdiff(V, S)]) >= ceil(sum(q[S]) / Q))
                    tcuts += 1
                    newcut = true
                end
            end
            iterations += 1
        end
        #PlotRoutes(value.(x))
        @printf "CVRP IP  cutting-plane:  status=%s  ObjVal=%10.4f  Time=%5.2f  iter=%4d  cuts=%5d \n" termination_status(model) objective_value(model) solve_time(model) iterations tcuts
        @printf io " IP C&B %12.4f %12.2f %4d %5d " objective_value(model) solve_time(model) iterations tcuts
        return objective_value(model)
    end

    function CVRPModelBranchAndCut(relaxation)
        A = [(i, j) for i in V for j in V if i != j]
        trows = tcuts = 0

        master = Model(() -> Gurobi.Optimizer(env))
        set_silent(master)
        #set_time_limit_sec(master, 10.0)

        if relaxation == "LP"
            @variable(master, x[a in A] >= 0)
        else
            @variable(master, x[a in A], Bin)
        end
        @objective(master, Min, sum(c[a[1], a[2]] * x[a] for a in A))
        @constraint(master, [i in Vc], sum(x[(i, j)] for j in V if j != i) == 1)
        @constraint(master, [i in Vc], sum(x[(j, i)] for j in V if j != i) == 1)
        @constraint(master, sum(x[(depot, i)] for i in Vc) == m)
        @constraint(master, sum(x[(i, depot)] for i in Vc) == m)

        separation = Model(() -> Gurobi.Optimizer(env)) #HiGHS.Optimizer())
        set_silent(separation)
        set_time_limit_sec(separation, 600.0)
        @variable(separation, w[a in A] >= 0)
        @variable(separation, y[i in V], Bin)
        @variable(separation, M >= 0, Int)
        @constraint(separation, [a in A], w[a] >= y[a[1]] - y[a[2]])
        @constraint(separation, sum(q[i] * y[i] for i in Vc) >= M * Q + 1)
        @constraint(separation, fix, y[depot] == 0)

        function CapacityCuts(cbdata)        # exact separation for Rounded Capacity Cuts
            trows += 1
            xval = Dict{Tuple{Int,Int},Float64}()
            for a in A
                xval[a] = callback_value(cbdata, x[a])
            end
            Mub = ceil(sum(q[:]) / Q) - 1
            @objective(separation, Min, sum(xval[a] * w[a] for a in A))
            for k in 1:Mub
                JuMP.fix(M, k, force=true)
                optimize!(separation)
                val = objective_value(separation)
                solcut = Tuple{Int,Int}[]
                if val < k + 1 - EPS
                    for a in A
                        if value(w[a]) ≈ 1.0
                            push!(solcut, a)
                        end
                    end
                    rcc = @build_constraint(sum(x[a] for a in solcut) >= k + 1)
                    MOI.submit(master, MOI.LazyConstraint(cbdata), rcc)
                    tcuts += 1
                end
            end
            return
        end
        MOI.set(master, MOI.LazyConstraintCallback(), CapacityCuts)

        optimize!(master)
        @printf "CVRP %s branch-and-cut:  status=%s  ObjVal=%10.4f  Time=%5.2f  iter=%4d  cuts=%5d \n" relaxation termination_status(master) objective_value(master) solve_time(master) trows tcuts
        @printf io " %s B&C %12.4f %12.2f %5d %5d" relaxation objective_value(master) solve_time(master) trows tcuts
        return objective_value(master)

    end

    function CVRPModelBranchAndPrice(variant, relaxation)
        A = [(i, j) for i in V for j in V if i != j]
        tcols = trows = tcuts = 0

        coluna = JuMP.optimizer_with_attributes(
            Coluna.Optimizer,
            "params" => Coluna.Params(solver=Coluna.Algorithm.BranchCutAndPriceAlgorithm()),
            "default_optimizer" => Gurobi.Optimizer #HiGHS.Optimizer, #MOI.Silent() => true
        )

        master = BlockModel(coluna)
        #set_silent(master)
        @axis(Vehicle, [1])
        if relaxation == "LP"
            @variable(master, x[t in Vehicle, a in A] >= 0)
        else
            @variable(master, x[t in Vehicle, a in A], Bin)
        end
        @objective(master, Min, sum(c[a[1], a[2]] * x[1, a] for a in A))
        @constraint(master, covering[i in Vc], sum(x[1, (i, j)] for j in V if j != i) == 1)
        @dantzig_wolfe_decomposition(master, dec, Vehicle)

        ########################################################################################
        #  Pricing Callback                                                                    #
        ########################################################################################

        pricing = Model(() -> Gurobi.Optimizer(env)) #HiGHS.Optimizer())
        set_silent(pricing)
        set_time_limit_sec(pricing, 600.0)
        @variable(pricing, z[a in A], Bin)
        @variable(pricing, y[i in Vc], Bin)
        @variable(pricing, u[i in Vc])
        @constraint(pricing, sum(z[(depot, i)] for i in Vc) == 1)
        @constraint(pricing, sum(z[(i, depot)] for i in Vc) == 1)
        @constraint(pricing, [i in Vc], sum(z[(i, j)] for j in V if j != i) == y[i])
        @constraint(pricing, [i in Vc], sum(z[(j, i)] for j in V if j != i) == y[i])
        @constraint(pricing, sum(q[i] * y[i] for i in Vc) <= Q)
        @constraint(pricing, [i in Vc, j in Vc; i != j], u[j] >= u[i] + z[(i, j)] - (n - 2) * (1 - z[(i, j)]) + (n - 3) * z[(j, i)])

        function ElementaryRoutes(cbdata)
            tcols += 1
            redcost = Dict{Tuple{Int,Int},Float64}()
            for a in A
                redcost[a] = BlockDecomposition.callback_reduced_cost(cbdata, x[1, a])
            end
            @objective(pricing, Min, sum(redcost[a] * z[a] for a in A))
            optimize!(pricing)
            solvars = JuMP.VariableRef[]
            solvals = Float64[]
            for a in A
                if value(z[a]) > 0.5
                    push!(solvars, x[1, a])
                    push!(solvals, value(z[a]))
                end
            end
            MOI.submit(master, BlockDecomposition.PricingSolution(cbdata), objective_value(pricing), solvars, solvals)
            MOI.submit(master, BlockDecomposition.PricingDualBound(cbdata), objective_bound(pricing))
        end

        subproblems = getsubproblems(dec)
        specify!(subproblems[1], lower_multiplicity=m, upper_multiplicity=m, solver=ElementaryRoutes)

        if occursin("cut", variant)
            ########################################################################################
            #  Rounded Capacity Cuts                                                               #
            ########################################################################################

            separation = Model(() -> Gurobi.Optimizer(env)) #HiGHS.Optimizer())
            set_silent(separation)
            set_time_limit_sec(separation, 600.0)
            @variable(separation, w[a in A] >= 0)
            @variable(separation, y[i in V], Bin)
            @variable(separation, M >= 0, Int)
            @constraint(separation, [a in A], w[a] >= y[a[1]] - y[a[2]])
            @constraint(separation, sum(q[i] * y[i] for i in Vc) >= M * Q + 1)
            @constraint(separation, fix, y[depot] == 0)

            function CapacityCuts(cbdata)        # exact separation for Rounded Capacity Cuts
                trows += 1
                xval = Dict{Tuple{Int,Int},Float64}()
                for a in A
                    xval[a] = callback_value(cbdata, x[1, a])
                end
                Mub = ceil(sum(q[:]) / Q) - 1
                @objective(separation, Min, sum(xval[a] * w[a] for a in A))
                for k in 1:Mub
                    JuMP.fix(M, k, force=true)
                    optimize!(separation)
                    val = objective_value(separation)
                    solcut = Tuple{Int,Int}[]
                    if val < k + 1 - EPS
                        for a in A
                            if value(w[a]) ≈ 1.0
                                push!(solcut, a)
                            end
                        end
                        rcc = @build_constraint(sum(x[1, a] for a in solcut) >= k + 1)
                        MOI.submit(master, MOI.UserCut(cbdata), rcc)
                        tcuts += 1
                    end
                end
                return
            end
            MOI.set(master, MOI.UserCutCallback(), CapacityCuts)
        end

        optimize!(master)
        @printf "CVRP %s B&P&%s:  status=%s  ObjVal=%10.4f  Time=%5.2f  pricings=%5d  separations=%5d  cuts=%4d\n" relaxation variant termination_status(master) objective_value(master) solve_time(master) tcols trows tcuts
        @printf io " %s B&P&%s %12.4f %12.2f %5d %5d %5d" relaxation variant objective_value(master) solve_time(master) tcols trows tcuts
        return objective_value(master)
    end

    CVRPModelCutAndBranch()
    List = ["MTZ1", "MTZ2", "SCF1", "SCF2", "MCF1a", "MCF1b", "MCF1c", "MCF1d", "MCF2a", "MCF2b", "MCF2c", "MCF2d", "MCF2e", "B&C"]
    for l in List
        CVRPModel(l, "IP")
    end
    CVRPModelBranchAndCut("IP")
    CVRPModelBranchAndPrice("xxx", "IP")
    CVRPModelBranchAndPrice("cut", "IP")
end

List = [
    "E-n13-k4"
    #    "E-n13-k4", "E-n22-k4", "E-n23-k3", "E-n30-k3", "E-n31-k7", "E-n33-k4",
    #    "P-n16-k8", "P-n19-k2", "P-n20-k2", "P-n21-k2", "P-n22-k2", "P-n22-k8", "P-n23-k8",
    #    "A-n32-k5", "A-n33-k5", "A-n33-k6", "A-n34-k5", "A-n36-k5", "A-n37-k5", "A-n37-k6", "A-n38-k5", "A-n39-k5", "A-n39-k6",
    #    "B-n31-k5", "B-n34-k5", "B-n35-k5", "B-n38-k6", "B-n39-k5"
]

for instance in List
    global io = open("statistics.txt", "a")
    @printf io "\n %20s " instance
    SolveCVRP(instance)
    close(io)
end
