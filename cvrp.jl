# Integer Linear Programming Formulations for the "Capacitated Vehicle Routing problem"
# Assumptions: Directed Graph, One Depot, Homogeneous Vehicle Fleet, All vehicles must be used
#                    Juan-Jose Salazar-Gonzalez     jjsalaza@ull.es     15 December 2023.

using Printf, JuMP, Gurobi, CVRPLIB, LightGraphs, LightGraphsFlows, Graphs, GraphPlot, Plots, Colors, Compose, Cairo, Coluna, BlockDecomposition, BilevelJuMP

env = Gurobi.Env()

function SolveCVRP(instance)
    cvrp, vrp_file, sol_file = readCVRPLIB(instance)

    n = cvrp.dimension                            # number of customes & depot (i.e. customers + 1 )
    c = cvrp.weights                              # routing costs
    q = cvrp.demand                               # demands
    Q = cvrp.capacity
    m = parse(Int64, split(cvrp.name, "-k")[2])
    depot = cvrp.depot
    if q[depot] != 0
        println("Warning: the depot has demand = ", q[depot], " ; we fix it to zero to continue!!!")
        q[depot] = 0
    end
    println("Solving CVRP $(cvrp.name) with $(n-1) customers and m=$m vehicles of capacity Q=$Q ; depot=$depot")
    K = 1:m                                       # vehicle set
    V = 1:n                                       # node set (customers & depot)
    Vc = setdiff(V, [depot])                      # customer set
    coord = cvrp.coordinates
    A = [(i, j) for i in V for j in V if i != j]  # arc set
    Ain = Dict{Int,Array{Tuple{Int,Int},1}}()
    Aou = Dict{Int,Array{Tuple{Int,Int},1}}()
    for i in V
        Aou[i] = [(i, j) for j in V if j != i]    # arcs leaving node i
        Ain[i] = [(j, i) for j in V if j != i]    # arcs enterning node i
    end

    function PlotRoutes(xval)
        if coord != nothing
            G = Graphs.SimpleDiGraph(Graphs.Edge.([a for a in A if xval[a] > EPS]))
            nodefillc = [colorant"lightseagreen" for i in V]
            nodefillc[depot] = colorant"red"
            p = gplot(G, [coord[i, 1] for i in V], [coord[i, 2] for i in V], nodelabel=V, nodefillc=nodefillc)
            display(p)   
            draw(PNG( cvrp.name*".png", 18cm, 18cm), p )
        end
    end

    EPS = 1e-5
    VIOLA = 1e-4

    function CVRPCompactModel(variant, relaxation)

        model = Model(() -> Gurobi.Optimizer(env))
        @variable(model, x[A], Bin)
        @objective(model, Min, sum(c[a[1], a[2]] * x[a] for a in A))

        @constraint(model, [i in Vc], sum(x[Aou[i]]) == 1)
        @constraint(model, [i in Vc], sum(x[Ain[i]]) == 1)
        @constraint(model, sum(x[Aou[depot]]) == m)
        @constraint(model, sum(x[Ain[depot]]) == m)

        if occursin("TSP-MTZ", variant)
            @variable(model, w[Vc])
            @constraint(model, [i in Vc], w[i] ≥ 1 + sum(x[(j, i)] for j in Vc if j != i))
            @constraint(model, [i in Vc], w[i] ≤ n - sum(x[(i, j)] for j in Vc if j != i))
            @constraint(model, [i in Vc, j in Vc; i != j], w[j] ≥ w[i] + x[(i, j)] - (n - 1) * (1 - x[(i, j)]) + (n - 2) * x[(j, i)])
        end
        if occursin("VRP-MTZ", variant)
            @variable(model, u[Vc])
            @constraint(model, [i in Vc], u[i] ≥ q[i] + sum(q[a[1]] * x[a] for a in Ain[i]))
            @constraint(model, [i in Vc], u[i] ≤ Q - sum(q[a[2]] * x[a] for a in Aou[i]))
            @constraint(model, [i in Vc, j in Vc; i != j], u[j] ≥ u[i] + q[j] * x[(i, j)] - (Q - q[j]) * (1 - x[(i, j)]) + (Q - q[i] - q[j]) * x[(j, i)])
        end

        if occursin("PRED", variant)
            @variable(model, v[i in Vc, j in Vc; i != j] ≥ 0)
            @constraint(model, [i in Vc, j in Vc; i < j], v[i, j] + v[j, i] ≤ 1)
            @constraint(model, [i in Vc, j in Vc, k in Vc; i != j && i != k && k != j], x[(j, i)] + v[i, j] + v[j, k] ≤ 1 + v[i, k])
            @constraint(model, [i in Vc, j in Vc; i != j], x[(i, j)] ≤ v[i, j])
        end
        if occursin("VRP-PRED", variant)
            @constraint(model, [i in Vc], sum(q[j] * (v[i, j] + v[j, i]) for j in Vc if j != i) ≤ Q - q[i])
        end

        if occursin("VRP-SCF", variant)
            @variable(model, f[A])
            @constraint(model, [i in Vc], sum(f[Ain[i]]) - sum(f[Aou[i]]) == q[i])
            @constraint(model, [a in A], f[a] ≤ (Q - q[a[1]]) * x[a])
            @constraint(model, [a in A], f[a] ≥ q[a[2]] * x[a])
        end

        if occursin("TSP-MCF", variant)
            @variable(model, h[A, Vc] ≥ 0)
            @constraint(model, [k in Vc], sum(h[Aou[depot], k]) == 1)
            @constraint(model, [k in Vc], sum(h[Ain[depot], k]) == 0)
            @constraint(model, [k in Vc], sum(h[Ain[k], k]) == 1)
            @constraint(model, [k in Vc], sum(h[Aou[k], k]) == 0)
            @constraint(model, [i in Vc, j in Vc; i != j], sum(h[Aou[i], j]) == sum(h[Ain[i], j]))
            @constraint(model, [a in A, k in Vc], h[a, k] ≤ x[a])
        end
        if occursin("VRP-MCF", variant)
            @variable(model, fm[A, Vc] ≥ 0)
            @constraint(model, [k in Vc], sum(fm[Aou[depot], k]) == 1)
            @constraint(model, [k in Vc], sum(fm[Ain[depot], k]) == 0)
            @constraint(model, [k in Vc], sum(fm[Ain[k], k]) == 1)
            @constraint(model, [k in Vc], sum(fm[Aou[k], k]) == 0)
            @constraint(model, [i in Vc, k in Vc; i != k], sum(fm[Aou[i], k]) == sum(fm[Ain[i], k]))
            #@constraint(model, [i in Vc,j in Vc,k in Vc ; i!=j && i!=k && j!=k], sum(fm[Aou[i],j])+sum(fm[Aou[j],k]) ≤ 1+sum(fm[Aou[i],k]))
            if occursin("MCF1", variant)
                @constraint(model, [a in A, k in Vc], fm[a, k] ≤ x[a])
                if occursin("MCF1a", variant)
                    @constraint(model, [i in Vc], sum(q[k] * (sum(fm[Aou[i], k]) + sum(fm[Aou[k], i])) for k in Vc if k != i) ≤ Q - q[i])
                end
                if occursin("MCF1b", variant)
                    @constraint(model, [a in A], sum(q[k] * fm[a, k] for k in Vc if k != a[1] && k != a[2]) ≤ (Q - q[a[1]] - q[a[2]]) * x[a])
                end
            end
            if occursin("MCF2", variant)
                @variable(model, gm[A, Vc] ≥ 0)
                @constraint(model, [k in Vc], sum(gm[Aou[depot], k]) == 0)
                @constraint(model, [k in Vc], sum(gm[Ain[depot], k]) == 1)
                @constraint(model, [k in Vc], sum(gm[Ain[k], k]) == 0)
                @constraint(model, [k in Vc], sum(gm[Aou[k], k]) == 1)
                @constraint(model, [i in Vc, k in Vc; i != k], sum(gm[Aou[i], k]) == sum(gm[Ain[i], k]))
                @constraint(model, [a in A, k in Vc], fm[a, k] + gm[a, k] ≤ x[a])
                if occursin("MCF2a", variant)
                    @constraint(model, [i in Vc], sum(q[k] * (sum(fm[Aou[k], i]) + sum(gm[Ain[k], i])) for k in Vc if k != i) ≤ Q - q[i])
                end
                if occursin("MCF2b", variant)
                    @constraint(model, [a in A], sum(q[k] * (fm[a, k] + gm[a, k]) for k in Vc if k != a[1] && k != a[2]) ≤ (Q - q[a[1]] - q[a[2]]) * x[a])
                end
                if occursin("MCF2c", variant)
                    @constraint(model, [i in Vc, k in Vc; i != k], sum(fm[Aou[i], k]) == sum(gm[Aou[k], i]))
                end
            end
            if occursin("MCF3", variant)
                @constraint(model, [i in V, j in V, k in Vc; i < j], fm[(i, j), k] + fm[(j, i), k] ≤ (x[(i, j)] + x[(j, i)]) / 2)
                @constraint(model, [i in V, j in V; i < j], sum(q[k] * (fm[(i, j), k] + fm[(j, i), k]) for k in Vc if k != i && k != j) ≤ (Q - q[i] - q[j]) * (x[(i, j)] + x[(j, i)]) / 2)
                @constraint(model, [i in Vc, k in Vc; i < k], sum(fm[Aou[i], k]) == sum(fm[Aou[k], i]))
            end
        end
        if occursin("VRP-DECOMP", variant)
            @variable(model, z[A, K] ≥ 0)
            @variable(model, y[Vc, K], Bin)
            @constraint(model, [a in A], sum(z[a, k] for k in K) == x[a])
            @constraint(model, [i in Vc], sum(y[i, k] for k in K) == 1)
            @constraint(model, [i in Vc, k in K], sum(z[Aou[i], k]) == y[i, k])
            @constraint(model, [i in Vc, k in K], sum(z[Ain[i], k]) == y[i, k])
            @constraint(model, [k in K], sum(z[Aou[depot], k]) == 1)
            @constraint(model, [k in K], sum(z[Ain[depot], k]) == 1)
            @constraint(model, [k in K], sum(q[i] * y[i, k] for i in Vc) ≤ Q)
        end

        set_silent(model)
        #set_time_limit_sec(model, 10.0)
        if relaxation
            relax_integrality(model)
        end
        #write_to_file(model,"model.lp")
        optimize!(model)
        if !relaxation
            PlotRoutes(value.(x))
        end
        @printf "CVRP %s %20s solved:  status=%10s  ObjVal=%10.4f  Time=%5.2f\n" (relaxation ? "LP" : "IP") variant termination_status(model) objective_value(model) solve_time(model)
        @printf io " %s %20s %12.4f %12.2f" (relaxation ? "LP" : "IP") variant objective_value(model) solve_time(model)
        return objective_value(model)
    end

    function CVRPCutAndBranch() # separating subtour & capacity cuts only on INTEGER solutons of a 2-index formulation
        tcuts = iterations = 0

        master = Model(() -> Gurobi.Optimizer(env))
        @variable(master, x[A], Bin)
        @objective(master, Min, sum(c[a[1], a[2]] * x[a] for a in A))
        @constraint(master, [i in Vc], sum(x[Aou[i]]) == 1)
        @constraint(master, [i in Vc], sum(x[Ain[i]]) == 1)
        @constraint(master, sum(x[Aou[depot]]) == m)
        @constraint(master, sum(x[Ain[depot]]) == m)

        set_silent(master)
        #set_time_limit_sec(master, 10.0)

        newcut = true
        while newcut
            newcut = false
            optimize!(master)
            xval = value.(x)
            G = LightGraphs.SimpleDiGraph(LightGraphs.Edge.([(i, j) for i in Vc for j in Vc if i != j && xval[(i, j)] > 0.5]))
            Components = LightGraphs.connected_components(G)
            for S in Components
                T = setdiff(V, S)
                if sum(xval[(u, v)] for u in S for v in T) < ceil(sum(q[S]) / Q) - VIOLA
                    @constraint(master, sum(x[(u, v)] for u in S for v in T) ≥ ceil(sum(q[S]) / Q))
                    tcuts += 1
                    newcut = true
                end
            end
            iterations += 1
        end
        PlotRoutes(value.(x))
        @printf "CVRP IP        cut-and-branch      :  status=%10s  ObjVal=%10.4f  Time=%5.2f  iter=%4d  cuts=%5d \n" termination_status(master) objective_value(master) solve_time(master) iterations tcuts
        @printf io " IP C&B %12.4f %12.2f %4d %5d " objective_value(master) solve_time(master) iterations tcuts
        return objective_value(master)
    end

    function CVRPBranchAndCut(ineq, relaxation)    # separating capacity cuts on INTEGER and FRATIONALS solutons
        tcuts = iterations = 0
        master = Model(() -> Gurobi.Optimizer(env))
        if relaxation
            @variable(master, x[A] ≥ 0)
        else
            @variable(master, x[A], Bin)
        end
        @objective(master, Min, sum(c[a[1], a[2]] * x[a] for a in A))
        @constraint(master, [i in Vc], sum(x[Aou[i]]) == 1)
        @constraint(master, [i in Vc], sum(x[Ain[i]]) == 1)
        @constraint(master, sum(x[Aou[depot]]) == m)
        @constraint(master, sum(x[Ain[depot]]) == m)

        if occursin("SEC", ineq)
            function SubtourEliminationCuts(xval, cbdata)
                ncuts = 0
                G = LightGraphs.SimpleDiGraph(n)
                weight = zeros(Float64, n, n)
                for a in A
                    if xval[a] > EPS
                        LightGraphs.add_edge!(G, a[1], a[2])
                        weight[a[1], a[2]] = xval[a]
                    end
                end
                for i in Vc
                    fval, fsol, labels = LightGraphsFlows.maximum_flow(G, depot, i, weight, algorithm=BoykovKolmogorovAlgorithm())
                    if fval < 1 - VIOLA
                        S = Set()
                        T = Set()
                        for j in V
                            push!((labels[j] == labels[i] ? S : T), j)
                        end
                        ncuts += 1
                        if relaxation
                            @constraint(master, sum(x[(u, v)] for u in S for v in T) ≥ 1)
                        else
                            cut = @build_constraint(sum(x[(u, v)] for u in S for v in T) ≥ 1)
                            MOI.submit(master, MOI.LazyConstraint(cbdata), cut)
                        end
                    end
                end
                return ncuts
            end
        end
        if occursin("FCC", ineq)
            function FractionalCapacityCuts(xval, cbdata)   # exact separation for FRACTIONAL Capacity Cuts
                ncuts = 0
                G = LightGraphs.SimpleDiGraph(n + 1)
                weight = zeros(Float64, n + 1, n + 1)
                for a in A
                    if xval[a] > EPS
                        LightGraphs.add_edge!(G, a[1], a[2])
                        weight[a[1], a[2]] = xval[a]
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
                    ncuts += 1
                    if relaxation
                        @constraint(master, sum(x[(u, v)] for u in S for v in T) ≥ ceil(sum(q[S]) / Q))
                    else
                        cut = @build_constraint(sum(x[(u, v)] for u in S for v in T) ≥ ceil(sum(q[S]) / Q))
                        MOI.submit(master, MOI.LazyConstraint(cbdata), cut)
                    end
                end
                return ncuts
            end
        end
        if occursin("RCC", ineq)
            separation = Model(() -> Gurobi.Optimizer(env))
            set_silent(separation)
            set_time_limit_sec(separation, 600.0)
            @variable(separation, w[A] ≥ 0)
            @variable(separation, y[V], Bin)
            @variable(separation, M ≥ 0, Int)
            @constraint(separation, [a in A], w[a] ≥ y[a[1]] - y[a[2]])
            @constraint(separation, sum(q[i] * y[i] for i in Vc) ≥ M * Q + 1)
            @constraint(separation, fix, y[depot] == 0)

            function RoundedCapacityCuts(xval, cbdata)        # exact separation for ROUNDED Capacity Cuts
                ncuts = 0
                Mub = ceil(sum(q[:]) / Q) - 1
                @objective(separation, Min, sum(xval[a] * w[a] for a in A))
                for k in 1:Mub
                    JuMP.fix(M, k, force=true)
                    optimize!(separation)
                    solcut = Tuple{Int,Int}[]
                    if objective_value(separation) < k + 1 - EPS
                        for a in A
                            if value(w[a]) ≈ 1.0
                                push!(solcut, a)
                            end
                        end
                        ncuts += 1
                        if relaxation
                            @constraint(master, sum(x[a] for a in solcut) ≥ k + 1)
                        else
                            cut = @build_constraint(sum(x[a] for a in solcut) ≥ k + 1)
                            MOI.submit(master, MOI.LazyConstraint(cbdata), cut)
                        end
                    end
                end
                return ncuts
            end
        end
        if occursin("BPC", ineq)
            separation = BilevelModel(() -> Gurobi.Optimizer(env))           # not yet solvable by BiLevelJuMP package
            set_silent(separation)
            set_time_limit_sec(separation, 600.0)
            @variable(Upper(separation), w[a in A] ≥ 0)
            @variable(Upper(separation), y[i in V], Bin)
            @constraint(Upper(separation), [a in A], w[a] ≥ y[a[1]] - y[a[2]])
            @constraint(Upper(separation), fix, y[depot] == 0)
            @variable(Lower(separation), z[i in Vc, k in K], Bin)
            @variable(Lower(separation), r[K], Bin)
            @constraint(Lower(separation), [i in Vc], sum(z[i, k] for k in K) == y[i])
            @constraint(Lower(separation), [i in Vc, k in K], z[i, k] ≤ r[k])
            @constraint(Lower(separation), [k in K], sum(q[i] * z[i, k] for i in Vc) ≤ Q * r[k])
            @objective(Lower(separation), Min, sum(r[K]))

            function BinPackingCuts(xval, cbdata)        # exact separation for Bin Packing Cuts (bilevel optimization problem)
                ncuts = 0
                @objective(Upper(separation), Min, sum(xval[a] * w[a] for a in A) - sum(r[K]))
                optimize!(separation)
                if objective_value(separation) < -VIOLA
                    solcut = Tuple{Int,Int}[]
                    for a in A
                        if value(w[a]) ≈ 1.0
                            push!(solcut, a)
                        end
                    end
                    ncuts += 1
                    if relaxation
                        @constraint(master, sum(x[a] for a in solcut) ≥ sum(value(r[K])))
                    else
                        cut = @build_constraint(sum(x[a] for a in solcut) ≥ sum(value(r[K])))
                        MOI.submit(master, MOI.LazyConstraint(cbdata), cut)
                    end
                end
                return ncuts
            end
        end

        function CutSeparation(cbdata)
            xval = ( relaxation ? value.(x) : callback_value.(Ref(cbdata), x) )
            ncuts = 0
            if occursin("SEC", ineq)
                ncuts += SubtourEliminationCuts(xval, cbdata)
            end
            if occursin("FCC", ineq)
                ncuts += FractionalCapacityCuts(xval, cbdata)
            end
            if occursin("RCC", ineq)
                ncuts += RoundedCapacityCuts(xval, cbdata)
            end
            if occursin("BPC", ineq)
                ncuts += BinPackingCuts(xval, cbdata)
            end
            iterations += 1
            tcuts += ncuts
            return ncuts
        end

        set_silent(master)
        #set_time_limit_sec(master, 10.0)
        if relaxation
            ncuts = 1
            while ncuts > 0
                optimize!(master)
                ncuts = CutSeparation(0)
            end
        else
            MOI.set(master, MOI.LazyConstraintCallback(), CutSeparation)
            optimize!(master)
        end

        @printf "CVRP %s %16s B&C solved:  status=%10s  ObjVal=%10.4f  Time=%5.2f  iter=%4d  cuts=%5d \n" (relaxation ? "LP" : "IP") ineq termination_status(master) objective_value(master) solve_time(master) iterations tcuts
        @printf io " %s %16s B&C %12.4f %12.2f %5d %5d" (relaxation ? "LP" : "IP") ineq objective_value(master) solve_time(master) iterations tcuts
        return objective_value(master)
    end

    function CVRPBranchAndPrice(cutting)
        tcols = trows = tcuts = 0

        coluna = JuMP.optimizer_with_attributes(
            Coluna.Optimizer,
            "params" => Coluna.Params(solver=Coluna.Algorithm.BranchCutAndPriceAlgorithm()),
            "default_optimizer" => Gurobi.Optimizer
        )

        master = BlockModel(coluna)
        #set_silent(master)
        #set_time_limit_sec(master, 600.0)
        @axis(Vehicle, [1])
        @variable(master, x[Vehicle, A], Bin)
        @objective(master, Min, sum(c[a[1], a[2]] * x[1, a] for a in A))
        @constraint(master, covering[i in Vc], sum(x[1, Aou[i]]) == 1)
        @dantzig_wolfe_decomposition(master, dec, Vehicle)

        ########################################################################################
        #  Pricing Callback                                                                    #
        ########################################################################################

        pricing = Model(() -> Gurobi.Optimizer(env)) #HiGHS.Optimizer())
        set_silent(pricing)
        #        set_time_limit_sec(pricing, 600.0)
        @variable(pricing, z[A], Bin)
        @variable(pricing, y[Vc], Bin)
        @variable(pricing, u[Vc])
        @constraint(pricing, sum(z[Aou[depot]]) == 1)
        @constraint(pricing, sum(z[Ain[depot]]) == 1)
        @constraint(pricing, [i in Vc], sum(z[Aou[i]]) == y[i])
        @constraint(pricing, [i in Vc], sum(z[Ain[i]]) == y[i])
        @constraint(pricing, sum(q[i] * y[i] for i in Vc) ≤ Q)
        @constraint(pricing, [i in Vc, j in Vc; i != j], u[j] ≥ u[i] + z[(i, j)] - (n - 2) * (1 - z[(i, j)]) + (n - 3) * z[(j, i)])

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

        if cutting
            ########################################################################################
            #  Rounded Capacity Cuts                                                               #
            ########################################################################################

            separation = Model(() -> Gurobi.Optimizer(env)) #HiGHS.Optimizer())
            set_silent(separation)
            #           set_time_limit_sec(separation, 600.0)
            @variable(separation, w[A] ≥ 0)
            @variable(separation, y[V], Bin)
            @variable(separation, M ≥ 0, Int)
            @constraint(separation, [a in A], w[a] ≥ y[a[1]] - y[a[2]])
            @constraint(separation, sum(q[i] * y[i] for i in Vc) ≥ M * Q + 1)
            @constraint(separation, fix, y[depot] == 0)

            function CapacityCuts(cbdata)        # exact separation for ROUNDED Capacity Cuts
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
                    solcut = Tuple{Int,Int}[]
                    if objective_value(separation) < k + 1 - VIOLA
                        for a in A
                            if value(w[a]) ≈ 1.0
                                push!(solcut, a)
                            end
                        end
                        cut = @build_constraint(sum(x[1, a] for a in solcut) ≥ k + 1)
                        MOI.submit(master, MOI.UserCut(cbdata), cut)
                        tcuts += 1
                    end
                end
            end
            MOI.set(master, MOI.UserCutCallback(), CapacityCuts)
        end

        optimize!(master)
        @printf "CVRP IP  B&P&%s:  status=%s  ObjVal=%10.4f  Time=%5.2f  pricings=%5d  separations=%5d  cuts=%4d\n" docut termination_status(master) objective_value(master) solve_time(master) tcols trows tcuts
        @printf io "IP  B&P&%s %12.4f %12.2f %5d %5d %5d" docut objective_value(master) solve_time(master) tcols trows tcuts
        return objective_value(master)
    end

    CVRPCutAndBranch()
    List = ["VRP-DECOMP + TSP-MTZ", "VRP-DECOMP + PRED", "VRP-DECOMP + TSP-MCF",
        "VRP-PRED", "VRP-SCF", "VRP-MTZ",
        "VRP-MCF1a", "VRP-MCF1b", "VRP-MCF1a-MCF1b",
        "VRP-MCF2a", "VRP-MCF2b", "VRP-MCF2c",
        "VRP-MCF2a-MCF2b", "VRP-MCF2a-MCF2c", "VRP-MCF2b-MCF2c", "VRP-MCF2aMCF2bMCF2c", "VRP-MCF3"]
        for l in List
            CVRPCompactModel(l, true)
        end
    CVRPBranchAndCut("SEC", true)     # Branch-and-Cut
    CVRPBranchAndCut("FCC", true)     # Branch-and-Cut
    CVRPBranchAndCut("RCC", true)     # Branch-and-Cut
    #CVRPBranchAndPrice(false)   # Branch-and-Price
    #CVRPBranchAndPrice(true)    # Branch-and-Cut-and-Price
end

List = [
    "E-n13-k4", "E-n22-k4", "E-n23-k3", "E-n30-k3", "E-n31-k7", "E-n33-k4",
    "P-n16-k8", "P-n19-k2", "P-n20-k2", "P-n21-k2", "P-n22-k2", "P-n22-k8", "P-n23-k8",
    "A-n32-k5", "A-n33-k5", "A-n33-k6", "A-n34-k5", "A-n36-k5", "A-n37-k5", "A-n37-k6", "A-n38-k5", "A-n39-k5", "A-n39-k6",
    "B-n31-k5", "B-n34-k5", "B-n35-k5", "B-n38-k6", "B-n39-k5"
]

#for instance in List
instance = "E-n22-k4"
global io = open("statistics.txt", "a")
@printf io "\n %20s " instance
SolveCVRP(instance)
close(io)
#end