using TreeTransform: topological_sort

# Given an array of node descriptions, each of which is a node name,
# and the name of successor nodes, construct a graph.  Return a successor
# function and a root node, which is the first node in the data.
function make_graph(data::Vector{Vector{T}}) where {T}
    succ = Dict()
    for node in data
        succ[node[1]] = node[2:end]
    end
    function successor(n)
        if n in keys(succ)
            return succ[n]
        else
            return []
        end
    end
    return (successor, data[1][1])
end

@testset "topological_sort tests" begin

    @testset "Test topological_sort 1" begin
        (succ, root) = make_graph([[1, 2, 3], [2, 3, 4]])
        @test topological_sort(succ, [root]) == [1, 2, 3, 4]
    end

    @testset "Test topological_sort 2" begin
        (succ, root) = make_graph([[1, 2, 3], [2, 3, 4], [3, 4, 5], [4, 5, 6], [5, 6, 7]])
        @test topological_sort(succ, [root]) == [1, 2, 3, 4, 5, 6, 7]
    end

    @testset "Test topological_sort 3" begin
        (succ, root) = make_graph([[5, 6, 7], [4, 5, 6], [3, 4, 5], [2, 3, 4], [1, 2, 3]])
        @test topological_sort(succ, [1]) == [1, 2, 3, 4, 5, 6, 7]
    end

    @testset "Test topological_sort 4" begin
        (succ, root) = make_graph([[5, 6, 7], [4, 5, 6], [3, 4, 5], [2, 3, 4], [1, 2, 3], [7, 1]])
        @test_throws ErrorException topological_sort(succ, [1]) == [1, 2, 3, 4, 5, 6, 7]
    end

end
