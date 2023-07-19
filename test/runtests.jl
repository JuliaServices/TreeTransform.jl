using TreeTransform: bottom_up_rewrite
using Test
using Random
using Rematch2: Rematch2, @match2
using AutoHashEqualsCached

include("types.jl")

@testset "TreeTransform.jl tests" begin
    include("bottom_up_rewrite_test.jl")
end
