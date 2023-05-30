module JuliaExpr

using Rematch2: @match2
using TreeTransform: bottom_up_rewrite, TreeTransform
using Test

function xform(node)
    @match2 node begin
        Expr(:call, [:+, a::Number, b::Number]) => a + b
        Expr(:call, [:+, a, b, c, xs...]) => Expr(:call, :+, :($a + $b), c, xs...)
        Expr(:call, [:^, a, 2]) => :($a * $a)

        # a + (b + c) = (a + b) + c
        Expr(:call, [:+, a, Expr(:call, [:+, b, c])]) => :(($a + $b) + $c)

        # a * (b * c) = (a * b) * c
        Expr(:call, [:*, a, Expr(:call, [:*, b, c])]) => :(($a * $b) * $c)

        # (a + b) * c = (a * c) + (b * c)
        Expr(:call, [:*, Expr(:call, [:+, a, b]), c]) => :($a * $c + $b * $c)

        # a * (b + c) = (a * b) + (a * c)
        Expr(:call, [:*, a, Expr(:call, [:+, b, c])]) => :($a * $b + $a * $c)

        x => x
    end
end

#	x*(y+z)	= x*y+x*z;
# x+(y+z)	= (x+y)+z;	x*(y*z)	= (x*y)*z;

function simplify(node)
    bottom_up_rewrite(xform, node)
end

@testset "Check some simple cases" begin
    @test simplify(:(5 + 3)) == 8
    @test simplify(:(5 + 3 + 100)) == 108
    @test simplify(:(5 + (3 + 100))) == 108
    @test simplify(:(5 + 3 + 100 + 1000)) == 1108
    @test simplify(:(x + (y + z))) == :((x + y) + z)
    @test simplify(:(x * (y * z))) == :((x * y) * z)
    @test simplify(:(x * (y + z))) == :((x * y) + (x * z))
    @test simplify(:(a + b + c + d)) == :(((a + b) + c) + d)
end

end
