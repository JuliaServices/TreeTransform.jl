module JuliaExpr

using Rematch2: @match2
using TreeTransform: bottom_up_rewrite, TreeTransform
using Test

# Deriv(x, e) = Expr(:deriv, [x, e])

struct Deriv
    name::Symbol
    expr::Any
end

function xform(node)
    println("--------------------")
    dump(node)
    @match2 node begin
        Expr(:call, [:+, a::Number, b::Number]) => a + b

        Expr(:call, [:*, a::Number, b::Number]) => a * b

        Expr(:call, [:*, 0, a]) => 0
        Expr(:call, [:+, 0, a]) => a

        Expr(:call, [:+, a, b::Number]) => :(b + a)
        Expr(:call, [:*, a, b::Number]) => :(b * a)

        # a + b + c + ... => (a + b) + c + ....
        Expr(:call, [:+, a, b, c, xs...]) => Expr(:call, :+, :($a + $b), c, xs...)

        # a^2 = a * a
        Expr(:call, [:^, a, 2]) => :($a * $a)

        # a + (b + c) => (a + b) + c
        Expr(:call, [:+, a, Expr(:call, [:+, b, c])]) => :(($a + $b) + $c)

        # a * (b * c) => (a * b) * c
        Expr(:call, [:*, a, Expr(:call, [:*, b, c])]) => :(($a * $b) * $c)

        # (a + b) * c => (a * c) + (b * c)
        Expr(:call, [:*, Expr(:call, [:+, a, b]), c]) => :($a * $c + $b * $c)

        # a * (b + c) => (a * b) + (a * c)
        Expr(:call, [:*, a, Expr(:call, [:+, b, c])]) => :($a * $b + $a * $c)

        # deriv x (a + b) => deriv x a + deriv x b
        Deriv(x, Expr(:call, [:+, a, b])) => :($(Deriv(x, a)) + $(Deriv(x, b)))

        # deriv x (a * b) => a * deriv x b + b * diff x a
        # deriv x x => 1
        Deriv(x, x::Symbol) => 1

        # deriv x y => 0
        Deriv(x, y::Symbol) where x != y => 0

        x => x
    end
end

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
    @test simplify(:(x * (0 + y))) == :(x * y)
    @test simplify(:(a + b + c + d)) == :(((a + b) + c) + d)

    @test simplify(Deriv(:a, :a)) == 1
    @test simplify(Deriv(:a, :(a + b))) == 1
end

end
