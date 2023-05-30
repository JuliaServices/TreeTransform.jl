using Rematch2: @match2
using TreeTransform: bottom_up_rewrite, TreeTransform
using AutoHashEqualsCached

abstract type Expression end
struct Add <: Expression
    s::Vector{Expression}
end
Base.:(==)(x::Add, y::Add) = x.s == y.s
Add(e::Expression...) = Add(Expression[e...])
struct Sub <: Expression
    x::Expression
    y::Expression
end
struct Neg <: Expression
    x::Expression
end
struct Mul <: Expression
    x::Expression
    y::Expression
end
struct Div <: Expression
    x::Expression
    y::Expression
end
struct Const <: Expression
    value::Float64
end
struct Variable <: Expression
    name::Symbol
end

function xform(node)
    @match2 node begin
        # identity elements
        Const(-0.0)        => Const(0.0)
        Add([Const(0.0), x]) => x
        Add([x, Const(0.0)]) => x
        Sub(x, Const(0.0)) => x
        Mul(Const(1.0), x) => x
        Mul(x, Const(1.0)) => x
        Div(x, Const(1.0)) => x
        Mul(Const(0.0) && x, _) => x
        Mul(_, x && Const(0.0)) => x
        # constant folding
        Add([Const(x), Const(y)]) => Const(x + y)
        Sub(Const(x), Const(y)) => Const(x - y)
        Neg(Const(x))           => Const(-x)
        Mul(Const(x), Const(y)) => Const(x * y)
        Div(Const(x), Const(y)) => Const(x / y)
        # Algebraic Identities
        Sub(x, x)               => Const(0.0)
        Neg(Neg(x))             => x
        Sub(x, Neg(y))          => Add(x, y)
        Add([x, Neg(y)])          => Sub(x, y)
        Add([Neg(x), y])          => Sub(y, x)
        Neg(Sub(x, y))          => Sub(y, x)
        Add([x, x])               => Mul(x, Const(2.0))
        Add([x, Mul(Const(k), x)])=> Mul(x, Const(k + 1))
        Add([Mul(Const(k), x), x])=> Mul(x, Const(k + 1))
        # Move constants to the left
        Add([x, k::Const])        => Add(k, x)
        Mul(x, k::Const)        => Mul(k, x)
        # Move negations up the tree
        Sub(Const(0.0), x)      => Neg(x)
        Sub(Neg(x), y)          => Neg(Add(x, y))
        Mul(Neg(x), y)          => Neg(Mul(x, y))
        Mul(x, Neg(y))          => Neg(Mul(x, y))
        x                       => x
    end
end

function simplify(node)
    bottom_up_rewrite(xform, node)
end

@testset "Check some simple cases" begin
    x = Variable(:x)
    y = Variable(:y)

    @test simplify(Sub(x, Neg(y))) == Add(x, y)
    @test simplify(Add(x, Neg(y))) == Sub(x, y)
end

@testset "Check some complex cases" begin
    x = Variable(:x)
    y = Variable(:y)
    z = Variable(:z)
    zero = Const(0.0)
    one = Const(1.0)

    e1 = Add(zero, x)
    e2 = Add(x, zero)
    e3 = Sub(x, zero)
    e4 = Mul(one, y)
    e5 = Mul(y, one)
    e6 = Div(z, one)
    e7 = Add(Const(3), Const(4))
    e8 = Sub(Const(5), Const(6))
    e9 = Neg(e7)
    e10 = Mul(e8, e9)
    e11 = Div(e10, Add(one, one))
    e12 = Neg(Neg(e1))
    e13 = Sub(e2, Neg(e3))
    e14 = Add(e4, Neg(e5))
    e15 = Add(Neg(e6), e7)
    e16 = Neg(Sub(e8, e9))
    e17 = Sub(Neg(e10), e11)
    e18 = Add(Neg(e12), Neg(e13))
    e19 = Mul(Neg(e14), e15)
    e20 = Mul(e16, Neg(e17))
    e21 = Sub(Neg(e18), e19)
    e22 = Add(e20, Neg(e21))
    expr = e22

    # The expected results of simplification
    expected = Sub(Const(-63.0), Mul(Const(3.0), x))

    @test simplify(expr) == expected
end

# We make a couple of these mutable so that equality can have a fast path
# using ===, making the expansionary test below run in a reasonable time.
@auto_hash_equals mutable struct B1; x; y; end
@auto_hash_equals_cached struct B2; x; y; end
@auto_hash_equals mutable struct B3; x; y; end
@auto_hash_equals mutable struct B4; x; y; end
@auto_hash_equals_cached struct B5; x; y; end
@auto_hash_equals_cached struct B6; x; y; end

@testset "Check that recursive rewrites occur for new children" begin
    function xform2(node)
        @match2 node begin
            B1(B2(x, y), B3(z, w)) => B5(B6(x, y), B6(z, w))
            B4(x, y)               => 1
            B5(1, 1)               => 2
            B6(x, y)               => B4(x, y)
            x                      => x
        end
    end
    value = B1(B2(:a, :b), B3(:c, :d))
    expected = 2
    @test bottom_up_rewrite(xform2, value) == expected
end

@testset "Check that rewrites occur at the leaves even if the root is good" begin
    function xform3(node)
        @match2 node begin
            B1(x, y)               => B2(x, y)
            x                      => x
        end
    end
    value =    B3(B4(:a, B1(1, 2)), B5(:c, B1(:a, :b)))
    expected = B3(B4(:a, B2(1, 2)), B5(:c, B2(:a, :b)))
    @test bottom_up_rewrite(xform3, value) == expected
end

@testset "Check that simple cycles are detected" begin
    function xform3(node)
        @match2 node begin
            B1(x, y)               => B2(x, y)
            B2(x, y)               => B1(y, x)
            x                      => x
        end
    end
    value =    B3(B4(:a, B1(1, 2)), B5(:c, B1(:a, :b)))
    @test_throws ErrorException bottom_up_rewrite(xform3, value;
        :max_transformations_per_node => 0, :detect_cycles => true)
end

@testset "Check that expansionary cycles are detected" begin
    function xform3(node)
        @match2 node begin
            B1(x, y)               => B2(x, y)
            B2(x, y)               => B1(B3(x, y), B4(x, y))
            x                      => x
        end
    end
    value =    B1(:a, :b)
    @test_throws ErrorException bottom_up_rewrite(xform3, value;
        :max_transformations_per_node => 5, :detect_cycles => false)
end

@testset "Check some Expr simplification" begin
    function xform4(node)
        @match2 node begin
            Expr(:call, [:+, a::Number, b::Number]) => a + b
            Expr(:call, [:+, a, b, c]) => Expr(:call, :+, :($a + $b), c)
            x => x
        end
    end

    function simplify(node)
        bottom_up_rewrite(xform4, node)
    end

    @test simplify(:(5 + 3)) == :(8)
    @test simplify(:(5 + 3 + 100)) == :(108)
end
