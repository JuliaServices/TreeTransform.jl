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

# We make a couple of these mutable so that equality can have a fast path
# using ===, making the expansionary test run in a reasonable time.
@auto_hash_equals mutable struct B1; x; y; end
@auto_hash_equals_cached struct B2; x; y; end
@auto_hash_equals mutable struct B3; x; y; end
@auto_hash_equals mutable struct B4; x; y; end
@auto_hash_equals_cached struct B5; x; y; end
@auto_hash_equals_cached struct B6; x; y; end
