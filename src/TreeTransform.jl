module TreeTransform

export bottom_up_rewrite, no_transform

include("TopologicalSort.jl")

# const fields only suppored >= Julia 1.8
macro _const(x)
    if VERSION >= v"1.8"
        Expr(:const, esc(x))
    else
        esc(x)
    end
end

dropfirst(a) = a[2:length(a)]

"""
    no_transform(node::Type) = true

Override this function to return true for any types that should not be transformed.
"""
no_transform(node) = false

function enumerate_children end
function enumerate_unprocessed_children end

# The state of the transformation is maintained in an instance of this struct.
mutable struct RewriteContext
    # The user's transformation function.
    @_const xform_fcn::Function

    # If true, we are detecting cycles of the first kind.
    @_const detect_cycles::Bool

    # If positive, the number of individual node transformations before we
    # throw an exception indicating a likely cycle.
    remaining_transformations::Int

    # A function to enumerate all children of a node.
    @_const enumerate_children_fcn::Function

    # A function to enumerate all children of a node that are not already fixed_points.
    @_const enumerate_unprocessed_children_fcn::Function

    # A map from each node to a fixed point for that node.  A node that
    # is a fixed point would also appear in this map, and map to itself.
    @_const fixed_points::IdDict{Any, Any}

    function RewriteContext(
        xform::Function,
        detect_cycles::Bool,
        max_transformations::Int,
        enumerate_children_fcn = enumerate_children)
        fixed_points = IdDict{Any, Any}()
        enumerate_unprocessed_children_fcn = node -> enumerate_unprocessed_children(node, enumerate_children_fcn, fixed_points)
        new(xform, detect_cycles, max_transformations, enumerate_children_fcn, enumerate_unprocessed_children_fcn, fixed_points);
    end
end

"""
    bottom_up_rewrite(
        xform::Function,
        data;
        detect_cycles::Bool = false,
        max_transformations::Int = 0)

Given a data structure (`data`) that does not contain cycles, we
apply a given transformation function (`xform`) at every node, and
return a new data structure with all possible transformations
applied.  Note that the result is a data structure in which every
node is a fixed-point of the transformation function provided.

By default, we do not detect cycles in the applied transformations.
There are two kinds of cycles that can occur: first, if some sequence
of transformations result in the same data structure.  Second, if
the transformation function produces additional nodes that were not
in the previous data structure, and additional rules apply to the
new nodes.

We offer two mechanisms to detect cycles.  First, we can detect the
simple cycles of the first kind automatically, but at additional
cost.  You can enable this by setting `detect_cycles` to `true`.
Second, you can give a limit on the number of transformations to
apply per node in the original data structure.  You can enable this
by setting `max_transformations` to a positive integer.  For example,
you set `max_transformations` to 3 and the original data structure
contained 100 nodes, then we will only apply 300 distinct non-identity
node transformations anywhere in the graph before throwing an
exception.

The `transform` function should take a single argument, the node
to transform, and return a transformed version of that node.  The
`transform` function should not modify the original node.  If no
transformation applies to a node, then the `transform` function
should return the original node.

The nodes of the data structure can be of arbitrary Julia struct
types, but the data structure as a whole must be a directed acyclic
graph, i.e., it must not contain cycles.  The implementation examines
the set of constructors of the nodes, and the set of fields that
correspond to the parameters of each constructor.  We only consider
constructors that are not vararg, have no keyword arguments, and
whose parameter names all correspond to fields of the node type.
We take the constructor(s) with the longest parameter list with
these properties.  We throw an exception if there are more than one
and they name different fields or in different orders. Finally, we
use such a unique order to determine the children nodes to which
we will apply the transformation function.  That constructor will
be called to rewrite the parent node if any transformed child is
different from the original child.

The implementation keeps track of which nodes have reached a
fixed-point, so that we can perform the minimum number of
transformations.  We also keep track of the number of transformations
applied to each node, so that we can detect cycles of the second
kind.

This facility is less general than the E-graph approach, but it is
(hopefully) more efficient and easier to use when it applies.  The
E-graph approach can handle cycles, but it is more expensive and
requires more work to set up. See also "Metatheory.jl: Fast and
Elegant Algebraic Computation in Julia with Extensible Equality
Saturation" by Alessandro Cheli, 2021, <https://arxiv.org/abs/2102.07888>

You can specialize the behavior for some nodes, e.g. to force child
nodes to be visited in a particular order.  For example, if you
have a node that represents the conjunction of two boolean expressions,
you might want to force the left child to be visited before the
right child, and then if the left child is `false`, you can skip
the right child.  You can also use this to skip rewriting of certain
child nodes.  **The way to do this is not yet defined.**
"""
function bottom_up_rewrite(
    xform::Function,
    data;
    enumerate_children_fcn = enumerate_children,
    detect_cycles::Bool = false,
    max_transformations::Int = 0
)

    # Build a work queue as a list of nodes to be transformed.  Since we are
    # doing a bottom-up transformation, we start with the leaves of the graph
    # as determined by a topological_sort of the nodes reachable from the root.
    # That way, when we get to higher levels in the dag, we will have already
    # transformed the children.  However, when new child nodes are built, they
    # will have to be visited again.
    nodes = topological_sort(enumerate_children_fcn, Any[data])

    # We use a mutable struct to hold the state of the transformation.
    # This is a bit of a hack (says CoPilot), but it is the easiest way to pass
    # around the state of the transformation without having to pass
    # around a lot of arguments.
    ctx = RewriteContext(xform, detect_cycles, max_transformations * length(nodes))

    # Process each node to compute its fixed-point.
    fixed_points(ctx, nodes)

    result = ctx.fixed_points[data]
    result
end

function enumerate_children_names(type::Type{T}) where { T }
    # We only consider constructors that are not vararg, have no keyword arguments,
    # and whose parameter names all correspond to fields of the node type.
    # We take the constructor(s) with the longest parameter list with these properties.
    # We throw an exception if there are more than one and they name different fields
    # or in different orders.

    members = fieldnames(type)

    # Search for constructor methods that have no keyword parameters, and are not varargs.
    meths = Method[methods(type)...]
    meths = filter(m -> !m.isva && length(Base.kwarg_decl(m))==0, meths)
    # drop the implicit var"#self#" argument
    argnames_list = map(m -> dropfirst(Base.method_argnames(m)), meths)
    # narrow to arg lists where all parameter names correspond to members
    argnames_list = unique(filter(l -> all(n -> n in members, l), argnames_list))
    # find the longest such arg list
    isempty(argnames_list) && return Symbol[]
    len = maximum(map(length, argnames_list))
    argnames_list = filter(l -> length(l) == len, argnames_list)

    if length(argnames_list) == 1
        # found a uniquely satisfying order for member names
        return only(argnames_list)
    elseif len == length(members)
        # no unique constructor, but the correct number of fields exist; use them
        return vcat(members)
    else
        # no unique constructor, and not all fields are used.  Throw an error when
        # a node is encountered.
        return :(error("Cannot infer an order in which to construct the children of $(type)."))
    end
end

# TODO: make this @generated
function enumerate_children(node::T) where { T }
    node_type = typeof(node)
    member_names = enumerate_children_names(node_type)
    Any[getfield(node, m) for m in member_names]
end

# Rebuild the node with revised children, if any
# If no children have changed, then return the original node.
# A prerequisite to calling this function is that all children must
# have had their fixed-point value recorded in ctx.fixed_points.
# @generated function rebuild_node(ctx::RewriteContext, node::T) where { T }
#     # Generate type-specific code to rebuild the node in case children have changed.

#     # Note: since this is a @generated function, node is actually the type of the arg.
#     node_type = node
#     member_names = enumerate_children_names(node)
#     length(member_names) == 0 && return :(node)

#     result_expression = Expr(:block)
#     code = result_expression.args

#     # Cache the fields and their translations in local variables.
#     cached_translations = map(m -> Symbol(m, "'"), member_names)
#     for (m, t) in zip(member_names, cached_translations)
#         push!(code, :(local $m = getfield(node, $m)))
#         push!(code, :(local $t = ctx.fixed_points[$m]))
#     end
#     # Determine if any have changed and, if so, reconstruct.
#     any_changed = mapreduce(
#         ((m, t),) -> :($m !== $t), (a,b) -> :($a || $b), zip(member_names, cached_translations))
#     rebuild = :($node_type($(cached_translations)...))
#     result = :($any_changed ? $rebuild : $node)
#     push!(code, result)
#     result_expression
# end
function rebuild_node(ctx::RewriteContext, node::T) where { T }
    no_transform(node) && return node
    node_type = typeof(node)
    member_names = enumerate_children_names(node_type)
    length(member_names) == 0 && return node
    fields = map(m -> getfield(node, m), member_names)
    cached_translations = map(m -> no_transform(m) ? m : ctx.fixed_points[m], fields)
    any_changed = any(map((m,t) -> m !== t, fields, cached_translations))
    return any_changed ? node_type(cached_translations...) : node
end

function enumerate_unprocessed_children(
        node::T,
        enumerate_children_fcn::Function,
        fixed_points::IdDict{Any, Any}) where { T }
    filter(enumerate_children_fcn(node)) do c
        get(fixed_points, c, :var"##an_unlikely_value##") !== c
    end
end

# Transform a node by applying a single iteration of the transformation function
function xform(ctx::RewriteContext, data)
    if ctx.remaining_transformations > 0 && (ctx.remaining_transformations -= 1) == 0
        error("Too many transformations.  Perhaps there is an expansionary cycle in the rewrite rules.")
    end
    ctx.xform_fcn(data)
end

# Transform a node by applying a single iteration of the transformation function,
# and then recursively transforming its newly built descendants until they each reach a
# fixed-point.  The top node, data, may not be at a fixed point after this is called.
function xformr(ctx::RewriteContext, data)
    res = xform(ctx, data)
    res === data && return res

    # There may be new children.  We need to process descendants recursively until they
    # have each reached a fixed-point.
    nodes = topological_sort(ctx.enumerate_unprocessed_children_fcn, Any[data])
    any_changes = fixed_points(ctx, dropfirst(nodes))

    # Rebuild the node with its new children if necessary.
    any_changes ? rebuild_node(ctx, res) : res
end

function fixed_points(ctx::RewriteContext, nodes)::Bool
    # Transform each node until it reaches a fixed-point.
    any_changes = false
    for node in reverse(nodes)
        # println("processing node ($(objectid(node))) $node")
        newnode = fixed_point(ctx, node, any_changes)
        if newnode !== node
            any_changes = true
        end
        @assert no_transform(node) || node in keys(ctx.fixed_points)
        @assert no_transform(newnode) || newnode in keys(ctx.fixed_points)
    end

    any_changes
end

# Transform the given node until it and each of its descendants reach a fixed-point.
function fixed_point(ctx::RewriteContext, node::T, any_changes::Bool) where { T }
    no_transform(node) && return node

    # if we already know the fixed-point for this node, return it
    if node in keys(ctx.fixed_points)
        return ctx.fixed_points[node]
    end

    rewritten = node
    if any_changes
        # In case children may have been revised, rebuild the node.
        rewritten = rebuild_node(ctx, node)
        # println("  rebuilt to ($(objectid(rewritten))) $rewritten")
        for child in ctx.enumerate_children_fcn(rewritten)
            @assert no_transform(child) || child in keys(ctx.fixed_points)
        end
    end

    # Apply a single transformation to the node, and then recursively transform
    # any new children to a fixed-point.  We don't apply further transformations
    # to the top-level node recursively because we want to avoid unnecessarily
    # deep recursion.  Instead we do it in a loop below.
    rewritten2 = xformr(ctx, rewritten)

    # If the transformation is an identity, then we are done.
    if rewritten2 === rewritten
        ctx.fixed_points[node] = rewritten
        ctx.fixed_points[rewritten] = rewritten
        # println("  rewritten to ($(objectid(node))) $node")
        return rewritten
    end

    # Prepare a dupicate-detection set, if needed to detect non-expansionary
    # cycles in the transformation.  We do this as late as possible, here, for perf.
    if ctx.detect_cycles
        duplicate_set = Set{Any}(node, rewritten, rewritten2)
    end
    rewritten = rewritten2

    # Continue transforming until we reach a fixed-point for this node
    while true
        rewritten2 = xformr(ctx, rewritten)
        if rewritten2 === rewritten
            ctx.fixed_points[node] = rewritten
            ctx.fixed_points[rewritten] = rewritten
            # println("  rewritten to ($(objectid(rewritten))) $rewritten")
            return rewritten
        end
        if ctx.detect_cycles
            if rewritten2 in duplicate_set
                error("Cycle detected in bottom_up_rewrite")
            end
            duplicate_set.add(rewritten2)
        end
        rewritten = rewritten2
    end

    # We should never get here
    error("Internal error in bottom_up_rewrite")
end

end
