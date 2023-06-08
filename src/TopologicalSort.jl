# Compute a topological ordering of a set of nodes reachable from the given
# roots by the given successor function.
function topological_sort(roots::AbstractVector{Any})
    # Compute pred_counts, the number of predecessors of each node
    pred_counts = Dict{Any, Int}()
    counted = Set{Any}()
    to_count = Vector{Any}(roots)

    # broken into a separate function to permit specialization on F and N.
    function tocount_successors(node::N) where { N }
        for name in fieldnames(N)
            @inbounds succ = getfield(node, name)
            push!(to_count, succ)
            pred_counts[succ] = get(pred_counts, succ, 0) + 1
            # println("pred count: $(pred_counts[succ]) for $succ")
        end
    end
    function tocount_successors(node::AbstractArray{N}) where { N }
        for succ::N in node
            push!(to_count, succ)
            pred_counts[succ] = get(pred_counts, succ, 0) + 1
            # println("pred count: $(pred_counts[succ]) for $succ")
        end
    end

    while !isempty(to_count)
        node = pop!(to_count)
        node in counted && continue
        push!(counted, node)
        get!(pred_counts, node, 0) # make sure every node has a pred count
        tocount_successors(node)
    end

    # Prepare a ready set of nodes to output that have no predecessors
    ready = Any[k for (k, v) in pred_counts if v == 0]
    result = Any[]
    sizehint!(result, length(pred_counts))

    function decrement_pred_count(@nospecialize(node))
        count = pred_counts[node]
        @assert count > 0
        count -= 1
        pred_counts[node] = count
        count == 0 && push!(ready, node)
    end

    # remove the node by decrementing the predecessor counts of its successors
    function remove_node(node::N) where { N }
        for name in fieldnames(N)
            @inbounds succ = getfield(node, name)
            decrement_pred_count(succ)
        end
    end
    function remove_node(node::AbstractArray{N}) where { N }
        for succ::N in node
            decrement_pred_count(succ)
        end
    end

    while !isempty(ready)
        node = pop!(ready)
        push!(result, node)
        remove_node(node)
    end

    # all of the nodes should have been output by now.  Otherwise there was a cycle.
    if length(pred_counts) != length(result)
        error("graph had a cycle involving ", N[k for (k, v) in pred_counts if v != 0], ".")
    end

    result
end
