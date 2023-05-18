using TreeTransform
using Documenter

DocMeta.setdocmeta!(TreeTransform, :DocTestSetup, :(using TreeTransform); recursive=true)

makedocs(;
    modules=[TreeTransform],
    authors="Neal Gafter <neal@gafter.com> and contributors",
    repo="https://github.com/?/TreeTransform.jl/blob/{commit}{path}#{line}",
    sitename="TreeTransform.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://?.github.io/TreeTransform.jl",
        edit_link="main",
        assets=String[],
    ),
    pages=[
        "Home" => "index.md",
    ],
)

deploydocs(;
    repo="github.com/?/TreeTransform.jl",
    devbranch="main",
)
