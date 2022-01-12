# roulette-tree

A red-black tree.  For didactic purposes.

## VecTree

A red-black tree implemented by holding nodes in a `Vec`.

Pointers are implemented as `Option<usize>`; `usize` is just an index into the inner `Vec`.

The implementation of this red-black tree does not actually delete nodes.  It instead leaks them.
Therefore this tree is best used when you need to insert and update objects, but not remove them - a tree that only grows.
In this sense it functions like an arena-allocated tree, which may be good if you only want to use it to store data,
and deallocate it entirely all at once.

Why use a Vec over pointers and heap allocation?  Well, pointers (dynamic object creation) are less performant and heap allocation struggles to exploit the cache.  We might lose the ability to deallocate individual elements, but we gain the ability of a fast linear search (which excels for small trees with little deletions), instant indexing of the tree, a quick determination of length, etc.

Read https://doc.rust-lang.org/std/collections/struct.BTreeMap.html for more information.  Note that while the same idea applies (try to exploit the cache), a B-tree is considerably different in representation than a red-black tree, with a red-black tree being a genuine binary search tree (albeit balanced), and the B-tree being superior in almost every way.  Nonetheless, one can demonstrate that red-black trees are a subset of B-trees by moving red nodes up to join their parents in a 2/3-node.

For more information about B-trees and Rust's implementation of them in the standard library, see Alexis' own blog: https://cglab.ca/~abeinges/blah/rust-btree-case/
