// The Computer Language Benchmark Game
// https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
//
// contributed by Ralph Ganszky
// *reset*

import Dispatch
import Foundation

class TreeNode {
    var left, right: TreeNode?

    init(left: TreeNode?, right: TreeNode?) {
        self.left = left
	self.right = right
    }

    func check() -> Int {
	if left != nil {
	    return left!.check() + right!.check() + 1
	} else {
	    return 1
	}
    }
}

func createTree(_ depth: Int) -> TreeNode? {
    if depth > 0 {
	let node = TreeNode(left: createTree(depth-1),
			    right: createTree(depth-1))
	return node
    } else {
	let node = TreeNode(left: nil, right: nil)
	return node
    }
}

let n: Int
if CommandLine.argc > 1 {
    n = Int(CommandLine.arguments[1]) ?? 10
} else {
    n = 10
}
let minDepth = 4
let maxDepth = (n > minDepth + 2) ? n : minDepth + 2

// Create big tree in first pool
let tree = createTree(maxDepth+1)
let check = tree!.check()
print("stretch tree of depth \(maxDepth+1)\t check: \(check)")

// Cleal first pool and allocate long living tree
let longLivingTree = createTree(maxDepth)

// Allocate binary trees of increasing depth up to maxDepth depth
let group = DispatchGroup()
let rq = DispatchQueue(label: "Result", attributes: [])
let queue = DispatchQueue(label: "Worker", attributes: .concurrent)
var results = [String](repeating: "", count: (maxDepth-minDepth)/2+1)
for currentDepth in stride(from: minDepth, through: maxDepth, by: 2) {
    queue.async(group: group) {
        let idx = (currentDepth - minDepth) / 2
	let iterations = 1 << (maxDepth - currentDepth + minDepth)
	var totalChecksum = 0
	for i in 1...iterations {
	    let tree1 = createTree(currentDepth)
	    totalChecksum += tree1!.check()
	}
	rq.async{
	    results[idx] = "\(iterations)\t trees of depth \(currentDepth)\t check: \(totalChecksum)"
	}
    }
}
group.wait()

rq.sync {
    for result in results {
	print(result)
    }
}

// Check long living tree and print out check info
print("long lived tree of depth \(maxDepth)\t check: \(longLivingTree!.check())")

