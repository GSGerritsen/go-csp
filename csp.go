package main

import (
	"fmt"
	"strconv"
)

const maximumDepth = 8

// Used to represent what variables exist at a given depth of the tree
var LetterDepth = map[int]string{
	1: "A",
	2: "B",
	3: "C",
	4: "D",
	5: "E",
	6: "F",
	7: "G",
	8: "H",
}

var LetterDepthWithHeuristic = map[int]string{
	1: "H",
	2: "F",
	3: "G",
	4: "D",
	5: "E",
	6: "C",
	7: "A",
	8: "B",
}

type Root struct {
	Children [4]*Node
	Depth    int
}

// Tombstone used to mark a dead end path with a constraint violation
type Node struct {
	Variable  *Variable
	Children  []*Node
	Tombstone bool
}

type Variable struct {
	Letter string
	Value  int
}

// Node constructor
func NewNode(variableLetter string) *Node {
	variable := NewVariable(variableLetter, 0)
	return &Node{variable, nil, false}
}

// Variable Constructor
func NewVariable(variableLetter string, value int) *Variable {
	return &Variable{variableLetter, value}
}

// Variable choice may depend on some heuristic, leaving it open to caller
func (root *Root) PopulateRoot(variableLetter string) {
	for i := 0; i < 4; i++ {
		variable := NewNode(variableLetter)
		root.Children[i] = variable
		root.Children[i].Variable.Value = i + 1
	}
}

func (node *Node) MarkTombstone() {
	node.Tombstone = true
}

// Where the real work goes on. On each call to GenerateTree(), the search space gets pruned, and then the next layer of variables gets added
// to any paths that haven't failed yet
func (root *Root) GenerateTree() {
	root.Prune()
	root.IncreaseSearchDepth()
}

func (root *Root) GenerateTreeWithHeuristic() {
	root.PruneWithHeuristic()
	root.IncreaseSearchDepthWithHeuristic()
}

// Generates a slice of slices. All of the inner slices are paths from the root to a leaf node.
// Example: [ [path1], [path2], [path3] ], where path-n is a slice of Nodes
func (root *Root) GeneratePaths() [][]*Node {
	var path []*Node
	var paths [][]*Node
	var getPaths func(node *Node, path []*Node) [][]*Node

	getPaths = func(node *Node, path []*Node) [][]*Node {
		if node == nil {
			return nil
		}
		path = append(path, node)

		if node.Children == nil {
			paths = append(paths, path)

		} else {
			for _, n := range node.Children {
				var nextPath []*Node
				nextPath = append(nextPath, path...)
				getPaths(n, nextPath)
			}
		}
		return paths
	}
	for _, child := range root.Children {
		getPaths(child, path)
	}
	//return getPaths(root.Children[0], path)
	return paths
}

// Generate all root-leaf paths in the search space, and for each one check if a constraint has been violated. If it has, mark
// the tombstone of the last node in that path to indicate a dead end. This path will no longer be expanded

func (root *Root) Prune() {
	paths := root.GeneratePaths()

	for i := 0; i < len(paths); i++ {
		if CheckConstraints(paths[i]) != true {
			paths[i][len(paths[i])-1].MarkTombstone()
		}
	}
}

func (root *Root) PruneWithHeuristic() {
	paths := root.GeneratePaths()

	for i := 0; i < len(paths); i++ {
		if CheckConstraintsUsingSelectionHeuristic(paths[i]) != true {
			paths[i][len(paths[i])-1].MarkTombstone()
		}
	}
}

// Assumes a node with no children yet assigned, and that variable only has its letter asigned, not value yet (which this function handles)
func (node *Node) AddVariableLayer(variableLetter string) {
	for i := 0; i < 4; i++ {
		newNode := NewNode(variableLetter)
		newNode.Variable.Value = i + 1
		node.Children = append(node.Children, newNode)
	}
}

// Recursive helper function
func RecursivelyAddVariableLayer(node *Node, variableLetter string) {
	// don't add a layer if we've marked this as a dead end
	if node.Children == nil && node.Tombstone != true {
		node.AddVariableLayer(variableLetter)
	} else {
		for _, n := range node.Children {
			RecursivelyAddVariableLayer(n, variableLetter)
		}
	}

}

// Increases depth of the search space by one, adding 4 new child nodes to each node whose tombstone is not marked, meaning we
// want to continue exploring this path for a model state.
func (root *Root) IncreaseSearchDepth() {
	if root == nil || root.Depth == 8 {
		return
	}
	root.Depth += 1
	variableToAssign := LetterDepth[root.Depth]
	for _, node := range root.Children {
		if node.Children == nil {
			node.AddVariableLayer(variableToAssign)
		} else {
			RecursivelyAddVariableLayer(node, variableToAssign)
		}
	}
}

func (root *Root) IncreaseSearchDepthWithHeuristic() {
	if root == nil || root.Depth == 8 {
		return
	}
	root.Depth += 1
	variableToAssign := LetterDepthWithHeuristic[root.Depth]
	for _, node := range root.Children {
		if node.Children == nil {
			node.AddVariableLayer(variableToAssign)
		} else {
			RecursivelyAddVariableLayer(node, variableToAssign)
		}
	}
}

// Here is where the constraints get checked:
// We switch on the length of the 'variables' input, which equals the depth of the tree at a given time.
// i.e, if len(variables) == 4, we know that we have (A, B, C, D), and can thus check constraints involving those variables
// As a reference:
// variables[0].Variable == A
// variables[1].Variable == B
// variables[2].Variable == C
// variables[3].Variable == D
// variables[4].Variable == E
// variables[5].Variable == F
// variables[6].Variable == G
// variables[7].Variable == H

func CheckConstraints(variables []*Node) bool {

	switch len(variables) {
	case 2:
		if variables[0].Variable.Value == variables[1].Variable.Value {
			return false
		}
	case 4:
		if variables[2].Variable.Value == variables[3].Variable.Value {
			return false
		}
	case 5:
		if variables[2].Variable.Value == variables[4].Variable.Value {
			return false
		}
		if variables[4].Variable.Value >= variables[3].Variable.Value-1 {
			return false
		}
	case 6:
		if AbsoluteValue(variables[5].Variable.Value-variables[1].Variable.Value) != 1 {
			return false
		}
		if variables[2].Variable.Value == variables[5].Variable.Value {
			return false
		}
		if variables[3].Variable.Value == variables[5].Variable.Value {
			return false
		}
		if AbsoluteValue(variables[4].Variable.Value-variables[5].Variable.Value)%2 == 0 {
			return false
		}
	case 7:
		if variables[0].Variable.Value <= variables[6].Variable.Value {
			return false
		}
		if AbsoluteValue(variables[6].Variable.Value-variables[2].Variable.Value) != 1 {
			return false
		}
		if variables[3].Variable.Value <= variables[6].Variable.Value {
			return false
		}
		if variables[6].Variable.Value == variables[5].Variable.Value {
			return false
		}
	case 8:
		if variables[0].Variable.Value > variables[7].Variable.Value {
			return false
		}
		if variables[6].Variable.Value >= variables[7].Variable.Value {
			return false
		}
		if AbsoluteValue(variables[7].Variable.Value-variables[2].Variable.Value)%2 != 0 {
			return false
		}
		if variables[7].Variable.Value == variables[3].Variable.Value {
			return false
		}
		if variables[4].Variable.Value == variables[7].Variable.Value-2 {
			return false
		}
		if variables[7].Variable.Value == variables[5].Variable.Value {
			return false
		}

	}
	return true
}

// Version with a selection heuristic. This one adds layers ordered by descending number of constraints
// that a given variable is involved in. H is involved in the most, followed by F, and so on, with B only being involved in 1 constraint.
// This way we can fail sooner than using the original A to H ordering.
// As an aside, I should figure out a more generic way to check constraints where the ordering can just be passed as an argument.
// Ordering: H, F, G, D, E, C, A, B.
// variables[0].Variable == H
// variables[1].Variable == F
// variables[2].Variable == G
// variables[3].Variable == D
// variables[4].Variable == E
// variables[5].Variable == C
// variables[6].Variable == A
// variables[7].Variable == B

func CheckConstraintsUsingSelectionHeuristic(variables []*Node) bool {

	switch len(variables) {
	case 2:
		if variables[0].Variable.Value == variables[1].Variable.Value {
			return false
		}
	case 3:
		if variables[2].Variable.Value >= variables[0].Variable.Value {
			return false
		}
		if variables[2].Variable.Value == variables[1].Variable.Value {
			return false
		}
	case 4:
		if variables[0].Variable.Value == variables[3].Variable.Value {
			return false
		}
		if variables[3].Variable.Value <= variables[2].Variable.Value {
			return false
		}
		if variables[3].Variable.Value == variables[1].Variable.Value {
			return false
		}
	case 5:
		if variables[4].Variable.Value >= variables[3].Variable.Value-1 {
			return false
		}
		if AbsoluteValue(variables[4].Variable.Value-variables[1].Variable.Value)%2 == 0 {
			return false
		}
		if variables[4].Variable.Value == variables[0].Variable.Value-2 {
			return false
		}
	case 6:
		if AbsoluteValue(variables[2].Variable.Value-variables[5].Variable.Value) != 1 {
			return false
		}
		if AbsoluteValue(variables[0].Variable.Value-variables[5].Variable.Value)%2 != 0 {
			return false
		}
		if variables[3].Variable.Value == variables[5].Variable.Value {
			return false
		}
		if variables[4].Variable.Value == variables[5].Variable.Value {
			return false
		}
		if variables[5].Variable.Value == variables[1].Variable.Value {
			return false
		}

	case 7:
		if variables[6].Variable.Value <= variables[2].Variable.Value {
			return false
		}
		if variables[6].Variable.Value > variables[0].Variable.Value {
			return false
		}
	case 8:
		if AbsoluteValue(variables[1].Variable.Value-variables[7].Variable.Value) != 1 {
			return false
		}
	}
	return true
}

//-------------- HELPERS -------------------//
func AbsoluteValue(a int) int {
	if a < 0 {
		return -a
	}
	return a
}

//-------------- PRINTING RESULTS -------------------//

func (node *Node) String() string {
	return node.Variable.Letter + ":" + strconv.Itoa(node.Variable.Value)
}

func RemoveDuplicates(nodes *[]*Node) {
	encountered := make(map[*Node]bool)
	j := 0
	for i, x := range *nodes {
		if !encountered[x] {
			encountered[x] = true
			(*nodes)[j] = (*nodes)[i]
			j++
		}
	}
	*nodes = (*nodes)[:j]
}

func (root *Root) PrintValidPaths() {
	paths := root.GeneratePaths()
	var validPaths [][]*Node
	for _, path := range paths {
		if path[len(path)-1].Variable.Letter == "H" && path[len(path)-1].Tombstone == false {
			validPaths = append(validPaths, path)
		}
	}
	fmt.Println("Valid paths:")
	for _, p := range validPaths {
		fmt.Printf("%v\n", p)
	}
}

func (root *Root) PrintValidPathsWithHeuristic() {
	paths := root.GeneratePaths()
	var validPaths [][]*Node
	for _, path := range paths {
		if path[len(path)-1].Variable.Letter == "B" && path[len(path)-1].Tombstone == false {
			validPaths = append(validPaths, path)
		}
	}
	fmt.Println("Valid paths:")
	for _, p := range validPaths {
		fmt.Printf("%v\n", p)
	}
}

func (root *Root) ReportInvalidPaths() {
	paths := root.GeneratePaths()
	count := 0
	for _, path := range paths {
		if path[len(path)-1].Tombstone == true {
			count++
		}
	}
	fmt.Printf("Total invalid paths: %d\n", count)
}

func main() {
	root := Root{}
	root.Depth = 1
	root.PopulateRoot("A")

	for i := 0; i < 8; i++ {
		root.GenerateTree()
	}

	root.PrintValidPaths()
	root.ReportInvalidPaths()

	heuristicRoot := Root{}
	heuristicRoot.Depth = 1
	heuristicRoot.PopulateRoot("H")

	for i := 0; i < 8; i++ {
		heuristicRoot.GenerateTreeWithHeuristic()
	}

	heuristicRoot.PrintValidPathsWithHeuristic()
	heuristicRoot.ReportInvalidPaths()

}
