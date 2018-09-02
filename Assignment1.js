// JavaScript source code

//Constructor definitions for the different AST nodes.

function flse() {
    return {type:FALSE, toString: function () { return "false"; } };
}
function vr(name) {
    return {type:VR,  name: name, toString: function () { return this.name; } };
}
function num(n) {
    return {type:NUM,  val: n, toString: function () { return this.val; } };
}
function plus(x, y) {
    return {type:PLUS,  left: x, right: y, toString: function () { return "("+ this.left.toString() + "+" + this.right.toString()+")"; } };
}
function times(x, y) {
    return {type:TIMES,  left: x, right: y, toString: function () { return "(" + this.left.toString() + "*" + this.right.toString() + ")"; } };
}
function lt(x, y) {
    return {type:LT,  left: x, right: y, toString: function () { return "(" + this.left.toString() + "<" + this.right.toString() + ")"; } };
}
function and(x, y) {
    return {type:AND,  left: x, right: y, toString: function () { return "(" + this.left.toString() + "&&" + this.right.toString() + ")"; } };
}
function not(x) {
    return {type:NOT,  left: x, toString: function () { return "(!" + this.left.toString()+ ")"; } };
}
function ite(c, t, f) {
    return {type:ITE,  cond: c, tcase: t, fcase: f, toString: function () { return "(if " + this.cond.toString() + " then " + this.tcase.toString() + " else " + this.fcase.toString() + ")"; } };
}


// Types of AST nodes.
// We wrapped on the type, information, about which arguments it receives
// and which arguments it returns.
// For some nodes, we need the types considered on execution as intOps,
// and boolOps, for that case, we define functions which return types
// according to this lists.
var NUM = {
  id: "NUM",
  args: [],
  returns: "INT",
  program: num
};
var FALSE = {
  id: "FALSE",
  args: [],
  returns: "BOOL",
  program: flse
};
var VR = {
  id: "VR",
  args: [],
  returns: (intOps, boolOps)=>{
    if(intOps.map(o=>o.id).includes("VR")) return "INT";
    if(boolOps.map(o=>o.id).includes("VR")) return "BOOL";
    return "ERROR";
  },
  program: vr
};
var PLUS = {
  id: "PLUS",
  args: ["INT", "INT"],
  returns: "INT",
  program: plus
};
var TIMES = {
  id: "TIMES",
  args: ["INT", "INT"],
  returns: "INT",
  program: times
}
var LT = {
  id: "LT",
  args: ["INT", "INT"],
  returns: "BOOL",
  program: lt
}
var AND = {
  id: "AND",
  args: ["BOOL", "BOOL"],
  returns: "BOOL",
  program: and
}
var NOT = {
  id: "NOT",
  args: ["BOOL"],
  returns: "BOOL",
  program: not
};
var ITE = {
  id: "ITE",
  args: (intOps, boolOps)=>{
    if(intOps.map(o=>o.id).includes("ITE"))
      return ["BOOL", "INT", "INT"];
    if(boolOps.map(o=>o.id).includes("ITE"))
      return ["BOOL", "BOOL", "BOOL"];
    return "ERROR";
  },
  returns: (intOps, boolOps)=>{
    if(intOps.map(o=>o.id).includes("ITE")) return "INT";
    if(boolOps.map(o=>o.id).includes("ITE")) return "BOOL";
    return "ERROR";
  },
  program: ite
};

var ALLOPS = [NUM, FALSE, VR, PLUS, TIMES, LT, AND, NOT, ITE];

// Tests are the test cases for the current synthesis problem.
var tests = null;

function str(obj) { return JSON.stringify(obj); }

//Interpreter for the AST.
function interpret(exp, envt) {
    switch (exp.type.id) {
        case "FALSE": return false;
        case "NUM": return exp.val;
        case "VR": return envt[exp.name];
        case "PLUS": return interpret(exp.left, envt) + interpret(exp.right, envt);
        case "TIMES": return interpret(exp.left, envt) * interpret(exp.right, envt);
        case "LT": return interpret(exp.left, envt) < interpret(exp.right, envt);
        case "AND": return interpret(exp.left, envt) && interpret(exp.right, envt);
        case "NOT": return !interpret(exp.left, envt);
        case "ITE": if (interpret(exp.cond, envt)) { return interpret(exp.tcase, envt); } else { return interpret(exp.fcase, envt); }
    }
}

//Some functions you may find useful:
function randInt(lb, ub) {
    var rf = Math.random();
    rf = rf * (ub - lb) + lb;
    return Math.floor(rf);
}

function randElem(from) {
    return from[randInt(0, from.length)];
}

function writeToConsole(text) {
    var csl = document.getElementById("console");
    if (typeof text == "string") {
        csl.value += text + "\n";
    } else {
        csl.value += text.toString() + "\n";
    }
}
function cls(){
  document.getElementById("console").value = "";
}


/*
Your goal for this first exercise is to implement a version of the algorithm that properly accounts for the types of sub-expressions when assembling new expressions. 
*/
function same(a, b){
  if(a.length!==b.length) return false;
  for(var i=0; i<a.length; i++)
    if(a[i]!==b[i]) return false;
  return true;
}
function equivalentWith(result, results, available){
  var eqs = [];
  for(i=0; i<available.length; i++){
    if(same(results[available[i]], result))
      eqs.push(available[i])
  }
  return eqs;
}
function getArgumentTypes(operation, intOps, boolOps){
  if(typeof(operation.args)==='function')
    return operation.args(intOps, boolOps);
  return operation.args;
}
function possibleArguments(args){
  // We implement a recursive solution to get the possible combinations.
  // We have an array, which elements are an array of elements which will
  // be combined.
  // The idea is that the possible combinations are the first element joined
  // with the possible combinations of the remaining arguments.
  if(args.length === 0)
    return [[]];
  return args[0].reduce((l, a)=>
    l.concat(
      possibleArguments(args.slice(1))
        .map(remaining=>[a].concat(remaining)))
  , []);
}
function argumentsForOperation(operation, intOps, boolOps, initialPrograms){
  // For the operation to use as "combinator" we get the
  // argument types it can receive.
  var argumentTypes = operation.args;
  // From the way the problem was structured, the argument
  // types, may depend on the value of intOps and boolOps.
  // For this reason, the args attribute, can be a function
  // that given those inputs, returns the possible argument
  // types.
  if(typeof(operation.args)==='function')
    argumentTypes = argumentTypes(intOps, boolOps);
  // Now that we know the argument types, we use the possible programs
  // of the already calculated programs.
  // And we generate an array which entries are the possible arguments
  // to the "combinator".
  return argumentTypes.map(a=>
    // For each argument type, we filter the programs, which match
    // the argument.
    initialPrograms.filter(p=>{
      var type = p.expression.type.returns;
      // In a similar way as with the "args" attribute, the "returns"
      // attribute, may depend on intOps, or boolOps, so we use the
      // same solution to take this into account.
      if(typeof(type)==='function')
        type = p.expression.type.returns(intOps, boolOps);
      return type===a;
    }).map(p=>p.expression));
}

function restrictedArguments(restrictions, programs){
  return restrictions.map(a=>
    programs.filter(p=>
      a.includes(p.expression.type.id)).map(p=>p.expression));
}

function addNextLayer(programs, intOps, boolOps){
  var initialPrograms = programs.programs;
  // First we iterate on all posible node types, 
  // while the solution hasn't been found.
  for(var i=0; i<ALLOPS.length && !programs.success(); i++){
    var operation = ALLOPS[i];
    // The operation may have restrictions specified, in
    // which case, we take advantage of this (1.b)
    if(typeof(operation.restrictions)!=="undefined")
      var args = restrictedArguments(operation.restrictions, initialPrograms);
    else 
      var args = argumentsForOperation(operation, intOps, boolOps, initialPrograms);


    // Now we need the possible combinations of this possible arguments
    // and apply them to the operator.
    var possibleArgs = possibleArguments(args);
    // Conditions to take into account ths possible empty program
    if(possibleArgs.length == 1)
      if(possibleArgs[0].length == 0)
        possibleArgs = [];
    programs.concat(
      possibleArgs // This is a list of all possible arguments
        .map(p=> operation.program(...p))); // We apply the "combinator" with this arguments. The concat method of our ProgramList, will take care of the testing logic.
  }
  return programs;
}
function Program(exp){
  this.expression = exp;
  this.testResults = tests.map(t=>interpret(this.expression, t));
  this.succesful = true;
  for(var i=0; i<this.testResults.length; i++)
    if(this.testResults[i] !== tests[i]['_out']){
      this.succesful = false;
      break;
    }
  this.testEquivalentTo = p=>{
    // p is a Program(), which tests will be compared
    // with this program results.
    var equivalent = true;
    for(var i=0; i<this.testResults.length; i++)
      if(this.testResults[i]!==p.testResults[i]){
        equivalent = false;
        break;
      }
    return equivalent;
  };
}
function ProgramList(){
  this.winner = null;
  this.success = ()=>this.winner!==null;
  this.programs = [];  // Array if Program() 's added.
  this.concat = programs=>{
    // The concatenation is made, with the variant that it
    // checks if the solution has been found and stops in
    // that case.
    for(var i=0; i<programs.length; i++){
      this.push(programs[i]);
      if(this.success())
        break;
    }
  };
  this.push = program=>{
    var p = new Program(program);
    // On the Program constructor, we already run the tests
    // and determine if the program is sucessful.
    if(p.succesful){
      this.winner = p;
      return;
    }

    // When we add a new program to the list, we check
    // with the previous programs, to see if it's
    // test equivalent to a previous program.
    var equivalentProgram = null;
    var equivalentProgramIndex = -1;
    for(var i=0; i<this.programs.length; i++){
      if(this.programs[i].testEquivalentTo(p)){
        equivalentProgram = p;
        equivalentProgramIndex = i;
        break;
      }
    }
    // If there's an equivalent program, we need to choose the 
    // "best" according to some metric.
    if(equivalentProgram!==null){
      var best = this.bestProgram(p, equivalentProgram);
      if(best == "fst"){
        // If the new program is better, we remove the previous
        this.programs = this.programs.slice(0, equivalentProgramIndex)
          .concat(this.programs.slice(equivalentProgramIndex+1));
        // and then add the new one.
        this.programs.push(p);
      }
    }

    // If not, we just add it to our list
    //
    else {
      this.programs.push(p);
    }
  };
  this.bestProgram = (p1, p2)=>{
    // Here implement an order function between
    // two test equivalent programs.
    // However, test equivalence is not required nor checked 
    // for this method.
    // The return value is either "fst" or "snd".
    // For this case, we choose the smaller expresion.
    // We assume the second program is the previous program
    // found, and since we are growing on complexity with
    // each new program tested, we can assume the 
    // previous one was simpler.
    return "snd";
  }
}
function bottomUp(globalBnd, intOps, boolOps, vars, consts, inputoutputs) {
  tests = inputoutputs;
  // ProgramList is a structure which pushes programs to a list, which aren't 
  // "observationally equivalent" to previous programs, and some other logic.
  possiblePrograms = new ProgramList();
  // Terminals considered as all expresions of our language, which don't require an expression to be constructed.
  possiblePrograms.concat(
    consts.map(c=>num(c))
    .concat(vars.map(v=>vr(v)))
    .concat([flse()]));

  var depth = 1;
  while(depth<globalBnd && !possiblePrograms.success()){
    possiblePrograms = addNextLayer(possiblePrograms, intOps, boolOps);
    depth++;
    // The logic of knowing if the programs added solve the problem
    // is in the structure.
  }
  if(!possiblePrograms.success())
    return 'FALSE'

  return possiblePrograms.winner.expression;
}


function bottomUpFaster(globalBnd, intOps, boolOps, vars, consts, inputoutputs){
  // restrictions will be an attribute of the operation,
  // that for each argument, especifies the types of expression it
  // is allowed to use.
  TIMES.restrictions = [["VR", "NUM"], ["VR", "NUM"]];
  LT.restrictions = [["VR", "NUM"], ["VR", "NUM"]];
  var program = bottomUp(globalBnd, intOps, boolOps, vars, consts, inputoutputs);
  delete TIMES['restrictions']; 
  delete LT['restrictions']; 
  return program;
}


function print1a(variables, constants, inputoutputs){
  var rv = bottomUp(4, [VR, NUM, PLUS, TIMES, ITE], [AND, NOT, LT, FALSE], variables, constants, inputoutputs);
  writeToConsole(" ");
  writeToConsole("Solving for: ");
  for(var i=0; i<inputoutputs.length; i++)
    writeToConsole(
      " "+Object.keys(inputoutputs[i]).reduce((st,k)=>
        st+" * "+k+": "+inputoutputs[i][k] ,""));
  writeToConsole("with constants: "+constants.join(", "));
	writeToConsole("Result: " + rv.toString());

}
function print1b(variables, constants, inputoutputs){
  var rv = bottomUpFaster(4, [VR, NUM, PLUS, TIMES, ITE], [AND, NOT, LT, FALSE], variables, constants, inputoutputs);
  writeToConsole(" ");
  writeToConsole("Solving for: ");
  for(var i=0; i<inputoutputs.length; i++)
    writeToConsole(
      " "+Object.keys(inputoutputs[i]).reduce((st,k)=>
        st+" * "+k+": "+inputoutputs[i][k] ,""));
  writeToConsole("with constants: "+constants.join(", "));
	writeToConsole("Result: " + rv.toString());
  writeToConsole("");
  writeToConsole("Clearly this was faster...");
}

function run1a1(){
  cls();
  writeToConsole("Exercise 1.a.1");
  var tests = [
    {
      variables: ["x", "y"],
      constants: [4, 5],
      inputoutputs: [{x:5,y:10, _out:5},{x:8,y:3, _out:3}]
    },
    {
      variables: ["x", "y"],
      constants: [],
      inputoutputs: [{x:5,y:10, _out:5},{x:8,y:3, _out:3}]
    },
    {
      variables: ["x"],
      constants: [],
      inputoutputs: [{x:2, _out:8},{x:3, _out:27}, {x:4, _out:64}]
    }
  ];

  for(var i=0; i<tests.length; i++)
    print1a(tests[i].variables, tests[i].constants, tests[i].inputoutputs);
}

function run1a2(){
  cls();
  writeToConsole("Exercise 1.a.2");
  var tests = [
    {
      variables: ["x", "y"],
      constants: [-1, 5],
      inputoutputs: [
        {x:10, y:7, _out:17},
        {x:4, y:7, _out:-7},
        {x:10, y:3, _out:13},
        {x:1, y:-7, _out:-6},
        {x:1, y:8, _out:-8}	]	
    }
  ];

  for(var i=0; i<tests.length; i++)
    print1a(tests[i].variables, tests[i].constants, tests[i].inputoutputs);
}


function run1b(){
  cls();
  writeToConsole("Exercise 1.b");
  var tests = [
    {
      variables: ["x", "y"],
      constants: [-1, 5],
      inputoutputs: [
        {x:10, y:7, _out:17},
        {x:4, y:7, _out:-7},
        {x:10, y:3, _out:13},
        {x:1, y:-7, _out:-6},
        {x:1, y:8, _out:-8}	]	
    }
  ];

  for(var i=0; i<tests.length; i++)
    print1b(tests[i].variables, tests[i].constants, tests[i].inputoutputs);

}




//Useful functions for exercise 2. 
//Not so much starter code, though.

function structured(inputoutputs){
  // First the given inputs, ouput are transformed,
  // since we know the structure:
  //  - the "<" comparison will work for the given input, 
  //  if it's compared with at least one bigger.
  //  - the expressions returned are:
  //   - 2*x+??, x*x+??, 3*x+??
  //  
  //  So we map the given information to the corresponding 
  //  values for each expression.
  //   - input+1
  //   - output-2*input, output-input*input, output-3*input 
  //   respectively
  //  After that, it's sorted according to the input, so I can take advantage of the
  //  conditional "fallback" kind of structure, which I explain latter.
  var orderedPossibilities = inputoutputs.map(io=>
    [ io[0]+1, io[1]-2*io[0], io[1]-io[0]*io[0], io[1]-3*io[0] ]).sort((x,y)=>
      x[0]-y[0]);
  // Depending on the implementation of sort on the browser,
  // until this step, it's safe to assume we have O(n log n) 
  // time complexity.

  // I'll exploit the following fact from the program structure:
  // with the if's checking "<" comparisons, we can assume the 
  // values which to compare are sorted in an increasing manner,
  // since not doing this, results on cases that can't be evaluated
  // (Suppose A>B, the if(x<A)...elseif(x<B)...
  // will never have the second condition evaluated, since any
  // value smaller than B will also be smaller than A)
  //
  // So, trying to find the limits to put for the comparisons, we 
  // need to check how can we group the possible expressions that
  // the program may be. Since the program must be fixed, the
  // constants must be the same through every test, so the corresponding
  // values that we previously mapped previously, can help us to
  // group them.
  //
  // For this, I take the longest common constant for the given sorted
  // expressions, as the one that define the group. I simply
  // compare every row with the previous one and keep track 
  // (on common) of the test cases with the same calculate constants.
  // When the program is not able no continue comparing, it assumes 
  // the creation of a group, saving its details on groupPosition
  //
  // This takes at most orderedPossibilities.length (O(n))
  var groups = 0;
  var test = 1; 
  var common = [1,2,3];
  var groupPosition = [];
  while (groups<4 && test < orderedPossibilities.length){
    previousRow = orderedPossibilities[test-1];
    currentRow = orderedPossibilities[test];
    var comparing = [];
    for(var i=0; i<common.length; i++){
      if(previousRow[common[i]] == currentRow[common[i]])
        comparing.push(common[i]);
    }
    if(comparing.length == 0){
      groups++;
      groupPosition.push([test-1, common[0]]);
      common = [1, 2, 3];
    }
    else
      common = comparing;
    test++;
  }

  if(groups == 4)
    return "No program with assumed structure can have this as test results.";

  // We keep track of the last group
  groupPosition.push([orderedPossibilities.length - 1, common[0]]);

  // At this point, in orderedPossibilities, in every element, we have the
  // index of the end of the group, and the index of the constant that was
  // common for the group.
  //
  // With this info we make the program (constant time complexity since 
  // the program's structure is fixed)
  return makeIteProgram(orderedPossibilities, groupPosition);
}

function makeExpression(type, data){
  // Here we just make an expression, according to the
  // common type found on the group.
  var cons = data[type];
  switch(type){
    case 1:
      return plus(times(num(2), vr("x")), num(cons));
      break;
    case 2: 
      return plus(times(vr("x"), vr("x")), num(cons));
      break;
    case 3:
      return plus(times(num(3), vr("x")), num(cons));
  }
}

function makeIteProgram(ordered, pos){
  // For the ITE program we need the condition, the value
  // to compare is in the first element of every row
  var findex = pos[0][0]; // Which row will be the one for this group
                          // is on groupPosition
  var ftype = pos[0][1];  // The type of expression which was common is
                          // saved on the second element of a groupPosition's
                          // element
  var fdata = ordered[findex]; // With this we get the data of this row.
  var fexpression = makeExpression(ftype, fdata); // And create the corresponding expression

  if(pos.length <= 2){
    // It may be the case we just have one group due to poor data, and we cannot
    // associate an expression, in which case we don't have enough info for the
    // "else" case, so we just use the same expression as the conditional case.
    var sexpression = makeExpression(1, fdata);
    if(pos.length == 2){
      // In this case we do have enough info and we make the expression
      // for the "else" case in an analogous manner.
      var sindex = pos[1][0];
      var stype = pos[1][1];
      var sdata = ordered[sindex];
      var sexpression = makeExpression(stype, sdata);
    }
    // We return the ite program with the calculated information
    // (this is the base case of our recursion)
    return ite(lt(vr("x"), num(fdata[0])), fexpression, sexpression);
  }
  // If we have more cases, we create an ITE expression recursively on the
  // "else" case, removing the expression for the first element on fexpression.
  return ite(lt(vr("x"), num(fdata[0])), fexpression, makeIteProgram(ordered, pos.slice(1)));
}


function run2() {
  cls();
  var inpt = JSON.parse(document.getElementById("input2").value);
  program = structured(inpt);
  writeToConsole(program);
  writeToConsole("");
  if(inpt.reduce((tf, io)=>
    tf && (interpret(program, {x: parseInt(io[0])}) == parseInt(io[1])), true))
    writeToConsole("All test cases passed!");
  else
    writeToConsole("Impossible!");
}


function genData() {
    //If you write a block of code in program1 that writes its output to a variable out,
    //and reads from variable x, this function will feed random inputs to that block of code
    //and write the input/output pairs to input2.
    program = document.getElementById("program1").value
    function gd(x) {
        var out;
        eval(program);
        return out;
    }
    textToIn = document.getElementById("input2");
    textToIn.value = "[";
    for(i=0; i<50; ++i){
        if(i!=0){ textToIn.value += ", "; }
        var inpt = randInt(0, 100);
        textToIn.value += "[" + inpt + ", " + gd(inpt) + "]";
    }
    textToIn.value += "]";
}
