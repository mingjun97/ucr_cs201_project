import java.util.Map;

import heros.solver.Pair;
import polyglot.ast.Assign;

import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;

import soot.Body;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StringConstant;
import soot.BodyTransformer;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.toolkits.graph.Block;
import soot.PackManager;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.Transform;
import soot.SootMethod;
import soot.options.Options;
import soot.toolkits.graph.BlockGraph;
import soot.toolkits.graph.ClassicCompleteBlockGraph;


public class Main {
	public static void main(String[] args) {
		//Static Analysis (Retrieve Flow Graph)
		staticAnalysis();

		//Dynamic Analysis (Instrumentation) 
		System.out.println("-----------Dynamic Analysis-----------");


		dynamicAnalysis();
 
		soot.Main.main(args);
		
		System.out.println("-------------------------------------");
		System.out.println("End of execution");
	}

	private static void staticAnalysis(){
		configure(".:/root/CS201Fall19/Analysis"); //Change this path to your Analysis folder path in your project directory
		SootClass sootClass = Scene.v().loadClassAndSupport("Test1");
	    sootClass.setApplicationClass();
	    //Static Analysis code
		List<SootMethod> methods = sootClass.getMethods();
		System.out.println("------Static Analysis 1-------\n-----------------------------");
	   	for (int i = 0; i < sootClass.getMethodCount(); i++) {
			SootMethod method = methods.get(i);
			Body body = method.retrieveActiveBody();
			BlockGraph blockgraph = new ClassicCompleteBlockGraph(body);
			System.out.println("Method: " + method.toString());
			
			for ( Iterator<Block> iter_blocks = blockgraph.iterator(); iter_blocks.hasNext() ;){  // Iterate basic blocks
				Block blocks = (Block) iter_blocks.next();
				System.out.println("BB" + blocks.getIndexInMethod() + ":");
				// Iterate print instructions
				for (Iterator<Unit> iter = blocks.iterator();iter.hasNext();){ 
					System.out.println(iter.next().toString());
				}
				// DEBUG: Comment out in release
				// System.out.println(blocks.toString());
					System.out.println();
			}

			// Grab loops
			System.out.println("Loops:");
			List<ArrayList<Integer>> loops = getLoops(blockgraph);
			for (Iterator<ArrayList<Integer>> iter_loop = loops.iterator(); iter_loop.hasNext(); ){
				List<String> loop_repr = new ArrayList<String>();
				for (Iterator<Integer> iter_int = iter_loop.next().iterator(); iter_int.hasNext(); ){
					loop_repr.add(String.format("BB%d", iter_int.next()));
				}
				if (loop_repr.size() > 0) System.out.println(loop_repr);
			}
			System.out.println();
		}
		System.out.println();
		
		System.out.println("------Static Analysis 2-------\n------------------------------");
		getTarget(methods, true).toString();
		System.out.println();
		
	}

	private static ArrayList<Unit> getTarget( List<SootMethod> methods, Boolean verbose){
		ArrayList<Unit> interested = new ArrayList<Unit>();
		for (SootMethod method: methods) {
			Body body = method.retrieveActiveBody();
			BlockGraph blockgraph = new ClassicCompleteBlockGraph(body);
			if (verbose) System.out.println("Method: " + method.toString());

			List<ArrayList<Integer>> loops = getLoops(blockgraph);
			for (ArrayList<Integer> loop : loops) {
				ArrayList<Value> INs = getINsOfLoop(blockgraph, loop);
				for (Integer idxBB : loop) {
					for (Unit unit : blockgraph.getBlocks().get(idxBB)) {
						for (ValueBox vb : unit.getUseBoxes()) {
							if (INs.contains(vb.getValue())){
								interested.add(unit);
								if (verbose) System.out.println(unit.toString());
							}
						}
					}
				}
			}
			if (verbose) System.out.println();
		}
		return interested;
	}
	// get INs of loop
	private static ArrayList<Value> getINsOfLoop(BlockGraph bg ,ArrayList<Integer> loop) {
		ArrayList<Value> INs = new ArrayList<Value>();
		Boolean[] visited = new Boolean[bg.getBlocks().size()];
		Arrays.fill(visited, false);
		ArrayList<Block> worklist = new ArrayList<Block>();
		for (int bb: loop) worklist.add(bg.getBlocks().get(bb));
		while (worklist.size() > 0) {
			for (Block pred : worklist.remove(0).getPreds()){
				if (! loop.contains(pred.getIndexInMethod()) && !visited[pred.getIndexInMethod()]){ // this pred is not in loop
					// System.out.println("Working on pred: " + String.valueOf(pred.getIndexInMethod()));

					worklist.add(pred);
					visited[pred.getIndexInMethod()] = true;
					for (Unit unit : pred){
						// System.out.println(unit.toString());
						for (ValueBox vb: unit.getDefBoxes()){
							// System.out.println(vb.getValue().toString());
							INs.add(vb.getValue());
						}
					}
				}
			}
		}
		return INs;
	}

	private static Boolean reachable(BlockGraph bg, int from, int to, int avoid, int level){
		Block start = bg.getBlocks().get(from);
		if (level > bg.getBlocks().size()) { // If recursive too much level, we believe that it's not reachable
			return false;
		}
		for (Iterator<Block> iter = start.getSuccs().iterator(); iter.hasNext();){
			Block next = iter.next();
			int idxNext = next.getIndexInMethod();
			if ( from == to ) return true;
			if ( idxNext == to ) return true;
			if ( idxNext == avoid ) continue;
			if ( idxNext == from ) continue;
			if (reachable(bg, idxNext, to, avoid, level + 1)) return true;
		}
		return false;
	}

	private static List<ArrayList<Integer>> getDominators(BlockGraph bg){
		List<ArrayList<Integer>> dt = new ArrayList<ArrayList<Integer>>();
		Boolean stable = false;

		// initialize dt
		for (int j = 0; j < bg.size(); j++){
			dt.add(new ArrayList<Integer>());
			if ( j == 0) {
				dt.get(j).add(0);
			}else{
				for (int t = 0; t < bg.size(); t++){
					dt.get(j).add(t); // Initialize
				}
			}
		}
		// calculate dominator tree
		while (!stable){
			stable = true;
			for (Iterator<Block> iter_block = bg.iterator(); iter_block.hasNext(); ){
				Block block = iter_block.next();
				int current_block = block.getIndexInMethod();
				List<Integer> propogated_dominator = new ArrayList<Integer>();
				for (Iterator<Block> iter_preds = block.getPreds().iterator(); iter_preds.hasNext();){
					int pred = iter_preds.next().getIndexInMethod();
					propogated_dominator.addAll(dt.get(pred));
				}
				if (block.getPreds().size() > 0){
					int saved_size = dt.get(current_block).size();
					dt.get(current_block).clear();
					for (int j = 0; j < bg.size(); j++){
						if (block.getPreds().size() > 0 && Collections.frequency(propogated_dominator, j) == block.getPreds().size()) {
							dt.get(current_block).add(j);
						} else if (j == current_block){
							dt.get(current_block).add(current_block);
						}
					}
					if (saved_size != dt.get(current_block).size()){
						stable = false;
					}
				}
			}
		}
		return dt;
	}

	private static List<ArrayList<Integer>> getLoops(BlockGraph blockgraph) {
		List<ArrayList<Integer>> loops = new ArrayList<ArrayList<Integer>>();

		// dt stores the dominators
		List<ArrayList<Integer>> dt = getDominators(blockgraph);

		List<List<Integer>> backedge = new ArrayList<List<Integer>>();
		
		for (Iterator<Block> iter_blocks = blockgraph.iterator(); iter_blocks.hasNext();){
			Block block = iter_blocks.next();
			int idxCur = block.getIndexInMethod();
			for (Iterator<Block> iter_succs = block.getSuccs().iterator(); iter_succs.hasNext();){
				Block succ = iter_succs.next();
				int idxSucc = succ.getIndexInMethod();
				if (dt.get(idxCur).contains(idxSucc)){ // current node is dominated by succesor
					ArrayList<Integer> tuple = new ArrayList<Integer>();
					tuple.add(idxCur); // from
					tuple.add(idxSucc); // to
					backedge.add(tuple);
				}
			}
		}

		for (Iterator<List<Integer>> iter = backedge.iterator(); iter.hasNext();){
			List<Integer> be = iter.next();
			ArrayList<Integer> loop = new ArrayList<Integer>();
			for (Iterator<Block> iter_blocks = blockgraph.getBlocks().iterator(); iter_blocks.hasNext();){
				int idxCur = iter_blocks.next().getIndexInMethod();
				if (reachable(blockgraph, idxCur , be.get(0), be.get(1), 0)){
					loop.add(idxCur);
				}
			}
			loops.add(loop);
		}
		System.out.println();
		return loops;
	}
	static class Pair<T1, T2> {
		public T1 p1;
		public T2 p2;
		Pair(T1 p1, T2 p2){
			this.p1 = p1;
			this.p2 = p2;
		}
		Pair(){}
	}

	private static void dynamicAnalysis(){
		PackManager.v().getPack("jtp").add(new Transform("jtp.myInstrumenter", new BodyTransformer() {


		protected ArrayList<Pair<String,SootField>> doInstrumentation(Body arg0, String arg1, Map arg2, ArrayList<Unit> target){
			SootClass sootClass = arg0.getMethod().getDeclaringClass();
			ArrayList<Pair<String,SootField>> fields = new ArrayList<Pair<String,SootField>>();
			List<Block> blocks = new ClassicCompleteBlockGraph(arg0).getBlocks();
			Local ref_counter = Jimple.v().newLocal("cs201_instrument_local", LongType.v());
			arg0.getLocals().add(ref_counter);
			Boolean added_my_name = false;
			for (Block block: blocks){ // for each block in this method
				ArrayList<Pair<Unit, ArrayList<AssignStmt>>> work_orders = new ArrayList<Main.Pair<Unit,ArrayList<AssignStmt>>>();
				for (Unit unit: block){ // for each unit in this block
					if (target.contains(unit)){ // if this unit is the interested one
						// create a variable coutner for it
						// static long method_name_BB0_hash;
						SootField counter_for_unit = new SootField(String.format("%s_BB%d_%x", arg0.getMethod().getName(), block.getIndexInMethod(), unit.hashCode()), LongType.v(), Modifier.STATIC);
						sootClass.addField(counter_for_unit);
						// DEBUG: comment out me
						// System.out.println(String.format("Match \'%s\' create field %s", unit.toString(), String.format("%s_BB%d_%x", arg0.getMethod().getName(), block.getIndexInMethod(), unit.hashCode())));
						if (added_my_name) fields.add(new Pair<String, SootField>(unit.toString(),counter_for_unit));
						else {
							fields.add(new Pair<String, SootField>(arg0.getMethod().toString() + "\n" + unit.toString(),counter_for_unit));
							added_my_name = true;
						}
						// cs201_instrument_local = method_name_BB0_hash;
						AssignStmt assignLocalToRef = Jimple.v().newAssignStmt(ref_counter, Jimple.v().newStaticFieldRef(counter_for_unit.makeRef()));
						// cs201_instrument_local += 1;
						AssignStmt assignIncreamen = Jimple.v().newAssignStmt(ref_counter, Jimple.v().newAddExpr(ref_counter, LongConstant.v(1)));
						// method_name_BB0_hash = cs201_instrument_local;
						AssignStmt assignBack = Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(counter_for_unit.makeRef()), ref_counter);
						Pair<Unit, ArrayList<AssignStmt>> order = new Pair<Unit,ArrayList<AssignStmt>>();
						order.p1 = unit;
						order.p2 = new ArrayList<AssignStmt>();
						order.p2.add(assignLocalToRef);
						order.p2.add(assignIncreamen);
						order.p2.add(assignBack);
						work_orders.add(order);
					}
				}
				for (Pair<Unit, ArrayList<AssignStmt>> order: work_orders){
					for (AssignStmt stmt: order.p2){
						block.insertBefore(stmt, order.p1);
					}
				}
			}

			return fields;
		}
		protected void internalTransform(Body arg0, String arg1, Map arg2) {
			//Dynamic Analysis (Instrumentation) code
				ArrayList<Pair<String,SootField>> counters = new ArrayList<Pair<String,SootField>>();
				if (arg0.getMethod().getSubSignature().equals("void main(java.lang.String[])") ) {
					// for each method in this class
					List<SootMethod> methods = arg0.getMethod().getDeclaringClass().getMethods();
					ArrayList<Unit> target = getTarget(methods, false);
					for (SootMethod method : methods) {
						if (method.getSubSignature().equals("void main(java.lang.String[])"))
							continue; // skip main function
						if (method.getName().equalsIgnoreCase("<init>"))
							continue;
						counters.addAll(this.doInstrumentation(method.retrieveActiveBody(), arg1, arg2, target));
					}
					// dealing with main function
					if (arg0.getMethod().getSubSignature().equals("void main(java.lang.String[])")){
						SootClass sootClass = arg0.getMethod().getDeclaringClass();
						List<Block> blocks = new ClassicCompleteBlockGraph(arg0).getBlocks();
	
						Local tmpRef = Jimple.v().newLocal("tmpRef", RefType.v("java.io.PrintStream"));
						arg0.getLocals().add(tmpRef);
						SootMethod printIntCall = Scene.v().getSootClass("java.io.PrintStream").getMethod("void println(int)");
						SootMethod printStringCall = Scene.v().getSootClass("java.io.PrintStream").getMethod("void print(java.lang.String)");
						for (Block block: blocks){
							Unit unit_return_stmt = block.getTail();
							if (unit_return_stmt instanceof ReturnVoidStmt){ // return unit of block of main
								Local ref_counter = Jimple.v().newLocal("cs201_instrument_local", LongType.v());
								arg0.getLocals().add(ref_counter);
								// java.io.PrintStream streamIO_cs201 = <java.lang.System: java.io.PrintStream out>;
								block.insertBefore(Jimple.v().newAssignStmt(tmpRef, Jimple.v().newStaticFieldRef(Scene.v().getField("<java.lang.System: java.io.PrintStream out>").makeRef())), unit_return_stmt);
							
								for (Pair<String, SootField> counter: counters){
									block.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(tmpRef, printStringCall.makeRef(), StringConstant.v(counter.p1))), unit_return_stmt);
									block.insertBefore(Jimple.v().newAssignStmt(ref_counter, Jimple.v().newStaticFieldRef(sootClass.getFieldByName(counter.p2.getName()).makeRef())), unit_return_stmt);
									block.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(tmpRef, printIntCall.makeRef(), ref_counter)), unit_return_stmt);
								}
							}
						}
					}
				}	// not interested funcitons
		}			
	   }));
	}
	
	public static void configure(String classpath) {		
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_src_prec(Options.src_prec_java);
        Options.v().set_output_format(Options.output_format_jimple);
        Options.v().set_soot_classpath(classpath);
        Options.v().set_prepend_classpath(true);
        Options.v().setPhaseOption("cg.spark", "on");        
    }
}
