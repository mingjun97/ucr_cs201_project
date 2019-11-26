import java.util.Map;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;

import soot.Body;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.BodyTransformer;
import soot.toolkits.graph.Block;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
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
		dynamicAnalysis();
 
		soot.Main.main(args);
		
		System.out.println("-------------------------------------");
		System.out.println("End of execution");
	}

	private static void staticAnalysis(){
		configure(".:/root/CS201Fall19/Analysis"); //Change this path to your Analysis folder path in your project directory
		SootClass sootClass = Scene.v().loadClassAndSupport("Test3");
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
		getTarget(sootClass, methods, true).toString();
		System.out.println();
		
	}

	private static ArrayList<Unit> getTarget(SootClass sootClass, List<SootMethod> methods, Boolean verbose){
		ArrayList<Unit> interested = new ArrayList<Unit>();
		for (int i = 0; i < sootClass.getMethodCount(); i++) {
			SootMethod method = methods.get(i);
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

	private static void dynamicAnalysis(){
		PackManager.v().getPack("jtp").add(new Transform("jtp.myInstrumenter", new BodyTransformer() {

		protected void internalTransform(Body arg0, String arg1, Map arg2) {
			//Dynamic Analysis (Instrumentation) code

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
