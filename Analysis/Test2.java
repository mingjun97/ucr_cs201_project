public class Test2 {

	public static void main(String[] args) {		
		int a = 20;
		func1(a);		
	}
	
	public static void func1 (int x) {
	    int y = x;
	    int z = x;
	    while(y > 0){
	        z = x;
	        while (z > 0){
	            z--;
	        }
	        y--;
	    }
	}
	
}