import java.util.*;
import java.util.concurrent.*;
import java.math.*;

class Eratosthenes{

    public static void main (String[] args){

		if(args.length > 1){
			Sync s = new Sync(Integer.parseInt(args[0]), args[1]);
		}
		else{
			Sync s = new Sync(Integer.parseInt(args[0]), "par");
		}

    }
}

class Sync{

    long N;
    int antall = 0;
	int[] primes;
	int threadCount = Runtime.getRuntime().availableProcessors();
    byte[] bitArr;
    final int[] maskIn = {127-1,127-2,127-4,127-8,127-16,127-32,127-64};
    final int [] maskOut = {1,2,4,8,16,32,64};
	long primeFacts[][] = new long[100][25];
    long[] factors;
    CyclicBarrier b;
    CyclicBarrier c;
    CyclicBarrier d;
    int curr = 1;
    int factStart = -1;

    Sync(long n, String type){
		
		N = n;
		factors = new long[100];
		bitArr = new byte[(int)(N/14)+1];
		if(N > 2000000){
			primes = new int[(int)N/12];
		}
		else if(N > 2000){
			primes = new int[(int)N/5];
		}
		else {
			primes = new int[(int)N];
		}
		

		setAllPrime(bitArr);

		numbersToFact();
		
		if(type.equals("seq")){
			startSeq();
		}
		else{
			startThreads();
		}
		printFacts(primeFacts);
    }
	
	//Starts the sequential methods and times them
	void startSeq(){
		long findPrimesStart = System.nanoTime();
		seqPrime();
		long findPrimesEnd = System.nanoTime();	
		long findPrimesTotal = (findPrimesEnd - findPrimesStart);
		System.out.println("Duration find primes sequential " + findPrimesTotal/1000000);
		long findFactorsStart = System.nanoTime();
		seqFact();
		long findFactorsEnd = System.nanoTime();	
		long findFactorsTotal = (findFactorsEnd - findFactorsStart);
		System.out.println("Duration find factors sequential " + findFactorsTotal/1000000);
	}
	//Fills the factor array
    void numbersToFact(){
		
		for(int i = 1; i < factors.length+1; i++){
			factors[i-1] = (long)((N*N) - i);
		}
		
    }
	//Set the primes
    void setAllPrime(byte[] b){
		for(int i = 0; i < b.length; i++){
			b[i] = (byte)127;
		}
    }
	//Sets the non-primes to 0
	
	 byte[] crossOutPar(int i, byte[] b){
		int index = i/14;
		int bit = (i%14)/2;
		
		b[index] = (byte)(b[index]&maskIn[bit]);
			
		return b;
    }

	//Starts the threads and times them
    void startThreads(){
		
		b = new CyclicBarrier(threadCount+1);
		c = new CyclicBarrier(threadCount+1);
		d = new CyclicBarrier(threadCount+1);
		bitArr = crossOutPar(1, bitArr);
		
		long findPrimesStart = System.nanoTime();

		for(int i = 0; i<threadCount; i++){
			Thread t = new Thread(new Work());
			t.start();
		}
		try{
			b.await();
		}
		catch(Exception e){return;}

		curr = 1;
		long findPrimesEnd = System.nanoTime();	
		long findPrimesTotal = (findPrimesEnd - findPrimesStart);
		System.out.println("Duration find primes paralell " + findPrimesTotal/1000000);

		long findFactorsStart = System.nanoTime();
		primes[0] = 2;
		try{
			d.await();
		}
		catch(Exception e){return;}

		try{
				c.await();
			}
		catch(Exception e){return;}
		getLeftOver();
		
		long findFactorsEnd = System.nanoTime();	
		long findFactorsTotal = (findFactorsEnd - findFactorsStart);
		System.out.println("Duration find factors paralell " + findFactorsTotal/1000000);
		
    }
	
	//Merges the temporary bit arrays together
	synchronized void merge(byte[] b){
		for(int i = 0; i<bitArr.length; i++){
			bitArr[i] = (byte)(bitArr[i]&b[i]);
		}
	}
	
	
    class Work implements Runnable{
		int start = 0;
		int offset = threadCount*2;
		byte[] threadBitArr = new byte[(int)(N/14)+1];
		byte[] tempbitArr = new byte[(int)(Math.sqrt(N)/14)+1];
		
		
		public void run(){

			int x = 3;
			setAllPrime(tempbitArr);
			while(x < Math.sqrt(Math.sqrt(N))){
				tempbitArr = eropar(x, (long)Math.sqrt(N), tempbitArr);
				x = x + 2;
			}

			int inital = init();
			start = inital;
			setAllPrime(threadBitArr);
			while(true){
				
				if(start*start >= N){break;}
				int index = start/14;
				int bit = (start%14)/2;
				byte temp = 0;
				temp = tempbitArr[index];
				temp = (byte)(temp&maskOut[bit]);
				temp = (byte)(temp >>> bit);
				if(temp == 1){
					threadBitArr = eropar(start, N, threadBitArr);
				}
				start = start + offset;
			}

			merge(threadBitArr);

			try{
				b.await();
			}
			catch(Exception e){return;}
			int a = initFact();
			offset = threadCount;
			count(inital, offset*2);
			try{
					d.await();
				}
			catch(Exception e){return;}
			for(int i = 0; i < 100; i++){
				long fact = getCurrentBest(i, primeFacts);
				int j = a;
				while(fact > 1 && primes[j] < Math.sqrt(fact) && primes[j] != 0){
					if(j > N){break;}
					fact = factParNew(primes[j], i, fact);
					
					j = j + offset;

					
				}
				
			}
			
			try{
					c.await();
				}
			catch(Exception e){return;}
		}
	}
	
	//Return the current rest of the number we're going to factorize. Let's the threads pick up on other threads work.
	long getCurrentBest(int index, long[][] fact){
		long temp = 1;
		for(int i = 0; i<25; i++){
			if(fact[index][i] == 0){
				break;
			}
			temp = fact[index][i] * temp;
		}
		temp = factors[index]/temp;
		return temp;
	}
    
	//Fills the found factor into the array and returns the up to date rest.
	synchronized long fill(long[][] fact, int index, long factor){
		long temp = 1;
		for(int i = 0; i<25; i++){
			if(fact[index][i] == 0){
				fact[index][i] = factor;
				break;
			}
			temp = fact[index][i] * temp;
		}
		temp = factors[index]/temp;
		return temp;
	}
	
	//Find the leftover factor after all the prime factors have been searched through.
	void getLeftOver(){
		long[] factors = new long[100];
		for(int i = 0; i < 100; i++){
			int counter = 0;
			factors[i] = (long)((N*N) - i);
			long temp = 1;
			for(int j = 0; j < 25; j++){
				if(primeFacts[i][j] == 0){break;}
				temp = primeFacts[i][j] * temp;			
				counter++;
			
			}
			temp = factors[i]/temp;
			if(temp != 1){
				primeFacts[i][counter] = temp;
			}
		}
	}
	
	//Print the 5 first and 5 last factorizations
	void printFacts(long[][] fac){
		for(int i = 0; i < 5; i++){
			for(int j = 0; j < 25; j++){
				if(fac[i][j] == 0){break;}
				System.out.print(fac[i][j] + " * ");							
			
			}
			System.out.println(" = " + factors[i]);
			
		}
		for(int i = 99; i > 94; i--){
			for(int j = 0; j < 25; j++){
				if(fac[i][j] == 0){break;}
				System.out.print(fac[i][j] + " * ");							
			
			}
			System.out.println(" = " + factors[i]);
			
		}
	}
	
	//Assign a starting number to the threads
    synchronized int init(){
        curr = curr + 2;
		return curr;
    }

    synchronized int initFact(){
		factStart = factStart + 1;
		return factStart;
	}

	//Runs the sequential algorithm for finding primes
	void seqPrime(){
		bitArr = crossOutPar(1, bitArr);;
		int start = 1;
		while(true){
			if(start*start >= N){break;}
			int index = start/14;
			int bit = (start%14)/2;
			byte temp = 0;
			temp = bitArr[index];
			temp = (byte)(temp&maskOut[bit]);
			temp = (byte)(temp >>> bit);
			if(temp == 1){
				bitArr = eropar(start, N, bitArr);
			}
			start = start + 2;
		}
    }
	
	//Runs the sequential algorithm for finding factors
	void seqFact(){
		primes[0] = 2;
		count(1,2);
		for(int i = 0; i < factors.length; i++){
			long fact = factors[i];
				int j = 0;
				while(fact > 1 && primes[j] < Math.sqrt(fact) && primes[j] != 0){
					if(j > N){break;}
					fact = factParNew(primes[j], i, fact);
					
					j++;

					
				}

		}
		getLeftOver();
		
	}
	
	//Checks if n is already crossed out, if not uses it to cross others off
	byte[] eropar(int n, long stop, byte[] b){
		if(n*n >= N){return b;}
		int number = n;
		int multiple = 0;
		int numberToCross = (number*number)+(multiple*number);
		while(numberToCross <= N || numberToCross < stop){
			if(numberToCross >= N || numberToCross > stop){break;}
			b = crossOutPar(numberToCross, b);
			numberToCross = (number*number)+(multiple*number);
			multiple = multiple + 2;
		}
		return b;
    }
	
	//Finds the factors
	long factParNew(int n, int ind, long fac){
		int number = n;
		long fact = fac;
		while(fact % number == 0){
			
				fact = fill(primeFacts, ind, n); //Put the found factor in the array and return the up to date rest
				fact = fact/number;
			
			}
			
		return fact;
    }
	
	//Puts the found primes into an array and counts the amount of primes at the same time.
    void count(int start, int offset){

		int count = 0;
		int n = start;
		int i;
		if(start == 1){
			i = 1;
		}
		else{
			i = (start/2);
		}
		while(true){
			if(n > N){break;}
			int number = n;
			int index = n/14;
			int bit = (n%14)/2;
			byte temp = 0;
			temp = bitArr[index];
			temp = (byte)(temp&maskOut[bit]);
			temp = (byte)(temp >>> bit);
			if(temp == 1){
				primes[i] = n;
				i = i + (offset/2);
				count++;
			}
			n = n + offset;
			
		}
		System.out.println("Count: " + count);
	
    }
}
