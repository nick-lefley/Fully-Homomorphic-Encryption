import random
import math

param_lambda = 2 #security parameter
param_rho = param_lambda #error term bit-length
param_rho_dash = 2*param_lambda #secondary noise parameter
param_eta = int(round((param_lambda**2)*math.log10(param_lambda**2))) #secret-key bit-length
param_gamma = int(round((param_lambda**5)*math.log10(param_lambda**5))) #public-key element bit-length
param_tau = param_lambda + param_gamma #number of integers in public key
param_kappa = param_gamma + 2 #fixed constant
param_theta = param_lambda #fixed constant
param_capital_theta = param_kappa*param_lambda #fixed constant

#####################################################################################

def mod(x,p): #returns x (modulo p)
    if ((float(x)/float(p))-0.5)%1 == 0:
        quotient = int(math.floor(float(x)/float(p)))
    else:
        quotient = int(round(float(x)/float(p)))
    remainder = x - (quotient*p)
    return remainder

def D(p): #distribution for generating public key
    q = random.randint(0,math.ceil(float(2**param_gamma)/float(p))-1)
    r = random.randint(-(2**param_rho)+1,(2**param_rho)-1)
    return (p*q)+r
    
def D_eval(p,index): #distribution for sampling elements required for modular reduction during evaluate
    q = random.randint(math.ceil(float(2**(param_gamma+index-1)/float(p))),math.ceil(float(2**(param_gamma+index))/float(p))-1)
    r = random.randint(-(2**param_rho)+1,(2**param_rho)-1)
    return 2*((p*q)+r)
    
def pkGen(sk): #generate public key
    store = []
    for i in range(0,param_tau+1):
        store.append(D(sk))
    store.sort(reverse=True)
    return store

def KeyGen(): #generate all keys required
    sk = 2*random.randint(math.ceil(2**(param_eta-2)),math.floor(2**(param_eta-1))-1)+1
    pk = [0]
    while (pk[0]%2 == 0) or (mod(pk[0],sk)%2 == 1):
        pk = pkGen(sk)
    pk_eval = []
    for i in range(0,param_gamma+1):
        pk_eval.append(D_eval(sk,param_gamma-i)) 
    x_p = int(round(float(2**param_kappa)/float(sk)))
    s = []
    S = []
    for i in range(1,param_capital_theta+1):
        s.append(0)
    while len(S)!=param_theta:
        rand = random.randint(1,param_capital_theta)
        if rand not in S:
            S.append(rand)
            s[rand-1] = 1
    y = []
    for i in range(1,param_capital_theta+1):
        y.append(float(random.randint(0,(2**(param_kappa+1))-1))/float(2**param_kappa))
    sum_set = 0
    for i in range(0,param_theta-1):
        sum_set += y[S[i]-1]*(2**param_kappa)
    sum_set = mod(sum_set,2**(param_kappa+1))
    if sum_set<x_p:
        y[S[param_theta-1]-1] = float(x_p-sum_set)/float(2**param_kappa)
    else:
        y[S[param_theta-1]-1] = float((2**(param_kappa+1))-sum_set+x_p)/float(2**param_kappa)  
    return s,pk,y,pk_eval #secret-key, public key, y needed for encryption, pk_eval reduction set for evaluation
    
def Encrypt(pk,y,m): #encrypt individual bits
    size = random.randint(1,param_tau-1)
    S = random.sample(pk[1:],size)
    r = random.randint(-(2**param_rho_dash)+1,(2**param_rho_dash)-1)
    calc = m + (2*r) + (2*sum(S))
    c = mod(calc,pk[0])
    z = []
    n = float(2**(-(math.ceil(math.log(param_theta,2))+3)))
    for i in range(0,param_capital_theta):
        z.append(math.floor(float((c*y[i])%2)/n)*n)
    return c,z #ciphertext value, z needed for decryption
    
def Three_For_Two(data,n): #bit-wise addition, recurrence on data set
    lst = []
    if len(data)%2 == 1:
        lst.append(data[len(data)-1])
    for i in range(0,len(data)/2):
        store1 = int(data[2*i]*(2**n))
        store2 = int(data[(2*i)+1]*(2**n))
        generate = []
        propagate = []
        recurrence = [0]
        result = 0
        for bit in range(0,n+1):
            generate.append(((store1&(2**bit))>>bit)*((store2&(2**bit))>>bit))
            propagate.append(((store1&(2**bit))>>bit)^((store2&(2**bit))>>bit))
            recurrence.append(generate[bit]^(propagate[bit]*recurrence[bit]))
            result += ((((store1&(2**bit))>>bit)+((store2&(2**bit))>>bit)+recurrence[bit])%2)*(2**(-n+bit))
        result += (recurrence[n+1])*2
        lst.append(result)
    if len(lst)==1:
        return lst[0] #sum of all elements in given data set
    else:
        return Three_For_Two(lst,n) #recurrence      

def Decrypt_star(sk,c,z): #fast decryption
    n = int(math.ceil(math.log(param_theta,2))+3)
    a = []
    for i in range(0,param_capital_theta):
        a.append(int((z[i]*sk[i])*(2**n)))
    W = []
    for j in range(0,n+1):
        b = []
        for a_i in a:
            b.append((a_i&(2**j))>>j)
        P = [[1]*(param_capital_theta+1)]
        for row in range(0,2**n):
            P.append([0]*(param_capital_theta+1))
        for g in range(1,param_capital_theta+1):
            for h in range(0,2**n):
                P[(2**n)-h][g] = (b[g-1]*P[(2**n)-h-1][g-1])^P[(2**n)-h][g-1]
        w = 0
        for i in range(0,n):
            w += (2**i)*P[2**i][param_capital_theta]
        W.append(w)
    for j in range(0,n+1):
        W[j] = mod(W[j]*(2**(-n+j)),2)
    store = Three_For_Two(W,n)
    if (int(store*2)&1)==1:
        m = mod(c-(int(store)+1),2)
    else:
        m = mod(c-int(store),2)
    return m #decrypted bit
    
def Three_For_Two_Recrypt(data,n,pk2,pk2_eval,y): #bit-wise addition of encryptions during recrypt
    lst = []
    if len(data)%2 == 1:
        lst.append(data[len(data)-1])
    for i in range(0,len(data)/2):
        store1 = data[2*i]
        store2 = data[(2*i)+1]
        generate = []
        propagate = []
        recurrence = [Encrypt(pk2,y,0)[0]]
        result = []
        for bit in range(0,n+1):
            generate.append(Evaluate('mult',store1[n-bit],store2[n-bit],pk2_eval,y)[0])
            propagate.append(Evaluate('add',store1[n-bit],store2[n-bit],pk2_eval,y)[0])
            recurrence.append(Evaluate('add',generate[bit],Evaluate('mult',propagate[bit],recurrence[bit],pk2_eval,y)[0],pk2_eval,y)[0])
            result.append(Evaluate('add',store1[n-bit],Evaluate('add',store2[n-bit],recurrence[bit],pk2_eval,y)[0],pk2_eval,y)[0])
        lst.append(result)
    if len(lst)==1:
        return lst[0] #sum of elements in given data set
    else:
        return Three_For_Two_Recrypt(lst,n,pk2,pk2_eval,y) #recurrence
    
def Recrypt(pk2,y,pk2_eval,sk_encrypted,c,z): #recrypt to refresh error term
    c = bin(c)[bin(c).find('b')+1:]
    c_bar = []
    for i in c:
        c_bar.append(Encrypt(pk2,y,int(i))[0])
    n = int(math.ceil(math.log(param_theta,2))+3)
    z_bar = []
    for row in range(0,len(z)):
        z_bar.append([])
    for i in range(0,len(z)):
        z[i] = bin(int(z[i]*(2**n)))[bin(int(z[i]*(2**n))).find('b')+1:]
        for j in range(0,(n+1)-len(z[i])):
            z_bar[i].append(Encrypt(pk2,y,0)[0])
        for j in z[i]:
            z_bar[i].append(Encrypt(pk2,y,int(j))[0])
    a = []
    for row in range(0,len(z)):
        a.append([])
    for i in range(0,param_capital_theta):
        for j in range(0,len(z_bar[i])):
            a[i].append(Evaluate('mult',z_bar[i][j],sk_encrypted[i],pk2_eval,y)[0])
    W = []
    for j in range(0,n+1):
        b = []
        for a_i in a:
            b.append(a_i[j])
        P = [[]]
        for column in range(0,param_capital_theta+1):
            P[0].append(Encrypt(pk2,y,1)[0])
        for row in range(0,2**n):
            P.append([0]*(param_capital_theta+1))
            P[row+1][0] = Encrypt(pk2,y,0)[0]
        for g in range(1,param_capital_theta+1):
            for h in range(0,2**n):
                P[(2**n)-h][g] = Evaluate('add',(Evaluate('mult',b[g-1],P[(2**n)-h-1][g-1],pk2_eval,y)[0]),P[(2**n)-h][g-1],pk2_eval,y)[0]
        w = []    
        for i in range(0,n):
            w.append(P[2**i][param_capital_theta])
        W.append(w)            
    for j in range(0,n+1):
        for shift in range(0,n-j):
            W[j].insert(0,0)
        W[j] = W[j][n:]
        for shift in range(0,(n+1)-len(W[j])):
            W[j].append(Encrypt(pk2,y,0)[0])
    rounding = [Encrypt(pk2,y,0)[0],Encrypt(pk2,y,1)[0]] 
    for boost in range(0,n-1):
        rounding.append(Encrypt(pk2,y,0)[0])
    W.append(rounding) 
    store = Three_For_Two_Recrypt(W,n,pk2,pk2_eval,y)
    final_result = Evaluate('add',store[len(store)-1],c_bar[len(c_bar)-1],pk2_eval,y)
    c_new = final_result[0]
    z_new = final_result[1]
    return c_new,z_new #refreshed ciphertext-value, z_new needed for decryption
    
    
def Evaluate(calc,c_1,c_2,reduction_set,y): #either 'add' or 'mult' two encryptions and reduce
    result = 0
    if calc == "add":
        result = c_1+c_2
    elif calc == "mult":
        result = c_1*c_2
    else:
        print "ERROR!"
    if abs(result)>(2**param_gamma):
        new_result = result
        for num in reduction_set:
            new_result = mod(new_result,num)
        result = new_result
    z = []
    n = float(2**(-(math.ceil(math.log(param_theta,2))+3)))
    for i in range(0,param_capital_theta):
        z.append(math.floor(float((result*y[i])%2)/n)*n) 
    return result,z #result of evaluation on given ciphertext values, z needed for decryption
  
  
  
########   TESTING   ############################################################################
 
  
def Recrypt_Test():
    keys1 = KeyGen()
    keys2 = KeyGen()
    encryption = Encrypt(keys1[1],keys1[2],1)
    sk = keys1[0]
    for key in range(0,param_capital_theta):
        sk[key] = Encrypt(keys2[1],keys2[2],sk[key])[0]
    new_encryption = Recrypt(keys2[1],keys2[2],keys2[3],sk,encryption[0],encryption[1])
    decrypt = Decrypt_star(keys2[0],new_encryption[0],new_encryption[1]) 
    print decrypt
    return decrypt 
  
      
def Encryption_Test():
    keys = KeyGen()
    encryption = Encrypt(keys[1],keys[2],1)
    return Decrypt_star(keys[0],encryption[0],encryption[1])
    
        
def Evaluation_Test():
    keys = KeyGen()
    encryption1 = Encrypt(keys[1],keys[2],0)
    encryption2 = Encrypt(keys[1],keys[2],1)
    store1 = Evaluate("add",encryption1[0],encryption2[0],keys[3],keys[2])
    return Decrypt_star(keys[0],store1[0],store1[1])   