###############################################################################
###############################################################################
#
# 			     SIGNIFICANCE TEST FUNCTION "SigTest"
#
# Input: Data frame with the following variables:
#
# 	 Censoring.status: 1 if event observed, 0 otherwise
# 	 Censoring.times: Time of last observation of patient
#	   Event.times:  Time from entry to event (must be set Infinity if Censoring.status=0)
# 	 group: Treatment group (must be set "A" or "B")
#
#
# Output: Value of Test Statistic Z, 2-sid. p-value of New Test and classical Two-Sample Log-Rank Test
#
###############################################################################
###############################################################################


library(survival)
library(sft)
library(zoo)

SigTest <- function(data){
  
  Daten_full <- data
  Daten_full$Observed.times <- pmin(Daten_full$Event.times, Daten_full$Censoring.times)
  Daten_full$Event.times[Daten_full$Censoring.status==0] <- Inf
  
  Daten_A <- Daten_full[which(Daten_full$group=="A"),]
  Daten_B <- Daten_full[which(Daten_full$group=="B"),]
  
  ##########################################################
  # Calculate Nelsen-Aalen Estimator in Group A
  
  # Number at risk in Group A
  Y.A.vec <- function(u){  
    as.numeric( Daten_A$Observed.times > u)  
  }
  Y.A.pre <- function(u){ 
    sum(Y.A.vec(u))
  }
  Y.A <- Vectorize(Y.A.pre)
  
  J.A.pre <- function(u){ 
    as.numeric(Y.A.pre(u) > 0)
  }
  J.A <- Vectorize(J.A.pre)
  
  
  
  # Number of Events in Group A
  Ni.A.vec <- function(u){
    as.numeric( Daten_A$Event.times <= u ) * as.numeric( Daten_A$Event.times <= Daten_A$Censoring.times)
  }
  # Event times in Group A
  index.A       <- function(s){ 
    which(Ni.A.vec(s)==1)
  }
  event.times.A <- function(s){
    Daten_A$Event.times[index.A(s)]
  }
  
  
  
  # Nelsen-Aalen estimator for Group A
  min.event.time.A <- min(event.times.A(Inf))
  max.event.time.A <- max(event.times.A(Inf))
  NA.A     <- function(s){ ifelse( s > min.event.time.A,  sum(  J.A(event.times.A(s))/(Y.A(event.times.A(s)))    ) , 0 ) }
  NA.A     <- Vectorize(NA.A)
  Var.NA.A <- function(s){ ifelse( s > min.event.time.A,  sum(  J.A(event.times.A(s))/(Y.A(event.times.A(s)))**2 ) , 0 ) }
  Var.NA.A     <- Vectorize(Var.NA.A)
  
  
  # calculate new two-sample survival test
  x1           <- pmin(Daten_B$Observed.times,Inf)
  x1.ascending <- sort(x1)
  M.s   <- sum( as.numeric(Daten_B$Event.times <= x1) ) - sum( na.locf(NA.A(x1.ascending)) )
  factor <- 1+2*nB+2*(-1)*(1:nB)
  Var.s <- sum( as.numeric(Daten_B$Event.times <= x1) ) + sum( factor*na.locf(Var.NA.A(x1.ascending)) )
  Z <- M.s/sqrt(Var.s)
  p <- 2*min(pnorm(Z),1-pnorm(Z))
  #rej <- ( abs(Z) >= qnorm(1-alpha/2) )
  
  # calculate "common" two-sample log-rank test
  LR     <- survdiff(Surv(Observed.times, Censoring.status) ~ group, data=Daten_full)
  p.LR   <- pchisq(LR$chisq, length(LR$n)-1, lower.tail = FALSE)
  #rej.LR <- ( p.LR <= alpha)
  
  
  erg 		<- cbind(Z,p,p.LR)
  colnames(erg) 	<- c("Value of Test Statistic Z","2-sid. p-value New Test","2-sid. p-value Log-Rank Test")
  
  return(erg)
  
}


###############################################################################
###############################################################################
#
# 			         POWER FUNCTION
#
# Input parameters:
#	  a: Prefixed length of the accrual period 
# 	f: Prefixed length of the follow-up period
# 	r: Overall accrual rate per year (pooled over both treatment groups)
# 	Pi: Allocation ratio of group B vs group A (Pi=nB/nA)
# 	omega.0: Expected hazard ratio (group B vs group A) under planning alternative K0: Lambda.A = omega.0 Lambda.B
# 	kappa, S1: Weibull distrubtion parameters of standard arm A survival times: Lambda.A(t) = S1**(t**kappa)
# 	alpha: Desired two-sided significance level
#
# Output: Calculates the theoretical power under planning alternative K0: Lambda.A = omega.0 Lambda.B for given input parameters  
#
###############################################################################
###############################################################################


Power <- function(a,f,r,Pi,omega.0,omega,kappa,S1,alpha){
  
  #####################################################
  # specification of Weibull distribution parameters
  shape      <- kappa
  scale.H0   <-         (log(1/S1))**( (-1)/shape )
  scale.H1   <- (omega.0*log(1/S1))**( (-1)/shape )
  
  #####################################################
  # Specification of true standard arm event distribution
  
  # true event probability for standard arm A 
  F.A <- function(u){ 
    1 + (-1)*exp( (-1)*(u/scale.H0)**shape )
  }
  # true survival function for standard arm A 
  S.A <- function(u){ 
    exp( (-1)*(u/scale.H0)**shape )
  }
  # true hazard function for standard arm A 
  lambda.A <- function(u){ 
    (shape/scale.H0)*(u/scale.H0)**(shape + (-1))
  }
  # true event probability density for standard arm A 
  f.A <- function(u){ 
    lambda.A(u)*S.A(u)
  }
  
  
  #####################################################
  # Specification of experimental arm event distribution under planning alternative K0: Lambda.A = omega.0 Lambda.B
  
  # expected event probability for experimental arm B under planning alternative K0: Lambda.A = omega.0 Lambda.B 
  F.B <- function(u){ 
    1 + (-1)*exp( (-1)*(u/scale.H1)**shape )
  }
  # true survival function for experimental arm B under planning alternative K0: Lambda.A = omega.0 Lambda.B 
  S.B <- function(u){ 
    exp( (-1)*(u/scale.H1)**shape )
  }
  # true hazard function for experimental arm B under planning alternative K0: Lambda.A = omega.0 Lambda.B 
  lambda.B <- function(u){ 
    (shape/scale.H1)*(u/scale.H1)**(shape + (-1))
  }
  # true event probability density for experimental arm B under planning alternative K0: Lambda.A = omega.0 Lambda.B 
  f.B <- function(u){ 
    lambda.B(u)*S.B(u)
  }
  
  
  #####################################################
  # Calculation of parameter mu from equation (8)
  mu <- sqrt(a*r)*sqrt(Pi/(1+Pi))*(1/a)*integrate(F.A, f, a+f)$value
  
  #####################################################
  # Calculation of parameter sigma from equation (8)
  sigma.square.summand1 <- (1/a)*integrate(F.A, f, a+f)$value
  
  InnerFunc2a = function(u) { lambda.A(u)/S.A(u)*max(1,(a)/(a+f-u)) }
  InnerFunc2b = function(u) { f.A(u)*S.A(u)*min(1,(a+f-u)/(a))*min(1,(a+f-u)/(a)) }
  InnerFunc2.final = Vectorize(function(y) { InnerFunc2b(y)*integrate(InnerFunc2a, 0, y)$value   })
  sigma.square.summand2 <- 2*Pi*integrate(InnerFunc2.final , 0, a+f)$value
  
  InnerFunc3a = function(u) { lambda.A(u)/S.A(u)*max(1,(a)/(a+f-u)) }
  InnerFunc3b = function(u) { S.A(u)*S.A(u)*min(1,(a+f-u)/(a))*(1/a) }
  InnerFunc3.final = Vectorize(function(y) { InnerFunc3b(y)*integrate(InnerFunc3a, 0, y)$value   })
  sigma.square.summand3 <- 2*Pi*integrate(InnerFunc3.final , f, a+f)$value
  
  sigma.square <- sigma.square.summand1 + sigma.square.summand2 + sigma.square.summand3
  
  sigma <- sqrt(sigma.square)
  
  power <- pnorm(  qnorm(alpha/2)   - log(omega.0)*mu/sigma   )
  
  mu*sqrt(a*r)*sqrt(Pi/(1+Pi))*log(omega.0)
  sigma.square*a*r*(Pi/(1+Pi))
  power
  
  #erg <- c(mu, sigma, power)
  #colnames(erg) 	<- c("mu", "sigma", "power")
  
  erg <- power
  return(erg)
  
}

###############################################################################
###############################################################################
#
# 			         REQUIRED SAMPLE SIZE FUNCTION
#
# Input parameters: 
# 	f: Prefixed length of the follow-up period
# 	r: Overall accrual rate per year (pooled over both treatment groups)
# 	Pi: Allocation ratio of group B vs group A (Pi=nB/nA)
# 	omega.0: Expected hazard ratio (group B vs group A) under planning alternative K0: Lambda.A = omega.0 Lambda.B
# 	kappa, S1: Weibull distrubtion parameters of standard arm A survival times: Lambda.A(t) = S1**(t**kappa)
# 	alpha: Desired two-sided significance level
# 	beta: Desired type II error rate under planning alternative K0: Lambda.A = omega.0 Lambda.B
#
# Output:   Sample size n to achieve desired power 1- beta under planning alternative K0: Lambda.A = omega.0 Lambda.B (calculated analytically)
#
###############################################################################
###############################################################################


ReqSampleSize <- function(f,r,Pi,omega.0,kappa,S1,alpha,beta){
  F <- function(a){beta + (-1) + Power(a,f,r,Pi,omega.0,kappa,S1,alpha) }
  Accrual <- uniroot(F,c(0.1,30))$root
  # Overall Sample Size pooled over both treatment groups ...
  n <- floor(Accrual*r)+1
  return(n)
}

###############################################################################
###############################################################################
#
# 			         EMPIRICAL TYPE I AND II ERROR RATE FUNCTION
#
# Input parameters: 
# 	n: Prefixed overall sample size (pooled over both treatment groups)
# 	f: Prefixed length of the follow-up period
# 	r: Overall accrual rate per year (pooled over both treatment groups)
# 	Pi: Allocation ratio of group B vs group A (Pi=nB/nA)
# 	omega.0: Expected hazard ratio (group B vs group A) under planning alternative K0: Lambda.A = omega.0 Lambda.B
# 	omega: True hazard ratio (group B vs group A)
# 	kappa, S1: Weibull distrubtion parameters of standard arm A survival times: Lambda.A(t) = S1**(t**kappa)
# 	alpha: Desired two-sided significance level
# 	anz.sims: Number of simulation steps for calculation of empirical type I and II error rates
#
# Output:  Empirical type I error rate and empirical power of the new test and classical two-sample log-rank test 
#	   (determined by simulation based on anz.sims simulation steps) 
#          under the truth Lambda.A = omega Lambda.B for allocated input parameters 
#
#
###############################################################################
###############################################################################

library(survival)
library(sft)
library(zoo)

EmpErrorRates <- function(n, f, r, Pi, omega.0, omega, kappa, S1, alpha, anz.sims){
  
  Rate <- r
  Follow.Up <- f
  Accrual <- n/r
  Weibull.shape.ref <- kappa
  s <- 1000
  HR.planned <- omega.0
  HR.true <- omega
  anz.sims <- anz.sims
  
  alpha <- alpha
  beta <- beta
  
  # simulation output 
  Z.vec   <- NULL
  rej.vec <- NULL
  rej.LR.vec <- NULL
  
  NA.vec <- NULL
  Var.NA.vec <- NULL
  
  M.s.vec <- NULL
  Var.s.vec <- NULL
  
  
  # Weibull distribution parameters
  shape      <- kappa
  scale.H0   <- (log(1/S1))**( (-1)/shape )
  scale.H1   <- (omega.0*log(1/S1))**( (-1)/shape )
  scale.true <- (omega*log(1/S1))**( (-1)/shape )
  # corresponding null cumulative hazard: Lambda(s)=(s/scale.H0)**shape 
  
  
  ######################################################
  ######################################################
  # Start of simulation loop
  
  for(i in 1:anz.sims){
    
    # For the purpose of reproducibility: Choose Seed that changes with each simulation step in a known way
    Saat <- 598573564 + 2684*i; Saat;
    
    ############################################################
    #  Generate virtual data set of simulation step i
    
    ################################################
    # Data set: Standard group A
    
    # Saat <- 598573564 + 2684*i; Saat;
    
    # sample size of group A
    nA <- n/(1+Pi)
    
    #Generate arrival times of the nA patients acc. to a uniform distribution on [0,Accrual]  
    set.seed(Saat + 27875984)
    Arrival.times <- runif(nA, 0, Accrual)
    
    # Generate Event Times of these n patients
    set.seed(Saat)
    Event.times <- rweibull(nA, shape, scale.H0)
    Event.times.calender <- Arrival.times + Event.times
    
    # Time of censoring = Time of last patient out (initially planned trial end = Accrual + Follow.Up)
    max.Arrival.time <- max(Arrival.times[which(Arrival.times<Accrual)])
    Censoring.time.calender <- ( max.Arrival.time + Follow.Up)
    Arrival.times + Event.times 
    Censoring.times <- Censoring.time.calender - Arrival.times 
    Censoring.time.calender <- Censoring.times + Arrival.times
    Censoring.status <- as.numeric(Event.times <= Censoring.times)
    
    Observed.times <- pmin(Event.times, Censoring.times)
    Observed.times.calender <- Observed.times + Arrival.times
    
    # Set of survival data
    Daten_A <- data.frame(Arrival.times, Event.times, Event.times.calender, Censoring.times, Censoring.time.calender, Observed.times, Observed.times.calender, Censoring.status)
    Daten_A[1:10, ]
    
    Daten_A$group <- "A"
    
    
    #################################################
    # Data set: Experimental group
    
    # sample size of group A
    nB <- n*Pi/(1+Pi)
    
    #Generate arrival times of the n patients acc. to a uniform distribution on [0,PF*Accrual]  
    set.seed(Saat + 37875984)
    Arrival.times <- runif(nB, 0, Accrual)
    
    # Generate Event Times of these n patients
    set.seed(Saat + 17875984)
    Event.times <- rweibull(nB, shape, scale.true)
    Event.times.calender <- Arrival.times + Event.times
    
    # Time of censoring = Time of last patient out (initially planned trial end = Accrual + Follow.Up)
    max.Arrival.time <- max(Arrival.times[which(Arrival.times<Accrual)])
    Censoring.time.calender <- ( max.Arrival.time + Follow.Up)
    Arrival.times + Event.times 
    Censoring.times <- Censoring.time.calender - Arrival.times 
    Censoring.time.calender <- Censoring.times + Arrival.times
    Censoring.status <- as.numeric(Event.times <= Censoring.times)
    
    Observed.times <- pmin(Event.times, Censoring.times)
    Observed.times.calender <- Observed.times + Arrival.times
    
    # Set of survival data
    Daten_B <- data.frame(Arrival.times, Event.times, Event.times.calender, Censoring.times, Censoring.time.calender, Observed.times, Observed.times.calender, Censoring.status)
    Daten_B[1:10, ]
    
    Daten_B$group <- "B"
    
    
    
    # full dataset: patients from both treatment arm, recruited in calender time [0,PF*Accrual]
    Daten_full <- rbind(Daten_A, Daten_B)
    
    
    
    
    # check
    # Expectation of Weibull distribution = scale.true*gamma(1+1/shape)
    mean(Daten_B$Event.times)
    scale.true*gamma(1+1/shape)
    
    #plot(Daten_B$Arrival.times ~ Daten_B$Event.times)
    #cor(Daten_B$Arrival.times,Daten_B$Event.times)
    
    
    
    
    ##########################################################
    # Calculate Nelsen-Aalen Estimator in Group A
    
    
    
    # Number at risk in Group A
    Y.A.vec <- function(u){  
      as.numeric( Daten_A$Observed.times > u)  
    }
    Y.A.pre <- function(u){ 
      sum(Y.A.vec(u))
    }
    Y.A <- Vectorize(Y.A.pre)
    
    J.A.pre <- function(u){ 
      as.numeric(Y.A.pre(u) > 0)
    }
    J.A <- Vectorize(J.A.pre)
    
    
    
    # Number of Events in Group A
    Ni.A.vec <- function(u){
      as.numeric( Daten_A$Event.times <= u ) * as.numeric( Daten_A$Event.times <= Daten_A$Censoring.times)
    }
    # Event times in Group A
    index.A       <- function(s){ 
      which(Ni.A.vec(s)==1)
    }
    event.times.A <- function(s){
      Daten_A$Event.times[index.A(s)]
    }
    
    
    
    # Nelsen-Aalen estimator for Group A
    min.event.time.A <- min(event.times.A(Inf))
    max.event.time.A <- max(event.times.A(Inf))
    NA.A     <- function(s){ ifelse( s > min.event.time.A,  sum(  J.A(event.times.A(s))/(Y.A(event.times.A(s)))    ) , 0 ) }
    NA.A     <- Vectorize(NA.A)
    Var.NA.A <- function(s){ ifelse( s > min.event.time.A,  sum(  J.A(event.times.A(s))/(Y.A(event.times.A(s)))**2 ) , 0 ) }
    Var.NA.A     <- Vectorize(Var.NA.A)
    
    
    NA.vec <- c(NA.vec,NA.A(s))
    Var.NA.vec <- c(Var.NA.vec,Var.NA.A(s))
    
    NA.A(1)/1
    NA.A(2)/2
    NA.A(3)/3
    
    
    
    
    x1           <- pmin(Daten_B$Observed.times,s)
    x1.ascending <- sort(x1)
    #x2.pre <- expand.grid(x0,x0)
    #x2 <- pmin(x2.pre[,1],x2.pre[,2],s)
    
    # calculate martingale . . .
    #Mi.s     <- as.numeric(Daten_B$Event.times <= x) - NA.A(x)
    #Var.Mi.s <- as.numeric(Daten_B$Event.times <= x) + Var.NA.A(x)
    
    #N1.vec     <- c(N1.vec,  sum(as.numeric(Daten_B$Event.times <= x)) -  sum(  (x/scale.H0)**shape   )  )
    #Var.N1.vec <- c(Var.N1.vec, sum(as.numeric(Daten_B$Event.times <= x)))
    
    #N2.vec     <- c(N2.vec, NA.A(s)  -  (s/scale.H0)**shape    )
    #Var.N2.vec <- c(Var.N2.vec, Var.NA.A(s))
    
    #N3.vec     <- c(N3.vec, sum( NA.A(x) )  -  sum( (x/scale.H0)**shape )    )
    #Var.N3.vec <- c(Var.N3.vec, sum( Var.NA.A(s) ))
    
    # . . . and corresponding new two-sample log-rank test
    M.s   <- sum( as.numeric(Daten_B$Event.times <= x1) ) - sum( na.locf(NA.A(x1.ascending)) )
    M.s.vec <- c(M.s.vec,M.s)
    factor <- 1+2*nB+2*(-1)*(1:nB)
    Var.s <- sum( as.numeric(Daten_B$Event.times <= x1) ) + sum( factor*na.locf(Var.NA.A(x1.ascending)) )
    Var.s.vec <- c(Var.s.vec,Var.s)
    Z <- M.s/sqrt(Var.s)
    rej <- ( abs(Z) >= qnorm(1-alpha/2) )
    
    # calculate "common" two-sample log-rank test
    LR     <- survdiff(Surv(Observed.times, Censoring.status) ~ group, data=Daten_full)
    p.LR   <- pchisq(LR$chisq, length(LR$n)-1, lower.tail = FALSE)
    rej.LR <- ( p.LR <= alpha)
    
    # count number of rejections for both log-rank tests
    (Z.vec <- cbind(Z.vec,Z))
    (rej.vec <- cbind(rej.vec,rej))
    (rej.LR.vec <- cbind(rej.LR.vec,rej.LR))
    
    
    #  Sys.sleep(0.01)
    #  print(i)
    #  flush.console() 
    
  }
  
  
  #erg 		<- cbind(n, omega.0, omega, sum(rej.vec)/length(rej.vec) , sum(rej.LR.vec)/length(rej.LR.vec), mean(M.s.vec), mean(Var.s.vec) )
  #colnames(erg) 	<- c("n","Planned HR", "True HR", "Rej. New Test", "Rej. Trad. LR-Test", "E(M0.hat)", "Var(M0.hat)")
  erg 		<- cbind(Pi,S1,kappa,omega.0,n, omega.0, omega, sum(rej.vec)/length(rej.vec) , sum(rej.LR.vec)/length(rej.LR.vec))
  colnames(erg) 	<- c("Pi","S1","kappa","omega.0","n","Planned HR", "True HR", "Rej. New Test", "Rej. Trad. LR-Test")
  return(erg)
  
}

