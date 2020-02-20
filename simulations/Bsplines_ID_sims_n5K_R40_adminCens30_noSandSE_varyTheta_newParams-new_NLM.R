## I want to make this code a little more flexible
time0 = proc.time()

library(dplyr)
library(survival)
require(stats)
library(splines2)
library(MASS)
library(pracma)
source("R/ID_frailty_LT_internalFunctions-updated-Bspline-sandwich-v3.R")

## BATCH MODE - take in arguments
## '--args runNum=1 theta=0' 
args=(commandArgs(TRUE))

for(i in 1:length(args)){
  eval(parse(text=args[[i]]))
}
print(paste("runNum", runNum))
print(paste("theta", theta))

## For estimating B-spline basis coefficients
obj.fn.1 <- function(eta.vec, spline.pred, h0.truth){ 
  ##
  spline.vals <- sapply(1:nrow(spline.pred), function(i) sum(spline.pred[i,]*(eta.vec)))
  sq.diffs <- (log(h0.truth)-spline.vals)^2
  return(sum(sq.diffs))
}


n = 5000
log.kappa1.true = -9.98  
log.alpha1.true = 1.05 
log.kappa2.true = -10.01
log.alpha2.true = 1.15  
log.kappa3.true = -2.50
log.alpha3.true = 0.42
log.theta.true = log(theta)  ## Reading this in
##
kappa1.true = exp(log.kappa1.true)
alpha1.true = exp(log.alpha1.true)
kappa2.true = exp(log.kappa2.true)
alpha2.true = exp(log.alpha2.true)
kappa3.true = exp(log.kappa3.true)
alpha3.true = exp(log.alpha3.true)
theta.true = exp(log.theta.true)

beta1.true = c(-0.03021803)  
beta2.true = c(-0.33064510)  
beta3.true = c(-0.10652843)

## l
Q1.l = 65  ## Actually the min
Q3.l = 78

## Male 
prev.gender = 0.57

cens = c(30, 30)

frailty <- ifelse(exp(log.theta.true)>0, T, F)

## B-spline baseline hazard specifications
n.internalKnots.1 <- 1
Bspline.degree.1 <- 1
num.Bspline.params.1 <- (n.internalKnots.1) + (Bspline.degree.1 + 1)

n.internalKnots.2 <- 1
Bspline.degree.2 <- 1
num.Bspline.params.2 <- (n.internalKnots.2) + (Bspline.degree.2 + 1)

n.internalKnots.3 <- 1  ## Trying to add more flexibility - the previously estimated BH was off!
Bspline.degree.3 <- 1
num.Bspline.params.3 <- (n.internalKnots.3) + (Bspline.degree.3 + 1)

lin.pred = list(as.formula(~gender), as.formula(~gender), as.formula(~gender))
frailty <- ifelse(theta>0, T, F)

num.Bspline.params.1 = (n.internalKnots.1) + (Bspline.degree.1 + 1)
num.Bspline.params.2 = (n.internalKnots.2) + (Bspline.degree.2 + 1)
num.Bspline.params.3 = (n.internalKnots.3) + (Bspline.degree.3 + 1)

R <- 40
n.params <- ifelse(frailty == T, num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 + length(beta1.true) + length(beta2.true) + length(beta3.true) + 1, 
                   num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 + length(beta1.true) + length(beta2.true) + length(beta3.true))

simMat <- matrix(NA, nrow = R, ncol = n.params+2);
seMat <- matrix(NA, nrow = R, ncol = n.params);
sandseMat <- matrix(NA, nrow = R, ncol = n.params);


ll <- rep(NA, R)
cols <- c(paste0("phi1.", c(0:(num.Bspline.params.1-1))), paste0("phi2.", c(0:(num.Bspline.params.2-1))), paste0("phi3.", c(0:(num.Bspline.params.3-1))))
if (frailty == T) cols <- c(cols, "log(theta)")
cols <- c(cols,  paste0("beta1.", 1:length(beta1.true)), 
          paste0("beta2.", 1:length(beta2.true)), 
          paste0("beta3.", 1:length(beta3.true)))
colnames(simMat) <- c(cols, "P(y1>L)", "P(y2>L)")
colnames(seMat) <- colnames(sandseMat) <- cols
eventDistMat <- matrix(NA, nrow=R, ncol=4); colnames(eventDistMat) = c("0,0", "1,0", "0,1", "1,1")

for (r in 1:R){
  ##
  tryCatch({
    print(r)
    set.seed((runNum-1)*R + r)  ## Different seed sets for each runNum
    print(paste("seed:", (runNum-1)*R + r))
    
    ## DATA
    gender = rbinom(n, 1, prev.gender)
    data0 = data.frame(gender)
    x1 = x2 = x3 = as.matrix(data0)
    
    lt = c(Q1.l, Q3.l) - 65
    
    Y.tmp = data.frame(simID.LT(cluster=NULL, x1, x2, x3, beta1.true, beta2.true, beta3.true,
                                alpha1.true, alpha2.true, alpha3.true,
                                kappa1.true, kappa2.true, kappa3.true, theta.true, SigmaV.true=NULL, cens, lt = lt), data0)
    ## No Left truncation here
    Y = Y.tmp %>% filter(y1 > L)
    data = data.frame(Y)
    
    delta1 = Y$delta1; delta2 = Y$delta2
    eventDistMat[r,] = round(100*c(table(Y$delta1, Y$delta2))/nrow(Y),1)
    
    simMat[r,length(cols)+1] = nrow(data)/n
    simMat[r,length(cols)+2] = nrow(Y.tmp %>% filter(y2 > L))/n
    y1 = Y[,1]; delta1 = Y[,2]; y2 = Y[,3]; delta2 = Y[,4]; l=Y[,5]
    
    bdy.knots.b.1 = c(0, max(y1)) 
    bdy.knots.b.2 = c(0, max(y2))
    bdy.knots.b.3.y2my1 = c(0, max(y2-y1))
    
    
    ## Estimate B-spline params
    ## log h0(t) = phi0 * B0(t) + ... + phik * Bk(t)
    ################
    ## 1-transition
    ################
    knot.loc.1 <- quantile(y1[delta1==1], ppoints(n.internalKnots.1))
    ##
    b.1.event <- bSpline(y1[delta1==1], 
                         knots = knot.loc.1,
                         degree = Bspline.degree.1, 
                         intercept=TRUE, Boundary.knots=c(0,max(y1)+.1))
    b.1 <- predict(b.1.event, y1)
    h0.1.truth.event <- alpha1.true*kappa1.true*y1[delta1==1]^(alpha1.true-1)
    phi.1.truth=nlm(f=obj.fn.1, p=rep(-1,num.Bspline.params.1), spline.pred=b.1.event, h0.truth=h0.1.truth.event)$estimate
    ## Plot to see
    # plot(y1[delta1==1], exp(phi.1.truth %*% t(b.1.event)), cex = 0.5)
    
    ################
    ## 2-transition
    ################
    knot.loc.2 <- quantile(y2[delta2==1], ppoints(n.internalKnots.2))
    ##
    b.2.event <- bSpline(y2[delta2==1], 
                         knots = knot.loc.2,
                         degree = Bspline.degree.2, 
                         intercept=TRUE, Boundary.knots=c(0,max(y2)+.1))
    b.2 <- predict(b.2.event, y2)
    h0.2.truth.event <- alpha2.true*kappa2.true*y2[delta2==1]^(alpha2.true-1)
    phi.2.truth=nlm(f=obj.fn.1, p=rep(-1,num.Bspline.params.2), spline.pred=b.2.event, h0.truth=h0.2.truth.event)$estimate
    #plot(y2[delta2==1], exp(phi.2.truth %*% t(b.2.event)), cex = 0.5)
    
    ################
    ## 3-transition
    ################
    knot.loc.3 <- quantile((y2-y1)[delta1==1], ppoints(n.internalKnots.3))
    ##
    b.3.event <- bSpline((y2-y1)[delta1==1], 
                         knots = knot.loc.3,
                         degree = Bspline.degree.3, 
                         intercept=TRUE, Boundary.knots=c(0,max(y2-y1)+.1))
    b.3.y2my1 <- predict(b.3.event, y2-y1)
    h0.3.truth.event <- alpha3.true*kappa3.true*(y2-y1)[delta1==1]^(alpha3.true-1)
    phi.3.truth=nlm(f=obj.fn.1, p=rep(-1,num.Bspline.params.3), spline.pred=b.3.event, h0.truth=h0.3.truth.event)$estimate
    #plot((y2-y1)[delta1==1], exp(phi.3.truth %*% t(b.3.event)), cex = 0.5)
    
    para = c(phi.1.truth,
             phi.2.truth,
             phi.3.truth)
    if (frailty == T) para = c(para, log(theta.true))
    para = c(para, beta1.true, beta2.true, beta3.true)
    ##
    test <- FreqID.LT.bSpline123.sand(Y=Y, lin.pred=lin.pred, data=data, model = "semi-Markov", startVals=para, frailty=frailty, 
                                      b.1=b.1, b.2=b.2, b.3.y2my1=b.3.y2my1,
                                      bdy.knots.b.1=bdy.knots.b.1, 
                                      bdy.knots.b.2=bdy.knots.b.2, 
                                      bdy.knots.b.3.y2my1=bdy.knots.b.3.y2my1,
                                      method = "nlm", sandSE=F)
    
    simMat[r,1:length(para)] <- test$estimate
    seMat[r,] <- test$aSE
    #sandseMat[r,] <- test$rSE
    ll[r] <- test$logLike
    
  }, error = function(e){ 
    cat(r, "ERROR :",conditionMessage(e), "\n")
  })  # end of tryCatch
  
  save(simMat, seMat, ll, eventDistMat, para, #sandseMat,
       file=paste0("output/ID_Bspline_NLM-1knot_linear_R40_n5K_noSandSE_theta", theta, "-", runNum,".Rdata"))
}


print(Sys.info()["nodename"])

print(proc.time() - time0)
print((proc.time() - time0)/3600)


