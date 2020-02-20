library(dplyr)
library(survival)
require(stats)
library(splines2)
library(pracma)  ## for numerical differentiation

## Simulate data from illness-death, shared frailty
## Adapted from Kyu Ha's simulation code from SemiCompRisks
## lt.type: draw left-truncation times from "unif" (uniform) or "norm" (normal)
##          - if "unif", lt=c(a, b) so that L ~ unif(n, a, b)
##          - if "norm", lt=c(mean, sd), so that L ~ Norm(mean, sd)
simID.LT <- function(cluster=NULL, x1, x2, x3, beta1.true, beta2.true, beta3.true,
                     alpha1.true, alpha2.true, alpha3.true,
                     kappa1.true, kappa2.true, kappa3.true, theta.true, SigmaV.true=NULL, cens, lt.type = "unif", lt)
{
  if(!is.null(cluster) & is.null(SigmaV.true)){
    print("SigmaV.true must be given to simulate correated data")
  }
  else
  {
    n <- dim(x1)[1]
    p1 <- dim(x1)[2]
    p2 <- dim(x2)[2]
    p3 <- dim(x3)[2]
    
    if(theta.true >0)
    {
      gamma.true <- rgamma(n, 1/theta.true, 1/theta.true)
    }
    if(theta.true == 0)
    {
      gamma.true <- rep(1, n)
    }
    
    
    if(is.null(cluster))
    {
      LP1	<- as.vector(beta1.true %*% t(x1))
      LP2	<- as.vector(beta2.true %*% t(x2))
      LP3	<- as.vector(beta3.true %*% t(x3))
    }
    if(!is.null(cluster))
    {
      J <- length(unique(cluster))
      nj <- as.vector(table(cluster))
      
      Vmat <- mvrnorm(J, rep(0, 3), SigmaV.true) # J X 3
      
      LP1 <- as.vector(beta1.true %*% t(x1) + rep(Vmat[,1], nj))
      LP2 <- as.vector(beta2.true %*% t(x2) + rep(Vmat[,2], nj))
      LP3 <- as.vector(beta3.true %*% t(x3) + rep(Vmat[,3], nj))
    }
    
    Rind <- NULL
    R <- rweibull(n, shape = alpha1.true, scale = exp(-(log(kappa1.true) +
                                                          LP1 + log(gamma.true))/alpha1.true))
    D <- rweibull(n, shape = alpha2.true, scale = exp(-(log(kappa2.true) +
                                                          LP2 + log(gamma.true))/alpha2.true))
    
    yesR <- R < D
    
    D[yesR] <- R[yesR] + rweibull(sum(yesR), shape = alpha3.true,
                                  scale = exp(-(log(kappa3.true) + LP3[yesR] + log(gamma.true[yesR]))/alpha3.true))
    delta1 <- rep(NA, n)
    delta2 <- rep(NA, n)
    y1 <- R
    y2 <- D
    Cen <- runif(n, cens[1], cens[2])
    ind01 <- which(D < R & D < Cen)
    y1[ind01] <- D[ind01]
    delta1[ind01] <- 0
    delta2[ind01] <- 1
    ind10 <- which(R < D & R < Cen & D >= Cen)
    y2[ind10] <- Cen[ind10]
    delta1[ind10] <- 1
    delta2[ind10] <- 0
    ind00 <- which(R >= Cen & D >= Cen)
    y1[ind00] <- Cen[ind00]
    y2[ind00] <- Cen[ind00]
    delta1[ind00] <- 0
    delta2[ind00] <- 0
    ind11 <- which(R < Cen & D < Cen & R < D)
    delta1[ind11] <- 1
    delta2[ind11] <- 1
    
    if (lt.type == "unif") L <- runif(n, lt[1], lt[2])
    if (lt.type == "norm") L <- rnorm(n, lt[1], lt[2])
    ret <- data.frame(cbind(y1, delta1, y2, delta2, L))
    return(ret)
  }
}





#################
## b-spline BH ##
#################

## Log-likelihood function for illness-death with shared frailty applied to left-truncated data
## bspline baseline hazard !!
## b.1: bspline basis function for the 1-transition (corresponds to y1)
## b.2: bspline basis function for the 2-transition (corresponds to y2)
## b.3.y2my1: bpline basis function for the 3-transition (corresponds to y2-y1)
## log h0,1(t) = phi.1,0 * B_1,0(t) + ... + phi.1,k1 * B_1,k1(t), where B_1,l(t) are the bspline basis functions
## log h0,2(t) = phi.2,0 * B_2,0(t) + ... + phi.2,k1 * B_2,k1(t)
## log h0,3(t) = phi.3,0 * B_3,0(t) + ... + phi.3,k1 * B_3,k1(t)
## para: vector of true
##       - c(phi.1.vector, phi.2.vector, phi.3.vector, log(theta), betas)
logLike.SCR.SM.LT.bSpline123.dropPrevCases <- function(para, y1, y2, delta1, delta2, l, Xmat1=NULL, Xmat2=NULL, Xmat3=NULL, frailty=TRUE,
                                         b.1,  
                                         b.2,  
                                         b.3.y2my1)
{
  ##
  if (is.vector(Xmat1)==T) Xmat1 = matrix(Xmat1, nrow=1)
  if (is.vector(Xmat2)==T) Xmat2 = matrix(Xmat2, nrow=1)
  if (is.vector(Xmat3)==T) Xmat3 = matrix(Xmat3, nrow=1)
  num.Bspline.params.1 <- ncol(b.1)
  num.Bspline.params.2 <- ncol(b.2)
  num.Bspline.params.3 <- ncol(b.3.y2my1)
  phi1 <- para[1:(1+num.Bspline.params.1-1)]
  phi2 <- para[(1+num.Bspline.params.1):(1+num.Bspline.params.1 + num.Bspline.params.2 - 1)]
  phi3 <- para[(1+num.Bspline.params.1 + num.Bspline.params.2):(1+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1)]
  
  if(frailty == TRUE){
    theta    <- exp(para[(2+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1)])
    thetaInv <- 1 / theta
  }
  ##
  nP.0 <- ifelse(frailty, (2+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1), (1+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1))
  nP.1 <- ncol(Xmat1)
  nP.2 <- ncol(Xmat2)
  nP.3 <- ncol(Xmat3)
  ##
  eta.1 <- as.vector(Xmat1 %*% para[nP.0 + c(1:nP.1)])
  eta.2 <- as.vector(Xmat2 %*% para[nP.0 + nP.1 + c(1:nP.2)])
  eta.3 <- as.vector(Xmat3 %*% para[nP.0 + nP.1 + nP.2 + c(1:nP.3)])
  
  ##
  type1 <- as.numeric(delta1 == 1 & delta2 == 1 & l < y1)
  type2 <- as.numeric(delta1 == 0 & delta2 == 1 & l < y1)
  type3 <- as.numeric(delta1 == 1 & delta2 == 0 & l < y1)
  type4 <- as.numeric(delta1 == 0 & delta2 == 0 & l < y1)
  #type5 <- as.numeric(delta1 == 1 & delta2 == 1 & y1 <= l & l < y2)
  #type6 <- as.numeric(delta1 == 1 & delta2 == 0 & y1 <= l & l < y2)
  ##
  ## log.h1star.y1 <- log(alpha1) + log(kappa1) + (alpha1 - 1) * log(y1) + eta.1
  ## Uses h1 - need to bSpline
  ## log.h1,0(t) = phi0 * B0(t) + ... + phik * Bk(t)
  ##############################################################################
  B0.1.y1 <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(b.1)))
  log.h1star.y1 <- B0.1.y1 + eta.1
  
  ## log.h2star.y1 <- log(alpha2) + log(kappa2) + (alpha2 - 1) * log(y1) + eta.2
  ##############################################################################
  B0.2.y1 <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(predict(b.2, y1))))
  log.h2star.y1 <- B0.2.y1 + eta.2
  
  ## log.h2star.y2 <- log(alpha2) + log(kappa2) + (alpha2 - 1) * log(y2) + eta.2
  ##############################################################################
  B0.2.y2 <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(b.2)))
  log.h2star.y2 <- B0.2.y2 + eta.2
  
  ## log.h3star.y2 <- log(alpha3) + log(kappa3) + (alpha3 - 1) * log(y2-y1) + eta.3
  ##################################################################################
  B0.3.y2my1 <- as.vector(matrix(phi3, nrow=1) %*% t(as.matrix(b.3.y2my1)))
  log.h3star.y2 <- B0.3.y2my1 + eta.3
  
  ## q.y1 <- kappa1*(y1)^alpha1 * exp(eta.1) + kappa2*(y1)^alpha2 * exp(eta.2)
  ## Uses h1 - needs bSpline
  ## Essentially uses H0.1.y1 and H0.2.y1
  ## exp(phi.3.truth %*% t(b.3.event))
  ############################################################################
  h0.1.y1 <- exp(B0.1.y1)
  h0.1.y1.interpolate.func <- approxfun(y1, h0.1.y1, rule=2)
  H0.1.y1 <- sapply(y1, function(x) integrate(h0.1.y1.interpolate.func, 0, x, stop.on.error = F)$value)
  
  h0.2.y1 <- exp(B0.2.y1)
  h0.2.y1.interpolate.func <- approxfun(y1, h0.2.y1, rule=2)
  H0.2.y1 <- sapply(y1, function(x) integrate(h0.2.y1.interpolate.func, 0, x, stop.on.error = F)$value)
  q.y1 <- H0.1.y1 * exp(eta.1) + H0.2.y1 * exp(eta.2)
  
  ## q.y2 <- kappa1*(y2)^alpha1 * exp(eta.1) + kappa2*(y2)^alpha2 * exp(eta.2)
  ## Essentially uses H0.1.y2 and H0.2.y2
  ############################################################################
  B0.1.y2 <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(predict(b.1, y2))))
  h0.1.y2 <- exp(B0.1.y2)
  h0.1.y2.interpolate.func <- approxfun(y2, h0.1.y2, rule=2)
  H0.1.y2 <- sapply(y2, function(x) integrate(h0.1.y2.interpolate.func, 0, x, stop.on.error = F)$value)
  
  h0.2.y2 <- exp(B0.2.y2)
  h0.2.y2.interpolate.func <- approxfun(y2, h0.2.y2, rule=2)
  H0.2.y2 <- sapply(y2, function(x) integrate(h0.2.y2.interpolate.func, 0, x, stop.on.error = F)$value)
  q.y2 <- H0.1.y2 * exp(eta.1) + H0.2.y2 * exp(eta.2)
  
  ## q.l <- kappa1*(l)^alpha1 * exp(eta.1) + kappa2*(l)^alpha2 * exp(eta.2)
  ## Essentially uses H0.1.l and H0.2.l
  ############################################################################
  B0.1.l <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(predict(b.1, l))))
  h0.1.l <- exp(B0.1.l)
  h0.1.l.interpolate.func <- approxfun(l, h0.1.l, rule=2)
  H0.1.l <- sapply(l, function(x) integrate(h0.1.l.interpolate.func, 0, x, stop.on.error = F)$value)
  
  B0.2.l <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(predict(b.2, l))))
  h0.2.l <- exp(B0.2.l)
  h0.2.l.interpolate.func <- approxfun(l, h0.2.l, rule=2)
  H0.2.l <- sapply(l, function(x) integrate(h0.2.l.interpolate.func, 0, x, stop.on.error = F)$value)
  q.l <- H0.1.l * exp(eta.1) + H0.2.l * exp(eta.2)
  
  ## w.y1.y2 <- kappa3*(y2-y1)^alpha3 * exp(eta.3)
  ## This is H0.3(y2-y1)
  ############################################################################
  h0.3.y2my1 <- exp(B0.3.y2my1)
  h0.3.y2my1.interpolate.func <- approxfun(y2-y1, h0.3.y2my1, rule=2)
  H0.3.y2my1 <- sapply(y2-y1, function(x) integrate(h0.3.y2my1.interpolate.func, 0, x, stop.on.error = F)$value)
  w.y1.y2 <- H0.3.y2my1 * exp(eta.3)
  
  ## w.y1.l  <- kappa3*(l-y1)^alpha3 * exp(eta.3)
  ## This is H0.3(l-y1)
  ############################################################################
  ## Don't need this if dropping prevalent cases
  #B0.3.lmy1 <- as.vector(matrix(phi3, nrow=1) %*% t(as.matrix(predict(b.3.y2my1, l-y1))))  ## Warnings - but do not apply in final likelihood
  #h0.3.lmy1 <- exp(B0.3.lmy1)
  #h0.3.lmy1.interpolate.func <- approxfun(l-y1, h0.3.lmy1, rule=2)
  #H0.3.lmy1 <- sapply(l-y1, function(x) integrate(h0.3.lmy1.interpolate.func, 0, x, stop.on.error = F)$value)
  ## If dropping prevalent nonterminal cases, then don't need the following:
  #H0.3.lmy1 <- sapply(l-y1, function(x) integrate(h0.3.t, 0, x, stop.on.error = F)$value)
  #w.y1.l  <- H0.3.lmy1 * exp(eta.3)
  
  ##
  k1 <- w.y1.y2
  k2.y1 <- q.y1 - q.l
  k2.y2 <- q.y2 - q.l
  #k3 <- w.y1.y2 - w.y1.l
  ##
  if(frailty == TRUE)
  {
    logLike1 <- log.h1star.y1 + log.h3star.y2 + log(1+theta) - ((thetaInv + 2) * log(1 + (theta * (k1 + k2.y1))))
    logLike2 <- log.h2star.y1 - ((thetaInv + 1) * log(1 + (theta * k2.y1)))  ## Making in terms of y1
    logLike3 <- log.h1star.y1 - ((thetaInv + 1) * log(1 + (theta * (k1 + k2.y1))))
    logLike4 <- - thetaInv * log(1 + (theta * k2.y1))  ## Making in terms of y1
    #logLike5 <- log.h3star.y2 - ((thetaInv + 1) * log(1 + (theta * k3)))
    #logLike6 <- - thetaInv * log(1 + (theta * k3))
  }
  if(frailty == FALSE)
  {
    logLike1 <- log.h1star.y1 + log.h3star.y2 - (k1 + k2.y1)
    logLike2 <- log.h2star.y1 - k2.y1  ## Making in terms of y1
    logLike3 <- log.h1star.y1 - (k1 + k2.y1)
    logLike4 <- - k2.y1  ## Making in terms of y1
    #logLike5 <- log.h3star.y2 - k3
    #logLike6 <- - k3
  }
  ##
  loglh <- sum(logLike1[type1==1]) + sum(logLike2[type2==1]) + sum(logLike3[type3==1]) + sum(logLike4[type4==1]) #+ sum(logLike5[type5==1]) + sum(logLike6[type6==1])
  ##
  return(-loglh)
}

## Just for the i'th individual
logLike.SCR.SM.LT.bSpline123.dropPrevCases.i <- function(para, y1, y2, delta1, delta2, l, Xmat1=NULL, Xmat2=NULL, Xmat3=NULL, frailty=TRUE,
                                                       b.1,  
                                                       b.2,  
                                                       b.3.y2my1,
                                                       i)
{
  ##
  if (is.vector(Xmat1)==T) Xmat1 = matrix(Xmat1, nrow=1)
  if (is.vector(Xmat2)==T) Xmat2 = matrix(Xmat2, nrow=1)
  if (is.vector(Xmat3)==T) Xmat3 = matrix(Xmat3, nrow=1)
  num.Bspline.params.1 <- ncol(b.1)
  num.Bspline.params.2 <- ncol(b.2)
  num.Bspline.params.3 <- ncol(b.3.y2my1)
  phi1 <- para[1:(1+num.Bspline.params.1-1)]
  phi2 <- para[(1+num.Bspline.params.1):(1+num.Bspline.params.1 + num.Bspline.params.2 - 1)]
  phi3 <- para[(1+num.Bspline.params.1 + num.Bspline.params.2):(1+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1)]
  
  if(frailty == TRUE){
    theta    <- exp(para[(2+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1)])
    thetaInv <- 1 / theta
  }
  ##
  nP.0 <- ifelse(frailty, (2+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1), (1+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1))
  nP.1 <- ncol(Xmat1)
  nP.2 <- ncol(Xmat2)
  nP.3 <- ncol(Xmat3)
  ##
  eta.1 <- as.vector(Xmat1 %*% para[nP.0 + c(1:nP.1)])
  eta.2 <- as.vector(Xmat2 %*% para[nP.0 + nP.1 + c(1:nP.2)])
  eta.3 <- as.vector(Xmat3 %*% para[nP.0 + nP.1 + nP.2 + c(1:nP.3)])
  
  ##
  type1 <- as.numeric(delta1 == 1 & delta2 == 1 & l < y1)
  type2 <- as.numeric(delta1 == 0 & delta2 == 1 & l < y1)
  type3 <- as.numeric(delta1 == 1 & delta2 == 0 & l < y1)
  type4 <- as.numeric(delta1 == 0 & delta2 == 0 & l < y1)
  ##
  ## log.h1star.y1 <- log(alpha1) + log(kappa1) + (alpha1 - 1) * log(y1) + eta.1
  ## Uses h1 - need to bSpline
  ## log.h1,0(t) = phi0 * B0(t) + ... + phik * Bk(t)
  ##############################################################################
  B0.1.y1 <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(b.1)))
  log.h1star.y1 <- B0.1.y1 + eta.1
  
  ## log.h2star.y1 <- log(alpha2) + log(kappa2) + (alpha2 - 1) * log(y1) + eta.2
  ##############################################################################
  B0.2.y1 <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(predict(b.2, y1))))
  log.h2star.y1 <- B0.2.y1 + eta.2
  
  ## log.h2star.y2 <- log(alpha2) + log(kappa2) + (alpha2 - 1) * log(y2) + eta.2
  ##############################################################################
  B0.2.y2 <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(b.2)))
  log.h2star.y2 <- B0.2.y2 + eta.2
  
  ## log.h3star.y2 <- log(alpha3) + log(kappa3) + (alpha3 - 1) * log(y2-y1) + eta.3
  ##################################################################################
  B0.3.y2my1 <- as.vector(matrix(phi3, nrow=1) %*% t(as.matrix(b.3.y2my1)))
  log.h3star.y2 <- B0.3.y2my1 + eta.3
  
  ## q.y1 <- kappa1*(y1)^alpha1 * exp(eta.1) + kappa2*(y1)^alpha2 * exp(eta.2)
  ## Uses h1 - needs bSpline
  ## Essentially uses H0.1.y1 and H0.2.y1
  ## exp(phi.3.truth %*% t(b.3.event))
  ############################################################################
  h0.1.y1 <- exp(B0.1.y1)
  h0.1.y1.interpolate.func <- approxfun(y1, h0.1.y1, rule=2)
  H0.1.y1 <- sapply(y1, function(x) integrate(h0.1.y1.interpolate.func, 0, x, stop.on.error = F)$value)
  
  h0.2.y1 <- exp(B0.2.y1)
  h0.2.y1.interpolate.func <- approxfun(y1, h0.2.y1, rule=2)
  H0.2.y1 <- sapply(y1, function(x) integrate(h0.2.y1.interpolate.func, 0, x, stop.on.error = F)$value)
  q.y1 <- H0.1.y1 * exp(eta.1) + H0.2.y1 * exp(eta.2)
  
  ## q.y2 <- kappa1*(y2)^alpha1 * exp(eta.1) + kappa2*(y2)^alpha2 * exp(eta.2)
  ## Essentially uses H0.1.y2 and H0.2.y2
  ############################################################################
  B0.1.y2 <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(predict(b.1, y2))))
  h0.1.y2 <- exp(B0.1.y2)
  h0.1.y2.interpolate.func <- approxfun(y2, h0.1.y2, rule=2)
  H0.1.y2 <- sapply(y2, function(x) integrate(h0.1.y2.interpolate.func, 0, x, stop.on.error = F)$value)
  
  h0.2.y2 <- exp(B0.2.y2)
  h0.2.y2.interpolate.func <- approxfun(y2, h0.2.y2, rule=2)
  H0.2.y2 <- sapply(y2, function(x) integrate(h0.2.y2.interpolate.func, 0, x, stop.on.error = F)$value)
  q.y2 <- H0.1.y2 * exp(eta.1) + H0.2.y2 * exp(eta.2)
  
  ## q.l <- kappa1*(l)^alpha1 * exp(eta.1) + kappa2*(l)^alpha2 * exp(eta.2)
  ## Essentially uses H0.1.l and H0.2.l
  ############################################################################
  B0.1.l <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(predict(b.1, l))))
  h0.1.l <- exp(B0.1.l)
  h0.1.l.interpolate.func <- approxfun(l, h0.1.l, rule=2)
  H0.1.l <- sapply(l, function(x) integrate(h0.1.l.interpolate.func, 0, x, stop.on.error = F)$value)
  
  B0.2.l <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(predict(b.2, l))))
  h0.2.l <- exp(B0.2.l)
  h0.2.l.interpolate.func <- approxfun(l, h0.2.l, rule=2)
  H0.2.l <- sapply(l, function(x) integrate(h0.2.l.interpolate.func, 0, x, stop.on.error = F)$value)
  q.l <- H0.1.l * exp(eta.1) + H0.2.l * exp(eta.2)
  
  ## w.y1.y2 <- kappa3*(y2-y1)^alpha3 * exp(eta.3)
  ## This is H0.3(y2-y1)
  ############################################################################
  h0.3.y2my1 <- exp(B0.3.y2my1)
  h0.3.y2my1.interpolate.func <- approxfun(y2-y1, h0.3.y2my1, rule=2)
  H0.3.y2my1 <- sapply(y2-y1, function(x) integrate(h0.3.y2my1.interpolate.func, 0, x, stop.on.error = F)$value)
  w.y1.y2 <- H0.3.y2my1 * exp(eta.3)
  
  ##
  k1 <- w.y1.y2
  k2.y1 <- q.y1 - q.l
  k2.y2 <- q.y2 - q.l
  #k3 <- w.y1.y2 - w.y1.l
  ##
  if(frailty == TRUE)
  {
    logLike1 <- log.h1star.y1 + log.h3star.y2 + log(1+theta) - ((thetaInv + 2) * log(1 + (theta * (k1 + k2.y1))))
    logLike2 <- log.h2star.y1 - ((thetaInv + 1) * log(1 + (theta * k2.y1)))  ## Making in terms of y1
    logLike3 <- log.h1star.y1 - ((thetaInv + 1) * log(1 + (theta * (k1 + k2.y1))))
    logLike4 <- - thetaInv * log(1 + (theta * k2.y1))  ## Making in terms of y1
  }
  if(frailty == FALSE)
  {
    logLike1 <- log.h1star.y1 + log.h3star.y2 - (k1 + k2.y1)
    logLike2 <- log.h2star.y1 - k2.y1  ## Making in terms of y1
    logLike3 <- log.h1star.y1 - (k1 + k2.y1)
    logLike4 <- - k2.y1  ## Making in terms of y1
  }
  ##
  loglh <- logLike1[i]*type1[i]+logLike2[i]*type2[i]+logLike3[i]*type3[i]+logLike4[i]*type4[i]
    #sum(logLike1[type1==1]) + sum(logLike2[type2==1]) + sum(logLike3[type3==1]) + sum(logLike4[type4==1])  
  ##
  return(-loglh)
}



### This one will allow us to get sandwich estimator :-)
logLike.SCR.SM.LT.bSpline123.dropPrevCases.Predict <- function(para , y1, y2, delta1, delta2, l, Xmat1, Xmat2, Xmat3, frailty,
                                                               b.1, bdy.knots.b.1, 
                                                               b.2, bdy.knots.b.2, 
                                                               b.3.y2my1, bdy.knots.b.3.y2my1)
{
  ##
  if (is.vector(Xmat1)==T) Xmat1 = matrix(Xmat1, nrow=1)
  if (is.vector(Xmat2)==T) Xmat2 = matrix(Xmat2, nrow=1)
  if (is.vector(Xmat3)==T) Xmat3 = matrix(Xmat3, nrow=1)
  num.Bspline.params.1 <- ncol(b.1)
  num.Bspline.params.2 <- ncol(b.2)
  num.Bspline.params.3 <- ncol(b.3.y2my1)
  phi1 <- para[1:(1+num.Bspline.params.1-1)]
  phi2 <- para[(1+num.Bspline.params.1):(1+num.Bspline.params.1 + num.Bspline.params.2 - 1)]
  phi3 <- para[(1+num.Bspline.params.1 + num.Bspline.params.2):(1+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1)]
  
  if(frailty == TRUE){
    theta    <- exp(para[(2+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1)])
    thetaInv <- 1 / theta
  }
  ##
  nP.0 <- ifelse(frailty, (2+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1), (1+num.Bspline.params.1 + num.Bspline.params.2 + num.Bspline.params.3 - 1))
  nP.1 <- ncol(Xmat1)
  nP.2 <- ncol(Xmat2)
  nP.3 <- ncol(Xmat3)
  ##
  eta.1 <- as.vector(Xmat1 %*% para[nP.0 + c(1:nP.1)])
  eta.2 <- as.vector(Xmat2 %*% para[nP.0 + nP.1 + c(1:nP.2)])
  eta.3 <- as.vector(Xmat3 %*% para[nP.0 + nP.1 + nP.2 + c(1:nP.3)])
  
  ##
  type1 <- as.numeric(delta1 == 1 & delta2 == 1 & l < y1)
  type2 <- as.numeric(delta1 == 0 & delta2 == 1 & l < y1)
  type3 <- as.numeric(delta1 == 1 & delta2 == 0 & l < y1)
  type4 <- as.numeric(delta1 == 0 & delta2 == 0 & l < y1)
  #type5 <- as.numeric(delta1 == 1 & delta2 == 1 & y1 <= l & l < y2)
  #type6 <- as.numeric(delta1 == 1 & delta2 == 0 & y1 <= l & l < y2)
  ##
  ## log.h1star.y1 <- log(alpha1) + log(kappa1) + (alpha1 - 1) * log(y1) + eta.1
  ## Uses h1 - need to bSpline
  ## log.h1,0(t) = phi0 * B0(t) + ... + phik * Bk(t)
  ##############################################################################
  B0.1.y1 <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(b.1)))
  log.h1star.y1 <- B0.1.y1 + eta.1
  
  ## log.h2star.y1 <- log(alpha2) + log(kappa2) + (alpha2 - 1) * log(y1) + eta.2
  ##############################################################################
  B0.2.y1 <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(predict(b.2, y1))))
  log.h2star.y1 <- B0.2.y1 + eta.2
  
  ## log.h2star.y2 <- log(alpha2) + log(kappa2) + (alpha2 - 1) * log(y2) + eta.2
  ##############################################################################
  B0.2.y2 <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(b.2)))
  log.h2star.y2 <- B0.2.y2 + eta.2
  
  ## log.h3star.y2 <- log(alpha3) + log(kappa3) + (alpha3 - 1) * log(y2-y1) + eta.3
  ##################################################################################
  B0.3.y2my1 <- as.vector(matrix(phi3, nrow=1) %*% t(as.matrix(b.3.y2my1)))
  log.h3star.y2 <- B0.3.y2my1 + eta.3
  
  ## q.y1 <- kappa1*(y1)^alpha1 * exp(eta.1) + kappa2*(y1)^alpha2 * exp(eta.2)
  ## Uses h1 - needs bSpline
  ## Essentially uses H0.1.y1 and H0.2.y1
  ## exp(phi.3.truth %*% t(b.3.event))
  ############################################################################
  h0.1.y1 <- exp(B0.1.y1)
  #h0.1.y1.interpolate.func <- approxfun(y1, h0.1.y1, rule=2)
  h0.1.t.support <- function(t) exp(phi.1.truth %*% t(predict(b.1, t)))
  h0.1.t <- function(t){
    y = rep(NA, length(t))
    y[which(((t >= bdy.knots.b.1[1]) & (t <= bdy.knots.b.1[2])) == T)] = h0.1.t.support(t[which(((t >= bdy.knots.b.1[1]) & (t <= bdy.knots.b.1[2])) == T)])
    y[which(t > bdy.knots.b.1[2])] = h0.1.t.support(bdy.knots.b.1[2])
    y[which(t < bdy.knots.b.1[1])] = h0.1.t.support(bdy.knots.b.1[1])
    return(y)
  }
  #H0.1.y1 <- sapply(y1, function(x) integrate(h0.1.y1.interpolate.func, 0, x, stop.on.error = F)$value)
  H0.1.y1 <- sapply(y1, function(x) integrate(h0.1.t, 0, x, stop.on.error = F)$value)
  
  h0.2.y1 <- exp(B0.2.y1)
  #h0.2.y1.interpolate.func <- approxfun(y1, h0.2.y1, rule=2)
  h0.2.t.support <- function(t) exp(phi.2.truth %*% t(predict(b.2, t)))
  h0.2.t <- function(t){
    y = rep(NA, length(t))
    y[which(((t >= bdy.knots.b.2[1]) & (t <= bdy.knots.b.2[2])) == T)] = h0.2.t.support(t[which(((t >= bdy.knots.b.2[1]) & (t <= bdy.knots.b.2[2])) == T)])
    y[which(t > bdy.knots.b.2[2])] = h0.2.t.support(bdy.knots.b.2[2])
    y[which(t < bdy.knots.b.2[1])] = h0.2.t.support(bdy.knots.b.2[1])
    return(y)
  }
  #H0.2.y1 <- sapply(y1, function(x) integrate(h0.2.y1.interpolate.func, 0, x, stop.on.error = F)$value)
  H0.2.y1 <- sapply(y1, function(x) integrate(h0.2.t, 0, x, stop.on.error = F)$value)
  q.y1 <- H0.1.y1 * exp(eta.1) + H0.2.y1 * exp(eta.2)
  
  ## q.y2 <- kappa1*(y2)^alpha1 * exp(eta.1) + kappa2*(y2)^alpha2 * exp(eta.2)
  ## Essentially uses H0.1.y2 and H0.2.y2
  ############################################################################
  B0.1.y2 <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(predict(b.1, y2))))
  h0.1.y2 <- exp(B0.1.y2)
  #h0.1.y2.interpolate.func <- approxfun(y2, h0.1.y2, rule=2)
  #H0.1.y2 <- sapply(y2, function(x) integrate(h0.1.y2.interpolate.func, 0, x, stop.on.error = F)$value)
  H0.1.y2 <- sapply(y2, function(x) integrate(h0.1.t, 0, x, stop.on.error = F)$value)
  
  h0.2.y2 <- exp(B0.2.y2)
  #h0.2.y2.interpolate.func <- approxfun(y2, h0.2.y2, rule=2)
  #H0.2.y2 <- sapply(y2, function(x) integrate(h0.2.y2.interpolate.func, 0, x, stop.on.error = F)$value)
  H0.2.y2 <- sapply(y2, function(x) integrate(h0.2.t, 0, x, stop.on.error = F)$value)
  q.y2 <- H0.1.y2 * exp(eta.1) + H0.2.y2 * exp(eta.2)
  
  ## q.l <- kappa1*(l)^alpha1 * exp(eta.1) + kappa2*(l)^alpha2 * exp(eta.2)
  ## Essentially uses H0.1.l and H0.2.l
  ############################################################################
  B0.1.l <- as.vector(matrix(phi1, nrow=1) %*% t(as.matrix(predict(b.1, l))))
  h0.1.l <- exp(B0.1.l)
  #h0.1.l.interpolate.func <- approxfun(l, h0.1.l, rule=2)
  #H0.1.l <- sapply(l, function(x) integrate(h0.1.l.interpolate.func, 0, x, stop.on.error = F)$value)
  H0.1.l <- sapply(l, function(x) integrate(h0.1.t, 0, x, stop.on.error = F)$value)
  
  B0.2.l <- as.vector(matrix(phi2, nrow=1) %*% t(as.matrix(predict(b.2, l))))
  h0.2.l <- exp(B0.2.l)
  #h0.2.l.interpolate.func <- approxfun(l, h0.2.l, rule=2)
  #H0.2.l <- sapply(l, function(x) integrate(h0.2.l.interpolate.func, 0, x, stop.on.error = F)$value)
  H0.2.l <- sapply(l, function(x) integrate(h0.2.t, 0, x, stop.on.error = F)$value)
  q.l <- H0.1.l * exp(eta.1) + H0.2.l * exp(eta.2)
  
  ## w.y1.y2 <- kappa3*(y2-y1)^alpha3 * exp(eta.3)
  ## This is H0.3(y2-y1)
  ############################################################################
  h0.3.y2my1 <- exp(B0.3.y2my1)
  #h0.3.y2my1.interpolate.func <- approxfun(y2-y1, h0.3.y2my1, rule=2)
  h0.3.t.support <- function(t) exp(phi.3.truth %*% t(predict(b.3.y2my1, t)))
  h0.3.t <- function(t){
    y = rep(NA, length(t))
    y[which(((t >= bdy.knots.b.3.y2my1[1]) & (t <= bdy.knots.b.3.y2my1[2])) == T)] = h0.3.t.support(t[which(((t >= bdy.knots.b.3.y2my1[1]) & (t <= bdy.knots.b.3.y2my1[2])) == T)])
    y[which(t > bdy.knots.b.3.y2my1[2])] = h0.3.t.support(bdy.knots.b.3.y2my1[2])
    y[which(t < bdy.knots.b.3.y2my1[1])] = h0.3.t.support(bdy.knots.b.3.y2my1[1])
    return(y)
  }
  H0.3.y2my1 <- sapply(y2-y1, function(x) integrate(h0.3.t, 0, x, stop.on.error = F)$value)
  w.y1.y2 <- H0.3.y2my1 * exp(eta.3)
  
  ## w.y1.l  <- kappa3*(l-y1)^alpha3 * exp(eta.3)
  ## This is H0.3(l-y1)
  ############################################################################
  ## Don't need this if dropping prevalent cases
  #B0.3.lmy1 <- as.vector(matrix(phi3, nrow=1) %*% t(as.matrix(predict(b.3.y2my1, l-y1))))  ## Warnings - but do not apply in final likelihood
  #h0.3.lmy1 <- exp(B0.3.lmy1)
  #h0.3.lmy1.interpolate.func <- approxfun(l-y1, h0.3.lmy1, rule=2)
  #H0.3.lmy1 <- sapply(l-y1, function(x) integrate(h0.3.lmy1.interpolate.func, 0, x, stop.on.error = F)$value)
  ## If dropping prevalent nonterminal cases, then don't need the following:
  #H0.3.lmy1 <- sapply(l-y1, function(x) integrate(h0.3.t, 0, x, stop.on.error = F)$value)
  #w.y1.l  <- H0.3.lmy1 * exp(eta.3)
  
  ##
  k1 <- w.y1.y2
  k2.y1 <- q.y1 - q.l
  k2.y2 <- q.y2 - q.l
  #k3 <- w.y1.y2 - w.y1.l
  ##
  if(frailty == TRUE)
  {
    logLike1 <- log.h1star.y1 + log.h3star.y2 + log(1+theta) - ((thetaInv + 2) * log(1 + (theta * (k1 + k2.y1))))
    logLike2 <- log.h2star.y1 - ((thetaInv + 1) * log(1 + (theta * k2.y1)))  ## Making in terms of y1
    logLike3 <- log.h1star.y1 - ((thetaInv + 1) * log(1 + (theta * (k1 + k2.y1))))
    logLike4 <- - thetaInv * log(1 + (theta * k2.y1))  ## Making in terms of y1
    #logLike5 <- log.h3star.y2 - ((thetaInv + 1) * log(1 + (theta * k3)))
    #logLike6 <- - thetaInv * log(1 + (theta * k3))
  }
  if(frailty == FALSE)
  {
    logLike1 <- log.h1star.y1 + log.h3star.y2 - (k1 + k2.y1)
    logLike2 <- log.h2star.y1 - k2.y1  ## Making in terms of y1
    logLike3 <- log.h1star.y1 - (k1 + k2.y1)
    logLike4 <- - k2.y1  ## Making in terms of y1
    #logLike5 <- log.h3star.y2 - k3
    #logLike6 <- - k3
  }
  ##
  loglh <- sum(logLike1[type1==1]) + sum(logLike2[type2==1]) + sum(logLike3[type3==1]) + sum(logLike4[type4==1]) #+ sum(logLike5[type5==1]) + sum(logLike6[type6==1])
  ##
  return(-loglh)
}


## Fitting illness-death, shared frailty, on left-truncated data
## bspline baseline hazard functions
## Note: startVals must be specified (see get.Bspline.startVals)
## 2019-10-07: Adding sandwich estimator
FreqID.LT.bSpline123.sand <- function(Y, lin.pred, data, model = "semi-Markov", startVals, frailty=TRUE, 
                      b.1, b.2, b.3.y2my1, 
                      bdy.knots.b.1, 
                      bdy.knots.b.2, 
                      bdy.knots.b.3.y2my1,
                      method = "optim", sandSE = F)
{	
  
  ##
  y1     <- as.vector(Y[,1])
  delta1 <- as.vector(Y[,2])
  y2     <- as.vector(Y[,3])
  delta2 <- as.vector(Y[,4])
  l      <- as.vector(Y[,5])
  Xmat1  <- as.matrix(model.frame(lin.pred[[1]], data=data))  
  Xmat2  <- as.matrix(model.frame(lin.pred[[2]], data=data))  
  Xmat3  <- as.matrix(model.frame(lin.pred[[3]], data=data))
  ##
  
  if(model == "semi-Markov")
  {
    if (method == "optim"){
      logLike <- function(p) logLike.SCR.SM.LT.bSpline123.dropPrevCases(p, y1=y1, y2=y2, delta1=delta1, delta2=delta2, l=l,
                                                  Xmat1=Xmat1, Xmat2=Xmat2, Xmat3=Xmat3, frailty=frailty,
                                                  b.1 = b.1,  
                                                  b.2 = b.2, 
                                                  b.3.y2my1 = b.3.y2my1)
    
      optim.control = list(REPORT = 50, maxit = 2000) ## Changed this!
    
      fit1 <- optim(startVals, #* runif(length(startVals), 0.9, 1.1), 
                  logLike, hessian = TRUE, method="Nelder-Mead", control = optim.control)
      
      H = fit1$hessian
      aSE = try(sqrt(diag(solve(H))))
      est = fit1$par
      logLike=-fit1$value
      code = fit1$convergence
    }
    if (method == "nlm"){    
      fit2 <- nlm(logLike.SCR.SM.LT.bSpline123.dropPrevCases, p=startVals, y1=y1, y2=y2,
                  delta1=delta1, delta2=delta2, l=l,
                  Xmat1=Xmat1, Xmat2=Xmat2, Xmat3=Xmat3, frailty=frailty,
                  b.1 = b.1,
                  b.2 = b.2,
                  b.3.y2my1 = b.3.y2my1, hessian=T)
      H = fit2$hessian
      logLike = -fit2$minimum
      aSE = try(sqrt(diag(solve(H))))
      est = fit2$estimate
      code = fit2$code
    }
  }
    ##
    myLabels <- c("phi1", "phi2", "phi3")
    if(frailty == TRUE) myLabels <- c(myLabels, "log(theta)")
    myLabels <- c(myLabels, colnames(Xmat1), colnames(Xmat2), colnames(Xmat3))
    nP <- c(ncol(Xmat1), ncol(Xmat2), ncol(Xmat3))
    
    #########################################
    ## Now adding sandwich estimator stuff
    
    if (sandSE == T){ 
      grad.mat <- matrix(NA, ncol=length(y1), nrow = length(startVals)^2) ## hold del^T del in the columns
      cat("Calculating meat...maybe take a bit \n")
      for (i in 1:length(y1)){
        #print(i)
        y1.i = y1[i]; y2.i = y2[i]; delta1.i = delta1[i]; delta2.i = delta2[i]; l.i = l[i]
        Xmat1.i = matrix(Xmat1[i,], nrow=1); Xmat2.i = matrix(Xmat2[i,], nrow=1); Xmat3.i = matrix(Xmat3[i,], nrow=1)
        # grad.i = grad(function(para){ logLike.SCR.SM.LT.bSpline123.dropPrevCases.Predict(para, 
        #                                                            y1=y1.i, y2=y2.i, delta1=delta1.i, delta2=delta2.i, l=l.i, 
        #                                                            Xmat1=Xmat1.i, 
        #                                                            Xmat2=Xmat2.i, 
        #                                                            Xmat3=Xmat3.i,
        #                                                            frailty=frailty,
        #                                                            b.1=b.1, bdy.knots.b.1=bdy.knots.b.1, 
        #                                                            b.2=b.2, bdy.knots.b.2=bdy.knots.b.2, 
        #                                                            b.3.y2my1=b.3.y2my1, bdy.knots.b.3.y2my1=bdy.knots.b.3.y2my1)}, est)
        
        grad.i = grad(function(para){ logLike.SCR.SM.LT.bSpline123.dropPrevCases.i(para, 
                                                                                   y1=y1, y2=y2, delta1=delta1, delta2=delta2, l=l, 
                                                                                   Xmat1=Xmat1, 
                                                                                   Xmat2=Xmat2, 
                                                                                   Xmat3=Xmat3,
                                                                                   frailty=frailty,
                                                                                   b.1=b.1,  
                                                                                   b.2=b.2,  
                                                                                   b.3.y2my1=b.3.y2my1, i=i)}, est)
        
        grad.i.mat = matrix(grad.i, ncol=1)
        V.i = grad.i.mat %*% t(grad.i.mat)
        grad.mat[,i] = as.vector(V.i)
      }
      V.hat = matrix(apply(grad.mat, 1, sum), ncol=length(startVals))
      
      rSE = try(sqrt(diag(solve(H) %*% V.hat %*% solve(H))))
      
      ##
      value <- list(estimate=est, H=H, logLike=logLike, myLabels=myLabels, frailty=frailty, nP=nP, 
                    aSE = aSE, rSE = rSE)
    }
    
    if (sandSE == F){
      value <- list(estimate=est, H=H, logLike=logLike, myLabels=myLabels, frailty=frailty, nP=nP, 
                    aSE = aSE, code = code)
    }
    if(model == "semi-Markov")
    {
      class(value) <- c("Freq", "ID", "Ind", "WB", "semi-Markov")
    }
    
    return(value)
  ##
  invisible()
}

## Fitting illness-death, shared frailty, on left-truncated data
## bspline baseline hazard functions
## Note: startVals must be specified (see get.Bspline.startVals)
## 2020-01-16: Testing!!!
## Need to specify optim.control : optim.control = list(REPORT = 50, maxit = 500)
FreqID.LT.bSpline123.test <- function(Y, lin.pred, data, model = "semi-Markov", startVals, frailty=TRUE, 
                                      b.1, b.2, b.3.y2my1, 
                                      bdy.knots.b.1, 
                                      bdy.knots.b.2, 
                                      bdy.knots.b.3.y2my1,
                                      method = "optim", 
                                      maxit = 500)
{	
  
  ##
  y1     <- as.vector(Y[,1])
  delta1 <- as.vector(Y[,2])
  y2     <- as.vector(Y[,3])
  delta2 <- as.vector(Y[,4])
  l      <- as.vector(Y[,5])
  Xmat1  <- as.matrix(model.frame(lin.pred[[1]], data=data))  
  Xmat2  <- as.matrix(model.frame(lin.pred[[2]], data=data))  
  Xmat3  <- as.matrix(model.frame(lin.pred[[3]], data=data))
  ##
  
  if(model == "semi-Markov")
  {
    if (method == "optim"){
      logLike <- function(p) logLike.SCR.SM.LT.bSpline123.dropPrevCases(p, y1=y1, y2=y2, delta1=delta1, delta2=delta2, l=l,
                                                                        Xmat1=Xmat1, Xmat2=Xmat2, Xmat3=Xmat3, frailty=frailty,
                                                                        b.1 = b.1,  
                                                                        b.2 = b.2, 
                                                                        b.3.y2my1 = b.3.y2my1)
      
      optim.control = list(REPORT = 50, maxit = maxit)
      
      fit1 <- optim(startVals, #* runif(length(startVals), 0.9, 1.1), 
                    logLike, hessian = TRUE, method="Nelder-Mead", control = optim.control)
      
      H = fit1$hessian
      aSE = try(sqrt(diag(solve(H))))
      est = fit1$par
      logLike=-fit1$value
      code = fit1$convergence
    }
    if (method == "nlm"){    
      fit1 <- nlm(logLike.SCR.SM.LT.bSpline123.dropPrevCases, p=startVals, y1=y1, y2=y2,
                  delta1=delta1, delta2=delta2, l=l,
                  Xmat1=Xmat1, Xmat2=Xmat2, Xmat3=Xmat3, frailty=frailty,
                  b.1 = b.1,
                  b.2 = b.2,
                  b.3.y2my1 = b.3.y2my1, hessian=T)
      H = fit1$hessian
      logLike = -fit1$minimum
      aSE = try(sqrt(diag(solve(H))))
      est = fit1$estimate
      code = fit1$code
    }
  }
  ##
  myLabels <- c("phi1", "phi2", "phi3")
  if(frailty == TRUE) myLabels <- c(myLabels, "log(theta)")
  myLabels <- c(myLabels, colnames(Xmat1), colnames(Xmat2), colnames(Xmat3))
  nP <- c(ncol(Xmat1), ncol(Xmat2), ncol(Xmat3))
  
  
 
  value <- list(fit.object = fit1, estimate=est, H=H, logLike=logLike, myLabels=myLabels, frailty=frailty, nP=nP, 
                aSE = aSE)
  
  if(model == "semi-Markov")
  {
    class(value) <- c("Freq", "ID", "Ind", "WB", "semi-Markov")
  }
  
  return(value)
  ##
  invisible()
}



## Getting bspline starting values for each baseline hazard
## It's convoluted, but it's the best that I could do
get.Bspline.startVals <- function(y, delta, lin.pred, data, b, knot.loc, Bspline.degree, method="nlm"){
  ## 
  num.Bspline.params <- length(knot.loc) + Bspline.degree + 1
  
  fitCox <- coxph(as.formula(paste("Surv(y, delta)", paste(lin.pred, collapse = ""))), data=data)
  H0.info <- basehaz(fitCox, centered = F) ## Get cumulative hazard from Cox
  H0.est.linInterpol <- approxfun(H0.info$time, H0.info$hazard, rule = 2) ## Get lin interpolated function
  yvals <- seq(min(y), max(y), length=500) ## get plenty of y-values
  h0.est.func2 <- numdiff(H0.est.linInterpol, yvals) ## estimate h0 using numerical differentiation
  h0.est.smooth.xy <- loess.smooth(yvals, h0.est.func2, evaluation=500) ## Smooth out using loess
  
  ## Now using least squares to get estimated phi coefficients based on loess-smoothed h0
  h0.est.smooth <- h0.est.smooth.xy$y
  yvals.bspline <- data.frame(predict(b, yvals))
  
  obj.fn.1 <- function(eta.vec, spline.pred, h0.truth){ 
    ##
    spline.vals <- sapply(1:nrow(spline.pred), function(i) sum(spline.pred[i,]*(eta.vec)))
    sq.diffs <- (log(h0.truth)-spline.vals)^2
    return(sum(sq.diffs))
  }
  if (method == "nlm"){
    phi.h0.est.smooth=nlm(f=obj.fn.1, p=rep(-1,num.Bspline.params), 
                          spline.pred=yvals.bspline, 
                          h0.truth=h0.est.smooth)$estimate
    return(c(phi.h0.est.smooth, fitCox$coef))
  }
  if (method == "nls"){
    ## Alternatively -- this seems to give better results? 
    g <- function(bSpline.mat, phi.vec){
      phi.list <- as.list(phi.vec)
      mat.list <- as.list(data.frame(bSpline.mat))
      return(apply(do.call(rbind, Map('*', phi.list, mat.list)), 2, sum))
    }
    phi.h0.est.smooth.ls <- nls(h0.est.smooth ~ exp(g(yvals.bspline, phi.vec)), 
                                start = list(phi.vec = rep(-1, ncol(yvals.bspline))))
    phi.h0.est.smooth <- summary(phi.h0.est.smooth.ls)$parameters[,1]  ## These will be good for starting values!
    return(c(phi.h0.est.smooth, fitCox$coef))
  }
}


################
## Weibull BH ##
################
## Log-likelihood illness-death, shared frailty, left-truncated data
## Weibull baseline hazards
logLike.weibull.SCR.SM.LT <- function(para, y1, y2, delta1, delta2, l, Xmat1=NULL, Xmat2=NULL, Xmat3=NULL, frailty=TRUE)
{
  ##
  kappa1    <- exp(para[1])
  alpha1 <- exp(para[2])
  kappa2    <- exp(para[3])
  alpha2 <- exp(para[4])
  kappa3    <- exp(para[5])
  alpha3 <- exp(para[6])
  if(frailty == TRUE){
    theta    <- exp(para[7])
    thetaInv <- 1 / theta
  }
  ##
  nP.0 <- ifelse(frailty, 7, 6)
  nP.1 <- ncol(Xmat1)
  nP.2 <- ncol(Xmat2)
  nP.3 <- ncol(Xmat3)
  ##
  eta.1 <- as.vector(Xmat1 %*% para[nP.0 + c(1:nP.1)])
  eta.2 <- as.vector(Xmat2 %*% para[nP.0 + nP.1 + c(1:nP.2)])
  eta.3 <- as.vector(Xmat3 %*% para[nP.0 + nP.1 + nP.2 + c(1:nP.3)])
  ##
  type1 <- as.numeric(delta1 == 1 & delta2 == 1 & l < y1)
  type2 <- as.numeric(delta1 == 0 & delta2 == 1 & l < y1)
  type3 <- as.numeric(delta1 == 1 & delta2 == 0 & l < y1)
  type4 <- as.numeric(delta1 == 0 & delta2 == 0 & l < y1)
  type5 <- as.numeric(delta1 == 1 & delta2 == 1 & y1 <= l & l < y2)
  type6 <- as.numeric(delta1 == 1 & delta2 == 0 & y1 <= l & l < y2)
  ##
  log.h1star.y1 <- log(alpha1) + log(kappa1) + (alpha1 - 1) * log(y1) + eta.1
  log.h2star.y1 <- log(alpha2) + log(kappa2) + (alpha2 - 1) * log(y1) + eta.2
  log.h2star.y2 <- log(alpha2) + log(kappa2) + (alpha2 - 1) * log(y2) + eta.2
  log.h3star.y2 <- log(alpha3) + log(kappa3) + (alpha3 - 1) * log(y2-y1) + eta.3
  ##
  q.y1 <- kappa1*(y1)^alpha1 * exp(eta.1) + kappa2*(y1)^alpha2 * exp(eta.2)
  q.y2 <- kappa1*(y2)^alpha1 * exp(eta.1) + kappa2*(y2)^alpha2 * exp(eta.2)
  q.l <- kappa1*(l)^alpha1 * exp(eta.1) + kappa2*(l)^alpha2 * exp(eta.2)
  ##
  w.y1.y2 <- kappa3*(y2-y1)^alpha3 * exp(eta.3)
  w.y1.l  <- kappa3*(l-y1)^alpha3 * exp(eta.3)
  ##
  k1 <- w.y1.y2
  k2.y1 <- q.y1 - q.l
  k2.y2 <- q.y2 - q.l
  k3 <- w.y1.y2 - w.y1.l
  ##
  if(frailty == TRUE)
  {
    logLike1 <- log.h1star.y1 + log.h3star.y2 + log(1+theta) - ((thetaInv + 2) * log(1 + (theta * (k1 + k2.y1))))
    logLike2 <- log.h2star.y1 - ((thetaInv + 1) * log(1 + (theta * k2.y1)))  ## Making in terms of y1
    logLike3 <- log.h1star.y1 - ((thetaInv + 1) * log(1 + (theta * (k1 + k2.y1))))
    logLike4 <- - thetaInv * log(1 + (theta * k2.y1))  ## Making in terms of y1
    logLike5 <- log.h3star.y2 - ((thetaInv + 1) * log(1 + (theta * k3)))
    logLike6 <- - thetaInv * log(1 + (theta * k3))
  }
  if(frailty == FALSE)
  {
    logLike1 <- log.h1star.y1 + log.h3star.y2 - (k1 + k2.y1)
    logLike2 <- log.h2star.y1 - k2.y1  ## Making in terms of y1
    logLike3 <- log.h1star.y1 - (k1 + k2.y1)
    logLike4 <- - k2.y1  ## Making in terms of y1
    logLike5 <- log.h3star.y2 - k3
    logLike6 <- - k3
  }
  ##
  loglh <- sum(logLike1[type1==1]) + sum(logLike2[type2==1]) + sum(logLike3[type3==1]) + sum(logLike4[type4==1]) + sum(logLike5[type5==1]) + sum(logLike6[type6==1])
  ##
  return(-loglh)
}

## Fit model: illness-death, shared frailty, left-truncated data
## Weibull baseline hazards
FreqID.LT <- function(Y, lin.pred, data, model = "semi-Markov", startVals, frailty=TRUE, method="optim")
{	
  
  ##
  y1     <- as.vector(Y[,1])
  delta1 <- as.vector(Y[,2])
  y2     <- as.vector(Y[,3])
  delta2 <- as.vector(Y[,4])
  l      <- as.vector(Y[,5])
  Xmat1  <- as.matrix(model.frame(lin.pred[[1]], data=data))  
  Xmat2  <- as.matrix(model.frame(lin.pred[[2]], data=data))  
  Xmat3  <- as.matrix(model.frame(lin.pred[[3]], data=data))
  ##
  fit.survreg.1 <- survreg(as.formula(paste("Surv(y1, delta1) ", as.character(lin.pred[[1]])[1], as.character(lin.pred[[1]])[2])), dist="weibull", data=data)
  fit.survreg.2 <- survreg(as.formula(paste("Surv(y2, delta2) ", as.character(lin.pred[[2]])[1], as.character(lin.pred[[2]])[2])), dist="weibull", data=data)
  data.delta1_1 = data[delta1==1,]
  data.delta1_1$y2.m.y1 = y2[delta1==1] - y1[delta1==1]
  fit.survreg.3 <- survreg(as.formula(paste("Surv(y2.m.y1, delta2) ", as.character(lin.pred[[3]])[1], as.character(lin.pred[[3]])[2])), dist="weibull", data=data.delta1_1)
  alpha1      <- 1 / fit.survreg.1$scale
  alpha2      <- 1 / fit.survreg.2$scale
  alpha3     	<- 1 / fit.survreg.3$scale
  
  if (is.null(startVals)==T){
    startVals     <- c(-alpha1*coef(fit.survreg.1)[1], log(alpha1),
                       -alpha2*coef(fit.survreg.2)[1], log(alpha2),
                       -alpha3*coef(fit.survreg.3)[1], log(alpha3))
    if(frailty == TRUE) startVals <- c(startVals, 0.5)
    startVals     <- c(startVals,
                       -coef(fit.survreg.1)[-1] * alpha1,
                       -coef(fit.survreg.2)[-1] * alpha2,
                       -coef(fit.survreg.3)[-1] * alpha3)
  }
  
  if(model == "semi-Markov")
  {
    if (method == "optim"){
    cat("fitting optim...please wait \n")
    logLike <- function(p) logLike.weibull.SCR.SM.LT(p, y1=y1, y2=y2, delta1=delta1, delta2=delta2, l=l,
                                                     Xmat1=Xmat1, Xmat2=Xmat2, Xmat3=Xmat3, frailty=frailty)
    optim.control = list(REPORT = 50)
    fit1 <- optim(startVals, #* runif(length(startVals), 0.9, 1.1), 
                  logLike, hessian = TRUE, method="Nelder-Mead", control = optim.control)
    value <- list(estimate=fit1$par, H=fit1$hessian, logLike=-fit1$value, code=fit1$convergence)#, Xmat=list(Xmat1, Xmat2, Xmat3))
    }
    if (method == "nlm"){
      fit1  <- suppressWarnings(nlm(logLike.weibull.SCR.SM.LT, p=startVals,
                                    y1=y1, delta1=delta1, y2=y2, delta2=delta2, Xmat1=as.matrix(Xmat1), Xmat2=as.matrix(Xmat2), Xmat3=as.matrix(Xmat3),
                                    l = l, frailty=frailty,
                                    iterlim=1000, hessian=TRUE))
      value <- list(estimate=fit1$est, H=fit1$hessian, logLike=-fit1$minimum, code=fit1$code)
    }
  }
  ##
  # myLabels <- c("log(kappa1)", "log(alpha1)", "log(kappa2)", "log(alpha2)", "log(kappa3)", "log(alpha3)")
  # if(frailty == TRUE) myLabels <- c(myLabels, "log(theta)")
  # myLabels <- c(myLabels, colnames(Xmat1), colnames(Xmat2), colnames(Xmat3))
  # nP <- c(ncol(Xmat1), ncol(Xmat2), ncol(Xmat3))
  ##
  
  
  if(model == "semi-Markov")
  {
    class(value) <- c("Freq", "ID", "Ind", "WB", "semi-Markov")
  }
  
  return(value)
  ##
  invisible()
}


## For estimating B-spline basis coefficients
obj.fn.1 <- function(eta.vec, spline.pred, h0.truth){ 
  ##
  spline.vals <- sapply(1:nrow(spline.pred), function(i) sum(spline.pred[i,]*(eta.vec)))
  sq.diffs <- (log(h0.truth)-spline.vals)^2
  return(sum(sq.diffs))
}


## Fit model: illness-death, shared frailty, left-truncated data
## Weibull baseline hazards
## Adding sandwich estimator!!!
FreqID.LT.sand <- function(Y, lin.pred, data, model = "semi-Markov", startVals, frailty=TRUE)
{	
  
  ##
  y1     <- as.vector(Y[,1])
  delta1 <- as.vector(Y[,2])
  y2     <- as.vector(Y[,3])
  delta2 <- as.vector(Y[,4])
  l      <- as.vector(Y[,5])
  Xmat1  <- as.matrix(model.frame(lin.pred[[1]], data=data))  
  Xmat2  <- as.matrix(model.frame(lin.pred[[2]], data=data))  
  Xmat3  <- as.matrix(model.frame(lin.pred[[3]], data=data))
  ##
  fit.survreg.1 <- survreg(as.formula(paste("Surv(y1, delta1) ", as.character(lin.pred[[1]])[1], as.character(lin.pred[[1]])[2])), dist="weibull", data=data)
  fit.survreg.2 <- survreg(as.formula(paste("Surv(y2, delta2) ", as.character(lin.pred[[2]])[1], as.character(lin.pred[[2]])[2])), dist="weibull", data=data)
  data.delta1_1 = data[delta1==1,]
  data.delta1_1$y2.m.y1 = y2[delta1==1] - y1[delta1==1]
  fit.survreg.3 <- survreg(as.formula(paste("Surv(y2.m.y1, delta2) ", as.character(lin.pred[[3]])[1], as.character(lin.pred[[3]])[2])), dist="weibull", data=data.delta1_1)
  alpha1      <- 1 / fit.survreg.1$scale
  alpha2      <- 1 / fit.survreg.2$scale
  alpha3     	<- 1 / fit.survreg.3$scale
  
  if (is.null(startVals)==T){
    startVals     <- c(-alpha1*coef(fit.survreg.1)[1], log(alpha1),
                       -alpha2*coef(fit.survreg.2)[1], log(alpha2),
                       -alpha3*coef(fit.survreg.3)[1], log(alpha3))
    if(frailty == TRUE) startVals <- c(startVals, 0.5)
    startVals     <- c(startVals,
                       -coef(fit.survreg.1)[-1] * alpha1,
                       -coef(fit.survreg.2)[-1] * alpha2,
                       -coef(fit.survreg.3)[-1] * alpha3)
  }
  
  if(model == "semi-Markov")
  {
    logLike <- function(p) logLike.weibull.SCR.SM.LT(p, y1=y1, y2=y2, delta1=delta1, delta2=delta2, l=l,
                                                     Xmat1=Xmat1, Xmat2=Xmat2, Xmat3=Xmat3, frailty=frailty)
    optim.control = list(REPORT = 50)
    fit1 <- optim(startVals, #* runif(length(startVals), 0.9, 1.1), 
                  logLike, hessian = TRUE, method="Nelder-Mead", control = optim.control)
  }
  ##
  myLabels <- c("log(kappa1)", "log(alpha1)", "log(kappa2)", "log(alpha2)", "log(kappa3)", "log(alpha3)")
  if(frailty == TRUE) myLabels <- c(myLabels, "log(theta)")
  myLabels <- c(myLabels, colnames(Xmat1), colnames(Xmat2), colnames(Xmat3))
  nP <- c(ncol(Xmat1), ncol(Xmat2), ncol(Xmat3))
  ##
  #########################################
  ## Now adding sandwich estimator stuff
  grad.mat <- matrix(NA, ncol=length(y1), nrow = length(startVals)^2) ## hold del^T del in the columns
  cat("Calculating meat...maybe take a bit \n")
  for (i in 1:length(y1)){
    y1.i = y1[i]; y2.i = y2[i]; delta1.i = delta1[i]; delta2.i = delta2[i]; l.i = l[i]
    Xmat1.i = matrix(Xmat1[i,], nrow=1); Xmat2.i = matrix(Xmat2[i,], nrow=1); Xmat3.i = matrix(Xmat3[i,], nrow=1)
    grad.i = grad(function(para){ logLike.weibull.SCR.SM.LT(para, 
                              y1=y1.i, y2=y2.i, delta1=delta1.i, delta2=delta2.i, l=l.i, 
                              Xmat1=Xmat1.i, 
                              Xmat2=Xmat2.i, 
                              Xmat3=Xmat3.i, frailty=frailty)}, fit1$par)
    grad.i.mat = matrix(grad.i, ncol=1)
    V.i = grad.i.mat %*% t(grad.i.mat)
    grad.mat[,i] = as.vector(V.i)
  }
  V.hat = matrix(apply(grad.mat, 1, sum), ncol=length(startVals))
  
  H = fit1$hessian
  aSE = try(sqrt(diag(solve(H))))
  rSE = try(sqrt(diag(solve(H) %*% V.hat %*% solve(H))))
  
  ##
  value <- list(estimate=fit1$par, Finv=solve(fit1$hessian), logLike=-fit1$value, myLabels=myLabels, frailty=frailty, nP=nP, 
                H = H, aSE = aSE, rSE = rSE)#, Xmat=list(Xmat1, Xmat2, Xmat3))
  
  if(model == "semi-Markov")
  {
    class(value) <- c("Freq", "ID", "Ind", "WB", "semi-Markov")
  }
  
  return(value)
  ##
  invisible()
}


