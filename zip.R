### Packages
library(knitr)
require(keras)
library(tidyverse)
library(OpenMPController)
library(caret)
library(flexmix)
library(lattice)
library(MASS)
require(pscl) # alternatively can use package ZIM for zero-inflated models
library(lmtest)
library(sandwich)
library(ggplot2)
library(SIBER)
library(factoextra)
library(FactoMineR)
library(xtable)
library(clues)
library(MBCbook)
library(HDclassif)
library(dplyr)
library(SIBER)
library(pROC)
require("markdown")
require("rattle")
require("xtable")
require("stringr")
require("fBasics")
require("MASS")
require("survival")
require("STAR")
require("gamlss.dist")
require("VGAM")
require("ggplot2")
library(pscl)
library(sandwich)
library(data.table)
library(plotROC);library(gridExtra);library(grid)
cores <- parallel::detectCores()
#install.packages("optimization")
library(optimization)


#### Simulation Study 

# Set the number of column of X and fix G

d <- 3; k <- 3; n <- 500; c1 <- 2; c2 <- 3

#d <- d1 + c1 + c2

sigma <- list()

mean <- matrix(c(.1,-2,2,0,1,3), nrow = (k-1), ncol = d)

set.seed(20)
sigma1 <- diag(d); mean1 <- rnorm(d)

for(l in 1:(k-1)) {
  
  sigma[[l]] <- diag(d)
  
}

pu <- z <- NULL
pr <- matrix(NA, nrow = n, ncol = k-1)

# Generating Algorithm 
u <- matrix(NA, nrow = n, ncol = 1)
v <- matrix(NA, nrow = n, ncol = 1)
w <- matrix(NA, nrow = n, ncol = d)
a <- matrix(NA, nrow = n, ncol = (k-1))
y <- matrix(NA, nrow = n, ncol = 1)
x <- matrix(NA, nrow = n, ncol = (d+2))
set.seed(20)
U <- runif(n, -1,1)
set.seed(20)
b <- matrix(runif((k-1)*ncol(x)), nrow = k-1, ncol = ncol(x))
Pi <- c(0.5, 0.3, 0.2)

for (i in 1:n) {
  
  if(U[i] < Pi[1]){
    
    w[i,]  <- mvnfast::rmvn(1, mean1, sigma1)
    u[i] <- rbinom(1, 1, .5)
    v[i] <- rbinom(1, 2, 1/3)
    x[i,] <- c(w[i,],u[i],v[i])
    z[i] <- 1
    y[i]   <- rzipois(1, lambda = 0)
    
  }else
    
    if(U[i] > Pi[1] & U[i] < (Pi[1] + Pi[2])){
      
      w[i,]  <- mvnfast::rmvn(1, mean[1,], sigma[[1]])
      u[i] <- rbinom(1, 1, .5)
      v[i] <- rbinom(1, 2, 1/3)
      z[i] <- 2
      x[i,] <- c(w[i,], u[i], v[i])
      a[i,]  <- as.matrix(x[i,] %*% t(b))
      y[i]   <- rpois(1, lambda = exp(a[i,1]))
      
    }else{
      
      w[i,]  <- mvnfast::rmvn(1, mean[2,], sigma[[2]])
      u[i] <- rbinom(1, 1, .5)
      v[i] <- rbinom(1, 2, 1/3)
      z[i] <- 3
      x[i,]  <- c(w[i,], u[i], v[i])
      a[i,]  <- as.matrix(x[i,] %*% t(b))
      y[i]   <- rpois(1, lambda = exp(a[i,2]))
      
    }
}

dat <- data.frame(x,y)
plot(dat, col = z)
table(z)

############### Optim SA

cmw_tru_use_real1 <- function(Y, w, u, v, k, maxit = 1000, tol = 0.1, show_table = FALSE){
  
  x <- cbind(rep(1, nrow(w)), w,u,v);
  if(!is.data.frame(x)) x <- unname(as.matrix(x))
  
  eps <- sqrt(.Machine$double.eps); n <- nrow(x)
  
  W1 <- keras::to_categorical(u); W2 <- keras::to_categorical(v)
  d <- ncol(x); d1 <- ncol(w); c1 <- ncol(W1); c2 <- ncol(W2)
  L1 <- ai <- ai3 <- lb <- L <- NULL
  L2 <- lf1 <- lf2 <- lp <- k1 <- matrix(NA, nrow = n, ncol = k)
  
  dm1 <- lki <- lk2 <- Linf <- al <- NULL
  pr <- matrix(NA, nrow = n, ncol = (k-1))
  lp1 <- dm <- lam <- matrix(NA, nrow = n, ncol = (k-1))
  b <- matrix(runif(d*(k-1)), nrow = (k-1))
  
  sigma <- wew <- list()
  
  mean <- matrix(runif(d1*(k-1)), nrow = k-1)
  
  P1i <- rep(1/k, k)
  
  P1 <- P1i[1]; Pi <- P1i[-1]
  
  for(l in 1:(k-1))sigma[[l]] <- diag(d1)
  
  m <- (k-1)*ncol(b) + (2 * (k-1) * d) + (k-1) + (k-1)*(d*d - d)/2
  
  sigma1 <- diag(d1)
  mean1 <-  rnorm(d1)
  
  py1 <- colMeans(W1)
  py2 <- colMeans(W2)
  
  py11 <- matrix(colMeans(W1), nrow = (k-1), ncol = c1, byrow = TRUE)
  py21 <- matrix(colMeans(W2), nrow = (k-1), ncol = c2, byrow = TRUE)
  
  sig1 <- sig <- array(NA, c(d1,d1,n))
  et1 <- list()
  
  count <- 2;
  
  L <- c(-16000,-15000,-14000);
  
  repeat{
    
    a <- x %*% t(b)
    lam <- exp(a)
    
    for (i in 1:n) {
      
      # Zero count
      dm1[i] <- VGAM::dzipois(Y[i], lambda = 0) * P1 *
        mvnfast::dmvn(w[i,], mean1, sigma1, ncores = 8) *
        dmultinom(W1[i,], 1, prob = py1, log = FALSE) *
        dmultinom(W2[i,], 1, prob = py2, log = FALSE)
      
      for(l in 1:(k-1)){
        
        # Non-zero count
        dm[i,l] <- Pi[l] * mvnfast::dmvn(w[i,], mean[l,], sigma[[l]], ncores = 8) *
          dpois(Y[i], lambda = lam[i,l]) * dmultinom(W1[i,], 1, prob = py11[l,], log = FALSE) *
          dmultinom(W2[i,], 1, prob = py21[l,], log = FALSE) #* y3[i,l+1]
      }
      
    }
    
    po <- dm / rowSums(cbind(dm1, dm))
    po1 <- 1 - rowSums(po)
    Poc <- cbind(po1, po)
    
    ### For zeroes 
    
    for(i in 1:n){
      
      lf1[i,1]  <- po1[i] * dmultinom(W1[i,], 1, prob = py1, log = FALSE) * dzipois(Y[i], lambda = 0)
      lf2[i,1]  <- po1[i] * dmultinom(W2[i,], 1, prob = py2, log = FALSE) * dzipois(Y[i], lambda = 0)
      
    }
    
    L2[,1]  <- po1 * mvnfast::dmvn(w, mean1, sigma1, ncores = 8,
                                   isChol = TRUE, log = FALSE) * dzipois(Y, lambda = 0)
    
    lp[,1] <- po1 * P1 * dzipois(Y, lambda = 0)
    k1[,1] <- lf1[,1] * lf2[,1] * L2[,1] * lp[,1]
    
    ### For non-zeros
    for (l in 1:(k-1)) {
      
      for (i in 1:n) {
        
        lf1[i,l+1] <- po[i,l] * dmultinom(W1[i,], 1, prob = py11[l,], log = FALSE) #* y3[i,l+1]
        lf2[i,l+1] <- po[i,l] * dmultinom(W2[i,], 1, prob = py21[l,], log = FALSE) #* y3[i,l+1]
        
      }
      
      lp[,l+1] <- po[,l ] * dpois(Y, lambda = lam[,l], log = FALSE) #* y3[,l+1]
      lp1[,l] <- po[,l] * Pi[l]
      L2[,l+1]  <- po[,l] * mvnfast::dmvn(w, mean[l,], sigma[[l]], ncores = 8,
                                          isChol = TRUE, log = FALSE) #* y3[,l+1]
      
      k1[,l+1] <- lf1[,l+1] * lf2[,l+1] * lp[,l+1] * L2[,l+1] * lp1[,l]
      
    }
    
    for(l in 1:(k-1)){
      
      LogLike <- function(par) {
        
        lambda <- exp(x %*% par)
        LL <- -sum(po[,l] * dpois(Y, lambda, log = TRUE))
        return(LL)
        
      }
      
      par <- b[l,]
      
      m.like <- optim_sa(fun = LogLike, start = par, 
                         lower = rep(eps,ncol(x)),
                         upper = rep(1, ncol(x)), trace = TRUE,
                         control = list(t0 = 100, nlimit = 550, t_min = 0.1,
                                        dyn_rf = F, rf = 1, r = 0.7))
      b[l,] <- m.like$par
    }
    
    # M-Step Updates
    P1 <- sum(po1) / n
    
    mean1 <- colSums(po1 * w) / sum(po1)
    
    for (i in 1:n) sig1[,,i] <- po1[i] * outer((w[i,] - mean1),(w[i,] - mean1))
    for(l in 1:(k-1)) mean[l,] <- colSums(po[,l] * w) / colSums(po)[l]
    sigma1 <- apply(sig1, c(1, 2), sum)/ sum(po1) + diag(eps, ncol(w))
    
    for (l in 1:(k-1)) {
      
      for (i in 1:nrow(x)) {sig[,,i] <- po[i,l] * outer((w[i,] - mean[l,]),(w[i,] - mean[l,]))}
      sigma[[l]] <- apply(sig, c(1, 2), sum)/ sum(po[,l]) + diag(eps, ncol(w))
      
    }
    
    #if(count %% 12 == 0){
    
    py1 <- (colSums(po1 *  W1) / sum(po1)) #+ 0.2
    py2 <- (colSums(po1 *  W2) / sum(po1)) #+ 0.2
    
    for (l in 1:(k-1)) {
      
      py11[l, ] <- (colSums(po[,l] * W1) / colSums(po)[l])
      py21[l, ] <- (colSums(po[,l] * W2) / colSums(po)[l])
      
    }
    
    #}
    
    Pi <- colSums(po) / n
    
    # Compute Log_likelihood lki, lk2,
    
    L[count] <- sum(log(rowSums(k1)))
    a_k <- (L[count+1] - L[count]) / (L[count] - L[count-1])
    L[count + 2] <- L[count] + ((1-a_k)^-1 * (L[count+1] - L[count]))
    
    if (show_table) {
      
      dif <- abs(L[count+2] - L[count+1])
      
      out_table = data.frame(Iteration = count, Likelihood = L[count+2], difference = dif)
      print(kable(out_table))
      
      if (count == maxit || dif < tol) break;
      
    }
    
    count <- count + 1
    
  }
  
  Z <- apply(Poc, 1, which.max)
  
  Prof <- Poc1 <- Poc
  
  for(i in 1:n){
    
    for(j in 1:k){
      
      Prof[i,j] <- ifelse(Poc[i,j] > 0.9, 1, 0)
      
      if(Poc[i,j] > 0){
        
        Poc1[i,j] <- log(Poc[i,j])
      }
      
    }
    
  }
  
  ai   <- -2*L[count + 2] - 2*m;
  ai3  <- -2*L[count + 2] - m*log(n)  
  ICL  <-  ai3 + suppressWarnings(sum(rowSums(Prof * Poc1)))
  AIcc <-  ai - 2*m*(m+1)/(n-m-1)
  AIC3 <- -2*L[count+2] - 3*m
  AICu <-  AIcc - n*log(n/(n-m-1))
  ICL  <-  ai3 + suppressWarnings(sum(rowSums(Prof * Poc1)))
  Caic <- -2*L[count+2] - m*(1+log(n))
  AWE  <- -2*L[count+2] - 2*m*(3/2 + log(n))
  
  return(list("mean" = mean, "mean1" = mean1, "sigma1" = sigma1, "Prob1" = P1,
              "prob2" = Pi, "post" = Poc,"poiwei" = b,
              "classification" = Z, "logLik" = L, "AIC" = ai, "BIC" = ai3,
              "sigma" = sigma, "ICL" = ICL, "AICc" = AIcc, "AIC3" = AIC3, 
              "AICu" = AICu, "Caic" = Caic, "AWE" = AWE))
  
}

conf <- function(x){
  
  cm_d  <- as.data.frame(x$table)
  cm_st <- data.frame(x$overall)
  cm_st$x.overall <- round(cm_st$x.overall, 2)
  cm_p <- as.data.frame(prop.table(x$table))
  cm_d$perc <- round(cm_p$Freq*100,2)
  cm_d_p <- ggplot(data = cm_d, aes(x = Prediction, y = Reference, fill = Freq)) +
    geom_tile()+
    geom_text(aes(label = paste("", Freq, ",",perc, "%")), col = "red")+
    theme_light()+
    guides(fill = FALSE)
  cm_st_p <- tableGrob(cm_st)
  
  print(grid.arrange(cm_d_p, cm_st_p, nrow = 1, ncol = 2,
                     top = textGrob("Confusion Matrix and Statistics", gp = gpar(fontsize = 25, font = 1))))
}

## Recorded results
FIn2 <- cmw_tru_use_real1(Y = y, w, u, v, k = 2, maxit = 100, tol = 0.05, show_table = TRUE)
FIn3 <- cmw_tru_use_real1(Y = y, w, u, v, k = 3, maxit = 100, tol = 0.05, show_table = TRUE)
FIn4 <- cmw_tru_use_real1(Y = y, w, u, v, k = 4, maxit = 100, tol = 0.05, show_table = TRUE)
FIn5 <- cmw_tru_use_real1(Y = y, w, u, v, k = 5, maxit = 100, tol = 0.05, show_table = TRUE)

table(z, FIn3$classification)


plot(FIn5$logLik, type = "l", col = "blue")
lines(FIn1[,2]$logLik, type = "l", col = "red")
lines(FIn1[,3]$logLik, type = "l", col = "green")


# Information criteria
FIn2$AIC;FIn3$AIC;FIn4$AIC;FIn5$AIC
FIn2$BIC;FIn3$BIC;FIn4$BIC;FIn5$BIC
FIn2$ICL;FIn3$ICL;FIn4$ICL;FIn5$ICL
FIn2$AWE;FIn3$AWE;FIn4$AWE;FIn5$AWE
FIn2$AIC3;FIn3$AIC3;FIn4$AIC3;FIn5$AIC3
FIn2$AICc;FIn3$AICc;FIn4$AICc;FIn5$AICc
FIn2$AICu;FIn3$AICu;FIn4$AICu;FIn5$AICu
FIn2$Caic;FIn3$Caic;FIn4$Caic;FIn5$Caic

library(ROCR)
# Multi-class ROC
multiclass.roc(ordered(z),ordered(FIn2$classification))
multiclass.roc(ordered(z),ordered(FIn3$classification))
multiclass.roc(ordered(z),ordered(FIn4$classification))
multiclass.roc(ordered(z),ordered(FIn5$classification))

F2 <- ifelse(FIn2$classification == 2, 1, 2)
F3 <- ifelse(FIn3$classification == 2, 1, 2)  
F4 <- ifelse(FIn4$classification == 2, 1, 2) 
F5 <- ifelse(FIn5$classification == 2, 1, 2) 
ZA <- ifelse(z == 2, 1, 2) 

pr2 <- prediction(F2, ZA)
pr3 <- prediction(F3, ZA)
pr4 <- prediction(F4, ZA)
pr5 <- prediction(F5, ZA)

perf2 <- performance(pr2, "tpr", "fpr")
perf3 <- performance(pr3, "tpr", "fpr")
perf4 <- performance(pr4, "tpr", "fpr")
perf5 <- performance(pr5, "tpr", "fpr")

plot(perf2, col = "red", lwd = 3)
plot(perf3, add = TRUE, lwd = 3, col = "blue")
plot(perf4, add = TRUE, col = "black", lwd = 3)
plot(perf5, add = TRUE, col = "Pink", lwd = 3)
legend(0.8,0.4, cex = 1, legend = c("G = 2", "G = 3", "G = 4", "G = 5"),
       col = c("red","blue", "black", "pink"), lwd = 2)


plot(dat, col = FIn2$classification, pch = FIn2$classification + 1, cex = .5)

adjustedRand(z,FIn2$classification)


data1 <- cbind(y,x)
colnames(data1) <- c("y","x1","x2","x3","w1", "w2")
da <- as.data.frame(data1)
plot(da, col = FIn$classification, pch = FIn$classification + 1, cex = .5)

FIn3$mean
FIn3$sigma1

# Confusion Matrix 
cm <- confusionMatrix(sort(as.factor(z)), sort(as.factor(FIn3$classification)))

conf(cm)


FIn3$mean1
FIn3$sigma
FIn3$poiwei
FIn3$Prob1
FIn3$prob2

