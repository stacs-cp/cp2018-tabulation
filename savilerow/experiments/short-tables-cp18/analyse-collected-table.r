
# 


avg.collected.table=function(fname, numsamples=5) {
  # Instead of all this guff,  the data table package can do this kind of thing. 
a=read.table(fname)

pts<-length(a$V1)/numsamples

b=data.frame(instance=rep(0,pts),extracseon=rep(0,pts),extracseheur=rep(0,pts),msolve=rep(0,pts),mtotal=rep(0,pts),msetup=rep(0,pts),nodes=rep(0,pts),
             mtimeout=rep(0,pts),msat=rep(0,pts),srtime=rep(0,pts),solvermemout=rep(0,pts), srtimeout=rep(0,pts), srclauseout=rep(0,pts), numsatvars=rep(0,pts), numsatclauses=rep(0,pts))


# instance names
b$instance<-a$V2[seq(1,length(a$V2),numsamples)]

# is estra-cse switched on
b$extracseon<-a$V4[seq(1,length(a$V4),numsamples)]

# extra-cse mode.
b$extracseheur<-a$V5[seq(1,length(a$V5),numsamples)]

# avg of solve time

tmp<-c()
for(i in seq(1, length(a$V6),numsamples)) { tmp<-append(tmp, median(a$V6[seq(i,i+numsamples-1,1)])) }

b$msolve<-tmp

# avg of total time

tmp<-c()
for(i in seq(1, length(a$V7),numsamples)) { tmp<-append(tmp, median(a$V7[seq(i,i+numsamples-1,1)])) }

b$mtotal<-tmp

# avg of m setup time

tmp<-c()
for(i in seq(1, length(a$V8),numsamples)) { tmp<-append(tmp, median(a$V8[seq(i,i+numsamples-1,1)])) }

b$msetup<-tmp

# nodes   -- take median

tmp<-c()
for(i in seq(1, length(a$V9),numsamples)) { tmp<-append(tmp, median(a$V9[seq(i,i+numsamples-1,1)])) }

b$nodes<-tmp

# solver timeout -- take majority
tmp<-c()
for(i in seq(1, length(a$V10),numsamples)) { tmp<-append(tmp, ifelse(median(a$V10[seq(i,i+numsamples-1,1)])>0, 1, 0)) }

b$mtimeout<-tmp

# satisfiable -- take majority
tmp<-c()
for(i in seq(1, length(a$V11),numsamples)) { tmp<-append(tmp, ifelse(median(a$V11[seq(i,i+numsamples-1,1)])>0, 1, 0)) }

b$msat<-tmp

# avg sr time 

tmp<-c()
for(i in seq(1, length(a$V12),numsamples)) { tmp<-append(tmp, median(a$V12[seq(i,i+numsamples-1,1)])) }

b$srtime<-tmp

if(ncol(a)>12) {
  # solvermemout -- take majority
  tmp<-c()
  for(i in seq(1, length(a$V13),numsamples)) { tmp<-append(tmp, ifelse(median(a$V13[seq(i,i+numsamples-1,1)])>0, 1, 0)) }
  
  b$solvermemout<-tmp
  
  # srtimeout -- take majority
  tmp<-c()
  for(i in seq(1, length(a$V14),numsamples)) { tmp<-append(tmp, ifelse(median(a$V14[seq(i,i+numsamples-1,1)])>0, 1, 0)) }
  
  b$srtimeout<-tmp
  
  # srclauseout -- take majority
  tmp<-c()
  for(i in seq(1, length(a$V15),numsamples)) { tmp<-append(tmp, ifelse(median(a$V15[seq(i,i+numsamples-1,1)])>0, 1, 0)) }
  
  b$srclauseout<-tmp
  
  # numsatvars -- take max
  tmp<-c()
  for(i in seq(1, length(a$V16),numsamples)) { tmp<-append(tmp, max(a$V16[seq(i,i+numsamples-1,1)])) }
  
  b$numsatvars<-tmp
  
  # numsatclauses -- take max
  tmp<-c()
  for(i in seq(1, length(a$V17),numsamples)) { tmp<-append(tmp, max(a$V17[seq(i,i+numsamples-1,1)])) }
  
  b$numsatclauses<-tmp
}

return(b)
}



#  Helper functions
tidyup = function(datframe, timelimit=3600) {
  #  Penalty of timelimit for clause out.
  datframe[which(datframe[,13]==1),5]=timelimit
  
  # Set NA to 0 in solver time.
  datframe[,5]=ifelse(is.na(datframe[,5]),0.0,datframe[,5])
  
  # Add 1 ms, smallest measurable unit of time for Minion, everywhere to avoid 0's with Lingeling.
  datframe[,5]=datframe[,5]+0.001
  
  #  When savile row time alone > timelimit, set the timeout flag and reduce it to timelimit.
  sel=which(datframe[,10]>timelimit)
  datframe[sel,8]=1
  datframe[sel,10]=timelimit
  
  #  When total time >timelimit set the timeout flag and set the solve time to timelimit-srtime.
  sel=which(datframe[,5]+datframe[,10]>timelimit)
  datframe[sel,8]=1
  datframe[sel,5]=timelimit-datframe[sel,10]
  
  # No negatives in solver time
  datframe[,5]=ifelse(datframe[,5]<0.001,0.001,datframe[,5])
  
  # No excesses in sr time.
  #datframe[,10]=ifelse(datframe[,10]>3600,3600,datframe[,10])
  
  return(datframe)
}

tidyupcp= function(datframe) {
  return(tidyup(datframe, timelimit=3600))
}

baseline.conflict=tidyupcp(avg.collected.table("table-conflict-notstr-baseline", numsamples=5))
tabulate.conflict=tidyupcp(avg.collected.table("table-conflict-notstr-tabulate", numsamples=5))


baseline=tidyupcp(avg.collected.table("table-baseline-notstr", numsamples=5))
tabulate=tidyupcp(avg.collected.table("table-tabulate-notstr", numsamples=5))

baseline.chuffed=tidyupcp(avg.collected.table("table-chuffed2-baseline", numsamples=5))
tabulate.chuffed=tidyupcp(avg.collected.table("table-chuffed2-tabulate", numsamples=5))

#  one_dataframe is the supposedly faster one. two_dataframe is the baseline. 
#  Filt is the 'master' filter -- usually "".
#  greplist is the list of highlight points.
#  legendlist is the names of the highlight points.
plotpair.highlight=function(filt, one_dataframe, two_dataframe, labely, labelx, filename, xlim, greplist, legendlist, clauses=FALSE, time=FALSE, height=6, main="", incsrtime=1, legendlocation="topleft", textsize=1.45) {
  pdf(filename, height=height)
  filtidx=grep(filt,one_dataframe$instance)
  if(!clauses && !time) {
    sizeparam=((two_dataframe[filtidx,]$numsatvars)/(one_dataframe[filtidx,]$numsatvars))
  }
  else {
    if(clauses) {
      sizeparam=(two_dataframe[filtidx,]$numsatclauses)/(one_dataframe[filtidx,]$numsatclauses)
    }
    else {
      #  Time on the x axis. 
      sizeparam=( (two_dataframe[filtidx,]$srtime*incsrtime)+two_dataframe[filtidx,]$mtotal)
    }
  }
  
  col=ifelse(greplist[1]!="" & grepl(greplist[1], one_dataframe$instance), "forestgreen",
             ifelse(greplist[2]!="" & grepl(greplist[2], one_dataframe$instance), "black",
                    ifelse(greplist[3]!="" & grepl(greplist[3], one_dataframe$instance), "blue", 
                           ifelse(greplist[4]!="" & grepl(greplist[4],one_dataframe$instance), "red", 
                                  ifelse(greplist[5]!="" & grepl(greplist[5],one_dataframe$instance),"green",
                                         ifelse(greplist[6]!="" & grepl(greplist[6],one_dataframe$instance),"turquoise4",
                                                ifelse(greplist[7]!="" & grepl(greplist[7],one_dataframe$instance),"deeppink3",
                                                "darkorange4")))))))
  pch=ifelse(greplist[1]!="" & grepl(greplist[1], one_dataframe$instance), 0,
             ifelse(greplist[2]!="" & grepl(greplist[2], one_dataframe$instance), 1,
                    ifelse(greplist[3]!="" & grepl(greplist[3], one_dataframe$instance), 2, 
                           ifelse(greplist[4]!="" & grepl(greplist[4],one_dataframe$instance), 3, 
                                  ifelse(greplist[5]!="" & grepl(greplist[5],one_dataframe$instance),4,
                                         ifelse(greplist[6]!="" & grepl(greplist[6],one_dataframe$instance),5,
                                                ifelse(greplist[7]!="" & grepl(greplist[7],one_dataframe$instance),7,
                                                10)))))))
  nonblankkeys=(greplist!="")
  plot( sizeparam, 
        (two_dataframe[filtidx,]$mtotal+(two_dataframe[filtidx,]$srtime*incsrtime))/(one_dataframe[filtidx,]$mtotal+(one_dataframe[filtidx,]$srtime*incsrtime)),
        log="xy", xlab=labelx, ylab=labely, cex.axis=textsize, cex.lab=textsize, cex.main=textsize, xlim=xlim, main=main, col=col, pch=pch)
  
  legend( legendlocation, legendlist[nonblankkeys], pch = c(0,1,2,3,4,5,7,10)[nonblankkeys], inset = .05, col=c("forestgreen","black","blue","red","green","turquoise4","deeppink3","darkorange4")[nonblankkeys])
  
  abline(h=1)
  if(!time) { abline(v=1) }
  dev.off()
}

which.interesting=function(one_dataframe, two_dataframe, incsrtime=1, sensitivity=2) {
  # one_ is supposedly the faster one. 
  ratio=((two_dataframe$srtime*incsrtime)+two_dataframe$mtotal)/( (one_dataframe$srtime*incsrtime)+one_dataframe$mtotal)
  sel=which( ratio>sensitivity | ratio<(1/sensitivity) )
  df=data.frame(one_dataframe[sel,1], ratio[sel], (two_dataframe[sel,]$srtime*incsrtime)+two_dataframe[sel,]$mtotal )
  names(df)=c("instance", "timeratio","basetime")
  return( df )
}

t.test.comparison=function(one_dataframe, two_dataframe, incsrtime=1) {
  t.test((one_dataframe$srtime*incsrtime)+one_dataframe$mtotal, (two_dataframe$srtime*incsrtime)+two_dataframe$mtotal, paired=TRUE)
}


geom.mean.speedup <- function(f1, f2, incsrtime=1) {
  # f1 is the supposedly faster one.
  gm=sum(log(((f2$srtime*incsrtime)+f2$mtotal)/((f1$srtime*incsrtime)+f1$mtotal)))/length(f1$instance)
  return(exp(gm))
}

#  Select non-timeout instances.  Use geometric mean. Arithmetic mean is a terrible cheat: 0.5 and 2 would avg to 1.25 not 1. 
mean.speedup.noto <- function(f1, f2, incsrtime=1) {
  # filter out solver timeouts
  idxs=which(f1$mtimeout==0 & f2$mtimeout==0)
  return(geom.mean.speedup(f1[idxs,], f2[idxs,], incsrtime))
}

confinterval <- function(f1, f2, incsrtime=1, geommean=1) {
  sampsize=100000
  bootstrap=c(1:sampsize)
  for(i in 1:sampsize) {
    ch=sample.int(nrow(f1), size=nrow(f1), replace=TRUE)
    f1sel=f1[ch,]   # The actual sample from both f1 and f2.
    f2sel=f2[ch,]
    if(geommean==1) {
      bootstrap[i]=geom.mean.speedup(f1sel, f2sel, incsrtime)
    }
    else {
      bootstrap[i]=mean.speedup.noto(f1sel, f2sel, incsrtime)
    }
  }
  hist(bootstrap)
  
  return(quantile(bootstrap, c(0.025, 0.5, 0.975)))
}

confinterval2 <- function(f1, f2, incsrtime=1) {
  return(confinterval(f1, f2, incsrtime, geommean=0))
}

########  Filter

filter=FALSE

if(filter) {
sel=grepl("langford", baseline$instance) | grepl("coprime", baseline$instance) | grepl("knights", baseline$instance) | grepl("sportsScheduling", baseline$instance) 

baseline=baseline[sel,]
tabulate=tabulate[sel,]
baseline.conflict=baseline.conflict[sel,]
tabulate.conflict=tabulate.conflict[sel,]
baseline.chuffed=baseline.chuffed[sel,]
tabulate.chuffed=tabulate.chuffed[sel,]
}

#########  Filter out too-easy instances

sel=which(baseline$srtime+baseline$mtotal >= 1)

baseline=baseline[sel,]
tabulate=tabulate[sel,]
baseline.conflict=baseline.conflict[sel,]
tabulate.conflict=tabulate.conflict[sel,]
baseline.chuffed=baseline.chuffed[sel,]
tabulate.chuffed=tabulate.chuffed[sel,]


#####   Conflict version.

which.interesting(tabulate.conflict,baseline.conflict)

if(!filter) {
greplist=c("blackHole", "bpmp", "coprime", "/hts/", "JPEncoding", "knights", "sportsScheduling", "langford")
legendlist=c("Black Hole", "BPMP", "Coprime Sets", "Handball7","JPEncoding", "Knights Tour", "Sports Scheduling", "Langford")
}
if(filter) {
greplist=c("coprime", "knights", "sportsScheduling", "langford")
legendlist=c("Coprime Sets", "Knights Tour", "Sports Scheduling", "Langford")
}

plotpair.highlight("", tabulate.conflict, baseline.conflict, "Speed-up: Tabulate", "Total time: Default configuration (s)", main="", "conflict_tabulate_v_baseline.pdf", NULL, greplist, legendlist, FALSE, TRUE, legendlocation="topleft", height=5)

mean.speedup.noto(tabulate.conflict, baseline.conflict, incsrtime = 1)
#confinterval2(tabulate.conflict,baseline.conflict, incsrtime = 1)

#####  Static version

which.interesting(tabulate,baseline)

plotpair.highlight("", tabulate, baseline, "Speed-up: Tabulate", "Total time: Default configuration (s)", main="", "static_tabulate_v_baseline.pdf", NULL, greplist, legendlist, FALSE, TRUE, legendlocation="topleft", height=5)

mean.speedup.noto(tabulate, baseline, incsrtime = 1)
#confinterval2(tabulate, baseline, incsrtime = 1)

########   Chuffed

which.interesting(tabulate.chuffed, baseline.chuffed)

plotpair.highlight("", tabulate.chuffed, baseline.chuffed, "Speed-up: Tabulate", "Total time: Default configuration (s)", main="", "chuffed_tabulate_v_baseline.pdf", NULL, greplist, legendlist, FALSE, TRUE, legendlocation="topleft", height=5)

mean.speedup.noto(tabulate.chuffed, baseline.chuffed, incsrtime = 1)

