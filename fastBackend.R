############################
############################
###                      ###
###        BACKEND       ###
###  FAST POSET VERSION  ###
###                      ###
############################
############################


###########################
##  Libraries and Pipes  ##
###########################
library(stringr)
library(combinat)
library(purrr)
library(gtools)
library(rje)
library(lpSolve)
library(utils)
#Create Pipes
`%$%` <- function(lst, func) {
  sapply(lst, match.fun(func))
}
`%#%` <- function(lst, func) {
  match.fun(func)(lst)
}


choiceSetMaker <- function(withImplicantString){
  tests <- c()
  covers <- c()
  implicantsRemoved <- removeTransitiveImplicants(withImplicantString)
  withImplicantVec <- strsplit(withImplicantString,",")
  withImplicantMatrix <- matrix(unlist(lapply(withImplicantVec,strsplit,split="")),ncol=2,byrow=TRUE)
  withoutImplicantVec <- strsplit(implicantsRemoved,",")
  withoutImplicantMatrix <- matrix(unlist(lapply(withoutImplicantVec,strsplit,split="")),ncol=2,byrow=TRUE)
  for(i in 1:dim(withoutImplicantMatrix)[1]){
    chosen<-withoutImplicantMatrix[i,1]
    rowsInWithMatrix <- which(withImplicantMatrix[,1]==chosen)
    chosenOver<-withoutImplicantMatrix[i,2]
    chosenOverWith <- withImplicantMatrix[rowsInWithMatrix,2]
    possibilitiesToAdd <- setdiff(chosenOverWith,chosenOver)
    tests <- c(tests,paste0(chosen,chosenOver,collapse=""))
    covers <- c(covers,i)
    if(length(possibilitiesToAdd)>0){
      powSetOfPossibilities <- powerSetCond(possibilitiesToAdd)
      for(j in 1:length(powSetOfPossibilities)){
        add <- paste0(powSetOfPossibilities[[j]],collapse = "")
        tests <- c(tests,paste0(chosen,chosenOver,add,collapse=""))
        covers <- c(covers,i)
        
      }
    }
  }
  returnList<- list()
  tests<-unlist(lapply(tests,breakThenSortThenPaste))
  
  for(i in 1:max(covers)){
    returnList[[i]]<-c(tests[which(covers==i)])
    
  }
  return(returnList)
}


breakThenSortThenPaste <-  function(string) {
  splitString<-unlist(strsplit(string,""))
  sorted <- sort(splitString)
  return(paste0(sorted,collapse = ""))
}


#################################################################
##                      Test Implication                       ##
##   Takes in a vector of pairs and returns any implication.   ##
#################################################################
testImplication <- function(pair) {
  matrixPair <-
    matrix(c(
      substr(pair[1], 1, 1),
      substr(pair[1], 2, 2),
      substr(pair[2], 1, 1),
      substr(pair[2], 2, 2)
    ), 2, 2, byrow = TRUE)
  if (matrixPair[1, 2] == matrixPair[2, 1]) {
    return(paste0(matrixPair[1, 1], matrixPair[2, 2], collapse = ""))
  } else if(matrixPair[1, 1] == matrixPair[2, 2]) {
    return(paste0(matrixPair[2, 1], matrixPair[1, 2], collapse = ""))
  } else{
    return("")
  }
}

donutReduction <- function(vectorOfPairs){
  # vectorOfPairs <- strsplit(string, split = ",")[[1]]
  matrixOfPairs <- do.call(rbind,sapply(as.matrix(vectorOfPairs),str_split,pattern=""))
  i <- 1
  returnVector <- c()
  for(chosen in unique(matrixOfPairs[,1])){
    returnVector[i] <- paste(chosen,paste(matrixOfPairs[which(matrixOfPairs[,1]==chosen),2],collapse=""),collapse="")
    i<- i+1
  }
  returnVector
}


##########################################################################
##                     Remove Transitive Implicants                     ##
##              Takes in a string of comma separated pairs.             ##
##  Returns a string of comma separated pairs with implicants removed.  ##
##########################################################################
removeTransitiveImplicants <- function(vectorOfPairs) {
  # vectorOfPairs <- strsplit(string, split = ",")[[1]]
  if(length(vectorOfPairs)<3){return(vectorOfPairs)}
  combinationMatrix <- utils::combn(vectorOfPairs, 2)
  implicants <- apply(combinationMatrix,2,testImplication)
  implicantNumbers <- which(vectorOfPairs %in% implicants)
  if(length(implicantNumbers)>0){vectorWithImplicantsRemoved <- vectorOfPairs[-implicantNumbers]}else{
    vectorWithImplicantsRemoved <- vectorOfPairs}
  
  return(vectorWithImplicantsRemoved)
}


#################################################################
##                 getAllAdjacentSubstrings                    ##
##     A function that returns all substrings of a string.     ##
##                       Input: A string                       ##
##               Output: A vector of substrings.               ##
#################################################################
getAllAdjacentSubstrings <-
  function(string) {
    length<-nchar(string)
    sapply(1:(length-1),function(x){substr(string,x,x+1)})
  }


#################################################################
##                     getAllSubstrings                        ##
##     A function that returns all substrings of a string.     ##
##                       Input: A string                       ##
##               Output: A vector of substrings.               ##
#################################################################
getAllSubstrings <-
  function(string) {
    as.vector(return(unlist(sapply(2:2, function(x) {
      unique(utils::combn(
        strsplit(string, "")[[1]],
        x,
        FUN = paste,
        collapse = ""
      ))
    }))))
  }

#############################################################################################
##                                          Rotato                                         ##
##                A function that permutes substrings in a fixed position.                 ##
##  Inputs: String to rotate, Integer Length of Block, Integer Position of start of block  ##
##                            Output: Vector of rotated strings.                           ##
#############################################################################################
rotato <- function(string,length,position){
  #Some checks
  stringLength <- nchar(string)
  if(stringLength < length){return(FALSE)}
  if(position + length - 1 > stringLength){return(FALSE)}
  #Split string into a vector
  stringAsVector <- unlist(strsplit(string,""))
  #Get the characters to rotate
  charactersToRotate <- stringAsVector[position:(position+length-1)]
  #Get all the rotations of those strings.
  allRotations <- permn(charactersToRotate)
  #Paste all the rotations into the string in the correction position. 
  rotatedStringsAsVectors <- lapply(allRotations,function(x){append(stringAsVector[-(position:(position+length-1))],x,after=(position-1))})
  #Return string version of these rotates strings by pasting the vectors together and then unlisting the result. 
  unlist(lapply(rotatedStringsAsVectors,paste,collapse=""))
}

rotatoPair <- function(string){
  rotato(string,2,1)[2]
}

##########################################################################
##                                Permuto                               ##
##         A Function that permutes blocks when they are found.         ##
##  Inputs: Vector of Strings to Permute, String to Permute when Found  ##
##                  Output: Vector of Permuted Strings                  ##
##########################################################################
permuto <- function(strings,blocks){
  #Perpare an empty string to see when the set of strings is stable. 
  oldstrings <- c("")
  #Keep permuting until the set of strings is stable
  while(!all(strings %in% oldstrings)){  
    #Set the old set of strings to the current set
    oldstrings <- strings
    #Loop through the blocks to permute
    for(block in blocks){
      #Get all the ways to permute that block (this could be sped up by saving this.) and turn it into strings. 
      permutedBlock <- permn(unlist(str_split(block,""))) 
      permutedBlock <- sapply(permutedBlock,paste,collapse="")
      #Look for anything in the permuted block and permute. 
      strings <- sapply(permutedBlock,function(x){str_replace(strings,paste(permutedBlock,collapse="|"),x)})
      #Just keep unique strings
      strings <- unique(as.vector(strings))
    }
  }
  strings
}



########################################################################################
##                                    PosetFinder                                     ##
##                Takes in a pair (vector) of rankings in string form.                ##
##  Returns a vector of rankings representing the smallest poset for those rankings.  ##
########################################################################################
posetFinder <- function(set,partitionRanks){
  poset <- reduce(lapply(set,getAllSubstrings),intersect) 
  relevantPairsToRotate <- setdiff(getAllSubstrings(set[1]),poset)
  posetRanks <- permuto(set,relevantPairsToRotate)
  if(all(posetRanks %in% partitionRanks)){
    return(posetRanks)
  }
}




#######################################################################################
##                                 Rankings to Poset                                 ##
##  Takes a set of rankings and returns the minimal poset relation containing them.  ##
#######################################################################################
rankingsToPoset <- function(rankings){
  as.vector(reduce(lapply(rankings,getAllSubstrings),intersect))
}





################################################################################
##                                 All Posets                                 ##
##  Given a set of rankings and universe of rankings, find all unique posets  ##
################################################################################
allPosets <- function(partitionRanks,universe){
  
  possiblePosetList <- list()
  maxDim <- 2
  if(nchar(partitionRanks[1])>5){
    maxDim <- floor(nchar(partitionRanks[1])/2)
  }
  
  for(length in 1:min(length(partitionRanks),maxDim)){
    if(length>1){
      possiblePosets <- apply(as.matrix(combn(partitionRanks,length)),2,posetFinder,partitionRanks=partitionRanks)
      possiblePosets <- possiblePosets[which(!sapply(possiblePosets,is.null))]
      if(!is.list(possiblePosets)){possiblePosets <- list(possiblePosets)}
    }else{
      possiblePosets <- as.list(partitionRanks)
    }
    if(!all(sapply(possiblePosets,is.null))){  
      possiblePosetList <- c(possiblePosetList,possiblePosets)
    }
  }
  possiblePosetList <- unique(possiblePosetList)
  return(possiblePosetList)
}



#################################################################
##                       Model to Posets                       ##
##            Given a model, return list of posets.            ##
#################################################################
modelToPosets <- function(rankings,partitions,universe){
  posetRankingsList <- list()  
  posetList <- list()
  commonToUniverse <- rankingsToPoset(universe)
  for(partition in unique(partitions)){
    indexOfPartition <- which(partitions == partition)
    partitionRanks <- rankings[indexOfPartition]
    posets <- allPosets(partitionRanks,universe)
    
    partitionPosets <- lapply(posets,rankingsToPoset)
    
    if(length(commonToUniverse>0)){
      partitionPosets <- lapply(partitionPosets,function(x){setdiff(x,commonToUniverse)})
    }
    unique <- partitionPosets
    posetRankingsList[[partition]] <- posets
    posetList[[partition]] <- partitionPosets
  }
  return(list(posetList = posetList,posetRankingsList=posetRankingsList))
}


####################################################################################
##                            Find Index Poset Covers                             ##
##  Takes in posets of a partition, returns index of the covers in the powerset.  ##
####################################################################################
findIndexPosetCovers <- function(posetRankingsInPartition){
  allRankingsInPartition <- unique(unlist(posetRankingsInPartition))
  sizeOfPartition <- length(allRankingsInPartition)
  allCombos <- powerSetCond(posetRankingsInPartition)
  rankingsInCombosNotUnique <-lapply(powerSetCond(posetRankingsInPartition),unlist)
  rankingsInCombosUnique <- lapply(rankingsInCombosNotUnique,unique)
  return(which((rankingsInCombosUnique %$% length)==sizeOfPartition ))
}



########################################################################
##                    Get Poset Covers from Model                     ##
##  Input a model, output a list of poset covers for each partition.  ##
########################################################################
getPosetCoversFromModel <- function(rankings,partitions,universe){
  list <- modelToPosets(rankings,partitions,universe)
  list <- getUniquePosets(list)
  list <- getEssentialPosets(list)
  
  
  posetList <- list$posetList
  posetRankingsList <- list$posetRankingsList
  posetCovers <- list()
  for(partition in unique(partitions)){
    posetsInPartition <- posetList[[partition]]
    posetRankingsInPartition <- posetRankingsList[[partition]]
    indexOfCovers <- findIndexPosetCovers(posetRankingsInPartition)
    posetCovers[[partition]] <- powerSetCond(posetsInPartition)[indexOfCovers]
  }
  return(posetCovers)
}


getUniquePosets <- function(posets){
  posetsOrder <- posets$posetList
  posetsRanking <- posets$posetRankingsList
  for(partition in 1:length(posetsOrder)){
    posetsOrderInPartition <- posetsOrder[[partition]]
    posetsRankingInPartition <- posetsRanking[[partition]]
    posetsOrderInPartition <- unique(unique(sapply(posetsOrderInPartition,sort)))
    posetsRankingInPartition <- unique(unique(sapply(posetsRankingInPartition,sort)))  
    posetsOrder[[partition]] <- posetsOrderInPartition
    posetsRanking[[partition]] <- posetsRankingInPartition

    }
return(list(posetList = posetsOrder,posetRankingsList=posetsRanking))  
}


getEssentialPosets <- function(posets){
  
  posetsRanking <- posets$posetRankingsList
  posets <- posets$posetList
  for(partition in 1:length(posets)){
    remove <- c()
    posetsInPartition <- posets[[partition]]
    posetsInPartition <- unique(sapply(posetsInPartition,sort))
    for(poset in 1:length(posetsInPartition)){
      currentPoset <- posetsInPartition[[poset]]
      choicesInPoset <- unique(sapply(currentPoset,substr,start=1,stop=1))
      for(otherPoset in posetsInPartition[-poset]){
        choicesInOther <- unique(sapply(otherPoset,substr,start=1,stop=1))
        if(all(choicesInOther %in% choicesInPoset) && length(choicesInPoset)>length(choicesInOther)){
          remove <- c(remove,poset)
          break}
      }
      
    }
    posetsRanking[[partition]] <- posetsRanking[[partition]][-remove]
    posets[[partition]] <- posetsInPartition[-remove]
  }
  return(list(posetList = posets,posetRankingsList=posetsRanking))
}



##################################################################
##          Find Minimal Experiment From Poset Covers           ##
##  Input a list of poset covers, output a minimal experiment.  ##
##################################################################
findMinimalExperimentFromPoset <- function(coveringPosets){
  numberPartitions <- length(coveringPosets)
  numberOfCovers <- c()
  for(part in 1:numberPartitions){
    numberOfCovers[part] <- length(coveringPosets[[part]])
  }
  testsNumbers <- do.call(expand.grid,lapply(as.vector(numberOfCovers),function(x){1:x}))
  minCost <- 100000
  for(testNum in 1:dim(testsNumbers)[1]){
    test <- c()  
    item <- 1
    names <- c()
    items.mat <- matrix(0,0,0)
    for(i in 1:numberPartitions){
      coveringPoset <- coveringPosets[[i]][[testsNumbers[testNum,i]]]
      for(j in 1:length(coveringPoset)){
        choiceSets <- choiceSetMaker(coveringPoset[[j]])
        for(k in 1:length(choiceSets)){
          sets <- choiceSets[[k]]
          items.mat <- rbind(items.mat,rep(0,dim(items.mat)[2]))
          for(l in 1:length(sets)){
            set <- sets[l]
            foundInNames <- which(names==set)
            if(length(foundInNames)>0){
              items.mat[item,foundInNames]<-1
            }else{
              items.mat<-cbind(items.mat,rep(0,0+dim(items.mat)[1]))
              items.mat[item,dim(items.mat)[2]]<-1
              names <- c(names,set)
            } 
          }
          item <- item+1
        }
      }
    }
    # f.obj <- rep(1, dim(items.mat)[2])
    choiceSetLengths <- sapply(names,nchar)
    maxSetSize <- max(choiceSetLengths)
    sizeFactor <- 1/(10^round(log(maxSetSize + 1,10)))
    f.obj <- 1+sizeFactor*sapply(names,nchar)
    f.dir <- rep(">=", dim(items.mat)[1])
    f.rhs <- rep(1, dim(items.mat)[1])
    solu <- lp("min", f.obj, items.mat, f.dir, f.rhs, all.bin = TRUE)
    cost <- sum(solu$solution * f.obj)
    if(cost<minCost){
      solution <- names[which(as.logical(solu$solution))]
      minCost<-cost
    }
  }
  return(solution)
}



###########################################################################
###########################################################################
###                                                                     ###
###                  FIND MINIMAL EXPERIMENT FROM MODEL                 ###
###             INPUT A MODEL, OUTPUT A MINIMAL EXPERIMENT.             ###
###                                                                     ###
###########################################################################
###########################################################################

findMinimalExperimentFromModel <- function(rankings,partitions,universe){
  findMinimalExperimentFromPoset(getPosetCoversFromModel(rankings,partitions,universe))
}



# From an experiment (list of sets) what partition does it make?
# This is Faster... somehow. 
findPartitionFromTest <- function(universe, test) {
  test <- as.list(test)
  test <- sapply(test,str_split,"")
  numberOfRankings <- length(universe)
  partitionVector <- rep(1, numberOfRankings)
  weight <- 1
  numberOfTests <- length(test)
  for (set in test) {
    for (choice in set) {
      logicalVector <- 1:numberOfRankings > 0
      for (other in set[-which(set == choice)]) {
        test <- c(choice, other)
        logicalVector <-
          logicalVector & sapply(universe, isThisChoiceMade, test = test)
      }
      partitionVector <- partitionVector + weight * logicalVector
      weight <- weight / 2
    }
  }
  return(reRank(rank(partitionVector, ties.method = "min")))
}

isThisChoiceMade <- function(ranking, test) {
  ranking <- unlist(str_split(ranking,""))
  rankingWithin <- match(test, ranking)
  
  if (rankingWithin[1] < rankingWithin[2]) {
    return(TRUE)
  }
  return(FALSE)
}

reRank <- function(vector) {
  uniqueRanks <- sort(unique(vector))
  return(match(vector, uniqueRanks))
}


parseTheoryToNumeric <-
  function(stringRankings,
           partitions,
           universe) {
    lengthOfTheory <- length(partitions)
    objectTheory <- sapply(stringRankings, strsplit, split = "")
    universe <- sapply(universe, strsplit, split = "")
    numericRankings <-
      unlist(lapply(objectTheory, objectRankingToNumeric, rankings = universe))
    numberOfRankings <- length(universe)
    numericTheory <- rep(numberOfRankings + 1, numberOfRankings)
    for (i in 1:lengthOfTheory) {
      numericTheory[numericRankings[i]] <- partitions[i]
    }
    numericTheory <- reRank(numericTheory)
    return(numericTheory)
  }


objectRankingToNumeric <- function(ranking, rankings) {
  return(which(unlist(lapply(
    rankings, identical, unlist(ranking)
  ))))
}




# 
# ################################################################
# #                           Sandbox                           ##
# # ################################################################
testTheory <- TRUE
rankings <- c("ABCD","ABDC","ACBD","ACDB")
objects <- nchar(rankings[1])
partitions <- c(1,1,1,1)
if(testTheory==FALSE){universe <- rankings}else{universe <- apply(permutations(objects, objects, LETTERS[1:objects]),1,paste,collapse="")}

coveringPosets <- getPosetCoversFromModel(rankings,partitions,universe)
test <- findMinimalExperimentFromModel(rankings,partitions,universe)


test


