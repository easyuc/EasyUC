open DlLexer
open DlParseTree
open EcLocation

type testCase = { filename:string; expectedResult:exn option }

let testLexicalError = 
{
	filename = "./tests/testLexicalError.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(2,12); loc_end=(2,13); loc_bchar=32; loc_echar=33},
None))
}

let testLexicalErrorOK = 
{
	filename = "./tests/testLexicalErrorOK.uc";
	expectedResult = None
}

let testParseError = 
{
	filename = "./tests/testParseError.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(3,0); loc_end=(3,10); loc_bchar=52; loc_echar=62},
None))
}

let testParseErrorOK = 
{
	filename = "./tests/testParseErrorOK.uc";
	expectedResult = None
}

let testNonExistingAdvIoIdInCompositeBody = 
{
	filename = "./tests/testNonExistingAdvIoIdInCompositeBody.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(2,4); loc_end=(2,7); loc_bchar=23; loc_echar=26},
(Some "adversarialIO bli hasn't been defined yet.")))
}

let testNonExistingAdvIoIdInCompositeBodyOK = 
{
	filename = "./tests/testNonExistingAdvIoIdInCompositeBodyOK.uc";
	expectedResult = None
}

let testCompositeAdvIOreferencingNonAdvIO = 
{
	filename = "./tests/testCompositeAdvIOreferencingNonAdvIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(6,3); loc_end=(6,4); loc_bchar=43; loc_echar=44},
(Some "adversarialIO d hasn't been defined yet.")))
}

let testCompositeAdvIOreferencingNonAdvIOOK = 
{
	filename = "./tests/testCompositeAdvIOreferencingNonAdvIOOK.uc";
	expectedResult = None
}


let testCompositeReferencingComposite = 
{
	filename = "./tests/testCompositeReferencingComposite.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(10,2); loc_end=(10,4); loc_bchar=69; loc_echar=71},
(Some "A1 is not a basic IO.")))
}

let testCompositeReferencingCompositeOK = 
{
	filename = "./tests/testCompositeReferencingCompositeOK.uc";
	expectedResult = None
}


let testCircularReferenceSelfReference = 
{
	filename = "./tests/testCircularReferenceSelfReference.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(2,2); loc_end=(2,3); loc_bchar=17; loc_echar=18},
(Some "A is not a basic IO.")))
}


let testCircularReferenceSelfReferenceOK = 
{
	filename = "./tests/testCircularReferenceSelfReferenceOK.uc";
	expectedResult = None
}

let testDuplicateIdInCompositIOBody = 
{
	filename = "./tests/testDuplicateIdInCompositIOBody.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(7,0); loc_end=(7,1); loc_bchar=49; loc_echar=50},
(Some "Duplicate identifier: a")))
}

let testDuplicateIdInCompositIOBodyOK = 
{
	filename = "./tests/testDuplicateIdInCompositIOBodyOK.uc";
	expectedResult = None
}

let testDuplicateIdInIODefinitions = 
{
	filename = "./tests/testDuplicateIdInIODefinitions.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(5,12); loc_end=(5,13); loc_bchar=40; loc_echar=41},
(Some "Duplicate identifier: A")))
}

let testDuplicateIdInIODefinitionsOK = 
{
	filename = "./tests/testDuplicateIdInIODefinitionsOK.uc";
	expectedResult = None
}

let testDuplicateMessageId = 
{
	filename = "./tests/testDuplicateMessageId.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(3,4); loc_end=(3,5); loc_bchar=28; loc_echar=29},
(Some "Duplicate identifier: M")))
}

let testDuplicateMessageIdOK = 
{
	filename = "./tests/testDuplicateMessageIdOK.uc";
	expectedResult = None
}

let testDuplicateParameterId = 
{
	filename = "./tests/testDuplicateParameterId.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(2,11); loc_end=(2,12); loc_bchar=27; loc_echar=28},
(Some "Duplicate identifier: p")))
}

let testDuplicateParameterIdOK = 
{
	filename = "./tests/testDuplicateParameterIdOK.uc";
	expectedResult = None
}

let testEmptyDirectIO = 
{
	filename = "./tests/testEmptyDirectIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(1,10); loc_end=(1,11); loc_bchar=10; loc_echar=11},
None))
}

let testEmptyDirectIOOK = 
{
	filename = "./tests/testEmptyDirectIOOK.uc";
	expectedResult = None
}

let testCompositeDirIOreferencingNonDirIO = 
{
	filename = "./tests/testCompositeDirIOreferencingNonDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(5,12); loc_end=(5,13); loc_bchar=40; loc_echar=41},
(Some "directIO A hasn't been defined yet.")))
}

let testCompositeDirIOreferencingNonDirIOOK = 
{
	filename = "./tests/testCompositeDirIOreferencingNonDirIOOK.uc";
	expectedResult = None
}

let testNonExistingDirIoIdInCompositeBody = 
{
	filename = "./tests/testNonExistingDirIoIdInCompositeBody.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(3,12); loc_end=(3,13); loc_bchar=14; loc_echar=15},
(Some "directIO A hasn't been defined yet.")))
}

let testNonExistingDirIoIdInCompositeBodyOK = 
{
	filename = "./tests/testNonExistingDirIoIdInCompositeBodyOK.uc";
	expectedResult = None
}

let testDirectIOTupleNonexistingType = 
{
	filename = "./tests/testDirectIOTupleNonexistingType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(1,36); loc_end=(1,40); loc_bchar=36; loc_echar=40},
(Some "Non-existing type: mint")))
}

let testDirectIOTupleNonexistingTypeOK = 
{
	filename = "./tests/testDirectIOTupleNonexistingTypeOK.uc";
	expectedResult = None
}


let testRealFunImplements2DirIOs = 
{
	filename = "./tests/testRealFunImplements2DirIOs.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(13,31); loc_end=(13,32); loc_bchar=113; loc_echar=114},
(Some "adversarialIO B doesn't exist.")))
}

let testRealFunImplements2DirIOsOK = 
{
	filename = "./tests/testRealFunImplements2DirIOsOK.uc";
	expectedResult = None
}


let testRealFunImplements2AdvIOs = 
{
	filename = "./tests/testRealFunImplements2AdvIOs.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(13,29); loc_end=(13,30); loc_bchar=127; loc_echar=128},
(Some "directIO A doesn't exist.")))
}

let testRealFunImplements2AdvIOsOK = 
{
	filename = "./tests/testRealFunImplements2AdvIOsOK.uc";
	expectedResult = None
}


let testRealFunParamIONonExisting = 
{
	filename = "./tests/testRealFunParamIONonExisting.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(7,24); loc_end=(7,25); loc_bchar=65; loc_echar=66},
(Some "directIO C doesn't exist.")))
}

let testRealFunParamIONonExistingOK = 
{
	filename = "./tests/testRealFunParamIONonExistingOK.uc";
	expectedResult = None
}

let testRealFunParamIdNotUnique = 
{
	filename = "./tests/testRealFunParamIdNotUnique.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(7,21); loc_end=(7,23); loc_bchar=61; loc_echar=63},
(Some "Duplicate identifier: F1")))
}

let testRealFunParamIdNotUniqueOK = 
{
	filename = "./tests/testRealFunParamIdNotUniqueOK.uc";
	expectedResult = None
}

let testRealFunParamIONotComposite = 
{
	filename = "./tests/testRealFunParamIONotComposite.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(7,18); loc_end=(7,19); loc_bchar=58; loc_echar=59},
(Some "The IO must be composite (even if it has only one component).")))
}

let testRealFunParamIONotCompositeOK = 
{
	filename = "./tests/testRealFunParamIONotCompositeOK.uc";
	expectedResult = None
}

let testRealFunParamIOAdversarial = 
{
	filename = "./tests/testRealFunParamIOAdversarial.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(13,18); loc_end=(13,19); loc_bchar=106; loc_echar=107},
(Some "directIO X doesn't exist.")))
}

let testRealFunParamIOAdversarialOK = 
{
	filename = "./tests/testRealFunParamIOAdversarialOK.uc";
	expectedResult = None
}

let testRealFunIdSameAsIOid = 
{
	filename = "./tests/testRealFunIdSameAsIOid.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(7,14); loc_end=(7,15); loc_bchar=55; loc_echar=56},
(Some "Duplicate identifier: A")))
}

let testRealFunIdSameAsIOidOK = 
{
	filename = "./tests/testRealFunIdSameAsIOidOK.uc";
	expectedResult = None
}

let testIdealFunImplements2DirIOs = 
{
	filename = "./tests/testIdealFunImplements2DirIOs.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(13,31); loc_end=(13,32); loc_bchar=122; loc_echar=123},
(Some "adversarialIO I doesn't exist.")))
}

let testIdealFunImplements2DirIOsOK = 
{
	filename = "./tests/testIdealFunImplements2DirIOsOK.uc";
	expectedResult = None
}

let testIdealFunImplements2AdvIOs = 
{
	filename = "./tests/testIdealFunImplements2AdvIOs.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(11,29); loc_end=(11,30); loc_bchar=107; loc_echar=108},
(Some "directIO D doesn't exist.")))
}

let testIdealFunImplements2AdvIOsOK = 
{
	filename = "./tests/testIdealFunImplements2AdvIOsOK.uc";
	expectedResult = None
}

let testIdealFunImplementsCompositeAdvIO = 
{
	filename = "./tests/testIdealFunImplementsCompositeAdvIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(18,31); loc_end=(18,32); loc_bchar=157; loc_echar=158},
(Some "This adversarialIO cannot be composite.")))
}

let testIdealFunImplementsCompositeAdvIOOK = 
{
	filename = "./tests/testIdealFunImplementsCompositeAdvIOOK.uc";
	expectedResult = None
}


let testCircFunRefSingleStep = 
{
	filename = "./tests/testCircFunRefSingleStep.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(7,14); loc_end=(7,15); loc_bchar=55; loc_echar=56},
(Some "R contains a circular reference.")))
}

let testCircFunRefSingleStepOK = 
{
	filename = "./tests/testCircFunRefSingleStepOK.uc";
	expectedResult = None
}

let testCircFunRefTwoSteps = 
{
	filename = "./tests/testCircFunRefTwoSteps.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(21,14); loc_end=(21,15); loc_bchar=210; loc_echar=211},
(Some "Q contains a circular reference.")))
}

let testCircFunRefTwoStepsOK = 
{
	filename = "./tests/testCircFunRefTwoStepsOK.uc";
	expectedResult = None
}

let testSubFunNonExistingFun = 
{
	filename = "./tests/testSubFunNonExistingFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(9,11); loc_end=(9,12); loc_bchar=86; loc_echar=87},
(Some "Nonexisting functionality : Q")))
}

let testSubFunNonExistingFunOK = 
{
	filename = "./tests/testSubFunNonExistingFunOK.uc";
	expectedResult = None
}

let testDuplicateSubFunId = 
{
	filename = "./tests/testDuplicateSubFunId.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(24,7); loc_end=(24,9); loc_bchar=239; loc_echar=241},
(Some "Duplicate identifier: SF")))
}

let testDuplicateSubFunIdOK = 
{
	filename = "./tests/testDuplicateSubFunIdOK.uc";
	expectedResult = None
}

let testSubFunRFWrongParamNo = 
{
	filename = "./tests/testSubFunRFWrongParamNo.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(20,8); loc_end=(20,10); loc_bchar=228; loc_echar=230},
(Some "Wrong number of parameters for subfunctionality")))
}

let testSubFunRFWrongParamNoOK = 
{
	filename = "./tests/testSubFunRFWrongParamNoOK.uc";
	expectedResult = None
}


let testSubFunRFWrongParamTypeIF = 
{
	filename = "./tests/testSubFunRFWrongParamTypeIF.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(41,8); loc_end=(41,10); loc_bchar=431; loc_echar=433},
(Some "Parameter provided to subfunctionality implement different directIOs from declared parameters.")))
}

let testSubFunRFWrongParamTypeIFOK = 
{
	filename = "./tests/testSubFunRFWrongParamTypeIFOK.uc";
	expectedResult = None
}

let testSubFunRFWrongParamTypeRF = 
{
	filename = "./tests/testSubFunRFWrongParamTypeRF.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(41,8); loc_end=(41,10); loc_bchar=428; loc_echar=430},
(Some "Parameter provided to subfunctionality implement different directIOs from declared parameters.")))
}

let testSubFunRFWrongParamTypeRFOK = 
{
	filename = "./tests/testSubFunRFWrongParamTypeRFOK.uc";
	expectedResult = None
}

let testSubFunRFWrongParamTypeParam = 
{
	filename = "./tests/testSubFunRFWrongParamTypeParam.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(26,8); loc_end=(26,10); loc_bchar=274; loc_echar=276},
(Some "Parameter provided to subfunctionality implement different directIOs from declared parameters.")))
}

let testSubFunRFWrongParamTypeParamOK = 
{
	filename = "./tests/testSubFunRFWrongParamTypeParamOK.uc";
	expectedResult = None
}

let testSubFunIdSameAsParamId = 
{
	filename = "./tests/testSubFunIdSameAsParamId.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(29,8); loc_end=(29,9); loc_bchar=272; loc_echar=273},
(Some "The name Q is the same name as one of the functionalities parameters.")))
}

let testSubFunIdSameAsParamIdOK = 
{
	filename = "./tests/testSubFunIdSameAsParamIdOK.uc";
	expectedResult = None
}

let testPartyServesDeclIOItemNotASubIO = 
{
	filename = "./tests/testPartyServesDeclIOItemNotASubIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(10,16); loc_end=(10,23); loc_bchar=94; loc_echar=101},
(Some "Bio.Cio is not a part of the interfaces implemented by functionality.")))
}

let testPartyServesDeclIOItemNotASubIOOK = 
{
	filename = "./tests/testPartyServesDeclIOItemNotASubIOOK.uc";
	expectedResult = None
}

let testPartyServesDeclNotInDirIO = 
{
	filename = "./tests/testPartyServesDeclNotInDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(14,16); loc_end=(14,19); loc_bchar=98; loc_echar=101},
(Some "Cio is not a part of the interfaces implemented by functionality.")))
}

let testPartyServesDeclNotInDirIOOK = 
{
	filename = "./tests/testPartyServesDeclNotInDirIOOK.uc";
	expectedResult = None
}

let testPartyServesDeclMultipleInIOs = 
{
	filename = "./tests/testPartyServesDeclMultipleInIOs.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(19,17); loc_end=(19,22); loc_bchar=154; loc_echar=159},
(Some "subio is ambiguous, it is in both direct and adversarial IOs implemented by functionality.")))
}

let testPartyServesDeclMultipleInIOsOK = 
{
	filename = "./tests/testPartyServesDeclMultipleInIOsOK.uc";
	expectedResult = None
}

let testPartiesServeSameIO = 
{
	filename = "./tests/testPartiesServeSameIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(21,17); loc_end=(21,21); loc_bchar=211; loc_echar=215},
(Some "Parties must serve distinct IOs")))
}

let testPartiesServeSameIOOK = 
{
	filename = "./tests/testPartiesServeSameIOOK.uc";
	expectedResult = None
}

let testPartiesDontServeEntireDirIO = 
{
	filename = "./tests/testPartiesDontServeEntireDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(12,17); loc_end=(21,21); loc_bchar=108; loc_echar=221},
(Some "These IOs are not served by any party: 
A.Bio3")))
}

let testPartiesDontServeEntireDirIOOK = 
{
	filename = "./tests/testPartiesDontServeEntireDirIOOK.uc";
	expectedResult = None
}

let testPartiesDontServeEntireAdvIO = 
{
	filename = "./tests/testPartiesDontServeEntireAdvIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(18,17); loc_end=(27,19); loc_bchar=156; loc_echar=270},
(Some "These IOs are not served by any party: 
A.Bio2")))
}

let testPartiesDontServeEntireAdvIOOK = 
{
	filename = "./tests/testPartiesDontServeEntireAdvIOOK.uc";
	expectedResult = None
}

let testPartyServesDeclNoDirIO = 
{
	filename = "./tests/testPartyServesDeclNoDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(28,17); loc_end=(28,24); loc_bchar=266; loc_echar=273},
(Some "A party must serve one basic direct IO.")))
}

let testPartyServesDeclNoDirIOOK = 
{
	filename = "./tests/testPartyServesDeclNoDirIOOK.uc";
	expectedResult = None
}

let testPartyServesDeclTwoDirIO = 
{
	filename = "./tests/testPartyServesDeclTwoDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(30,26); loc_end=(30,34); loc_bchar=301; loc_echar=309},
(Some "A party can serve at most one basic direct IO and one basic adversarial IO.")))
}

let testPartyServesDeclTwoDirIOOK = 
{
	filename = "./tests/testPartyServesDeclTwoDirIOOK.uc";
	expectedResult = None
}

let testPartyNoInitialState = 
{
	filename = "./tests/testPartyNoInitialState.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(8,7); loc_end=(8,8); loc_bchar=81; loc_echar=82},
(Some "P doesn't have initial state")))
}

let testPartyNoInitialStateOK = 
{
	filename = "./tests/testPartyNoInitialStateOK.uc";
	expectedResult = None
}

let testPartyMultipleInitialStates = 
{
	filename = "./tests/testPartyMultipleInitialStates.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(8,7); loc_end=(8,8); loc_bchar=81; loc_echar=82},
(Some "P has more than one initial state")))
}

let testPartyMultipleInitialStatesOK = 
{
	filename = "./tests/testPartyMultipleInitialStatesOK.uc";
	expectedResult = None
}

let testPartyDuplicateStateId = 
{
	filename = "./tests/testPartyDuplicateStateId.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,8); loc_end=(16,9); loc_bchar=182; loc_echar=183},
(Some "Duplicate identifier: S")))
}

let testPartyDuplicateStateIdOK = 
{
	filename = "./tests/testPartyDuplicateStateIdOK.uc";
	expectedResult = None
}

let testStateParamsDuplicateIds = 
{
	filename = "./tests/testStateParamsDuplicateIds.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,18); loc_end=(16,19); loc_bchar=192; loc_echar=193},
(Some "Duplicate identifier: p")))
}

let testStateParamsDuplicateIdsOK = 
{
	filename = "./tests/testStateParamsDuplicateIdsOK.uc";
	expectedResult = None
}

let testStateParamsNonExistingType = 
{
	filename = "./tests/testStateParamsNonExistingType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,20); loc_end=(16,24); loc_bchar=194; loc_echar=198},
(Some "Non-existing type: qort")))
}

let testStateParamsNonExistingTypeOK = 
{
	filename = "./tests/testStateParamsNonExistingTypeOK.uc";
	expectedResult = None
}

let testStateVarsDuplicateIds = 
{
	filename = "./tests/testStateVarsDuplicateIds.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(18,19); loc_end=(18,20); loc_bchar=209; loc_echar=210},
(Some "Duplicate identifier: p")))
}

let testStateVarsDuplicateIdsOK = 
{
	filename = "./tests/testStateVarsDuplicateIdsOK.uc";
	expectedResult = None
}

let testStateVarParamDuplicateIds = 
{
	filename = "./tests/testStateVarParamDuplicateIds.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,10); loc_end=(16,11); loc_bchar=184; loc_echar=185},
(Some "Variable name p is the same as one of the states parameters.")))
}

let testStateVarParamDuplicateIdsOK = 
{
	filename = "./tests/testStateVarParamDuplicateIdsOK.uc";
	expectedResult = None
}

let testStateVarsNonExistingType = 
{
	filename = "./tests/testStateVarsNonExistingType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(18,21); loc_end=(18,25); loc_bchar=211; loc_echar=215},
(Some "Non-existing type: qort")))
}

let testStateVarsNonExistingTypeOK = 
{
	filename = "./tests/testStateVarsNonExistingTypeOK.uc";
	expectedResult = None
}

let testMsgMatchAlreadyCovered = 
{
	filename = "./tests/testMsgMatchAlreadyCovered.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(42,5); loc_end=(42,13); loc_bchar=580; loc_echar=588},
(Some "This match is covered by previous matches and would never execute.")))
}

let testMsgMatchAlreadyCoveredOK = 
{
	filename = "./tests/testMsgMatchAlreadyCoveredOK.uc";
	expectedResult = None
}

let testMsgMatchIncomplete = 
{
	filename = "./tests/testMsgMatchIncomplete.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(20,7); loc_end=(20,10); loc_bchar=230; loc_echar=233},
(Some "Message match is not exhaustive, these messages are not matched:
I.othermsg")))
}

let testMsgMatchIncompleteOK = 
{
	filename = "./tests/testMsgMatchIncompleteOK.uc";
	expectedResult = None
}

let testMsgMatchUnexpected = 
{
	filename = "./tests/testMsgMatchUnexpected.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(38,9); loc_end=(38,12); loc_bchar=484; loc_echar=487},
(Some "The message is unexpected. These messages are expected:
D.D.bla
A.A.bla
X.D.bli
f.D.bli")))
}

let testMsgMatchUnexpectedOK = 
{
	filename = "./tests/testMsgMatchUnexpectedOK.uc";
	expectedResult = None
}

let testMsgMatchAmbiguous = 
{
	filename = "./tests/testMsgMatchAmbiguous.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(34,5); loc_end=(34,8); loc_bchar=380; loc_echar=383},
(Some "The message is ambiguous. There are multiple messages that match the description:
D.D.bla
A.A.bla")))
}

let testMsgMatchAmbiguousOK = 
{
	filename = "./tests/testMsgMatchAmbiguousOK.uc";
	expectedResult = None
}

let testMsgMatchInternalNotFQ = 
{
	filename = "./tests/testMsgMatchInternalNotFQ.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(14,5); loc_end=(14,10); loc_bchar=160; loc_echar=165},
(Some "Internal messages must have full paths. Did you mean P.D.bli ?")))
}

let testMsgMatchInternalNotFQOK = 
{
	filename = "./tests/testMsgMatchInternalNotFQOK.uc";
	expectedResult = None
}

let testMsgMatchBindingPortVarNonDirIO = 
{
	filename = "./tests/testMsgMatchBindingPortVarNonDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(23,5); loc_end=(23,6); loc_bchar=224; loc_echar=225},
(Some "The message A maybe isn't an incoming message of a directIO served by the party and cannot bind the source port to a variable.")))
}

let testMsgMatchBindingPortVarNonDirIOOK = 
{
	filename = "./tests/testMsgMatchBindingPortVarNonDirIOOK.uc";
	expectedResult = None
}

let testMsgMatchBindingOtherMsg = 
{
	filename = "./tests/testMsgMatchBindingOtherMsg.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(23,7); loc_end=(23,15); loc_bchar=226; loc_echar=234},
(Some "othermsg cannot have value bindings. Do you have redundant parenthesis?")))
}

let testMsgMatchBindingOtherMsgOK = 
{
	filename = "./tests/testMsgMatchBindingOtherMsgOK.uc";
	expectedResult = None
}

let testMsgMatchBindingWrongParamNo = 
{
	filename = "./tests/testMsgMatchBindingWrongParamNo.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(23,11); loc_end=(23,12); loc_bchar=230; loc_echar=231},
(Some "The number of bindings is different then the number of message parameters.")))
}

let testMsgMatchBindingWrongParamNoOK = 
{
	filename = "./tests/testMsgMatchBindingWrongParamNoOK.uc";
	expectedResult = None
}

let testMsgMatchBindingWrongTyp = 
{
	filename = "./tests/testMsgMatchBindingWrongTyp.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(25,9); loc_end=(25,10); loc_bchar=269; loc_echar=270},
(Some "e doesn't have type compatible with key")))
}

let testMsgMatchBindingWrongTypOK = 
{
	filename = "./tests/testMsgMatchBindingWrongTypOK.uc";
	expectedResult = None
}

let testMsgMatchBindingToStateParam = 
{
	filename = "./tests/testMsgMatchBindingToStateParam.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(30,11); loc_end=(30,12); loc_bchar=316; loc_echar=317},
(Some "p is already used.")))
}

let testMsgMatchBindingToStateParamOK = 
{
	filename = "./tests/testMsgMatchBindingToStateParamOK.uc";
	expectedResult = None
}

let testExprNonExistingVarOp = 
{
	filename = "./tests/testExprNonExistingVarOp.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,60); loc_end=(16,63); loc_bchar=249; loc_echar=252},
(Some "Nonexisting variable or constant: k.k")))
}

let testExprNonExistingVarOpOK = 
{
	filename = "./tests/testExprNonExistingVarOpOK.uc";
	expectedResult = None
}

let testExprNonexistingFun = 
{
	filename = "./tests/testExprNonexistingFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,20); loc_end=(17,23); loc_bchar=223; loc_echar=226},
(Some "Nonexisting operator or function.")))
}

let testExprNonexistingFunOK = 
{
	filename = "./tests/testExprNonexistingFunOK.uc";
	expectedResult = None
}

let testExprNaryOpUsedAsNullaryOp = 
{
	filename = "./tests/testExprNaryOpUsedAsNullaryOp.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,60); loc_end=(16,63); loc_bchar=249; loc_echar=252},
(Some "Nullary operator expected, operator inj has arguments.")))
}

let testExprNaryOpUsedAsNullaryOpOK = 
{
	filename = "./tests/testExprNaryOpUsedAsNullaryOpOK.uc";
	expectedResult = None
}

let testExprWrongArgNo = 
{
	filename = "./tests/testExprWrongArgNo.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,60); loc_end=(16,63); loc_bchar=249; loc_echar=252},
(Some "gen expects 1 arguments, 2 arguments provided")))
}

let testExprWrongArgNoOK = 
{
	filename = "./tests/testExprWrongArgNoOK.uc";
	expectedResult = None
}

let testExprWrongArgType = 
{
	filename = "./tests/testExprWrongArgType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,62); loc_end=(16,63); loc_bchar=251; loc_echar=252},
(Some "Type mismatch for 2. argument. Expected type:exp. Provided type:key.")))
}

let testExprWrongArgTypeOK = 
{
	filename = "./tests/testExprWrongArgTypeOK.uc";
	expectedResult = None
}

let testExprWrongArgTypeVar = 
{
	filename = "./tests/testExprWrongArgTypeVar.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,60); loc_end=(16,61); loc_bchar=249; loc_echar=250},
(Some "Type mismatch, 2. and 1. argument must have the same type.")))
}

let testExprWrongArgTypeVarOK = 
{
	filename = "./tests/testExprWrongArgTypeVarOK.uc";
	expectedResult = None
}

let testExprEncode = 
{
	filename = "./tests/testExprEncode.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,24); loc_end=(17,25); loc_bchar=228; loc_echar=229},
(Some "s doesn't have type compatible with univ")))
}

let testExprEncodeOK = 
{
	filename = "./tests/testExprEncodeOK.uc";
	expectedResult = None
}

let testExprTupleWrongArity = 
{
	filename = "./tests/testExprTupleWrongArity.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,24); loc_end=(17,26); loc_bchar=234; loc_echar=236},
(Some "pp doesn't have type compatible with port")))
}

let testExprTupleWrongArityOK = 
{
	filename = "./tests/testExprTupleWrongArityOK.uc";
	expectedResult = None
}

let testTransitionNonExistingState = 
{
	filename = "./tests/testTransitionNonExistingState.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,57); loc_end=(16,60); loc_bchar=246; loc_echar=249},
(Some "Non-existing state: III")))
}

let testTransitionNonExistingStateOK = 
{
	filename = "./tests/testTransitionNonExistingStateOK.uc";
	expectedResult = None
}

let testTransitionWrongParamNo = 
{
	filename = "./tests/testTransitionWrongParamNo.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,57); loc_end=(16,59); loc_bchar=246; loc_echar=248},
(Some "Wrong number of parameters.")))
}

let testTransitionWrongParamNoOK = 
{
	filename = "./tests/testTransitionWrongParamNoOK.uc";
	expectedResult = None
}

let testTransitionWrongParamType = 
{
	filename = "./tests/testTransitionWrongParamType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,60); loc_end=(16,61); loc_bchar=250; loc_echar=251},
(Some "1. parameter of state II has type key, which is incompatible with provided type exp")))
}

let testTransitionWrongParamTypeOK = 
{
	filename = "./tests/testTransitionWrongParamTypeOK.uc";
	expectedResult = None
}

let testTransitionNoParams = 
{
	filename = "./tests/testTransitionNoParams.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,57); loc_end=(16,59); loc_bchar=246; loc_echar=248},
(Some "State has parameters, none are provided.")))
}

let testTransitionNoParamsOK = 
{
	filename = "./tests/testTransitionNoParamsOK.uc";
	expectedResult = None
}

let testTransitionInitialWithParams = 
{
	filename = "./tests/testTransitionInitialWithParams.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,57); loc_end=(16,58); loc_bchar=246; loc_echar=247},
(Some "State doesn't have parameters, do you have reduntant parentheses?")))
}

let testTransitionInitialWithParamsOK = 
{
	filename = "./tests/testTransitionInitialWithParamsOK.uc";
	expectedResult = None
}

let testStateParamNonExistingType = 
{
	filename = "./tests/testStateParamNonExistingType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(19,13); loc_end=(19,16); loc_bchar=226; loc_echar=229},
(Some "Non-existing type: kye")))
}

let testStateParamNonExistingTypeOK = 
{
	filename = "./tests/testStateParamNonExistingTypeOK.uc";
	expectedResult = None
}

let testStateVarNonExistingType = 
{
	filename = "./tests/testStateVarNonExistingType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(15,13); loc_end=(15,14); loc_bchar=180; loc_echar=181},
(Some "Non-existing type: c")))
}

let testStateVarNonExistingTypeOK = 
{
	filename = "./tests/testStateVarNonExistingTypeOK.uc";
	expectedResult = None
}

let testValueAssignWrongType = 
{
	filename = "./tests/testValueAssignWrongType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,18); loc_end=(17,19); loc_bchar=223; loc_echar=224},
(Some "x doesn't have type compatible with key")))
}

let testValueAssignWrongTypeOK = 
{
	filename = "./tests/testValueAssignWrongTypeOK.uc";
	expectedResult = None
}

let testValueAssignInternalPortWrongType = 
{
	filename = "./tests/testValueAssignInternalPortWrongType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,18); loc_end=(17,19); loc_bchar=226; loc_echar=227},
(Some "x doesn't have type compatible with port")))
}

let testValueAssignInternalPortWrongTypeOK = 
{
	filename = "./tests/testValueAssignInternalPortWrongTypeOK.uc";
	expectedResult = None
}

let testValueAssignNonexistingVar = 
{
	filename = "./tests/testValueAssignNonexistingVar.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,18); loc_end=(17,19); loc_bchar=223; loc_echar=224},
(Some "y is neither a local variable nor a state parameter")))
}

let testValueAssignNonexistingVarOK = 
{
	filename = "./tests/testValueAssignNonexistingVarOK.uc";
	expectedResult = None
}

let testValueAssignConst = 
{
	filename = "./tests/testValueAssignConst.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,16); loc_end=(17,17); loc_bchar=226; loc_echar=227},
(Some "k is not a local variable and values cannot be bound to it.")))
}

let testValueAssignConstOK = 
{
	filename = "./tests/testValueAssignConstOK.uc";
	expectedResult = None
}

let testExprUsesUnassignedVar = 
{
	filename = "./tests/testExprUsesUnassignedVar.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,22); loc_end=(17,23); loc_bchar=238; loc_echar=239},
(Some "x is not initialized.")))
}

let testExprUsesUnassignedVarOK = 
{
	filename = "./tests/testExprUsesUnassignedVarOK.uc";
	expectedResult = None
}

let testSampleAssignWrongType = 
{
	filename = "./tests/testSampleAssignWrongType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,17); loc_end=(17,18); loc_bchar=222; loc_echar=223},
(Some "x doesn't have type compatible with exp")))
}

let testSampleAssignWrongTypeOK = 
{
	filename = "./tests/testSampleAssignWrongTypeOK.uc";
	expectedResult = None
}

let testSampleAssignNotFromDistr = 
{
	filename = "./tests/testSampleAssignNotFromDistr.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,22); loc_end=(17,23); loc_bchar=227; loc_echar=228},
(Some "You can sample only from distributions.")))
}

let testSampleAssignNotFromDistrOK = 
{
	filename = "./tests/testSampleAssignNotFromDistrOK.uc";
	expectedResult = None
}

let testSendDirectNoPort = 
{
	filename = "./tests/testSendDirectNoPort.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,22); loc_end=(16,25); loc_bchar=211; loc_echar=214},
(Some "Missing destination port.")))
}

let testSendDirectNoPortOK = 
{
	filename = "./tests/testSendDirectNoPortOK.uc";
	expectedResult = None
}

let testSendDirectIn = 
{
	filename = "./tests/testSendDirectIn.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,24); loc_end=(16,27); loc_bchar=213; loc_echar=216},
(Some "The message is unexpected. These messages are expected:
A.A.bli")))
}

let testSendDirectInOK = 
{
	filename = "./tests/testSendDirectInOK.uc";
	expectedResult = None
}

let testSendAdversWithPort = 
{
	filename = "./tests/testSendAdversWithPort.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(23,34); loc_end=(23,37); loc_bchar=288; loc_echar=291},
(Some "Only direct messages can have destination port.")))
}

let testSendAdversWithPortOK = 
{
	filename = "./tests/testSendAdversWithPortOK.uc";
	expectedResult = None
}

let testSendAdversIn = 
{
	filename = "./tests/testSendAdversIn.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(23,34); loc_end=(23,37); loc_bchar=288; loc_echar=291},
(Some "The message is unexpected. These messages are expected:
D.D.bli
A.A.bli")))
}

let testSendAdversInOK = 
{
	filename = "./tests/testSendAdversInOK.uc";
	expectedResult = None
}

let testSendInternWithPort = 
{
	filename = "./tests/testSendInternWithPort.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,36); loc_end=(16,39); loc_bchar=228; loc_echar=231},
(Some "Messages to subfunctionalities cannot have destination port.")))
}

let testSendInternWithPortOK = 
{
	filename = "./tests/testSendInternWithPortOK.uc";
	expectedResult = None
}

let testSendInternOut = 
{
	filename = "./tests/testSendInternOut.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,36); loc_end=(16,39); loc_bchar=228; loc_echar=231},
(Some "The message is unexpected. These messages are expected:
D.D.bli
G.D.bla")))
}

let testSendInternOutOK = 
{
	filename = "./tests/testSendInternOutOK.uc";
	expectedResult = None
}

let testSendWrongParamNo = 
{
	filename = "./tests/testSendWrongParamNo.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,40); loc_end=(16,46); loc_bchar=232; loc_echar=238},
(Some "Parameter number mismatch.")))
}

let testSendWrongParamNoOK = 
{
	filename = "./tests/testSendWrongParamNoOK.uc";
	expectedResult = None
}

let testSendWrongParamType = 
{
	filename = "./tests/testSendWrongParamType.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,40); loc_end=(16,46); loc_bchar=237; loc_echar=243},
(Some "Parameter type mismatch")))
}

let testSendWrongParamTypeOK = 
{
	filename = "./tests/testSendWrongParamTypeOK.uc";
	expectedResult = None
}

let testITEcondNotBoolean = 
{
	filename = "./tests/testITEcondNotBoolean.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(14,31); loc_end=(14,37); loc_bchar=185; loc_echar=191},
(Some "The condition must be a boolean expression.")))
}

let testITEcondNotBooleanOK = 
{
	filename = "./tests/testITEcondNotBooleanOK.uc";
	expectedResult = None
}

let testITEInitVarInOneBranch = 
{
	filename = "./tests/testITEInitVarInOneBranch.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,57); loc_end=(17,58); loc_bchar=268; loc_echar=269},
(Some "k is not initialized.")))
}

let testITEInitVarInOneBranchOK = 
{
	filename = "./tests/testITEInitVarInOneBranchOK.uc";
	expectedResult = None
}

let testDecodeNonuniv = 
{
	filename = "./tests/testDecodeNonuniv.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,23); loc_end=(16,24); loc_bchar=217; loc_echar=218},
(Some "Only expressions of univ type can be decoded.")))
}

let testDecodeNonunivOK = 
{
	filename = "./tests/testDecodeNonunivOK.uc";
	expectedResult = None
}

let testDecodeTupleWrongParamNo = 
{
	filename = "./tests/testDecodeTupleWrongParamNo.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(15,21); loc_end=(15,22); loc_bchar=221; loc_echar=222},
(Some "The number of bindings is different from the arity of decoded type.")))
}

let testDecodeTupleWrongParamNoOK = 
{
	filename = "./tests/testDecodeTupleWrongParamNoOK.uc";
	expectedResult = None
}

let testEndsWSaTorFInstAfterF = 
{
	filename = "./tests/testEndsWSaTorFInstAfterF.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,27); loc_end=(17,32); loc_bchar=238; loc_echar=243},
(Some "The instructions after fail will not be executed")))
}

let testEndsWSaTorFInstAfterFOK = 
{
	filename = "./tests/testEndsWSaTorFInstAfterFOK.uc";
	expectedResult = None
}

let testEndsWSaTorFInstAfterSaT = 
{
	filename = "./tests/testEndsWSaTorFInstAfterSaT.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,27); loc_end=(17,62); loc_bchar=238; loc_echar=273},
(Some "The instructions after send and transition will not be executed")))
}

let testEndsWSaTorFInstAfterSaTOK = 
{
	filename = "./tests/testEndsWSaTorFInstAfterSaTOK.uc";
	expectedResult = None
}

let testEndsWSaTorFNoSaTorF = 
{
	filename = "./tests/testEndsWSaTorFNoSaTorF.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(17,27); loc_end=(17,32); loc_bchar=238; loc_echar=243},
(Some "Every branch of execution must end with send and transition or fail command.")))
}

let testEndsWSaTorFNoSaTorFOK = 
{
	filename = "./tests/testEndsWSaTorFNoSaTorFOK.uc";
	expectedResult = None
}

let testEndsWSaTorFInstAfterITE = 
{
	filename = "./tests/testEndsWSaTorFInstAfterITE.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(16,57); loc_end=(16,62); loc_bchar=267; loc_echar=272},
(Some "The instructions after if-then-else will not be executed since both branches contain send and transition or fail commands.")))
}

let testEndsWSaTorFInstAfterITEOK = 
{
	filename = "./tests/testEndsWSaTorFInstAfterITEOK.uc";
	expectedResult = None
}

let testEndsWSaTorFInstAfterDecode = 
{
	filename = "./tests/testEndsWSaTorFInstAfterDecode.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(18,2); loc_end=(18,7); loc_bchar=259; loc_echar=264},
(Some "The instructions after decode will not be executed since both branches contain send and transition or fail commands.")))
}

let testEndsWSaTorFInstAfterDecodeOK = 
{
	filename = "./tests/testEndsWSaTorFInstAfterDecodeOK.uc";
	expectedResult = None
}

let testIdealFunMsgMatchIncomplete = 
{
	filename = "./tests/testIdealFunMsgMatchIncomplete.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(20,7); loc_end=(20,10); loc_bchar=230; loc_echar=233},
(Some "Message match is not exhaustive, these messages are not matched:
I.othermsg")))
}

let testIdealFunMsgMatchIncompleteOK = 
{
	filename = "./tests/testIdealFunMsgMatchIncompleteOK.uc";
	expectedResult = None
}

let testSimUsesNonI2SIO = 
{
	filename = "./tests/testSimUsesNonI2SIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(18,17); loc_end=(18,18); loc_bchar=201; loc_echar=202},
(Some "adversarialIO D doesn't exist.")))
}

let testSimUsesNonI2SIOOK = 
{
	filename = "./tests/testSimUsesNonI2SIOOK.uc";
	expectedResult = None
}

let testSimSimulatesNonRealFun = 
{
	filename = "./tests/testSimSimulatesNonRealFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(20,31); loc_end=(20,32); loc_bchar=237; loc_echar=238},
(Some "The simulated functionality must have parties.")))
}

let testSimSimulatesNonRealFunOK = 
{
	filename = "./tests/testSimSimulatesNonRealFunOK.uc";
	expectedResult = None
}

let testSimWrongParamNumForSimFun = 
{
	filename = "./tests/testSimWrongParamNumForSimFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(30,31); loc_end=(30,32); loc_bchar=368; loc_echar=369},
(Some "Wrong number of parameters for functionality.")))
}

let testSimWrongParamNumForSimFunOK = 
{
	filename = "./tests/testSimWrongParamNumForSimFunOK.uc";
	expectedResult = None
}

let testSimParamForSimFunNotIdealFun = 
{
	filename = "./tests/testSimParamForSimFunNotIdealFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(30,33); loc_end=(30,34); loc_bchar=373; loc_echar=374},
(Some "The parameter to simulated functionality cannot have parties")))
}

let testSimParamForSimFunNotIdealFunOK = 
{
	filename = "./tests/testSimParamForSimFunNotIdealFunOK.uc";
	expectedResult = None
}

let testSimWrongParamDirIOForSimFun = 
{
	filename = "./tests/testSimWrongParamDirIOForSimFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(37,33); loc_end=(37,34); loc_bchar=432; loc_echar=433},
(Some "Parameter implements different directIO than required by functionality.")))
}

let testSimWrongParamDirIOForSimFunOK = 
{
	filename = "./tests/testSimWrongParamDirIOForSimFunOK.uc";
	expectedResult = None
}

let testSimInitStateNonI2SMsgMatch = 
{
	filename = "./tests/testSimInitStateNonI2SMsgMatch.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(33,27); loc_end=(33,35); loc_bchar=427; loc_echar=435},
(Some "Initial state can handle only messages comming from ideal functionality. Did you omit prefix iio.?")))
}

let testSimInitStateNonI2SMsgMatchOK = 
{
	filename = "./tests/testSimInitStateNonI2SMsgMatchOK.uc";
	expectedResult = None
}

let testSimMsgMatchOutMsg = 
{
	filename = "./tests/testSimMsgMatchOutMsg.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(37,29); loc_end=(37,32); loc_bchar=495; loc_echar=498},
(Some "bli is not an incoming message of R.F.iio")))
}

let testSimMsgMatchOutMsgOK = 
{
	filename = "./tests/testSimMsgMatchOutMsgOK.uc";
	expectedResult = None
}

let testSimMsgMatchI2SInMsg = 
{
	filename = "./tests/testSimMsgMatchI2SInMsg.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(33,25); loc_end=(33,31); loc_bchar=430; loc_echar=436},
(Some "i2sbla is not an incoming message of iio")))
}

let testSimMsgMatchI2SInMsgOK = 
{
	filename = "./tests/testSimMsgMatchI2SInMsgOK.uc";
	expectedResult = None
}

let testSimMsgMatchRealFunDirIO = 
{
	filename = "./tests/testSimMsgMatchRealFunDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(44,27); loc_end=(44,30); loc_bchar=560; loc_echar=563},
(Some "Not a valid destination, these destinations are valid:
iio
R.A.A
R.F.iio")))
}

let testSimMsgMatchRealFunDirIOOK = 
{
	filename = "./tests/testSimMsgMatchRealFunDirIOOK.uc";
	expectedResult = None
}


let testSimMsgMatchSubFunDirIO = 
{
	filename = "./tests/testSimMsgMatchSubFunDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(70,33); loc_end=(70,36); loc_bchar=852; loc_echar=855},
(Some "Not a valid destination, these destinations are valid:
iio
R.A.A
R.F.iio
R.SFQ.A2.A2")))
}

let testSimMsgMatchSubFunDirIOOK = 
{
	filename = "./tests/testSimMsgMatchSubFunDirIOOK.uc";
	expectedResult = None
}

let testSimMsgMatchParamFunDirIO = 
{
	filename = "./tests/testSimMsgMatchParamFunDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(70,29); loc_end=(70,32); loc_bchar=848; loc_echar=851},
(Some "Not a valid destination, these destinations are valid:
iio
R.A.A
R.F.iio
R.SFQ.A2.A2")))
}

let testSimMsgMatchParamFunDirIOOK = 
{
	filename = "./tests/testSimMsgMatchParamFunDirIOOK.uc";
	expectedResult = None
}

let testSimMsgMatchAlreadyCovered = 
{
	filename = "./tests/testSimMsgMatchAlreadyCovered.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(35,8); loc_end=(35,11); loc_bchar=458; loc_echar=461},
(Some "This match is covered by previous matches and would never execute.")))
}

let testSimMsgMatchAlreadyCoveredOK = 
{
	filename = "./tests/testSimMsgMatchAlreadyCoveredOK.uc";
	expectedResult = None
}

let testSimSendNotI2SorRealFun = 
{
	filename = "./tests/testSimSendNotI2SorRealFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(66,44); loc_end=(66,52); loc_bchar=802; loc_echar=810},
(Some "The message is unexpected. These messages are expected:
iio.i2sbla
R.A.A.abli
R.F.iio.i2sbli
R.SFQ.A2.A2.abli2")))
}

let testSimSendNotI2SorRealFunOK = 
{
	filename = "./tests/testSimSendNotI2SorRealFunOK.uc";
	expectedResult = None
}

let testSimSendI2SOutMsg = 
{
	filename = "./tests/testSimSendI2SOutMsg.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(71,48); loc_end=(71,54); loc_bchar=855; loc_echar=861},
(Some "The message is unexpected. These messages are expected:
iio.i2sbla
R.A.A.abli
R.F.iio2.i2sbli
R.SFQ.A2.A2.abli2")))
}

let testSimSendI2SOutMsgOK = 
{
	filename = "./tests/testSimSendI2SOutMsgOK.uc";
	expectedResult = None
}

let testSimSendRFDirIO = 
{
	filename = "./tests/testSimSendRFDirIO.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(66,50); loc_end=(66,53); loc_bchar=808; loc_echar=811},
(Some "The message is unexpected. These messages are expected:
iio.i2sbla
R.A.A.abli
R.F.iio.i2sbli
R.SFQ.A2.A2.abli2")))
}

let testSimSendRFDirIOOK = 
{
	filename = "./tests/testSimSendRFDirIOOK.uc";
	expectedResult = None
}

let testSimSendRFInAdvMsg = 
{
	filename = "./tests/testSimSendRFInAdvMsg.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(66,49); loc_end=(66,53); loc_bchar=807; loc_echar=811},
(Some "The message is unexpected. These messages are expected:
iio.i2sbla
R.A.A.abli
R.F.iio.i2sbli
R.SFQ.A2.A2.abli2")))
}

let testSimSendRFInAdvMsgOK = 
{
	filename = "./tests/testSimSendRFInAdvMsgOK.uc";
	expectedResult = None
}

let testSimSendNotAdvIOofSubFun = 
{
	filename = "./tests/testSimSendNotAdvIOofSubFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(66,52); loc_end=(66,56); loc_bchar=810; loc_echar=814},
(Some "The message is unexpected. These messages are expected:
iio.i2sbla
R.A.A.abli
R.F.iio.i2sbli
R.SFQ.A2.A2.abli2")))
}

let testSimSendNotAdvIOofSubFunOK = 
{
	filename = "./tests/testSimSendNotAdvIOofSubFunOK.uc";
	expectedResult = None
}


let testSimSendNotOutAdvMsgofSubFun = 
{
	filename = "./tests/testSimSendNotOutAdvMsgofSubFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(66,56); loc_end=(66,61); loc_bchar=814; loc_echar=819},
(Some "The message is unexpected. These messages are expected:
iio.i2sbla
R.A.A.abli
R.F.iio.i2sbli
R.SFQ.A2.A2.abli2")))
}

let testSimSendNotOutAdvMsgofSubFunOK = 
{
	filename = "./tests/testSimSendNotOutAdvMsgofSubFunOK.uc";
	expectedResult = None
}

let testSimSendNotIOofParamFun = 
{
	filename = "./tests/testSimSendNotIOofParamFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(66,52); loc_end=(66,56); loc_bchar=810; loc_echar=814},
(Some "The message is unexpected. These messages are expected:
iio.i2sbla
R.A.A.abli
R.F.iio.i2sbli
R.SFQ.A2.A2.abli2")))
}

let testSimSendNotIOofParamFunOK = 
{
	filename = "./tests/testSimSendNotIOofParamFunOK.uc";
	expectedResult = None
}

let testSimSendNotOutMsgOfParamFun = 
{
	filename = "./tests/testSimSendNotOutMsgOfParamFun.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(66,52); loc_end=(66,58); loc_bchar=810; loc_echar=816},
(Some "The message is unexpected. These messages are expected:
iio.i2sbla
R.A.A.abli
R.F.iio.i2sbli
R.SFQ.A2.A2.abli2")))
}

let testSimSendNotOutMsgOfParamFunOK = 
{
	filename = "./tests/testSimSendNotOutMsgOfParamFunOK.uc";
	expectedResult = None
}

let testSimSendMsgPathIncomplete = 
{
	filename = "./tests/testSimSendMsgPathIncomplete.uc";
	expectedResult = Some (ParseError (
{ loc_fname="";loc_start=(71,44); loc_end=(71,50); loc_bchar=851; loc_echar=857},
(Some "Messages sent by simulator must have complete path, did you mean iio.i2sbla ?")))
}

let testSimSendMsgPathIncompleteOK = 
{
	filename = "./tests/testSimSendMsgPathIncompleteOK.uc";
	expectedResult = None
}

let testCaseStudy = 
{
	filename = "./tests/case-study.uc";
	expectedResult = None
}

let suite = [

testLexicalError;
testLexicalErrorOK;

testParseError;
testParseErrorOK;

testNonExistingAdvIoIdInCompositeBody;
testNonExistingAdvIoIdInCompositeBodyOK;

testCompositeAdvIOreferencingNonAdvIO;
testCompositeAdvIOreferencingNonAdvIOOK;

testCompositeReferencingComposite;
testCompositeReferencingCompositeOK;

testCircularReferenceSelfReference;
testCircularReferenceSelfReferenceOK;

testDuplicateIdInCompositIOBody;
testDuplicateIdInCompositIOBodyOK;

testDuplicateIdInIODefinitions;
testDuplicateIdInIODefinitionsOK;

testDuplicateMessageId;
testDuplicateMessageIdOK;

testDuplicateParameterId;
testDuplicateParameterIdOK;

testEmptyDirectIO;
testEmptyDirectIOOK;

testCompositeDirIOreferencingNonDirIO;
testCompositeDirIOreferencingNonDirIOOK;

testNonExistingDirIoIdInCompositeBody;
testNonExistingDirIoIdInCompositeBodyOK;

testDirectIOTupleNonexistingType;
testDirectIOTupleNonexistingTypeOK;

testRealFunImplements2DirIOs;
testRealFunImplements2DirIOsOK;

testRealFunImplements2AdvIOs;
testRealFunImplements2AdvIOsOK;

testRealFunParamIONonExisting;
testRealFunParamIONonExistingOK;

testRealFunParamIdNotUnique;
testRealFunParamIdNotUniqueOK;

testRealFunParamIONotComposite;
testRealFunParamIONotCompositeOK;

testRealFunParamIOAdversarial;
testRealFunParamIOAdversarialOK;

testRealFunIdSameAsIOid;
testRealFunIdSameAsIOidOK;

testIdealFunImplements2DirIOs;
testIdealFunImplements2DirIOsOK;

testIdealFunImplements2AdvIOs;
testIdealFunImplements2AdvIOsOK;

testIdealFunImplementsCompositeAdvIO;
testIdealFunImplementsCompositeAdvIOOK;

testCircFunRefSingleStep;
testCircFunRefSingleStepOK;

testCircFunRefTwoSteps;
testCircFunRefTwoStepsOK;

testSubFunNonExistingFun;
testSubFunNonExistingFunOK;

testDuplicateSubFunId;
testDuplicateSubFunIdOK;

testSubFunRFWrongParamNo;
testSubFunRFWrongParamNoOK;

testSubFunRFWrongParamTypeIF;
testSubFunRFWrongParamTypeIFOK;

testSubFunRFWrongParamTypeRF;
testSubFunRFWrongParamTypeRFOK;

testSubFunRFWrongParamTypeParam;
testSubFunRFWrongParamTypeParamOK;

testSubFunIdSameAsParamId;
testSubFunIdSameAsParamIdOK;

testPartyServesDeclIOItemNotASubIO;
testPartyServesDeclIOItemNotASubIOOK;

testPartyServesDeclNotInDirIO;
testPartyServesDeclNotInDirIOOK;

testPartyServesDeclMultipleInIOs;
testPartyServesDeclMultipleInIOsOK;

testPartiesServeSameIO;
testPartiesServeSameIOOK;

testPartiesDontServeEntireDirIO;
testPartiesDontServeEntireDirIOOK;

testPartiesDontServeEntireAdvIO;
testPartiesDontServeEntireAdvIOOK;

testPartyServesDeclNoDirIO;
testPartyServesDeclNoDirIOOK;

testPartyServesDeclTwoDirIO;
testPartyServesDeclTwoDirIOOK;

testPartyNoInitialState;
testPartyNoInitialStateOK;

testPartyMultipleInitialStates;
testPartyMultipleInitialStatesOK;

testPartyDuplicateStateId;
testPartyDuplicateStateIdOK;

testStateParamsDuplicateIds;
testStateParamsDuplicateIdsOK;

testStateParamsNonExistingType;
testStateParamsNonExistingTypeOK;

testStateVarsDuplicateIds;
testStateVarsDuplicateIdsOK;

testStateVarParamDuplicateIds;
testStateVarParamDuplicateIdsOK;

testStateVarsNonExistingType;
testStateVarsNonExistingTypeOK;

testMsgMatchAlreadyCovered;
testMsgMatchAlreadyCoveredOK;

testMsgMatchIncomplete;
testMsgMatchIncompleteOK;

testIdealFunMsgMatchIncomplete;
testIdealFunMsgMatchIncompleteOK;

testMsgMatchUnexpected;
testMsgMatchUnexpectedOK;

testMsgMatchAmbiguous;
testMsgMatchAmbiguousOK;

testMsgMatchInternalNotFQ;
testMsgMatchInternalNotFQOK;

testMsgMatchBindingPortVarNonDirIO;
testMsgMatchBindingPortVarNonDirIOOK;

testMsgMatchBindingOtherMsg;
testMsgMatchBindingOtherMsgOK;

testMsgMatchBindingWrongParamNo;
testMsgMatchBindingWrongParamNoOK;

testMsgMatchBindingWrongTyp;
testMsgMatchBindingWrongTypOK;

testMsgMatchBindingToStateParam;
testMsgMatchBindingToStateParamOK;

testExprNonExistingVarOp;
testExprNonExistingVarOpOK;

testExprNonexistingFun;
testExprNonexistingFunOK;

testExprNaryOpUsedAsNullaryOp;
testExprNaryOpUsedAsNullaryOpOK;

testExprWrongArgNo;
testExprWrongArgNoOK;

testExprWrongArgType;
testExprWrongArgTypeOK;

testExprWrongArgTypeVar;
testExprWrongArgTypeVarOK;

testExprEncode;
testExprEncodeOK;

testExprTupleWrongArity;
testExprTupleWrongArityOK;

testTransitionNonExistingState;
testTransitionNonExistingStateOK;

testTransitionWrongParamNo;
testTransitionWrongParamNoOK;

testTransitionWrongParamType;
testTransitionWrongParamTypeOK;

testTransitionNoParams;
testTransitionNoParamsOK;

testTransitionInitialWithParams;
testTransitionInitialWithParamsOK;

testStateParamNonExistingType;
testStateParamNonExistingTypeOK;

testStateVarNonExistingType;
testStateVarNonExistingTypeOK;

testValueAssignWrongType;
testValueAssignWrongTypeOK;

testValueAssignInternalPortWrongType;
testValueAssignInternalPortWrongTypeOK;

testValueAssignNonexistingVar;
testValueAssignNonexistingVarOK;

testValueAssignConst;
testValueAssignConstOK;

testExprUsesUnassignedVar;
testExprUsesUnassignedVarOK;

testSampleAssignWrongType;
testSampleAssignWrongTypeOK;

testSampleAssignNotFromDistr;
testSampleAssignNotFromDistrOK;

testSendDirectNoPort;
testSendDirectNoPortOK;

testSendDirectIn;
testSendDirectInOK;

testSendAdversWithPort;
testSendAdversWithPortOK;

testSendAdversIn;
testSendAdversInOK;

testSendInternWithPort;
testSendInternWithPortOK;

testSendInternOut;
testSendInternOutOK;

testSendWrongParamNo;
testSendWrongParamNoOK;

testSendWrongParamType;
testSendWrongParamTypeOK;

testITEcondNotBoolean;
testITEcondNotBooleanOK;

testITEInitVarInOneBranch;
testITEInitVarInOneBranchOK;

testDecodeNonuniv;
testDecodeNonunivOK;

testDecodeTupleWrongParamNo;
testDecodeTupleWrongParamNoOK;

testEndsWSaTorFInstAfterF;
testEndsWSaTorFInstAfterFOK;

testEndsWSaTorFInstAfterSaT;
testEndsWSaTorFInstAfterSaTOK;

testEndsWSaTorFNoSaTorF;
testEndsWSaTorFNoSaTorFOK;

testEndsWSaTorFInstAfterITE;
testEndsWSaTorFInstAfterITEOK;

testEndsWSaTorFInstAfterDecode;
testEndsWSaTorFInstAfterDecodeOK;

testSimUsesNonI2SIO;
testSimUsesNonI2SIOOK;

testSimSimulatesNonRealFun;
testSimSimulatesNonRealFunOK;

testSimWrongParamNumForSimFun;
testSimWrongParamNumForSimFunOK;

testSimParamForSimFunNotIdealFun;
testSimParamForSimFunNotIdealFunOK;

testSimWrongParamDirIOForSimFun;
testSimWrongParamDirIOForSimFunOK;

testSimInitStateNonI2SMsgMatch;
testSimInitStateNonI2SMsgMatchOK;

testSimMsgMatchOutMsg;
testSimMsgMatchOutMsgOK;

testSimMsgMatchI2SInMsg;
testSimMsgMatchI2SInMsgOK;

testSimMsgMatchRealFunDirIO;
testSimMsgMatchRealFunDirIOOK;

testSimMsgMatchSubFunDirIO;
testSimMsgMatchSubFunDirIOOK;

testSimMsgMatchParamFunDirIO;
testSimMsgMatchParamFunDirIOOK;

testSimMsgMatchAlreadyCovered;
testSimMsgMatchAlreadyCoveredOK;

testSimSendNotI2SorRealFun;
testSimSendNotI2SorRealFunOK;

testSimSendI2SOutMsg;
testSimSendI2SOutMsgOK;

testSimSendRFDirIO;
testSimSendRFDirIOOK;

testSimSendRFInAdvMsg;
testSimSendRFInAdvMsgOK;

testSimSendNotAdvIOofSubFun;
testSimSendNotAdvIOofSubFunOK;

testSimSendNotOutAdvMsgofSubFun;
testSimSendNotOutAdvMsgofSubFunOK;

testSimSendNotIOofParamFun;
testSimSendNotIOofParamFunOK;

testSimSendNotOutMsgOfParamFun;
testSimSendNotOutMsgOfParamFunOK;

testSimSendMsgPathIncomplete;
testSimSendMsgPathIncompleteOK;

testCaseStudy;
] 

