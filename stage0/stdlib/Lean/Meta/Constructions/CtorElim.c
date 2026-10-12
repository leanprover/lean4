// Lean compiler output
// Module: Lean.Meta.Constructions.CtorElim
// Imports: public import Lean.Meta.Basic import Lean.Meta.CompletionName import Lean.Meta.Constructions.CtorIdx import Lean.Meta.NatTable import Lean.Elab.App
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_privatePrefix_x3f(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabAsElim;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* lean_array_pop(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_mkNatLookupTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Constructions.CtorElim"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "_private.Lean.Meta.Constructions.CtorElim.0.Lean.maxLevels"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "assertion violation: es.size > 0\n  "};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PULift"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 77, 143, 37, 66, 207, 42, 107)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "withMkPULiftUp: expected PULift type, got "};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "up"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 77, 143, 37, 66, 207, 42, 107)}};
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 120, 128, 163, 171, 232, 167, 16)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "mkULiftDown: expected ULift type, got "};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "down"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 77, 143, 37, 66, 207, 42, 107)}};
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__2_value),LEAN_SCALAR_PTR_LITERAL(147, 247, 173, 71, 100, 103, 101, 210)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ctorElimType"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(lean_object*);
static const lean_string_object l_Lean_mkCtorElimName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ctorElim"};
static const lean_object* l_Lean_mkCtorElimName___closed__0 = (const lean_object*)&l_Lean_mkCtorElimName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorElimName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkConstructorElimName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_mkConstructorElimName___closed__0 = (const lean_object*)&l_Lean_mkConstructorElimName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 144, 38, 31, 46, 196, 243, 73)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Meta.Constructions.CtorElim.0.Lean.mkCtorElimType"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 52, 149, 243, 146, 99, 67, 163)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Constructions.CtorElim.0.Lean.mkIndCtorElim"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpected universe levels on `casesOn`"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Meta.Constructions.CtorElim.0.Lean.mkConstructorElim"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CtorElim"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 253, 69, 137, 213, 7, 141, 52)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(138, 217, 179, 185, 248, 184, 54, 141)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 224, 8, 193, 47, 190, 182, 11)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 6, 21, 1, 55, 47, 253, 187)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 144, 244, 152, 195, 165, 36, 15)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(158, 198, 213, 216, 190, 23, 241, 76)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 17, 191, 88, 165, 126, 19, 129)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 199, 211, 227, 241, 205, 232, 129)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 138, 84, 9, 24, 18, 85, 236)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)(((size_t)(299025572) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(230, 184, 217, 127, 62, 217, 243, 107)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 105, 93, 149, 36, 247, 240, 255)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 201, 74, 183, 227, 228, 127, 217)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(68, 15, 105, 173, 83, 172, 219, 199)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "gen_constructor_elims"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 157, 17, 212, 199, 20, 220, 215)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__28_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed, .m_arity = 9, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__28_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__28_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__29_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__29_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__29_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__30_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "generate the `.toCtorIdx` and `.ctor.elim` definitions for the given inductive"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__30_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__30_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__31_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__30_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__31_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__31_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__31_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__28_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__29_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 261, .m_capacity = 261, .m_length = 260, .m_data = "Generate the `.toCtorIdx` and `.ctor.elim` definitions for the given inductive.\n\nThis attribute is only meant to be used in `Init.Prelude` to build these constructions for\ntypes where we did not generate them immediately (due to `set_option genCtorIdx false`)."};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(lean_object* v_l_1_, lean_object* v_lvls_2_){
_start:
{
if (lean_obj_tag(v_l_1_) == 2)
{
lean_object* v_a_3_; lean_object* v_a_4_; lean_object* v___x_5_; 
v_a_3_ = lean_ctor_get(v_l_1_, 0);
lean_inc(v_a_3_);
v_a_4_ = lean_ctor_get(v_l_1_, 1);
lean_inc(v_a_4_);
lean_dec_ref_known(v_l_1_, 2);
v___x_5_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(v_a_3_, v_lvls_2_);
v_l_1_ = v_a_4_;
v_lvls_2_ = v___x_5_;
goto _start;
}
else
{
lean_object* v___x_7_; 
v___x_7_ = lean_array_push(v_lvls_2_, v_l_1_);
return v___x_7_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(lean_object* v_as_8_, size_t v_i_9_, size_t v_stop_10_, lean_object* v_b_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_usize_dec_eq(v_i_9_, v_stop_10_);
if (v___x_12_ == 0)
{
size_t v___x_13_; size_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = ((size_t)1ULL);
v___x_14_ = lean_usize_sub(v_i_9_, v___x_13_);
v___x_15_ = lean_array_uget_borrowed(v_as_8_, v___x_14_);
lean_inc(v___x_15_);
v___x_16_ = l_Lean_mkLevelMax(v___x_15_, v_b_11_);
v_i_9_ = v___x_14_;
v_b_11_ = v___x_16_;
goto _start;
}
else
{
return v_b_11_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_8_ = stack[0].m_obj;
size_t v_i_9_ = stack[1].m_num;
size_t v_stop_10_ = stack[2].m_num;
lean_object* v_b_11_ = stack[3].m_obj;
lean_object* v_res_18_;
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(v_as_8_, v_i_9_, v_stop_10_, v_b_11_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0___boxed(lean_object* v_as_19_, lean_object* v_i_20_, lean_object* v_stop_21_, lean_object* v_b_22_){
_start:
{
size_t v_i_boxed_23_; size_t v_stop_boxed_24_; lean_object* v_res_25_; 
v_i_boxed_23_ = lean_unbox_usize(v_i_20_);
lean_dec(v_i_20_);
v_stop_boxed_24_ = lean_unbox_usize(v_stop_21_);
lean_dec(v_stop_21_);
v_res_25_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(v_as_19_, v_i_boxed_23_, v_stop_boxed_24_, v_b_22_);
lean_dec_ref(v_as_19_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(lean_object* v_l_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v_lvls_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_last_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0));
v_lvls_32_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(v_l_28_, v___x_31_);
v___x_33_ = lean_array_get_size(v_lvls_32_);
v___x_34_ = lean_unsigned_to_nat(1u);
v___x_35_ = lean_nat_sub(v___x_33_, v___x_34_);
v_last_36_ = lean_array_get(v___x_29_, v_lvls_32_, v___x_35_);
lean_dec(v___x_35_);
v___x_37_ = lean_array_pop(v_lvls_32_);
v___x_38_ = lean_array_get_size(v___x_37_);
v___x_39_ = lean_nat_dec_lt(v___x_30_, v___x_38_);
if (v___x_39_ == 0)
{
lean_dec_ref(v___x_37_);
return v_last_36_;
}
else
{
size_t v___x_40_; size_t v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_usize_of_nat(v___x_38_);
v___x_41_ = ((size_t)0ULL);
v___x_42_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(v___x_37_, v___x_40_, v___x_41_, v_last_36_);
lean_dec_ref(v___x_37_);
return v___x_42_;
}
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(lean_object* v_msg_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___f_50_; lean_object* v___x_1562__overap_51_; lean_object* v___x_52_; 
v___f_50_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_1562__overap_51_ = lean_panic_fn_borrowed(v___f_50_, v_msg_44_);
lean_inc(v___y_48_);
lean_inc_ref(v___y_47_);
lean_inc(v___y_46_);
lean_inc_ref(v___y_45_);
v___x_52_ = lean_apply_5(v___x_1562__overap_51_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, lean_box(0));
return v___x_52_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_44_ = stack[0].m_obj;
lean_object* v___y_45_ = stack[1].m_obj;
lean_object* v___y_46_ = stack[2].m_obj;
lean_object* v___y_47_ = stack[3].m_obj;
lean_object* v___y_48_ = stack[4].m_obj;
lean_object* v_res_53_;
v_res_53_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(v_msg_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___boxed(lean_object* v_msg_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(v_msg_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_60_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(lean_object* v_a_61_, lean_object* v_b_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_array_68_; lean_object* v_start_69_; lean_object* v_stop_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_86_; 
v_array_68_ = lean_ctor_get(v_a_61_, 0);
v_start_69_ = lean_ctor_get(v_a_61_, 1);
v_stop_70_ = lean_ctor_get(v_a_61_, 2);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_86_ == 0)
{
v___x_72_ = v_a_61_;
v_isShared_73_ = v_isSharedCheck_86_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_stop_70_);
lean_inc(v_start_69_);
lean_inc(v_array_68_);
lean_dec(v_a_61_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_86_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
uint8_t v___x_74_; 
v___x_74_ = lean_nat_dec_lt(v_start_69_, v_stop_70_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_del_object(v___x_72_);
lean_dec(v_stop_70_);
lean_dec(v_start_69_);
lean_dec_ref(v_array_68_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_b_62_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_add(v_start_69_, v___x_76_);
lean_inc_ref(v_array_68_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___x_77_);
v___x_79_ = v___x_72_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_array_68_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v_stop_70_);
v___x_79_ = v_reuseFailAlloc_85_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_array_fget(v_array_68_, v_start_69_);
lean_dec(v_start_69_);
lean_dec_ref(v_array_68_);
v___x_81_ = l_Lean_Meta_getLevel(v___x_80_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_83_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
v___x_83_ = l_Lean_mkLevelMax_x27(v_b_62_, v_a_82_);
v_a_61_ = v___x_79_;
v_b_62_ = v___x_83_;
goto _start;
}
else
{
lean_dec_ref(v___x_79_);
lean_dec(v_b_62_);
return v___x_81_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_61_ = stack[0].m_obj;
lean_object* v_b_62_ = stack[1].m_obj;
lean_object* v___y_63_ = stack[2].m_obj;
lean_object* v___y_64_ = stack[3].m_obj;
lean_object* v___y_65_ = stack[4].m_obj;
lean_object* v___y_66_ = stack[5].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v_a_61_, v_b_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg___boxed(lean_object* v_a_88_, lean_object* v_b_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v_a_88_, v_b_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_95_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2));
v___x_100_ = lean_unsigned_to_nat(2u);
v___x_101_ = lean_unsigned_to_nat(32u);
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1));
v___x_103_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_104_ = l_mkPanicMessageWithDecl(v___x_103_, v___x_102_, v___x_101_, v___x_100_, v___x_99_);
return v___x_104_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(lean_object* v_es_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_array_get_size(v_es_105_);
v___x_113_ = lean_nat_dec_lt(v___x_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec_ref(v_es_105_);
v___x_114_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3);
v___x_115_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(v___x_114_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = l_Lean_instInhabitedExpr;
v___x_117_ = lean_array_get_borrowed(v___x_116_, v_es_105_, v___x_111_);
lean_inc(v___x_117_);
v___x_118_ = l_Lean_Meta_getLevel(v___x_117_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = l_Array_toSubarray___redArg(v_es_105_, v___x_120_, v___x_112_);
v___x_122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v___x_121_, v_a_119_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_132_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_132_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_132_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_132_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_127_ = l_Lean_Level_normalize(v_a_123_);
lean_dec(v_a_123_);
v___x_128_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(v___x_127_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_128_);
v___x_130_ = v___x_125_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
else
{
return v___x_122_;
}
}
else
{
lean_dec_ref(v_es_105_);
return v___x_118_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_105_ = stack[0].m_obj;
lean_object* v_a_106_ = stack[1].m_obj;
lean_object* v_a_107_ = stack[2].m_obj;
lean_object* v_a_108_ = stack[3].m_obj;
lean_object* v_a_109_ = stack[4].m_obj;
lean_object* v_res_133_;
v_res_133_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(v_es_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___boxed(lean_object* v_es_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(v_es_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
return v_res_140_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1(lean_object* v_inst_141_, lean_object* v_R_142_, lean_object* v_a_143_, lean_object* v_b_144_, lean_object* v_c_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v_a_143_, v_b_144_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
return v___x_151_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_143_ = stack[2].m_obj;
lean_object* v_b_144_ = stack[3].m_obj;
lean_object* v___y_146_ = stack[5].m_obj;
lean_object* v___y_147_ = stack[6].m_obj;
lean_object* v___y_148_ = stack[7].m_obj;
lean_object* v___y_149_ = stack[8].m_obj;
lean_object* v_res_152_;
v_res_152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1(lean_box(0), lean_box(0), v_a_143_, v_b_144_, lean_box(0), v___y_146_, v___y_147_, v___y_148_, v___y_149_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___boxed(lean_object* v_inst_153_, lean_object* v_R_154_, lean_object* v_a_155_, lean_object* v_b_156_, lean_object* v_c_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1(v_inst_153_, v_R_154_, v_a_155_, v_b_156_, v_c_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_163_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(lean_object* v_r_167_, lean_object* v_t_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
lean_inc_ref(v_t_168_);
v___x_174_ = l_Lean_Meta_getLevel(v_t_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_188_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_188_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_188_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_188_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_179_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v_a_175_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v_r_167_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = l_Lean_mkConst(v___x_179_, v___x_182_);
v___x_184_ = l_Lean_Expr_app___override(v___x_183_, v_t_168_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_184_);
v___x_186_ = v___x_177_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec_ref(v_t_168_);
lean_dec(v_r_167_);
v_a_189_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_174_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_174_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_167_ = stack[0].m_obj;
lean_object* v_t_168_ = stack[1].m_obj;
lean_object* v_a_169_ = stack[2].m_obj;
lean_object* v_a_170_ = stack[3].m_obj;
lean_object* v_a_171_ = stack[4].m_obj;
lean_object* v_a_172_ = stack[5].m_obj;
lean_object* v_res_197_;
v_res_197_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(v_r_167_, v_t_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___boxed(lean_object* v_r_198_, lean_object* v_t_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(v_r_198_, v_t_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_205_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(lean_object* v_msgData_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_env_213_; uint8_t v___x_214_; lean_object* v_env_215_; lean_object* v___x_216_; lean_object* v_toCold_217_; lean_object* v_mctx_218_; lean_object* v_lctx_219_; lean_object* v_options_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_212_ = lean_st_ref_get(v___y_210_);
v_env_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc_ref(v_env_213_);
lean_dec(v___x_212_);
v___x_214_ = 0;
v_env_215_ = l_Lean_Environment_setRecordingDeps(v_env_213_, v___x_214_);
v___x_216_ = lean_st_ref_get(v___y_208_);
v_toCold_217_ = lean_ctor_get(v___y_209_, 0);
v_mctx_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc_ref(v_mctx_218_);
lean_dec(v___x_216_);
v_lctx_219_ = lean_ctor_get(v___y_207_, 2);
v_options_220_ = lean_ctor_get(v_toCold_217_, 2);
lean_inc_ref(v_options_220_);
lean_inc_ref(v_lctx_219_);
v___x_221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_221_, 0, v_env_215_);
lean_ctor_set(v___x_221_, 1, v_mctx_218_);
lean_ctor_set(v___x_221_, 2, v_lctx_219_);
lean_ctor_set(v___x_221_, 3, v_options_220_);
v___x_222_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_msgData_206_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_206_ = stack[0].m_obj;
lean_object* v___y_207_ = stack[1].m_obj;
lean_object* v___y_208_ = stack[2].m_obj;
lean_object* v___y_209_ = stack[3].m_obj;
lean_object* v___y_210_ = stack[4].m_obj;
lean_object* v_res_224_;
v_res_224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msgData_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0___boxed(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msgData_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_231_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_ref_238_; lean_object* v___x_239_; lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_ref_238_ = lean_ctor_get(v___y_235_, 2);
v___x_239_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msg_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_248_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
lean_inc(v_ref_238_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_ref_238_);
lean_ctor_set(v___x_244_, 1, v_a_240_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 1);
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_232_ = stack[0].m_obj;
lean_object* v___y_233_ = stack[1].m_obj;
lean_object* v___y_234_ = stack[2].m_obj;
lean_object* v___y_235_ = stack[3].m_obj;
lean_object* v___y_236_ = stack[4].m_obj;
lean_object* v_res_249_;
v_res_249_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg___boxed(lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(lean_object* v_t_264_, lean_object* v_k_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
lean_inc(v_a_269_);
lean_inc_ref(v_a_268_);
lean_inc(v_a_267_);
lean_inc_ref(v_a_266_);
v___x_271_ = lean_whnf(v_t_264_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = l_Lean_Expr_isAppOfArity(v_a_272_, v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec_ref(v_k_265_);
v___x_276_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1);
v___x_277_ = l_Lean_MessageData_ofExpr(v_a_272_);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_278_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = l_Lean_Expr_appArg_x21(v_a_272_);
lean_inc(v_a_269_);
lean_inc_ref(v_a_268_);
lean_inc(v_a_267_);
lean_inc_ref(v_a_266_);
lean_inc_ref(v___x_280_);
v___x_281_ = lean_apply_6(v_k_265_, v___x_280_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, lean_box(0));
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_294_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_294_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3));
v___x_287_ = l_Lean_Expr_appFn_x21(v_a_272_);
lean_dec(v_a_272_);
v___x_288_ = l_Lean_Expr_constLevels_x21(v___x_287_);
lean_dec_ref(v___x_287_);
v___x_289_ = l_Lean_mkConst(v___x_286_, v___x_288_);
v___x_290_ = l_Lean_mkAppB(v___x_289_, v___x_280_, v_a_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_290_);
v___x_292_ = v___x_284_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_dec_ref(v___x_280_);
lean_dec(v_a_272_);
return v___x_281_;
}
}
}
else
{
lean_dec_ref(v_k_265_);
return v___x_271_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_264_ = stack[0].m_obj;
lean_object* v_k_265_ = stack[1].m_obj;
lean_object* v_a_266_ = stack[2].m_obj;
lean_object* v_a_267_ = stack[3].m_obj;
lean_object* v_a_268_ = stack[4].m_obj;
lean_object* v_a_269_ = stack[5].m_obj;
lean_object* v_res_295_;
v_res_295_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v_t_264_, v_k_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___boxed(lean_object* v_t_296_, lean_object* v_k_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v_t_296_, v_k_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_303_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(lean_object* v_00_u03b1_304_, lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_305_ = stack[1].m_obj;
lean_object* v___y_306_ = stack[2].m_obj;
lean_object* v___y_307_ = stack[3].m_obj;
lean_object* v___y_308_ = stack[4].m_obj;
lean_object* v___y_309_ = stack[5].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(lean_box(0), v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___boxed(lean_object* v_00_u03b1_313_, lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(v_00_u03b1_313_, v_msg_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(lean_object* v_e_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
lean_inc(v_a_332_);
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
lean_inc_ref(v_a_329_);
lean_inc_ref(v_e_328_);
v___x_334_ = lean_infer_type(v_e_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
lean_inc(v_a_332_);
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
lean_inc_ref(v_a_329_);
v___x_336_ = lean_whnf(v_a_335_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_357_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_357_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_357_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_357_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = l_Lean_Expr_isAppOfArity(v_a_337_, v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_del_object(v___x_339_);
lean_dec_ref(v_e_328_);
v___x_344_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1);
v___x_345_ = l_Lean_MessageData_ofExpr(v_a_337_);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_346_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_348_ = l_Lean_Expr_appArg_x21(v_a_337_);
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3));
v___x_350_ = l_Lean_Expr_appFn_x21(v_a_337_);
lean_dec(v_a_337_);
v___x_351_ = l_Lean_Expr_constLevels_x21(v___x_350_);
lean_dec_ref(v___x_350_);
v___x_352_ = l_Lean_mkConst(v___x_349_, v___x_351_);
v___x_353_ = l_Lean_mkAppB(v___x_352_, v___x_348_, v_e_328_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_353_);
v___x_355_ = v___x_339_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_dec_ref(v_e_328_);
return v___x_336_;
}
}
else
{
lean_dec_ref(v_e_328_);
return v___x_334_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_328_ = stack[0].m_obj;
lean_object* v_a_329_ = stack[1].m_obj;
lean_object* v_a_330_ = stack[2].m_obj;
lean_object* v_a_331_ = stack[3].m_obj;
lean_object* v_a_332_ = stack[4].m_obj;
lean_object* v_res_358_;
v_res_358_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_e_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___boxed(lean_object* v_e_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_e_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
return v_res_365_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(lean_object* v_a_366_, size_t v_sz_367_, size_t v_i_368_, lean_object* v_bs_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = lean_usize_dec_lt(v_i_368_, v_sz_367_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec(v_a_366_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v_bs_369_);
return v___x_376_;
}
else
{
lean_object* v_v_377_; lean_object* v___x_378_; lean_object* v_bs_x27_379_; lean_object* v___x_380_; 
v_v_377_ = lean_array_uget(v_bs_369_, v_i_368_);
v___x_378_ = lean_unsigned_to_nat(0u);
v_bs_x27_379_ = lean_array_uset(v_bs_369_, v_i_368_, v___x_378_);
lean_inc(v_a_366_);
v___x_380_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(v_a_366_, v_v_377_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_368_, v___x_382_);
v___x_384_ = lean_array_uset(v_bs_x27_379_, v_i_368_, v_a_381_);
v_i_368_ = v___x_383_;
v_bs_369_ = v___x_384_;
goto _start;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v_bs_x27_379_);
lean_dec(v_a_366_);
v_a_386_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_380_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_380_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_366_ = stack[0].m_obj;
size_t v_sz_367_ = stack[1].m_num;
size_t v_i_368_ = stack[2].m_num;
lean_object* v_bs_369_ = stack[3].m_obj;
lean_object* v___y_370_ = stack[4].m_obj;
lean_object* v___y_371_ = stack[5].m_obj;
lean_object* v___y_372_ = stack[6].m_obj;
lean_object* v___y_373_ = stack[7].m_obj;
lean_object* v_res_394_;
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_366_, v_sz_367_, v_i_368_, v_bs_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0___boxed(lean_object* v_a_395_, lean_object* v_sz_396_, lean_object* v_i_397_, lean_object* v_bs_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
size_t v_sz_boxed_404_; size_t v_i_boxed_405_; lean_object* v_res_406_; 
v_sz_boxed_404_ = lean_unbox_usize(v_sz_396_);
lean_dec(v_sz_396_);
v_i_boxed_405_ = lean_unbox_usize(v_i_397_);
lean_dec(v_i_397_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_395_, v_sz_boxed_404_, v_i_boxed_405_, v_bs_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = l_Lean_Level_ofNat(v___x_407_);
return v___x_408_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(lean_object* v_n_409_, lean_object* v_es_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
lean_inc_ref(v_es_410_);
v___x_416_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(v_es_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; size_t v_sz_422_; size_t v___x_423_; lean_object* v___x_424_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc_n(v_a_417_, 2);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0);
v___x_419_ = l_Lean_mkLevelMax_x27(v_a_417_, v___x_418_);
v___x_420_ = l_Lean_Level_normalize(v___x_419_);
lean_dec(v___x_419_);
v___x_421_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(v___x_420_);
v_sz_422_ = lean_array_size(v_es_410_);
v___x_423_ = ((size_t)0ULL);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_417_, v_sz_422_, v___x_423_, v_es_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = l_Lean_Expr_sort___override(v___x_421_);
v___x_427_ = l_Lean_mkNatLookupTable(v_n_409_, v___x_426_, v_a_425_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_425_);
return v___x_427_;
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v___x_421_);
lean_dec_ref(v_n_409_);
v_a_428_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_424_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v_es_410_);
lean_dec_ref(v_n_409_);
v_a_436_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_416_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_416_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_409_ = stack[0].m_obj;
lean_object* v_es_410_ = stack[1].m_obj;
lean_object* v_a_411_ = stack[2].m_obj;
lean_object* v_a_412_ = stack[3].m_obj;
lean_object* v_a_413_ = stack[4].m_obj;
lean_object* v_a_414_ = stack[5].m_obj;
lean_object* v_res_444_;
v_res_444_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_n_409_, v_es_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___boxed(lean_object* v_n_445_, lean_object* v_es_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_n_445_, v_es_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(lean_object* v_indName_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0));
v___x_456_ = l_Lean_Name_str___override(v_indName_454_, v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElimName(lean_object* v_indName_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_mkCtorElimName___closed__0));
v___x_460_ = l_Lean_Name_str___override(v_indName_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(lean_object* v_n1_461_, lean_object* v_n2_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_privatePrefix_x3f(v_n2_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_privateToUserName(v_n1_461_);
return v___x_464_;
}
else
{
lean_object* v_val_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_val_465_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_463_, 1);
v___x_466_ = l_Lean_privateToUserName(v_n1_461_);
v___x_467_ = l_Lean_Name_appendCore(v_val_465_, v___x_466_);
lean_dec(v_val_465_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs___boxed(lean_object* v_n1_468_, lean_object* v_n2_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(v_n1_468_, v_n2_469_);
lean_dec(v_n2_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName(lean_object* v_indName_472_, lean_object* v_conName_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((lean_object*)(l_Lean_mkConstructorElimName___closed__0));
v___x_475_ = l_Lean_Name_str___override(v_conName_473_, v___x_474_);
v___x_476_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(v___x_475_, v_indName_472_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName___boxed(lean_object* v_indName_477_, lean_object* v_conName_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_mkConstructorElimName(v_indName_477_, v_conName_478_);
lean_dec(v_indName_477_);
return v_res_479_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(lean_object* v_k_480_, lean_object* v_b_481_, lean_object* v_c_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; 
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
v___x_488_ = lean_apply_7(v_k_480_, v_b_481_, v_c_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, lean_box(0));
return v___x_488_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_480_ = stack[0].m_obj;
lean_object* v_b_481_ = stack[1].m_obj;
lean_object* v_c_482_ = stack[2].m_obj;
lean_object* v___y_483_ = stack[3].m_obj;
lean_object* v___y_484_ = stack[4].m_obj;
lean_object* v___y_485_ = stack[5].m_obj;
lean_object* v___y_486_ = stack[6].m_obj;
lean_object* v_res_489_;
v_res_489_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(v_k_480_, v_b_481_, v_c_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed(lean_object* v_k_490_, lean_object* v_b_491_, lean_object* v_c_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(v_k_490_, v_b_491_, v_c_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
return v_res_498_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(lean_object* v_type_499_, lean_object* v_k_500_, uint8_t v_cleanupAnnotations_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___f_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___f_507_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_507_, 0, v_k_500_);
v___x_508_ = 0;
v___x_509_ = lean_box(0);
v___x_510_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_508_, v___x_509_, v_type_499_, v___f_507_, v_cleanupAnnotations_501_, v___x_508_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_510_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_510_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_499_ = stack[0].m_obj;
lean_object* v_k_500_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_501_ = stack[2].m_num;
lean_object* v___y_502_ = stack[3].m_obj;
lean_object* v___y_503_ = stack[4].m_obj;
lean_object* v___y_504_ = stack[5].m_obj;
lean_object* v___y_505_ = stack[6].m_obj;
lean_object* v_res_527_;
v_res_527_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_499_, v_k_500_, v_cleanupAnnotations_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___boxed(lean_object* v_type_528_, lean_object* v_k_529_, lean_object* v_cleanupAnnotations_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_536_; lean_object* v_res_537_; 
v_cleanupAnnotations_boxed_536_ = lean_unbox(v_cleanupAnnotations_530_);
v_res_537_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_528_, v_k_529_, v_cleanupAnnotations_boxed_536_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_537_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(lean_object* v_00_u03b1_538_, lean_object* v_type_539_, lean_object* v_k_540_, uint8_t v_cleanupAnnotations_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_539_, v_k_540_, v_cleanupAnnotations_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
return v___x_547_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_539_ = stack[1].m_obj;
lean_object* v_k_540_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_541_ = stack[3].m_num;
lean_object* v___y_542_ = stack[4].m_obj;
lean_object* v___y_543_ = stack[5].m_obj;
lean_object* v___y_544_ = stack[6].m_obj;
lean_object* v___y_545_ = stack[7].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(lean_box(0), v_type_539_, v_k_540_, v_cleanupAnnotations_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___boxed(lean_object* v_00_u03b1_549_, lean_object* v_type_550_, lean_object* v_k_551_, lean_object* v_cleanupAnnotations_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_558_; lean_object* v_res_559_; 
v_cleanupAnnotations_boxed_558_ = lean_unbox(v_cleanupAnnotations_552_);
v_res_559_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(v_00_u03b1_549_, v_type_550_, v_k_551_, v_cleanupAnnotations_boxed_558_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_559_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(lean_object* v_name_560_, lean_object* v_levelParams_561_, lean_object* v_type_562_, lean_object* v_value_563_, lean_object* v_hints_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; uint8_t v___y_569_; uint8_t v___y_576_; lean_object* v_env_579_; uint8_t v___x_580_; 
v___x_567_ = lean_st_ref_get(v___y_565_);
v_env_579_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref_n(v_env_579_, 2);
lean_dec(v___x_567_);
v___x_580_ = l_Lean_Environment_hasUnsafe(v_env_579_, v_type_562_);
if (v___x_580_ == 0)
{
uint8_t v___x_581_; 
v___x_581_ = l_Lean_Environment_hasUnsafe(v_env_579_, v_value_563_);
v___y_576_ = v___x_581_;
goto v___jp_575_;
}
else
{
lean_dec_ref(v_env_579_);
v___y_576_ = v___x_580_;
goto v___jp_575_;
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_inc(v_name_560_);
v___x_570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_570_, 0, v_name_560_);
lean_ctor_set(v___x_570_, 1, v_levelParams_561_);
lean_ctor_set(v___x_570_, 2, v_type_562_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_name_560_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_573_, 0, v___x_570_);
lean_ctor_set(v___x_573_, 1, v_value_563_);
lean_ctor_set(v___x_573_, 2, v_hints_564_);
lean_ctor_set(v___x_573_, 3, v___x_572_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*4, v___y_569_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
uint8_t v___x_577_; 
v___x_577_ = 1;
v___y_569_ = v___x_577_;
goto v___jp_568_;
}
else
{
uint8_t v___x_578_; 
v___x_578_ = 0;
v___y_569_ = v___x_578_;
goto v___jp_568_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_560_ = stack[0].m_obj;
lean_object* v_levelParams_561_ = stack[1].m_obj;
lean_object* v_type_562_ = stack[2].m_obj;
lean_object* v_value_563_ = stack[3].m_obj;
lean_object* v_hints_564_ = stack[4].m_obj;
lean_object* v___y_565_ = stack[5].m_obj;
lean_object* v_res_582_;
v_res_582_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_560_, v_levelParams_561_, v_type_562_, v_value_563_, v_hints_564_, v___y_565_);
stack->m_obj
 = v_res_582_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg___boxed(lean_object* v_name_583_, lean_object* v_levelParams_584_, lean_object* v_type_585_, lean_object* v_value_586_, lean_object* v_hints_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_583_, v_levelParams_584_, v_type_585_, v_value_586_, v_hints_587_, v___y_588_);
lean_dec(v___y_588_);
return v_res_590_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(lean_object* v_name_591_, lean_object* v_levelParams_592_, lean_object* v_type_593_, lean_object* v_value_594_, lean_object* v_hints_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_591_, v_levelParams_592_, v_type_593_, v_value_594_, v_hints_595_, v___y_599_);
return v___x_601_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_591_ = stack[0].m_obj;
lean_object* v_levelParams_592_ = stack[1].m_obj;
lean_object* v_type_593_ = stack[2].m_obj;
lean_object* v_value_594_ = stack[3].m_obj;
lean_object* v_hints_595_ = stack[4].m_obj;
lean_object* v___y_596_ = stack[5].m_obj;
lean_object* v___y_597_ = stack[6].m_obj;
lean_object* v___y_598_ = stack[7].m_obj;
lean_object* v___y_599_ = stack[8].m_obj;
lean_object* v_res_602_;
v_res_602_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(v_name_591_, v_levelParams_592_, v_type_593_, v_value_594_, v_hints_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
stack->m_obj
 = v_res_602_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___boxed(lean_object* v_name_603_, lean_object* v_levelParams_604_, lean_object* v_type_605_, lean_object* v_value_606_, lean_object* v_hints_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(v_name_603_, v_levelParams_604_, v_type_605_, v_value_606_, v_hints_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_613_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___f_620_; lean_object* v___x_4196__overap_621_; lean_object* v___x_622_; 
v___f_620_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_4196__overap_621_ = lean_panic_fn_borrowed(v___f_620_, v_msg_614_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
v___x_622_ = lean_apply_5(v___x_4196__overap_621_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, lean_box(0));
return v___x_622_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_614_ = stack[0].m_obj;
lean_object* v___y_615_ = stack[1].m_obj;
lean_object* v___y_616_ = stack[2].m_obj;
lean_object* v___y_617_ = stack[3].m_obj;
lean_object* v___y_618_ = stack[4].m_obj;
lean_object* v_res_623_;
v_res_623_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(lean_object* v_msg_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v_msg_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
return v_res_630_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(size_t v_sz_631_, size_t v_i_632_, lean_object* v_bs_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_lt(v_i_632_, v_sz_631_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_bs_633_);
return v___x_640_;
}
else
{
lean_object* v_v_641_; lean_object* v___x_642_; lean_object* v_bs_x27_643_; lean_object* v___x_644_; 
v_v_641_ = lean_array_uget(v_bs_633_, v_i_632_);
v___x_642_ = lean_unsigned_to_nat(0u);
v_bs_x27_643_ = lean_array_uset(v_bs_633_, v_i_632_, v___x_642_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
v___x_644_ = lean_infer_type(v_v_641_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_632_, v___x_646_);
v___x_648_ = lean_array_uset(v_bs_x27_643_, v_i_632_, v_a_645_);
v_i_632_ = v___x_647_;
v_bs_633_ = v___x_648_;
goto _start;
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_bs_x27_643_);
v_a_650_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_644_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_644_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_631_ = stack[0].m_num;
size_t v_i_632_ = stack[1].m_num;
lean_object* v_bs_633_ = stack[2].m_obj;
lean_object* v___y_634_ = stack[3].m_obj;
lean_object* v___y_635_ = stack[4].m_obj;
lean_object* v___y_636_ = stack[5].m_obj;
lean_object* v___y_637_ = stack[6].m_obj;
lean_object* v_res_658_;
v_res_658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_sz_631_, v_i_632_, v_bs_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
stack->m_obj
 = v_res_658_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1___boxed(lean_object* v_sz_659_, lean_object* v_i_660_, lean_object* v_bs_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
size_t v_sz_boxed_667_; size_t v_i_boxed_668_; lean_object* v_res_669_; 
v_sz_boxed_667_ = lean_unbox_usize(v_sz_659_);
lean_dec(v_sz_659_);
v_i_boxed_668_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_sz_boxed_667_, v_i_boxed_668_, v_bs_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_669_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v___x_672_, uint8_t v___x_673_, lean_object* v_ctorIdx_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
size_t v_sz_680_; size_t v___x_681_; lean_object* v___x_682_; 
v_sz_680_ = lean_array_size(v___x_670_);
v___x_681_ = ((size_t)0ULL);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_sz_680_, v___x_681_, v___x_670_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
lean_inc_ref(v_ctorIdx_674_);
v___x_684_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_ctorIdx_674_, v_a_683_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; uint8_t v___x_692_; lean_object* v___x_693_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = lean_unsigned_to_nat(2u);
v___x_687_ = lean_mk_empty_array_with_capacity(v___x_686_);
v___x_688_ = lean_array_push(v___x_687_, v___x_671_);
v___x_689_ = lean_array_push(v___x_688_, v_ctorIdx_674_);
v___x_690_ = l_Array_append___redArg(v___x_672_, v___x_689_);
lean_dec_ref(v___x_689_);
v___x_691_ = 1;
v___x_692_ = 1;
v___x_693_ = l_Lean_Meta_mkLambdaFVars(v___x_690_, v_a_685_, v___x_673_, v___x_691_, v___x_673_, v___x_691_, v___x_692_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec_ref(v___x_690_);
return v___x_693_;
}
else
{
lean_dec_ref(v_ctorIdx_674_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
return v___x_684_;
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v_ctorIdx_674_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
v_a_694_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_682_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_682_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_670_ = stack[0].m_obj;
lean_object* v___x_671_ = stack[1].m_obj;
lean_object* v___x_672_ = stack[2].m_obj;
uint8_t v___x_673_ = stack[3].m_num;
lean_object* v_ctorIdx_674_ = stack[4].m_obj;
lean_object* v___y_675_ = stack[5].m_obj;
lean_object* v___y_676_ = stack[6].m_obj;
lean_object* v___y_677_ = stack[7].m_obj;
lean_object* v___y_678_ = stack[8].m_obj;
lean_object* v_res_702_;
v_res_702_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(v___x_670_, v___x_671_, v___x_672_, v___x_673_, v_ctorIdx_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
stack->m_obj
 = v_res_702_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed(lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_ctorIdx_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_6937__boxed_713_; lean_object* v_res_714_; 
v___x_6937__boxed_713_ = lean_unbox(v___x_706_);
v_res_714_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(v___x_703_, v___x_704_, v___x_705_, v___x_6937__boxed_713_, v_ctorIdx_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_714_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0(lean_object* v_k_715_, lean_object* v_b_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
v___x_722_ = lean_apply_6(v_k_715_, v_b_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, lean_box(0));
return v___x_722_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_715_ = stack[0].m_obj;
lean_object* v_b_716_ = stack[1].m_obj;
lean_object* v___y_717_ = stack[2].m_obj;
lean_object* v___y_718_ = stack[3].m_obj;
lean_object* v___y_719_ = stack[4].m_obj;
lean_object* v___y_720_ = stack[5].m_obj;
lean_object* v_res_723_;
v_res_723_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0(v_k_715_, v_b_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0(v_k_724_, v_b_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_731_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(lean_object* v_name_732_, uint8_t v_bi_733_, lean_object* v_type_734_, lean_object* v_k_735_, uint8_t v_kind_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___f_742_; lean_object* v___x_743_; 
v___f_742_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_742_, 0, v_k_735_);
v___x_743_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_732_, v_bi_733_, v_type_734_, v___f_742_, v_kind_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
v_a_752_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_743_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_743_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_732_ = stack[0].m_obj;
uint8_t v_bi_733_ = stack[1].m_num;
lean_object* v_type_734_ = stack[2].m_obj;
lean_object* v_k_735_ = stack[3].m_obj;
uint8_t v_kind_736_ = stack[4].m_num;
lean_object* v___y_737_ = stack[5].m_obj;
lean_object* v___y_738_ = stack[6].m_obj;
lean_object* v___y_739_ = stack[7].m_obj;
lean_object* v___y_740_ = stack[8].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_732_, v_bi_733_, v_type_734_, v_k_735_, v_kind_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___boxed(lean_object* v_name_761_, lean_object* v_bi_762_, lean_object* v_type_763_, lean_object* v_k_764_, lean_object* v_kind_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v_bi_boxed_771_; uint8_t v_kind_boxed_772_; lean_object* v_res_773_; 
v_bi_boxed_771_ = lean_unbox(v_bi_762_);
v_kind_boxed_772_ = lean_unbox(v_kind_765_);
v_res_773_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_761_, v_bi_boxed_771_, v_type_763_, v_k_764_, v_kind_boxed_772_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_773_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(lean_object* v_name_774_, lean_object* v_type_775_, lean_object* v_k_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
uint8_t v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; 
v___x_782_ = 0;
v___x_783_ = 0;
v___x_784_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_774_, v___x_782_, v_type_775_, v_k_776_, v___x_783_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
return v___x_784_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_774_ = stack[0].m_obj;
lean_object* v_type_775_ = stack[1].m_obj;
lean_object* v_k_776_ = stack[2].m_obj;
lean_object* v___y_777_ = stack[3].m_obj;
lean_object* v___y_778_ = stack[4].m_obj;
lean_object* v___y_779_ = stack[5].m_obj;
lean_object* v___y_780_ = stack[6].m_obj;
lean_object* v_res_785_;
v_res_785_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v_name_774_, v_type_775_, v_k_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
stack->m_obj
 = v_res_785_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg___boxed(lean_object* v_name_786_, lean_object* v_type_787_, lean_object* v_k_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v_name_786_, v_type_787_, v_k_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_box(0);
v___x_802_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_803_ = l_Lean_mkConst(v___x_802_, v___x_801_);
return v___x_803_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(lean_object* v_val_804_, lean_object* v___x_805_, lean_object* v___x_806_, uint8_t v___x_807_, lean_object* v_xs_808_, lean_object* v_x_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_numParams_815_; lean_object* v_numIndices_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_numParams_815_ = lean_ctor_get(v_val_804_, 1);
lean_inc_n(v_numParams_815_, 2);
v_numIndices_816_ = lean_ctor_get(v_val_804_, 2);
lean_inc(v_numIndices_816_);
lean_dec_ref(v_val_804_);
lean_inc_ref(v_xs_808_);
v___x_817_ = l_Array_toSubarray___redArg(v_xs_808_, v___x_805_, v_numParams_815_);
v___x_818_ = l_Subarray_copy___redArg(v___x_817_);
v___x_819_ = lean_array_get(v___x_806_, v_xs_808_, v_numParams_815_);
v___x_820_ = lean_unsigned_to_nat(1u);
v___x_821_ = lean_nat_add(v_numParams_815_, v___x_820_);
lean_dec(v_numParams_815_);
v___x_822_ = lean_nat_add(v___x_821_, v_numIndices_816_);
lean_dec(v_numIndices_816_);
lean_dec(v___x_821_);
v___x_823_ = lean_nat_add(v___x_822_, v___x_820_);
lean_dec(v___x_822_);
v___x_824_ = lean_array_get_size(v_xs_808_);
v___x_825_ = l_Array_toSubarray___redArg(v_xs_808_, v___x_823_, v___x_824_);
v___x_826_ = l_Subarray_copy___redArg(v___x_825_);
v___x_827_ = lean_box(v___x_807_);
v___f_828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_828_, 0, v___x_826_);
lean_closure_set(v___f_828_, 1, v___x_819_);
lean_closure_set(v___f_828_, 2, v___x_818_);
lean_closure_set(v___f_828_, 3, v___x_827_);
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_830_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_831_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_829_, v___x_830_, v___f_828_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_831_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_804_ = stack[0].m_obj;
lean_object* v___x_805_ = stack[1].m_obj;
lean_object* v___x_806_ = stack[2].m_obj;
uint8_t v___x_807_ = stack[3].m_num;
lean_object* v_xs_808_ = stack[4].m_obj;
lean_object* v_x_809_ = stack[5].m_obj;
lean_object* v___y_810_ = stack[6].m_obj;
lean_object* v___y_811_ = stack[7].m_obj;
lean_object* v___y_812_ = stack[8].m_obj;
lean_object* v___y_813_ = stack[9].m_obj;
lean_object* v_res_832_;
v_res_832_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(v_val_804_, v___x_805_, v___x_806_, v___x_807_, v_xs_808_, v_x_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed(lean_object* v_val_833_, lean_object* v___x_834_, lean_object* v___x_835_, lean_object* v___x_836_, lean_object* v_xs_837_, lean_object* v_x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
uint8_t v___x_7205__boxed_844_; lean_object* v_res_845_; 
v___x_7205__boxed_844_ = lean_unbox(v___x_836_);
v_res_845_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(v_val_833_, v___x_834_, v___x_835_, v___x_7205__boxed_844_, v_xs_837_, v_x_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v_x_838_);
lean_dec_ref(v___x_835_);
return v_res_845_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_846_, lean_object* v_msg_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_toCold_853_; lean_object* v_currRecDepth_854_; lean_object* v_ref_855_; uint16_t v_optionFlags_856_; uint8_t v_suppressElabErrors_857_; uint8_t v_isRecordingDeps_858_; lean_object* v_ref_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_toCold_853_ = lean_ctor_get(v___y_850_, 0);
v_currRecDepth_854_ = lean_ctor_get(v___y_850_, 1);
v_ref_855_ = lean_ctor_get(v___y_850_, 2);
v_optionFlags_856_ = lean_ctor_get_uint16(v___y_850_, sizeof(void*)*3);
v_suppressElabErrors_857_ = lean_ctor_get_uint8(v___y_850_, sizeof(void*)*3 + 2);
v_isRecordingDeps_858_ = lean_ctor_get_uint8(v___y_850_, sizeof(void*)*3 + 3);
v_ref_859_ = l_Lean_replaceRef(v_ref_846_, v_ref_855_);
lean_inc(v_currRecDepth_854_);
lean_inc_ref(v_toCold_853_);
v___x_860_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_860_, 0, v_toCold_853_);
lean_ctor_set(v___x_860_, 1, v_currRecDepth_854_);
lean_ctor_set(v___x_860_, 2, v_ref_859_);
lean_ctor_set_uint16(v___x_860_, sizeof(void*)*3, v_optionFlags_856_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*3 + 2, v_suppressElabErrors_857_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*3 + 3, v_isRecordingDeps_858_);
v___x_861_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_847_, v___y_848_, v___y_849_, v___x_860_, v___y_851_);
lean_dec_ref_known(v___x_860_, 3);
return v___x_861_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_846_ = stack[0].m_obj;
lean_object* v_msg_847_ = stack[1].m_obj;
lean_object* v___y_848_ = stack[2].m_obj;
lean_object* v___y_849_ = stack[3].m_obj;
lean_object* v___y_850_ = stack[4].m_obj;
lean_object* v___y_851_ = stack[5].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_846_, v_msg_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_863_, lean_object* v_msg_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_863_, v_msg_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v_ref_863_);
return v_res_870_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_871_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
lean_ctor_set(v___x_877_, 2, v___x_876_);
lean_ctor_set(v___x_877_, 3, v___x_876_);
lean_ctor_set(v___x_877_, 4, v___x_875_);
lean_ctor_set(v___x_877_, 5, v___x_875_);
lean_ctor_set(v___x_877_, 6, v___x_875_);
lean_ctor_set(v___x_877_, 7, v___x_875_);
lean_ctor_set(v___x_877_, 8, v___x_875_);
lean_ctor_set(v___x_877_, 9, v___x_875_);
lean_ctor_set(v___x_877_, 10, v___x_875_);
lean_ctor_set(v___x_877_, 11, v___x_874_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = lean_unsigned_to_nat(32u);
v___x_879_ = lean_mk_empty_array_with_capacity(v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_881_ = ((size_t)5ULL);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_unsigned_to_nat(32u);
v___x_884_ = lean_mk_empty_array_with_capacity(v___x_883_);
v___x_885_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_886_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
lean_ctor_set(v___x_886_, 2, v___x_882_);
lean_ctor_set(v___x_886_, 3, v___x_882_);
lean_ctor_set_usize(v___x_886_, 4, v___x_881_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = lean_box(1);
v___x_888_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_888_);
lean_ctor_set(v___x_890_, 2, v___x_887_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_896_ = l_Lean_stringToMessageData(v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_899_ = l_Lean_stringToMessageData(v___x_898_);
return v___x_899_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__25(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24));
v___x_920_ = l_Lean_stringToMessageData(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__27(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__26));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_924_, lean_object* v_declHint_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_env_930_; uint8_t v___x_931_; 
v___x_928_ = lean_box(0);
v___x_929_ = lean_st_ref_get(v___y_926_);
v_env_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc_ref(v_env_930_);
lean_dec(v___x_929_);
v___x_931_ = l_Lean_Name_isAnonymous(v_declHint_925_);
if (v___x_931_ == 0)
{
uint8_t v_isExporting_932_; 
v_isExporting_932_ = lean_ctor_get_uint8(v_env_930_, sizeof(void*)*13);
if (v_isExporting_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec_ref(v_env_930_);
lean_dec(v_declHint_925_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v_msg_924_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; uint8_t v___x_935_; 
lean_inc_ref(v_env_930_);
v___x_934_ = l_Lean_Environment_setExporting(v_env_930_, v___x_931_);
lean_inc(v_declHint_925_);
lean_inc_ref(v___x_934_);
v___x_935_ = l_Lean_Environment_contains(v___x_934_, v_declHint_925_, v_isExporting_932_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_dec_ref(v___x_934_);
lean_dec_ref(v_env_930_);
lean_dec(v_declHint_925_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_msg_924_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_c_942_; lean_object* v___x_943_; 
v___x_937_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_938_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_939_ = l_Lean_Options_empty;
v___x_940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_940_, 0, v___x_934_);
lean_ctor_set(v___x_940_, 1, v___x_937_);
lean_ctor_set(v___x_940_, 2, v___x_938_);
lean_ctor_set(v___x_940_, 3, v___x_939_);
lean_inc(v_declHint_925_);
v___x_941_ = l_Lean_MessageData_ofConstName(v_declHint_925_, v___x_931_);
v_c_942_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_942_, 0, v___x_940_);
lean_ctor_set(v_c_942_, 1, v___x_941_);
v___x_943_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_930_, v_declHint_925_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec_ref(v_env_930_);
lean_dec(v_declHint_925_);
v___x_944_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v_c_942_);
v___x_946_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = l_Lean_MessageData_note(v___x_947_);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v_msg_924_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1007_; 
v_val_951_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_953_ = v___x_943_;
v_isShared_954_ = v_isSharedCheck_1007_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v___x_943_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1007_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v_modules_956_; lean_object* v_moduleNames_957_; lean_object* v_mod_958_; uint8_t v___y_960_; uint8_t v___x_990_; 
v___x_955_ = l_Lean_Environment_header(v_env_930_);
lean_dec_ref(v_env_930_);
v_modules_956_ = lean_ctor_get(v___x_955_, 3);
lean_inc_ref(v_modules_956_);
v_moduleNames_957_ = lean_ctor_get(v___x_955_, 4);
lean_inc_ref(v_moduleNames_957_);
lean_dec_ref(v___x_955_);
v_mod_958_ = lean_array_get(v___x_928_, v_moduleNames_957_, v_val_951_);
lean_dec_ref(v_moduleNames_957_);
v___x_990_ = l_Lean_isPrivateName(v_declHint_925_);
lean_dec(v_declHint_925_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_array_get_size(v_modules_956_);
v___x_992_ = lean_nat_dec_lt(v_val_951_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v_modules_956_);
lean_dec(v_val_951_);
v___y_960_ = v___x_990_;
goto v___jp_959_;
}
else
{
lean_object* v___x_993_; lean_object* v_toImport_994_; uint8_t v_isExported_995_; 
v___x_993_ = lean_array_fget(v_modules_956_, v_val_951_);
lean_dec(v_val_951_);
lean_dec_ref(v_modules_956_);
v_toImport_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc_ref(v_toImport_994_);
lean_dec(v___x_993_);
v_isExported_995_ = lean_ctor_get_uint8(v_toImport_994_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_994_);
v___y_960_ = v_isExported_995_;
goto v___jp_959_;
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v_modules_956_);
lean_del_object(v___x_953_);
lean_dec(v_val_951_);
v___x_996_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_c_942_);
v___x_998_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__25);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l_Lean_MessageData_ofName(v_mod_958_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__27);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_MessageData_note(v___x_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_msg_924_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
v___jp_959_:
{
if (v___y_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v_c_942_);
v___x_963_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_MessageData_ofName(v_mod_958_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_MessageData_note(v___x_968_);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v_msg_924_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 0);
lean_ctor_set(v___x_953_, 0, v___x_970_);
v___x_972_ = v___x_953_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_974_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v_c_942_);
v___x_976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l_Lean_MessageData_ofName(v_mod_958_);
lean_inc_ref(v___x_978_);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_978_);
v___x_983_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = l_Lean_MessageData_note(v___x_984_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v_msg_924_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 0);
lean_ctor_set(v___x_953_, 0, v___x_986_);
v___x_988_ = v___x_953_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1008_; 
lean_dec_ref(v_env_930_);
lean_dec(v_declHint_925_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_msg_924_);
return v___x_1008_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_924_ = stack[0].m_obj;
lean_object* v_declHint_925_ = stack[1].m_obj;
lean_object* v___y_926_ = stack[2].m_obj;
lean_object* v_res_1009_;
v_res_1009_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_924_, v_declHint_925_, v___y_926_);
stack->m_obj
 = v_res_1009_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1010_, lean_object* v_declHint_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_1010_, v_declHint_1011_, v___y_1012_);
lean_dec(v___y_1012_);
return v_res_1014_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_1015_, lean_object* v_declHint_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1032_; 
v___x_1022_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_1015_, v_declHint_1016_, v___y_1020_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = l_Lean_unknownIdentifierMessageTag;
v___x_1028_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1028_);
v___x_1030_ = v___x_1025_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1015_ = stack[0].m_obj;
lean_object* v_declHint_1016_ = stack[1].m_obj;
lean_object* v___y_1017_ = stack[2].m_obj;
lean_object* v___y_1018_ = stack[3].m_obj;
lean_object* v___y_1019_ = stack[4].m_obj;
lean_object* v___y_1020_ = stack[5].m_obj;
lean_object* v_res_1033_;
v_res_1033_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_1015_, v_declHint_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
stack->m_obj
 = v_res_1033_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_1034_, lean_object* v_declHint_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_1034_, v_declHint_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1041_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_1042_, lean_object* v_msg_1043_, lean_object* v_declHint_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; lean_object* v_a_1051_; lean_object* v___x_1052_; 
v___x_1050_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_1043_, v_declHint_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_1042_, v_a_1051_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1042_ = stack[0].m_obj;
lean_object* v_msg_1043_ = stack[1].m_obj;
lean_object* v_declHint_1044_ = stack[2].m_obj;
lean_object* v___y_1045_ = stack[3].m_obj;
lean_object* v___y_1046_ = stack[4].m_obj;
lean_object* v___y_1047_ = stack[5].m_obj;
lean_object* v___y_1048_ = stack[6].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1042_, v_msg_1043_, v_declHint_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_1054_, lean_object* v_msg_1055_, lean_object* v_declHint_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1054_, v_msg_1055_, v_declHint_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v_ref_1054_);
return v_res_1062_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1069_, lean_object* v_constName_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1076_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_1077_ = 0;
lean_inc(v_constName_1070_);
v___x_1078_ = l_Lean_MessageData_ofConstName(v_constName_1070_, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1076_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1069_, v___x_1081_, v_constName_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
return v___x_1082_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1069_ = stack[0].m_obj;
lean_object* v_constName_1070_ = stack[1].m_obj;
lean_object* v___y_1071_ = stack[2].m_obj;
lean_object* v___y_1072_ = stack[3].m_obj;
lean_object* v___y_1073_ = stack[4].m_obj;
lean_object* v___y_1074_ = stack[5].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1069_, v_constName_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1084_, lean_object* v_constName_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1084_, v_constName_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v_ref_1084_);
return v_res_1091_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(lean_object* v_constName_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_ref_1098_; lean_object* v___x_1099_; 
v_ref_1098_ = lean_ctor_get(v___y_1095_, 2);
v___x_1099_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1098_, v_constName_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1092_ = stack[0].m_obj;
lean_object* v___y_1093_ = stack[1].m_obj;
lean_object* v___y_1094_ = stack[2].m_obj;
lean_object* v___y_1095_ = stack[3].m_obj;
lean_object* v___y_1096_ = stack[4].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1107_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_env_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1114_ = lean_st_ref_get(v___y_1112_);
v_env_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_env_1115_);
lean_dec(v___x_1114_);
v___x_1116_ = 0;
lean_inc(v_constName_1108_);
v___x_1117_ = l_Lean_Environment_find_x3f(v_env_1115_, v_constName_1108_, v___x_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1118_;
}
else
{
lean_object* v_val_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_constName_1108_);
v_val_1119_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1117_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_val_1119_);
lean_dec(v___x_1117_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 0);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_val_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1108_ = stack[0].m_obj;
lean_object* v___y_1109_ = stack[1].m_obj;
lean_object* v___y_1110_ = stack[2].m_obj;
lean_object* v___y_1111_ = stack[3].m_obj;
lean_object* v___y_1112_ = stack[4].m_obj;
lean_object* v_res_1127_;
v_res_1127_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
stack->m_obj
 = v_res_1127_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(lean_object* v_constName_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_constName_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1134_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
v___x_1140_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
lean_ctor_set(v___x_1140_, 2, v___x_1139_);
lean_ctor_set(v___x_1140_, 3, v___x_1139_);
lean_ctor_set(v___x_1140_, 4, v___x_1139_);
lean_ctor_set(v___x_1140_, 5, v___x_1139_);
return v___x_1140_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(lean_object* v_declName_1141_, uint8_t v_s_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v_env_1147_; lean_object* v_nextMacroScope_1148_; lean_object* v_ngen_1149_; lean_object* v_auxDeclNGen_1150_; lean_object* v_traceState_1151_; lean_object* v_recordedDeps_1152_; lean_object* v_messages_1153_; lean_object* v_infoState_1154_; lean_object* v_snapshotTasks_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1184_; 
v___x_1146_ = lean_st_ref_take(v___y_1144_);
v_env_1147_ = lean_ctor_get(v___x_1146_, 0);
v_nextMacroScope_1148_ = lean_ctor_get(v___x_1146_, 1);
v_ngen_1149_ = lean_ctor_get(v___x_1146_, 2);
v_auxDeclNGen_1150_ = lean_ctor_get(v___x_1146_, 3);
v_traceState_1151_ = lean_ctor_get(v___x_1146_, 4);
v_recordedDeps_1152_ = lean_ctor_get(v___x_1146_, 6);
v_messages_1153_ = lean_ctor_get(v___x_1146_, 7);
v_infoState_1154_ = lean_ctor_get(v___x_1146_, 8);
v_snapshotTasks_1155_ = lean_ctor_get(v___x_1146_, 9);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v___x_1146_, 5);
lean_dec(v_unused_1185_);
v___x_1157_ = v___x_1146_;
v_isShared_1158_ = v_isSharedCheck_1184_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_snapshotTasks_1155_);
lean_inc(v_infoState_1154_);
lean_inc(v_messages_1153_);
lean_inc(v_recordedDeps_1152_);
lean_inc(v_traceState_1151_);
lean_inc(v_auxDeclNGen_1150_);
lean_inc(v_ngen_1149_);
lean_inc(v_nextMacroScope_1148_);
lean_inc(v_env_1147_);
lean_dec(v___x_1146_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1184_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1159_ = 0;
v___x_1160_ = lean_box(0);
v___x_1161_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1147_, v_declName_1141_, v_s_1142_, v___x_1159_, v___x_1160_);
v___x_1162_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 5, v___x_1162_);
lean_ctor_set(v___x_1157_, 0, v___x_1161_);
v___x_1164_ = v___x_1157_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_nextMacroScope_1148_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_ngen_1149_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_auxDeclNGen_1150_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_traceState_1151_);
lean_ctor_set(v_reuseFailAlloc_1183_, 5, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1183_, 6, v_recordedDeps_1152_);
lean_ctor_set(v_reuseFailAlloc_1183_, 7, v_messages_1153_);
lean_ctor_set(v_reuseFailAlloc_1183_, 8, v_infoState_1154_);
lean_ctor_set(v_reuseFailAlloc_1183_, 9, v_snapshotTasks_1155_);
v___x_1164_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_mctx_1167_; lean_object* v_zetaDeltaFVarIds_1168_; lean_object* v_postponed_1169_; lean_object* v_diag_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1181_; 
v___x_1165_ = lean_st_ref_put(v___y_1144_, v___x_1164_);
v___x_1166_ = lean_st_ref_take(v___y_1143_);
v_mctx_1167_ = lean_ctor_get(v___x_1166_, 0);
v_zetaDeltaFVarIds_1168_ = lean_ctor_get(v___x_1166_, 2);
v_postponed_1169_ = lean_ctor_get(v___x_1166_, 3);
v_diag_1170_ = lean_ctor_get(v___x_1166_, 4);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v___x_1166_, 1);
lean_dec(v_unused_1182_);
v___x_1172_ = v___x_1166_;
v_isShared_1173_ = v_isSharedCheck_1181_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_diag_1170_);
lean_inc(v_postponed_1169_);
lean_inc(v_zetaDeltaFVarIds_1168_);
lean_inc(v_mctx_1167_);
lean_dec(v___x_1166_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1181_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v___x_1175_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_mctx_1167_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_zetaDeltaFVarIds_1168_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_postponed_1169_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_diag_1170_);
v___x_1177_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_st_ref_put(v___y_1143_, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1174_);
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1141_ = stack[0].m_obj;
uint8_t v_s_1142_ = stack[1].m_num;
lean_object* v___y_1143_ = stack[2].m_obj;
lean_object* v___y_1144_ = stack[3].m_obj;
lean_object* v_res_1186_;
v_res_1186_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1141_, v_s_1142_, v___y_1143_, v___y_1144_);
stack->m_obj
 = v_res_1186_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object* v_declName_1187_, lean_object* v_s_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_s_boxed_1192_; lean_object* v_res_1193_; 
v_s_boxed_1192_ = lean_unbox(v_s_1188_);
v_res_1193_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1187_, v_s_boxed_1192_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
return v_res_1193_;
}
}
lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object* v_declName_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = 0;
v___x_1201_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1194_, v___x_1200_, v___y_1196_, v___y_1198_);
return v___x_1201_;
}
}
LEAN_EXPORT void l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1194_ = stack[0].m_obj;
lean_object* v___y_1195_ = stack[1].m_obj;
lean_object* v___y_1196_ = stack[2].m_obj;
lean_object* v___y_1197_ = stack[3].m_obj;
lean_object* v___y_1198_ = stack[4].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v_declName_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___boxed(lean_object* v_declName_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v_declName_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(lean_object* v_constName_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v_env_1217_; uint8_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = lean_st_ref_get(v___y_1214_);
v_env_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_env_1217_);
lean_dec(v___x_1216_);
v___x_1218_ = 0;
lean_inc(v_constName_1210_);
v___x_1219_ = l_Lean_Environment_findConstVal_x3f(v_env_1217_, v_constName_1210_, v___x_1218_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1220_;
}
else
{
lean_object* v_val_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_constName_1210_);
v_val_1221_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1219_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_val_1221_);
lean_dec(v___x_1219_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 0);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_val_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1210_ = stack[0].m_obj;
lean_object* v___y_1211_ = stack[1].m_obj;
lean_object* v___y_1212_ = stack[2].m_obj;
lean_object* v___y_1213_ = stack[3].m_obj;
lean_object* v___y_1214_ = stack[4].m_obj;
lean_object* v_res_1229_;
v_res_1229_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v_constName_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
stack->m_obj
 = v_res_1229_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(lean_object* v_constName_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v_constName_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1240_ = lean_unsigned_to_nat(60u);
v___x_1241_ = lean_unsigned_to_nat(81u);
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0));
v___x_1243_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1244_ = l_mkPanicMessageWithDecl(v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_, v___x_1239_);
return v___x_1244_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(lean_object* v_indName_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1245_);
v___x_1252_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1386_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1386_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1386_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
if (lean_obj_tag(v_a_1253_) == 5)
{
lean_object* v_val_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_val_1257_ = lean_ctor_get(v_a_1253_, 0);
lean_inc_ref(v_val_1257_);
lean_dec_ref_known(v_a_1253_, 1);
v___x_1258_ = l_Lean_InductiveVal_numCtors(v_val_1257_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_nat_dec_eq(v___x_1258_, v___x_1259_);
lean_dec(v___x_1258_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_del_object(v___x_1255_);
v___x_1261_ = lean_box(v___x_1260_);
v___f_1262_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1262_, 0, v_val_1257_);
lean_closure_set(v___f_1262_, 1, v___x_1259_);
lean_closure_set(v___f_1262_, 2, v___x_1251_);
lean_closure_set(v___f_1262_, 3, v___x_1261_);
lean_inc(v_indName_1245_);
v___x_1263_ = l_Lean_mkCasesOnName(v_indName_1245_);
v___x_1264_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1263_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v_levelParams_1266_; lean_object* v_type_1267_; lean_object* v___x_1268_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v_levelParams_1266_ = lean_ctor_get(v_a_1265_, 1);
lean_inc(v_levelParams_1266_);
v_type_1267_ = lean_ctor_get(v_a_1265_, 2);
lean_inc_ref(v_type_1267_);
lean_dec(v_a_1265_);
v___x_1268_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1267_, v___f_1262_, v___x_1260_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc_n(v_a_1269_, 2);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1245_);
lean_inc(v_a_1249_);
lean_inc_ref(v_a_1248_);
lean_inc(v_a_1247_);
lean_inc_ref(v_a_1246_);
v___x_1271_ = lean_infer_type(v_a_1269_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1355_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v___x_1273_ = lean_box(1);
lean_inc(v___x_1270_);
v___x_1274_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1270_, v_levelParams_1266_, v_a_1272_, v_a_1269_, v___x_1273_, v_a_1249_);
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1355_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1355_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
uint8_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = 1;
v___x_1282_ = l_Lean_addAndCompile(v___x_1280_, v___x_1281_, v___x_1260_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; lean_object* v_env_1284_; lean_object* v_nextMacroScope_1285_; lean_object* v_ngen_1286_; lean_object* v_auxDeclNGen_1287_; lean_object* v_traceState_1288_; lean_object* v_recordedDeps_1289_; lean_object* v_messages_1290_; lean_object* v_infoState_1291_; lean_object* v_snapshotTasks_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref_known(v___x_1282_, 1);
v___x_1283_ = lean_st_ref_take(v_a_1249_);
v_env_1284_ = lean_ctor_get(v___x_1283_, 0);
v_nextMacroScope_1285_ = lean_ctor_get(v___x_1283_, 1);
v_ngen_1286_ = lean_ctor_get(v___x_1283_, 2);
v_auxDeclNGen_1287_ = lean_ctor_get(v___x_1283_, 3);
v_traceState_1288_ = lean_ctor_get(v___x_1283_, 4);
v_recordedDeps_1289_ = lean_ctor_get(v___x_1283_, 6);
v_messages_1290_ = lean_ctor_get(v___x_1283_, 7);
v_infoState_1291_ = lean_ctor_get(v___x_1283_, 8);
v_snapshotTasks_1292_ = lean_ctor_get(v___x_1283_, 9);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v___x_1283_, 5);
lean_dec(v_unused_1353_);
v___x_1294_ = v___x_1283_;
v_isShared_1295_ = v_isSharedCheck_1352_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_snapshotTasks_1292_);
lean_inc(v_infoState_1291_);
lean_inc(v_messages_1290_);
lean_inc(v_recordedDeps_1289_);
lean_inc(v_traceState_1288_);
lean_inc(v_auxDeclNGen_1287_);
lean_inc(v_ngen_1286_);
lean_inc(v_nextMacroScope_1285_);
lean_inc(v_env_1284_);
lean_dec(v___x_1283_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1352_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_inc(v___x_1270_);
v___x_1296_ = l_Lean_Meta_addToCompletionBlackList(v_env_1284_, v___x_1270_);
v___x_1297_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 5, v___x_1297_);
lean_ctor_set(v___x_1294_, 0, v___x_1296_);
v___x_1299_ = v___x_1294_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_nextMacroScope_1285_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_ngen_1286_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_auxDeclNGen_1287_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_traceState_1288_);
lean_ctor_set(v_reuseFailAlloc_1351_, 5, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1351_, 6, v_recordedDeps_1289_);
lean_ctor_set(v_reuseFailAlloc_1351_, 7, v_messages_1290_);
lean_ctor_set(v_reuseFailAlloc_1351_, 8, v_infoState_1291_);
lean_ctor_set(v_reuseFailAlloc_1351_, 9, v_snapshotTasks_1292_);
v___x_1299_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_mctx_1302_; lean_object* v_zetaDeltaFVarIds_1303_; lean_object* v_postponed_1304_; lean_object* v_diag_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1349_; 
v___x_1300_ = lean_st_ref_put(v_a_1249_, v___x_1299_);
v___x_1301_ = lean_st_ref_take(v_a_1247_);
v_mctx_1302_ = lean_ctor_get(v___x_1301_, 0);
v_zetaDeltaFVarIds_1303_ = lean_ctor_get(v___x_1301_, 2);
v_postponed_1304_ = lean_ctor_get(v___x_1301_, 3);
v_diag_1305_ = lean_ctor_get(v___x_1301_, 4);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v___x_1301_, 1);
lean_dec(v_unused_1350_);
v___x_1307_ = v___x_1301_;
v_isShared_1308_ = v_isSharedCheck_1349_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_diag_1305_);
lean_inc(v_postponed_1304_);
lean_inc(v_zetaDeltaFVarIds_1303_);
lean_inc(v_mctx_1302_);
lean_dec(v___x_1301_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1349_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1309_);
v___x_1311_ = v___x_1307_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_mctx_1302_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_zetaDeltaFVarIds_1303_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v_postponed_1304_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v_diag_1305_);
v___x_1311_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_env_1314_; lean_object* v_nextMacroScope_1315_; lean_object* v_ngen_1316_; lean_object* v_auxDeclNGen_1317_; lean_object* v_traceState_1318_; lean_object* v_recordedDeps_1319_; lean_object* v_messages_1320_; lean_object* v_infoState_1321_; lean_object* v_snapshotTasks_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1346_; 
v___x_1312_ = lean_st_ref_put(v_a_1247_, v___x_1311_);
v___x_1313_ = lean_st_ref_take(v_a_1249_);
v_env_1314_ = lean_ctor_get(v___x_1313_, 0);
v_nextMacroScope_1315_ = lean_ctor_get(v___x_1313_, 1);
v_ngen_1316_ = lean_ctor_get(v___x_1313_, 2);
v_auxDeclNGen_1317_ = lean_ctor_get(v___x_1313_, 3);
v_traceState_1318_ = lean_ctor_get(v___x_1313_, 4);
v_recordedDeps_1319_ = lean_ctor_get(v___x_1313_, 6);
v_messages_1320_ = lean_ctor_get(v___x_1313_, 7);
v_infoState_1321_ = lean_ctor_get(v___x_1313_, 8);
v_snapshotTasks_1322_ = lean_ctor_get(v___x_1313_, 9);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1313_, 5);
lean_dec(v_unused_1347_);
v___x_1324_ = v___x_1313_;
v_isShared_1325_ = v_isSharedCheck_1346_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_snapshotTasks_1322_);
lean_inc(v_infoState_1321_);
lean_inc(v_messages_1320_);
lean_inc(v_recordedDeps_1319_);
lean_inc(v_traceState_1318_);
lean_inc(v_auxDeclNGen_1317_);
lean_inc(v_ngen_1316_);
lean_inc(v_nextMacroScope_1315_);
lean_inc(v_env_1314_);
lean_dec(v___x_1313_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1346_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_inc(v___x_1270_);
v___x_1326_ = l_Lean_addProtected(v_env_1314_, v___x_1270_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 5, v___x_1297_);
lean_ctor_set(v___x_1324_, 0, v___x_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_nextMacroScope_1315_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_ngen_1316_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_auxDeclNGen_1317_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_traceState_1318_);
lean_ctor_set(v_reuseFailAlloc_1345_, 5, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1345_, 6, v_recordedDeps_1319_);
lean_ctor_set(v_reuseFailAlloc_1345_, 7, v_messages_1320_);
lean_ctor_set(v_reuseFailAlloc_1345_, 8, v_infoState_1321_);
lean_ctor_set(v_reuseFailAlloc_1345_, 9, v_snapshotTasks_1322_);
v___x_1328_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_mctx_1331_; lean_object* v_zetaDeltaFVarIds_1332_; lean_object* v_postponed_1333_; lean_object* v_diag_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1343_; 
v___x_1329_ = lean_st_ref_put(v_a_1249_, v___x_1328_);
v___x_1330_ = lean_st_ref_take(v_a_1247_);
v_mctx_1331_ = lean_ctor_get(v___x_1330_, 0);
v_zetaDeltaFVarIds_1332_ = lean_ctor_get(v___x_1330_, 2);
v_postponed_1333_ = lean_ctor_get(v___x_1330_, 3);
v_diag_1334_ = lean_ctor_get(v___x_1330_, 4);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1330_, 1);
lean_dec(v_unused_1344_);
v___x_1336_ = v___x_1330_;
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_diag_1334_);
lean_inc(v_postponed_1333_);
lean_inc(v_zetaDeltaFVarIds_1332_);
lean_inc(v_mctx_1331_);
lean_dec(v___x_1330_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1309_);
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_mctx_1331_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_zetaDeltaFVarIds_1332_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_postponed_1333_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_diag_1334_);
v___x_1339_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_st_ref_put(v_a_1247_, v___x_1339_);
v___x_1341_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_1270_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1341_;
}
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1270_);
return v___x_1282_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v___x_1270_);
lean_dec(v_a_1269_);
lean_dec(v_levelParams_1266_);
v_a_1356_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1271_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1271_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_levelParams_1266_);
lean_dec(v_indName_1245_);
v_a_1364_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1268_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1268_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v___f_1262_);
lean_dec(v_indName_1245_);
v_a_1372_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1264_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1264_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_dec_ref(v_val_1257_);
lean_dec(v_indName_1245_);
v___x_1380_ = lean_box(0);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1380_);
v___x_1382_ = v___x_1255_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_del_object(v___x_1255_);
lean_dec(v_a_1253_);
lean_dec(v_indName_1245_);
v___x_1384_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2);
v___x_1385_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_1384_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1385_;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_indName_1245_);
v_a_1387_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1252_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1252_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_1245_ = stack[0].m_obj;
lean_object* v_a_1246_ = stack[1].m_obj;
lean_object* v_a_1247_ = stack[2].m_obj;
lean_object* v_a_1248_ = stack[3].m_obj;
lean_object* v_a_1249_ = stack[4].m_obj;
lean_object* v_res_1395_;
v_res_1395_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
stack->m_obj
 = v_res_1395_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___boxed(lean_object* v_indName_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1402_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(lean_object* v_00_u03b1_1403_, lean_object* v_name_1404_, uint8_t v_bi_1405_, lean_object* v_type_1406_, lean_object* v_k_1407_, uint8_t v_kind_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_1404_, v_bi_1405_, v_type_1406_, v_k_1407_, v_kind_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1404_ = stack[1].m_obj;
uint8_t v_bi_1405_ = stack[2].m_num;
lean_object* v_type_1406_ = stack[3].m_obj;
lean_object* v_k_1407_ = stack[4].m_obj;
uint8_t v_kind_1408_ = stack[5].m_num;
lean_object* v___y_1409_ = stack[6].m_obj;
lean_object* v___y_1410_ = stack[7].m_obj;
lean_object* v___y_1411_ = stack[8].m_obj;
lean_object* v___y_1412_ = stack[9].m_obj;
lean_object* v_res_1415_;
v_res_1415_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(lean_box(0), v_name_1404_, v_bi_1405_, v_type_1406_, v_k_1407_, v_kind_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
stack->m_obj
 = v_res_1415_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_name_1417_, lean_object* v_bi_1418_, lean_object* v_type_1419_, lean_object* v_k_1420_, lean_object* v_kind_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v_bi_boxed_1427_; uint8_t v_kind_boxed_1428_; lean_object* v_res_1429_; 
v_bi_boxed_1427_ = lean_unbox(v_bi_1418_);
v_kind_boxed_1428_ = lean_unbox(v_kind_1421_);
v_res_1429_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(v_00_u03b1_1416_, v_name_1417_, v_bi_boxed_1427_, v_type_1419_, v_k_1420_, v_kind_boxed_1428_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1429_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(lean_object* v_00_u03b1_1430_, lean_object* v_name_1431_, lean_object* v_type_1432_, lean_object* v_k_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v_name_1431_, v_type_1432_, v_k_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1431_ = stack[1].m_obj;
lean_object* v_type_1432_ = stack[2].m_obj;
lean_object* v_k_1433_ = stack[3].m_obj;
lean_object* v___y_1434_ = stack[4].m_obj;
lean_object* v___y_1435_ = stack[5].m_obj;
lean_object* v___y_1436_ = stack[6].m_obj;
lean_object* v___y_1437_ = stack[7].m_obj;
lean_object* v_res_1440_;
v_res_1440_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(lean_box(0), v_name_1431_, v_type_1432_, v_k_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
stack->m_obj
 = v_res_1440_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___boxed(lean_object* v_00_u03b1_1441_, lean_object* v_name_1442_, lean_object* v_type_1443_, lean_object* v_k_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(v_00_u03b1_1441_, v_name_1442_, v_type_1443_, v_k_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1450_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(lean_object* v_declName_1451_, uint8_t v_s_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1451_, v_s_1452_, v___y_1454_, v___y_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1451_ = stack[0].m_obj;
uint8_t v_s_1452_ = stack[1].m_num;
lean_object* v___y_1453_ = stack[2].m_obj;
lean_object* v___y_1454_ = stack[3].m_obj;
lean_object* v___y_1455_ = stack[4].m_obj;
lean_object* v___y_1456_ = stack[5].m_obj;
lean_object* v_res_1459_;
v_res_1459_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(v_declName_1451_, v_s_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
stack->m_obj
 = v_res_1459_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___boxed(lean_object* v_declName_1460_, lean_object* v_s_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_s_boxed_1467_; lean_object* v_res_1468_; 
v_s_boxed_1467_ = lean_unbox(v_s_1461_);
v_res_1468_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(v_declName_1460_, v_s_boxed_1467_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1468_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(lean_object* v_00_u03b1_1469_, lean_object* v_constName_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1470_ = stack[1].m_obj;
lean_object* v___y_1471_ = stack[2].m_obj;
lean_object* v___y_1472_ = stack[3].m_obj;
lean_object* v___y_1473_ = stack[4].m_obj;
lean_object* v___y_1474_ = stack[5].m_obj;
lean_object* v_res_1477_;
v_res_1477_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(lean_box(0), v_constName_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
stack->m_obj
 = v_res_1477_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1478_, lean_object* v_constName_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(v_00_u03b1_1478_, v_constName_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
return v_res_1485_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_1486_, lean_object* v_ref_1487_, lean_object* v_constName_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1487_, v_constName_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1487_ = stack[1].m_obj;
lean_object* v_constName_1488_ = stack[2].m_obj;
lean_object* v___y_1489_ = stack[3].m_obj;
lean_object* v___y_1490_ = stack[4].m_obj;
lean_object* v___y_1491_ = stack[5].m_obj;
lean_object* v___y_1492_ = stack[6].m_obj;
lean_object* v_res_1495_;
v_res_1495_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(lean_box(0), v_ref_1487_, v_constName_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
stack->m_obj
 = v_res_1495_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1496_, lean_object* v_ref_1497_, lean_object* v_constName_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(v_00_u03b1_1496_, v_ref_1497_, v_constName_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v_ref_1497_);
return v_res_1504_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_1505_, lean_object* v_ref_1506_, lean_object* v_msg_1507_, lean_object* v_declHint_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1506_, v_msg_1507_, v_declHint_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1506_ = stack[1].m_obj;
lean_object* v_msg_1507_ = stack[2].m_obj;
lean_object* v_declHint_1508_ = stack[3].m_obj;
lean_object* v___y_1509_ = stack[4].m_obj;
lean_object* v___y_1510_ = stack[5].m_obj;
lean_object* v___y_1511_ = stack[6].m_obj;
lean_object* v___y_1512_ = stack[7].m_obj;
lean_object* v_res_1515_;
v_res_1515_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(lean_box(0), v_ref_1506_, v_msg_1507_, v_declHint_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
stack->m_obj
 = v_res_1515_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_1516_, lean_object* v_ref_1517_, lean_object* v_msg_1518_, lean_object* v_declHint_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_1516_, v_ref_1517_, v_msg_1518_, v_declHint_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v_ref_1517_);
return v_res_1525_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_1526_, lean_object* v_declHint_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_1526_, v_declHint_1527_, v___y_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1526_ = stack[0].m_obj;
lean_object* v_declHint_1527_ = stack[1].m_obj;
lean_object* v___y_1528_ = stack[2].m_obj;
lean_object* v___y_1529_ = stack[3].m_obj;
lean_object* v___y_1530_ = stack[4].m_obj;
lean_object* v___y_1531_ = stack[5].m_obj;
lean_object* v_res_1534_;
v_res_1534_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_1526_, v_declHint_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
stack->m_obj
 = v_res_1534_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1535_, lean_object* v_declHint_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_1535_, v_declHint_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1542_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_1543_, lean_object* v_ref_1544_, lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_1544_, v_msg_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1544_ = stack[1].m_obj;
lean_object* v_msg_1545_ = stack[2].m_obj;
lean_object* v___y_1546_ = stack[3].m_obj;
lean_object* v___y_1547_ = stack[4].m_obj;
lean_object* v___y_1548_ = stack[5].m_obj;
lean_object* v___y_1549_ = stack[6].m_obj;
lean_object* v_res_1552_;
v_res_1552_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_box(0), v_ref_1544_, v_msg_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
stack->m_obj
 = v_res_1552_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1553_, lean_object* v_ref_1554_, lean_object* v_msg_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_1553_, v_ref_1554_, v_msg_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v_ref_1554_);
return v_res_1561_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(lean_object* v___x_1562_, lean_object* v_k_1563_, lean_object* v_zs_1564_, uint8_t v___x_1565_, uint8_t v___x_1566_, uint8_t v___x_1567_, lean_object* v_h_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
lean_inc_ref(v_h_1568_);
v___x_1574_ = l_Lean_Meta_mkEqNDRec(v___x_1562_, v_k_1563_, v_h_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1576_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_a_1575_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = l_Lean_mkAppN(v_a_1577_, v_zs_1564_);
v___x_1579_ = lean_array_push(v_zs_1564_, v_h_1568_);
v___x_1580_ = l_Lean_Meta_mkLambdaFVars(v___x_1579_, v___x_1578_, v___x_1565_, v___x_1566_, v___x_1565_, v___x_1566_, v___x_1567_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec_ref(v___x_1579_);
return v___x_1580_;
}
else
{
lean_dec_ref(v_h_1568_);
lean_dec_ref(v_zs_1564_);
return v___x_1576_;
}
}
else
{
lean_dec_ref(v_h_1568_);
lean_dec_ref(v_zs_1564_);
return v___x_1574_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1562_ = stack[0].m_obj;
lean_object* v_k_1563_ = stack[1].m_obj;
lean_object* v_zs_1564_ = stack[2].m_obj;
uint8_t v___x_1565_ = stack[3].m_num;
uint8_t v___x_1566_ = stack[4].m_num;
uint8_t v___x_1567_ = stack[5].m_num;
lean_object* v_h_1568_ = stack[6].m_obj;
lean_object* v___y_1569_ = stack[7].m_obj;
lean_object* v___y_1570_ = stack[8].m_obj;
lean_object* v___y_1571_ = stack[9].m_obj;
lean_object* v___y_1572_ = stack[10].m_obj;
lean_object* v_res_1581_;
v_res_1581_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(v___x_1562_, v_k_1563_, v_zs_1564_, v___x_1565_, v___x_1566_, v___x_1567_, v_h_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
stack->m_obj
 = v_res_1581_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___x_1582_, lean_object* v_k_1583_, lean_object* v_zs_1584_, lean_object* v___x_1585_, lean_object* v___x_1586_, lean_object* v___x_1587_, lean_object* v_h_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v___x_6062__boxed_1594_; uint8_t v___x_6063__boxed_1595_; uint8_t v___x_6064__boxed_1596_; lean_object* v_res_1597_; 
v___x_6062__boxed_1594_ = lean_unbox(v___x_1585_);
v___x_6063__boxed_1595_ = lean_unbox(v___x_1586_);
v___x_6064__boxed_1596_ = lean_unbox(v___x_1587_);
v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(v___x_1582_, v_k_1583_, v_zs_1584_, v___x_6062__boxed_1594_, v___x_6063__boxed_1595_, v___x_6064__boxed_1596_, v_h_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1597_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(lean_object* v___x_1601_, lean_object* v_k_1602_, uint8_t v___x_1603_, uint8_t v___x_1604_, uint8_t v___x_1605_, lean_object* v___x_1606_, lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_ctorIdx_1610_, lean_object* v___x_1611_, lean_object* v_zs_1612_, lean_object* v___ctorRet_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1619_ = lean_box(v___x_1603_);
v___x_1620_ = lean_box(v___x_1604_);
v___x_1621_ = lean_box(v___x_1605_);
v___f_1622_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1622_, 0, v___x_1601_);
lean_closure_set(v___f_1622_, 1, v_k_1602_);
lean_closure_set(v___f_1622_, 2, v_zs_1612_);
lean_closure_set(v___f_1622_, 3, v___x_1619_);
lean_closure_set(v___f_1622_, 4, v___x_1620_);
lean_closure_set(v___f_1622_, 5, v___x_1621_);
v___x_1623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1));
v___x_1624_ = l_Lean_Level_ofNat(v___x_1606_);
v___x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v___x_1607_);
v___x_1626_ = l_Lean_mkConst(v___x_1623_, v___x_1625_);
v___x_1627_ = l_Lean_mkRawNatLit(v___x_1608_);
v___x_1628_ = l_Lean_mkApp3(v___x_1626_, v___x_1609_, v_ctorIdx_1610_, v___x_1627_);
v___x_1629_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1611_, v___x_1628_, v___f_1622_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1629_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1601_ = stack[0].m_obj;
lean_object* v_k_1602_ = stack[1].m_obj;
uint8_t v___x_1603_ = stack[2].m_num;
uint8_t v___x_1604_ = stack[3].m_num;
uint8_t v___x_1605_ = stack[4].m_num;
lean_object* v___x_1606_ = stack[5].m_obj;
lean_object* v___x_1607_ = stack[6].m_obj;
lean_object* v___x_1608_ = stack[7].m_obj;
lean_object* v___x_1609_ = stack[8].m_obj;
lean_object* v_ctorIdx_1610_ = stack[9].m_obj;
lean_object* v___x_1611_ = stack[10].m_obj;
lean_object* v_zs_1612_ = stack[11].m_obj;
lean_object* v___ctorRet_1613_ = stack[12].m_obj;
lean_object* v___y_1614_ = stack[13].m_obj;
lean_object* v___y_1615_ = stack[14].m_obj;
lean_object* v___y_1616_ = stack[15].m_obj;
lean_object* v___y_1617_ = stack[16].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(v___x_1601_, v_k_1602_, v___x_1603_, v___x_1604_, v___x_1605_, v___x_1606_, v___x_1607_, v___x_1608_, v___x_1609_, v_ctorIdx_1610_, v___x_1611_, v_zs_1612_, v___ctorRet_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1631_ = _args[0];
lean_object* v_k_1632_ = _args[1];
lean_object* v___x_1633_ = _args[2];
lean_object* v___x_1634_ = _args[3];
lean_object* v___x_1635_ = _args[4];
lean_object* v___x_1636_ = _args[5];
lean_object* v___x_1637_ = _args[6];
lean_object* v___x_1638_ = _args[7];
lean_object* v___x_1639_ = _args[8];
lean_object* v_ctorIdx_1640_ = _args[9];
lean_object* v___x_1641_ = _args[10];
lean_object* v_zs_1642_ = _args[11];
lean_object* v___ctorRet_1643_ = _args[12];
lean_object* v___y_1644_ = _args[13];
lean_object* v___y_1645_ = _args[14];
lean_object* v___y_1646_ = _args[15];
lean_object* v___y_1647_ = _args[16];
lean_object* v___y_1648_ = _args[17];
_start:
{
uint8_t v___x_6136__boxed_1649_; uint8_t v___x_6137__boxed_1650_; uint8_t v___x_6138__boxed_1651_; lean_object* v_res_1652_; 
v___x_6136__boxed_1649_ = lean_unbox(v___x_1633_);
v___x_6137__boxed_1650_ = lean_unbox(v___x_1634_);
v___x_6138__boxed_1651_ = lean_unbox(v___x_1635_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(v___x_1631_, v_k_1632_, v___x_6136__boxed_1649_, v___x_6137__boxed_1650_, v___x_6138__boxed_1651_, v___x_1636_, v___x_1637_, v___x_1638_, v___x_1639_, v_ctorIdx_1640_, v___x_1641_, v_zs_1642_, v___ctorRet_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v___ctorRet_1643_);
lean_dec(v___x_1636_);
return v_res_1652_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(lean_object* v___x_1656_, lean_object* v_k_1657_, lean_object* v_ctorIdx_1658_, lean_object* v_tail_1659_, lean_object* v___x_1660_, size_t v_sz_1661_, size_t v_i_1662_, lean_object* v_bs_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_usize_dec_lt(v_i_1662_, v_sz_1661_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_dec(v_tail_1659_);
lean_dec_ref(v_ctorIdx_1658_);
lean_dec_ref(v_k_1657_);
lean_dec_ref(v___x_1656_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_bs_1663_);
return v___x_1670_;
}
else
{
uint8_t v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_v_1677_; lean_object* v___x_1678_; lean_object* v_bs_x27_1679_; lean_object* v___y_1681_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___f_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1671_ = 0;
v___x_1672_ = 1;
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_1676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v_v_1677_ = lean_array_uget(v_bs_1663_, v_i_1662_);
v___x_1678_ = lean_unsigned_to_nat(0u);
v_bs_x27_1679_ = lean_array_uset(v_bs_1663_, v_i_1662_, v___x_1678_);
v___x_1695_ = lean_usize_to_nat(v_i_1662_);
v___x_1696_ = lean_box(v___x_1671_);
v___x_1697_ = lean_box(v___x_1669_);
v___x_1698_ = lean_box(v___x_1672_);
lean_inc_ref(v_ctorIdx_1658_);
lean_inc_ref(v_k_1657_);
lean_inc_ref(v___x_1656_);
v___f_1699_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed), 18, 11);
lean_closure_set(v___f_1699_, 0, v___x_1656_);
lean_closure_set(v___f_1699_, 1, v_k_1657_);
lean_closure_set(v___f_1699_, 2, v___x_1696_);
lean_closure_set(v___f_1699_, 3, v___x_1697_);
lean_closure_set(v___f_1699_, 4, v___x_1698_);
lean_closure_set(v___f_1699_, 5, v___x_1673_);
lean_closure_set(v___f_1699_, 6, v___x_1674_);
lean_closure_set(v___f_1699_, 7, v___x_1695_);
lean_closure_set(v___f_1699_, 8, v___x_1675_);
lean_closure_set(v___f_1699_, 9, v_ctorIdx_1658_);
lean_closure_set(v___f_1699_, 10, v___x_1676_);
lean_inc(v_tail_1659_);
v___x_1700_ = l_Lean_mkConst(v_v_1677_, v_tail_1659_);
v___x_1701_ = l_Lean_mkAppN(v___x_1700_, v___x_1660_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
v___x_1702_ = lean_infer_type(v___x_1701_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_a_1703_, v___f_1699_, v___x_1671_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
v___y_1681_ = v___x_1704_;
goto v___jp_1680_;
}
else
{
lean_dec_ref(v___f_1699_);
v___y_1681_ = v___x_1702_;
goto v___jp_1680_;
}
v___jp_1680_:
{
if (lean_obj_tag(v___y_1681_) == 0)
{
lean_object* v_a_1682_; size_t v___x_1683_; size_t v___x_1684_; lean_object* v___x_1685_; 
v_a_1682_ = lean_ctor_get(v___y_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___y_1681_, 1);
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = lean_usize_add(v_i_1662_, v___x_1683_);
v___x_1685_ = lean_array_uset(v_bs_x27_1679_, v_i_1662_, v_a_1682_);
v_i_1662_ = v___x_1684_;
v_bs_1663_ = v___x_1685_;
goto _start;
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v_bs_x27_1679_);
lean_dec(v_tail_1659_);
lean_dec_ref(v_ctorIdx_1658_);
lean_dec_ref(v_k_1657_);
lean_dec_ref(v___x_1656_);
v_a_1687_ = lean_ctor_get(v___y_1681_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___y_1681_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___y_1681_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___y_1681_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1656_ = stack[0].m_obj;
lean_object* v_k_1657_ = stack[1].m_obj;
lean_object* v_ctorIdx_1658_ = stack[2].m_obj;
lean_object* v_tail_1659_ = stack[3].m_obj;
lean_object* v___x_1660_ = stack[4].m_obj;
size_t v_sz_1661_ = stack[5].m_num;
size_t v_i_1662_ = stack[6].m_num;
lean_object* v_bs_1663_ = stack[7].m_obj;
lean_object* v___y_1664_ = stack[8].m_obj;
lean_object* v___y_1665_ = stack[9].m_obj;
lean_object* v___y_1666_ = stack[10].m_obj;
lean_object* v___y_1667_ = stack[11].m_obj;
lean_object* v_res_1705_;
v_res_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1656_, v_k_1657_, v_ctorIdx_1658_, v_tail_1659_, v___x_1660_, v_sz_1661_, v_i_1662_, v_bs_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
stack->m_obj
 = v_res_1705_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___boxed(lean_object* v___x_1706_, lean_object* v_k_1707_, lean_object* v_ctorIdx_1708_, lean_object* v_tail_1709_, lean_object* v___x_1710_, lean_object* v_sz_1711_, lean_object* v_i_1712_, lean_object* v_bs_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
size_t v_sz_boxed_1719_; size_t v_i_boxed_1720_; lean_object* v_res_1721_; 
v_sz_boxed_1719_ = lean_unbox_usize(v_sz_1711_);
lean_dec(v_sz_1711_);
v_i_boxed_1720_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1706_, v_k_1707_, v_ctorIdx_1708_, v_tail_1709_, v___x_1710_, v_sz_boxed_1719_, v_i_boxed_1720_, v_bs_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec_ref(v___x_1710_);
return v_res_1721_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(lean_object* v___x_1722_, lean_object* v___x_1723_, lean_object* v_a_1724_, lean_object* v_name_1725_, lean_object* v___x_1726_, lean_object* v___x_1727_, lean_object* v_ctors_1728_, lean_object* v___x_1729_, lean_object* v_ctorIdx_1730_, lean_object* v_tail_1731_, lean_object* v_h_1732_, lean_object* v_k_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_inc_ref(v___x_1722_);
v___x_1739_ = l_Lean_mkAppN(v___x_1722_, v___x_1723_);
v___x_1740_ = l_Lean_mkArrow(v_a_1724_, v___x_1739_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; uint8_t v___x_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1742_ = 0;
v___x_1743_ = 1;
v___x_1744_ = 1;
v___x_1745_ = l_Lean_Meta_mkLambdaFVars(v___x_1723_, v_a_1741_, v___x_1742_, v___x_1743_, v___x_1742_, v___x_1743_, v___x_1744_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; size_t v_sz_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = l_Lean_mkConst(v_name_1725_, v___x_1726_);
v___x_1748_ = l_Lean_mkAppN(v___x_1747_, v___x_1727_);
v___x_1749_ = l_Lean_Expr_app___override(v___x_1748_, v_a_1746_);
v___x_1750_ = l_Lean_mkAppN(v___x_1749_, v___x_1723_);
v___x_1751_ = lean_array_mk(v_ctors_1728_);
v_sz_1752_ = lean_array_size(v___x_1751_);
v___x_1753_ = ((size_t)0ULL);
lean_inc_ref(v_ctorIdx_1730_);
lean_inc_ref(v_k_1733_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1729_, v_k_1733_, v_ctorIdx_1730_, v_tail_1731_, v___x_1727_, v_sz_1752_, v___x_1753_, v___x_1751_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l_Lean_mkAppN(v___x_1750_, v_a_1755_);
lean_dec(v_a_1755_);
lean_inc_ref(v_h_1732_);
v___x_1757_ = l_Lean_Expr_app___override(v___x_1756_, v_h_1732_);
v___x_1758_ = lean_unsigned_to_nat(2u);
v___x_1759_ = lean_mk_empty_array_with_capacity(v___x_1758_);
lean_inc_ref(v___x_1759_);
v___x_1760_ = lean_array_push(v___x_1759_, v___x_1722_);
v___x_1761_ = lean_array_push(v___x_1760_, v_ctorIdx_1730_);
v___x_1762_ = l_Array_append___redArg(v___x_1727_, v___x_1761_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = l_Array_append___redArg(v___x_1762_, v___x_1723_);
v___x_1764_ = lean_array_push(v___x_1759_, v_h_1732_);
v___x_1765_ = lean_array_push(v___x_1764_, v_k_1733_);
v___x_1766_ = l_Array_append___redArg(v___x_1763_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l_Lean_Meta_mkLambdaFVars(v___x_1766_, v___x_1757_, v___x_1742_, v___x_1743_, v___x_1742_, v___x_1743_, v___x_1744_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec_ref(v___x_1766_);
return v___x_1767_;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v___x_1750_);
lean_dec_ref(v_k_1733_);
lean_dec_ref(v_h_1732_);
lean_dec_ref(v_ctorIdx_1730_);
lean_dec_ref(v___x_1727_);
lean_dec_ref(v___x_1722_);
v_a_1768_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1754_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1754_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_dec_ref(v_k_1733_);
lean_dec_ref(v_h_1732_);
lean_dec(v_tail_1731_);
lean_dec_ref(v_ctorIdx_1730_);
lean_dec_ref(v___x_1729_);
lean_dec(v_ctors_1728_);
lean_dec_ref(v___x_1727_);
lean_dec(v___x_1726_);
lean_dec(v_name_1725_);
lean_dec_ref(v___x_1722_);
return v___x_1745_;
}
}
else
{
lean_dec_ref(v_k_1733_);
lean_dec_ref(v_h_1732_);
lean_dec(v_tail_1731_);
lean_dec_ref(v_ctorIdx_1730_);
lean_dec_ref(v___x_1729_);
lean_dec(v_ctors_1728_);
lean_dec_ref(v___x_1727_);
lean_dec(v___x_1726_);
lean_dec(v_name_1725_);
lean_dec_ref(v___x_1722_);
return v___x_1740_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1722_ = stack[0].m_obj;
lean_object* v___x_1723_ = stack[1].m_obj;
lean_object* v_a_1724_ = stack[2].m_obj;
lean_object* v_name_1725_ = stack[3].m_obj;
lean_object* v___x_1726_ = stack[4].m_obj;
lean_object* v___x_1727_ = stack[5].m_obj;
lean_object* v_ctors_1728_ = stack[6].m_obj;
lean_object* v___x_1729_ = stack[7].m_obj;
lean_object* v_ctorIdx_1730_ = stack[8].m_obj;
lean_object* v_tail_1731_ = stack[9].m_obj;
lean_object* v_h_1732_ = stack[10].m_obj;
lean_object* v_k_1733_ = stack[11].m_obj;
lean_object* v___y_1734_ = stack[12].m_obj;
lean_object* v___y_1735_ = stack[13].m_obj;
lean_object* v___y_1736_ = stack[14].m_obj;
lean_object* v___y_1737_ = stack[15].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(v___x_1722_, v___x_1723_, v_a_1724_, v_name_1725_, v___x_1726_, v___x_1727_, v_ctors_1728_, v___x_1729_, v_ctorIdx_1730_, v_tail_1731_, v_h_1732_, v_k_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed(lean_object** _args){
lean_object* v___x_1777_ = _args[0];
lean_object* v___x_1778_ = _args[1];
lean_object* v_a_1779_ = _args[2];
lean_object* v_name_1780_ = _args[3];
lean_object* v___x_1781_ = _args[4];
lean_object* v___x_1782_ = _args[5];
lean_object* v_ctors_1783_ = _args[6];
lean_object* v___x_1784_ = _args[7];
lean_object* v_ctorIdx_1785_ = _args[8];
lean_object* v_tail_1786_ = _args[9];
lean_object* v_h_1787_ = _args[10];
lean_object* v_k_1788_ = _args[11];
lean_object* v___y_1789_ = _args[12];
lean_object* v___y_1790_ = _args[13];
lean_object* v___y_1791_ = _args[14];
lean_object* v___y_1792_ = _args[15];
lean_object* v___y_1793_ = _args[16];
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(v___x_1777_, v___x_1778_, v_a_1779_, v_name_1780_, v___x_1781_, v___x_1782_, v_ctors_1783_, v___x_1784_, v_ctorIdx_1785_, v_tail_1786_, v_h_1787_, v_k_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec_ref(v___x_1778_);
return v_res_1794_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(lean_object* v___x_1798_, lean_object* v___x_1799_, lean_object* v_a_1800_, lean_object* v_name_1801_, lean_object* v___x_1802_, lean_object* v___x_1803_, lean_object* v_ctors_1804_, lean_object* v___x_1805_, lean_object* v_ctorIdx_1806_, lean_object* v_tail_1807_, lean_object* v___x_1808_, lean_object* v_h_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___f_1815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1815_, 0, v___x_1798_);
lean_closure_set(v___f_1815_, 1, v___x_1799_);
lean_closure_set(v___f_1815_, 2, v_a_1800_);
lean_closure_set(v___f_1815_, 3, v_name_1801_);
lean_closure_set(v___f_1815_, 4, v___x_1802_);
lean_closure_set(v___f_1815_, 5, v___x_1803_);
lean_closure_set(v___f_1815_, 6, v_ctors_1804_);
lean_closure_set(v___f_1815_, 7, v___x_1805_);
lean_closure_set(v___f_1815_, 8, v_ctorIdx_1806_);
lean_closure_set(v___f_1815_, 9, v_tail_1807_);
lean_closure_set(v___f_1815_, 10, v_h_1809_);
v___x_1816_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1));
v___x_1817_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1816_, v___x_1808_, v___f_1815_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
return v___x_1817_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1798_ = stack[0].m_obj;
lean_object* v___x_1799_ = stack[1].m_obj;
lean_object* v_a_1800_ = stack[2].m_obj;
lean_object* v_name_1801_ = stack[3].m_obj;
lean_object* v___x_1802_ = stack[4].m_obj;
lean_object* v___x_1803_ = stack[5].m_obj;
lean_object* v_ctors_1804_ = stack[6].m_obj;
lean_object* v___x_1805_ = stack[7].m_obj;
lean_object* v_ctorIdx_1806_ = stack[8].m_obj;
lean_object* v_tail_1807_ = stack[9].m_obj;
lean_object* v___x_1808_ = stack[10].m_obj;
lean_object* v_h_1809_ = stack[11].m_obj;
lean_object* v___y_1810_ = stack[12].m_obj;
lean_object* v___y_1811_ = stack[13].m_obj;
lean_object* v___y_1812_ = stack[14].m_obj;
lean_object* v___y_1813_ = stack[15].m_obj;
lean_object* v_res_1818_;
v_res_1818_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(v___x_1798_, v___x_1799_, v_a_1800_, v_name_1801_, v___x_1802_, v___x_1803_, v_ctors_1804_, v___x_1805_, v_ctorIdx_1806_, v_tail_1807_, v___x_1808_, v_h_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
stack->m_obj
 = v_res_1818_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed(lean_object** _args){
lean_object* v___x_1819_ = _args[0];
lean_object* v___x_1820_ = _args[1];
lean_object* v_a_1821_ = _args[2];
lean_object* v_name_1822_ = _args[3];
lean_object* v___x_1823_ = _args[4];
lean_object* v___x_1824_ = _args[5];
lean_object* v_ctors_1825_ = _args[6];
lean_object* v___x_1826_ = _args[7];
lean_object* v_ctorIdx_1827_ = _args[8];
lean_object* v_tail_1828_ = _args[9];
lean_object* v___x_1829_ = _args[10];
lean_object* v_h_1830_ = _args[11];
lean_object* v___y_1831_ = _args[12];
lean_object* v___y_1832_ = _args[13];
lean_object* v___y_1833_ = _args[14];
lean_object* v___y_1834_ = _args[15];
lean_object* v___y_1835_ = _args[16];
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(v___x_1819_, v___x_1820_, v_a_1821_, v_name_1822_, v___x_1823_, v___x_1824_, v_ctors_1825_, v___x_1826_, v_ctorIdx_1827_, v_tail_1828_, v___x_1829_, v_h_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1836_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(lean_object* v___x_1837_, lean_object* v___x_1838_, lean_object* v___x_1839_, lean_object* v___x_1840_, lean_object* v_indName_1841_, lean_object* v_tail_1842_, lean_object* v___x_1843_, lean_object* v_name_1844_, lean_object* v_ctors_1845_, lean_object* v_ctorIdx_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_inc(v___x_1838_);
v___x_1852_ = l_Lean_mkConst(v___x_1837_, v___x_1838_);
lean_inc_ref(v___x_1840_);
lean_inc_ref_n(v___x_1839_, 2);
v___x_1853_ = lean_array_push(v___x_1839_, v___x_1840_);
v___x_1854_ = l_Lean_mkAppN(v___x_1852_, v___x_1853_);
lean_dec_ref(v___x_1853_);
lean_inc_ref_n(v_ctorIdx_1846_, 2);
lean_inc_ref(v___x_1854_);
v___x_1855_ = l_Lean_Expr_app___override(v___x_1854_, v_ctorIdx_1846_);
v___x_1856_ = l_Lean_mkCtorIdxName(v_indName_1841_);
lean_inc(v_tail_1842_);
v___x_1857_ = l_Lean_mkConst(v___x_1856_, v_tail_1842_);
v___x_1858_ = l_Array_append___redArg(v___x_1839_, v___x_1843_);
v___x_1859_ = l_Lean_mkAppN(v___x_1857_, v___x_1858_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = l_Lean_Meta_mkEq(v_ctorIdx_1846_, v___x_1859_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___f_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_n(v_a_1861_, 2);
lean_dec_ref_known(v___x_1860_, 1);
v___f_1862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed), 17, 11);
lean_closure_set(v___f_1862_, 0, v___x_1840_);
lean_closure_set(v___f_1862_, 1, v___x_1843_);
lean_closure_set(v___f_1862_, 2, v_a_1861_);
lean_closure_set(v___f_1862_, 3, v_name_1844_);
lean_closure_set(v___f_1862_, 4, v___x_1838_);
lean_closure_set(v___f_1862_, 5, v___x_1839_);
lean_closure_set(v___f_1862_, 6, v_ctors_1845_);
lean_closure_set(v___f_1862_, 7, v___x_1854_);
lean_closure_set(v___f_1862_, 8, v_ctorIdx_1846_);
lean_closure_set(v___f_1862_, 9, v_tail_1842_);
lean_closure_set(v___f_1862_, 10, v___x_1855_);
v___x_1863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_1864_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1863_, v_a_1861_, v___f_1862_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1864_;
}
else
{
lean_dec_ref(v___x_1855_);
lean_dec_ref(v___x_1854_);
lean_dec_ref(v_ctorIdx_1846_);
lean_dec(v_ctors_1845_);
lean_dec(v_name_1844_);
lean_dec_ref(v___x_1843_);
lean_dec(v_tail_1842_);
lean_dec_ref(v___x_1840_);
lean_dec_ref(v___x_1839_);
lean_dec(v___x_1838_);
return v___x_1860_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1837_ = stack[0].m_obj;
lean_object* v___x_1838_ = stack[1].m_obj;
lean_object* v___x_1839_ = stack[2].m_obj;
lean_object* v___x_1840_ = stack[3].m_obj;
lean_object* v_indName_1841_ = stack[4].m_obj;
lean_object* v_tail_1842_ = stack[5].m_obj;
lean_object* v___x_1843_ = stack[6].m_obj;
lean_object* v_name_1844_ = stack[7].m_obj;
lean_object* v_ctors_1845_ = stack[8].m_obj;
lean_object* v_ctorIdx_1846_ = stack[9].m_obj;
lean_object* v___y_1847_ = stack[10].m_obj;
lean_object* v___y_1848_ = stack[11].m_obj;
lean_object* v___y_1849_ = stack[12].m_obj;
lean_object* v___y_1850_ = stack[13].m_obj;
lean_object* v_res_1865_;
v_res_1865_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(v___x_1837_, v___x_1838_, v___x_1839_, v___x_1840_, v_indName_1841_, v_tail_1842_, v___x_1843_, v_name_1844_, v_ctors_1845_, v_ctorIdx_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
stack->m_obj
 = v_res_1865_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed(lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v___x_1868_, lean_object* v___x_1869_, lean_object* v_indName_1870_, lean_object* v_tail_1871_, lean_object* v___x_1872_, lean_object* v_name_1873_, lean_object* v_ctors_1874_, lean_object* v_ctorIdx_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(v___x_1866_, v___x_1867_, v___x_1868_, v___x_1869_, v_indName_1870_, v_tail_1871_, v___x_1872_, v_name_1873_, v_ctors_1874_, v_ctorIdx_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1881_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(lean_object* v_val_1882_, lean_object* v___x_1883_, lean_object* v___x_1884_, lean_object* v___x_1885_, lean_object* v_indName_1886_, lean_object* v_tail_1887_, lean_object* v_name_1888_, lean_object* v___x_1889_, lean_object* v_xs_1890_, lean_object* v_x_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_numParams_1897_; lean_object* v_numIndices_1898_; lean_object* v_ctors_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___f_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_numParams_1897_ = lean_ctor_get(v_val_1882_, 1);
lean_inc_n(v_numParams_1897_, 2);
v_numIndices_1898_ = lean_ctor_get(v_val_1882_, 2);
lean_inc(v_numIndices_1898_);
v_ctors_1899_ = lean_ctor_get(v_val_1882_, 4);
lean_inc(v_ctors_1899_);
lean_dec_ref(v_val_1882_);
v___x_1900_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_1890_, 2);
v___x_1901_ = l_Array_toSubarray___redArg(v_xs_1890_, v___x_1900_, v_numParams_1897_);
v___x_1902_ = l_Subarray_copy___redArg(v___x_1901_);
v___x_1903_ = lean_array_get(v___x_1883_, v_xs_1890_, v_numParams_1897_);
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = lean_nat_add(v_numParams_1897_, v___x_1904_);
lean_dec(v_numParams_1897_);
v___x_1906_ = lean_nat_add(v___x_1905_, v_numIndices_1898_);
lean_dec(v_numIndices_1898_);
lean_inc(v___x_1906_);
v___x_1907_ = l_Array_toSubarray___redArg(v_xs_1890_, v___x_1905_, v___x_1906_);
v___x_1908_ = l_Subarray_copy___redArg(v___x_1907_);
v___x_1909_ = lean_array_get(v___x_1883_, v_xs_1890_, v___x_1906_);
lean_dec(v___x_1906_);
lean_dec_ref(v_xs_1890_);
v___x_1910_ = lean_array_push(v___x_1908_, v___x_1909_);
v___f_1911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed), 15, 9);
lean_closure_set(v___f_1911_, 0, v___x_1884_);
lean_closure_set(v___f_1911_, 1, v___x_1885_);
lean_closure_set(v___f_1911_, 2, v___x_1902_);
lean_closure_set(v___f_1911_, 3, v___x_1903_);
lean_closure_set(v___f_1911_, 4, v_indName_1886_);
lean_closure_set(v___f_1911_, 5, v_tail_1887_);
lean_closure_set(v___f_1911_, 6, v___x_1910_);
lean_closure_set(v___f_1911_, 7, v_name_1888_);
lean_closure_set(v___f_1911_, 8, v_ctors_1899_);
v___x_1912_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_1913_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_1914_ = l_Lean_mkConst(v___x_1913_, v___x_1889_);
v___x_1915_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1912_, v___x_1914_, v___f_1911_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
return v___x_1915_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1882_ = stack[0].m_obj;
lean_object* v___x_1883_ = stack[1].m_obj;
lean_object* v___x_1884_ = stack[2].m_obj;
lean_object* v___x_1885_ = stack[3].m_obj;
lean_object* v_indName_1886_ = stack[4].m_obj;
lean_object* v_tail_1887_ = stack[5].m_obj;
lean_object* v_name_1888_ = stack[6].m_obj;
lean_object* v___x_1889_ = stack[7].m_obj;
lean_object* v_xs_1890_ = stack[8].m_obj;
lean_object* v_x_1891_ = stack[9].m_obj;
lean_object* v___y_1892_ = stack[10].m_obj;
lean_object* v___y_1893_ = stack[11].m_obj;
lean_object* v___y_1894_ = stack[12].m_obj;
lean_object* v___y_1895_ = stack[13].m_obj;
lean_object* v_res_1916_;
v_res_1916_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(v_val_1882_, v___x_1883_, v___x_1884_, v___x_1885_, v_indName_1886_, v_tail_1887_, v_name_1888_, v___x_1889_, v_xs_1890_, v_x_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
stack->m_obj
 = v_res_1916_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed(lean_object* v_val_1917_, lean_object* v___x_1918_, lean_object* v___x_1919_, lean_object* v___x_1920_, lean_object* v_indName_1921_, lean_object* v_tail_1922_, lean_object* v_name_1923_, lean_object* v___x_1924_, lean_object* v_xs_1925_, lean_object* v_x_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(v_val_1917_, v___x_1918_, v___x_1919_, v___x_1920_, v_indName_1921_, v_tail_1922_, v_name_1923_, v___x_1924_, v_xs_1925_, v_x_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec_ref(v_x_1926_);
lean_dec_ref(v___x_1918_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
if (lean_obj_tag(v_a_1933_) == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = l_List_reverse___redArg(v_a_1934_);
return v___x_1935_;
}
else
{
lean_object* v_head_1936_; lean_object* v_tail_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1946_; 
v_head_1936_ = lean_ctor_get(v_a_1933_, 0);
v_tail_1937_ = lean_ctor_get(v_a_1933_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_a_1933_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1939_ = v_a_1933_;
v_isShared_1940_ = v_isSharedCheck_1946_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_tail_1937_);
lean_inc(v_head_1936_);
lean_dec(v_a_1933_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1946_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = l_Lean_mkLevelParam(v_head_1936_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v_a_1934_);
lean_ctor_set(v___x_1939_, 0, v___x_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_a_1934_);
v___x_1943_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
v_a_1933_ = v_tail_1937_;
v_a_1934_ = v___x_1943_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1949_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_1950_ = lean_unsigned_to_nat(58u);
v___x_1951_ = lean_unsigned_to_nat(113u);
v___x_1952_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1953_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1954_ = l_mkPanicMessageWithDecl(v___x_1953_, v___x_1952_, v___x_1951_, v___x_1950_, v___x_1949_);
return v___x_1954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1956_ = lean_unsigned_to_nat(60u);
v___x_1957_ = lean_unsigned_to_nat(109u);
v___x_1958_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1960_ = l_mkPanicMessageWithDecl(v___x_1959_, v___x_1958_, v___x_1957_, v___x_1956_, v___x_1955_);
return v___x_1960_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(lean_object* v_indName_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1961_);
v___x_1968_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
if (lean_obj_tag(v_a_1969_) == 5)
{
lean_object* v_val_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_val_1970_ = lean_ctor_get(v_a_1969_, 0);
lean_inc_ref(v_val_1970_);
lean_dec_ref_known(v_a_1969_, 1);
lean_inc_n(v_indName_1961_, 2);
v___x_1971_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1961_);
v___x_1972_ = l_Lean_mkCasesOnName(v_indName_1961_);
v___x_1973_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1972_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v_name_1975_; lean_object* v_levelParams_1976_; lean_object* v_type_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v_name_1975_ = lean_ctor_get(v_a_1974_, 0);
lean_inc(v_name_1975_);
v_levelParams_1976_ = lean_ctor_get(v_a_1974_, 1);
lean_inc_n(v_levelParams_1976_, 2);
v_type_1977_ = lean_ctor_get(v_a_1974_, 2);
lean_inc_ref(v_type_1977_);
lean_dec(v_a_1974_);
v___x_1978_ = lean_box(0);
v___x_1979_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_1976_, v___x_1978_);
if (lean_obj_tag(v___x_1979_) == 1)
{
lean_object* v_tail_1980_; lean_object* v___f_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; 
v_tail_1980_ = lean_ctor_get(v___x_1979_, 1);
lean_inc(v_tail_1980_);
lean_inc(v_indName_1961_);
v___f_1981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed), 15, 8);
lean_closure_set(v___f_1981_, 0, v_val_1970_);
lean_closure_set(v___f_1981_, 1, v___x_1967_);
lean_closure_set(v___f_1981_, 2, v___x_1971_);
lean_closure_set(v___f_1981_, 3, v___x_1979_);
lean_closure_set(v___f_1981_, 4, v_indName_1961_);
lean_closure_set(v___f_1981_, 5, v_tail_1980_);
lean_closure_set(v___f_1981_, 6, v_name_1975_);
lean_closure_set(v___f_1981_, 7, v___x_1978_);
v___x_1982_ = 0;
v___x_1983_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1977_, v___f_1981_, v___x_1982_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc_n(v_a_1984_, 2);
lean_dec_ref_known(v___x_1983_, 1);
v___x_1985_ = l_Lean_mkCtorElimName(v_indName_1961_);
lean_inc(v_a_1965_);
lean_inc_ref(v_a_1964_);
lean_inc(v_a_1963_);
lean_inc_ref(v_a_1962_);
v___x_1986_ = lean_infer_type(v_a_1984_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2104_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = lean_box(1);
lean_inc(v___x_1985_);
v___x_1989_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1985_, v_levelParams_1976_, v_a_1987_, v_a_1984_, v___x_1988_, v_a_1965_);
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2104_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2104_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 1);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_2103_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
uint8_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = 1;
v___x_1997_ = l_Lean_addAndCompile(v___x_1995_, v___x_1996_, v___x_1982_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1998_; lean_object* v_env_1999_; lean_object* v_nextMacroScope_2000_; lean_object* v_ngen_2001_; lean_object* v_auxDeclNGen_2002_; lean_object* v_traceState_2003_; lean_object* v_recordedDeps_2004_; lean_object* v_messages_2005_; lean_object* v_infoState_2006_; lean_object* v_snapshotTasks_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2101_; 
lean_dec_ref_known(v___x_1997_, 1);
v___x_1998_ = lean_st_ref_take(v_a_1965_);
v_env_1999_ = lean_ctor_get(v___x_1998_, 0);
v_nextMacroScope_2000_ = lean_ctor_get(v___x_1998_, 1);
v_ngen_2001_ = lean_ctor_get(v___x_1998_, 2);
v_auxDeclNGen_2002_ = lean_ctor_get(v___x_1998_, 3);
v_traceState_2003_ = lean_ctor_get(v___x_1998_, 4);
v_recordedDeps_2004_ = lean_ctor_get(v___x_1998_, 6);
v_messages_2005_ = lean_ctor_get(v___x_1998_, 7);
v_infoState_2006_ = lean_ctor_get(v___x_1998_, 8);
v_snapshotTasks_2007_ = lean_ctor_get(v___x_1998_, 9);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v___x_1998_, 5);
lean_dec(v_unused_2102_);
v___x_2009_ = v___x_1998_;
v_isShared_2010_ = v_isSharedCheck_2101_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snapshotTasks_2007_);
lean_inc(v_infoState_2006_);
lean_inc(v_messages_2005_);
lean_inc(v_recordedDeps_2004_);
lean_inc(v_traceState_2003_);
lean_inc(v_auxDeclNGen_2002_);
lean_inc(v_ngen_2001_);
lean_inc(v_nextMacroScope_2000_);
lean_inc(v_env_1999_);
lean_dec(v___x_1998_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2101_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
lean_inc(v___x_1985_);
v___x_2011_ = l_Lean_markAuxRecursor(v_env_1999_, v___x_1985_);
v___x_2012_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 5, v___x_2012_);
lean_ctor_set(v___x_2009_, 0, v___x_2011_);
v___x_2014_ = v___x_2009_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_nextMacroScope_2000_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_ngen_2001_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_auxDeclNGen_2002_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_traceState_2003_);
lean_ctor_set(v_reuseFailAlloc_2100_, 5, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2100_, 6, v_recordedDeps_2004_);
lean_ctor_set(v_reuseFailAlloc_2100_, 7, v_messages_2005_);
lean_ctor_set(v_reuseFailAlloc_2100_, 8, v_infoState_2006_);
lean_ctor_set(v_reuseFailAlloc_2100_, 9, v_snapshotTasks_2007_);
v___x_2014_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v_mctx_2017_; lean_object* v_zetaDeltaFVarIds_2018_; lean_object* v_postponed_2019_; lean_object* v_diag_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2098_; 
v___x_2015_ = lean_st_ref_put(v_a_1965_, v___x_2014_);
v___x_2016_ = lean_st_ref_take(v_a_1963_);
v_mctx_2017_ = lean_ctor_get(v___x_2016_, 0);
v_zetaDeltaFVarIds_2018_ = lean_ctor_get(v___x_2016_, 2);
v_postponed_2019_ = lean_ctor_get(v___x_2016_, 3);
v_diag_2020_ = lean_ctor_get(v___x_2016_, 4);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; 
v_unused_2099_ = lean_ctor_get(v___x_2016_, 1);
lean_dec(v_unused_2099_);
v___x_2022_ = v___x_2016_;
v_isShared_2023_ = v_isSharedCheck_2098_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_diag_2020_);
lean_inc(v_postponed_2019_);
lean_inc(v_zetaDeltaFVarIds_2018_);
lean_inc(v_mctx_2017_);
lean_dec(v___x_2016_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2098_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 1, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_mctx_2017_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_zetaDeltaFVarIds_2018_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_postponed_2019_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_diag_2020_);
v___x_2026_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v_env_2029_; lean_object* v_nextMacroScope_2030_; lean_object* v_ngen_2031_; lean_object* v_auxDeclNGen_2032_; lean_object* v_traceState_2033_; lean_object* v_recordedDeps_2034_; lean_object* v_messages_2035_; lean_object* v_infoState_2036_; lean_object* v_snapshotTasks_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2095_; 
v___x_2027_ = lean_st_ref_put(v_a_1963_, v___x_2026_);
v___x_2028_ = lean_st_ref_take(v_a_1965_);
v_env_2029_ = lean_ctor_get(v___x_2028_, 0);
v_nextMacroScope_2030_ = lean_ctor_get(v___x_2028_, 1);
v_ngen_2031_ = lean_ctor_get(v___x_2028_, 2);
v_auxDeclNGen_2032_ = lean_ctor_get(v___x_2028_, 3);
v_traceState_2033_ = lean_ctor_get(v___x_2028_, 4);
v_recordedDeps_2034_ = lean_ctor_get(v___x_2028_, 6);
v_messages_2035_ = lean_ctor_get(v___x_2028_, 7);
v_infoState_2036_ = lean_ctor_get(v___x_2028_, 8);
v_snapshotTasks_2037_ = lean_ctor_get(v___x_2028_, 9);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v___x_2028_, 5);
lean_dec(v_unused_2096_);
v___x_2039_ = v___x_2028_;
v_isShared_2040_ = v_isSharedCheck_2095_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_snapshotTasks_2037_);
lean_inc(v_infoState_2036_);
lean_inc(v_messages_2035_);
lean_inc(v_recordedDeps_2034_);
lean_inc(v_traceState_2033_);
lean_inc(v_auxDeclNGen_2032_);
lean_inc(v_ngen_2031_);
lean_inc(v_nextMacroScope_2030_);
lean_inc(v_env_2029_);
lean_dec(v___x_2028_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2095_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
lean_inc(v___x_1985_);
v___x_2041_ = l_Lean_Meta_addToCompletionBlackList(v_env_2029_, v___x_1985_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 5, v___x_2012_);
lean_ctor_set(v___x_2039_, 0, v___x_2041_);
v___x_2043_ = v___x_2039_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_nextMacroScope_2030_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_ngen_2031_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v_auxDeclNGen_2032_);
lean_ctor_set(v_reuseFailAlloc_2094_, 4, v_traceState_2033_);
lean_ctor_set(v_reuseFailAlloc_2094_, 5, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2094_, 6, v_recordedDeps_2034_);
lean_ctor_set(v_reuseFailAlloc_2094_, 7, v_messages_2035_);
lean_ctor_set(v_reuseFailAlloc_2094_, 8, v_infoState_2036_);
lean_ctor_set(v_reuseFailAlloc_2094_, 9, v_snapshotTasks_2037_);
v___x_2043_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v_mctx_2046_; lean_object* v_zetaDeltaFVarIds_2047_; lean_object* v_postponed_2048_; lean_object* v_diag_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2092_; 
v___x_2044_ = lean_st_ref_put(v_a_1965_, v___x_2043_);
v___x_2045_ = lean_st_ref_take(v_a_1963_);
v_mctx_2046_ = lean_ctor_get(v___x_2045_, 0);
v_zetaDeltaFVarIds_2047_ = lean_ctor_get(v___x_2045_, 2);
v_postponed_2048_ = lean_ctor_get(v___x_2045_, 3);
v_diag_2049_ = lean_ctor_get(v___x_2045_, 4);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v___x_2045_, 1);
lean_dec(v_unused_2093_);
v___x_2051_ = v___x_2045_;
v_isShared_2052_ = v_isSharedCheck_2092_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_diag_2049_);
lean_inc(v_postponed_2048_);
lean_inc(v_zetaDeltaFVarIds_2047_);
lean_inc(v_mctx_2046_);
lean_dec(v___x_2045_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2092_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2024_);
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_mctx_2046_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_zetaDeltaFVarIds_2047_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v_postponed_2048_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v_diag_2049_);
v___x_2054_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v_env_2057_; lean_object* v_nextMacroScope_2058_; lean_object* v_ngen_2059_; lean_object* v_auxDeclNGen_2060_; lean_object* v_traceState_2061_; lean_object* v_recordedDeps_2062_; lean_object* v_messages_2063_; lean_object* v_infoState_2064_; lean_object* v_snapshotTasks_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2089_; 
v___x_2055_ = lean_st_ref_put(v_a_1963_, v___x_2054_);
v___x_2056_ = lean_st_ref_take(v_a_1965_);
v_env_2057_ = lean_ctor_get(v___x_2056_, 0);
v_nextMacroScope_2058_ = lean_ctor_get(v___x_2056_, 1);
v_ngen_2059_ = lean_ctor_get(v___x_2056_, 2);
v_auxDeclNGen_2060_ = lean_ctor_get(v___x_2056_, 3);
v_traceState_2061_ = lean_ctor_get(v___x_2056_, 4);
v_recordedDeps_2062_ = lean_ctor_get(v___x_2056_, 6);
v_messages_2063_ = lean_ctor_get(v___x_2056_, 7);
v_infoState_2064_ = lean_ctor_get(v___x_2056_, 8);
v_snapshotTasks_2065_ = lean_ctor_get(v___x_2056_, 9);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; 
v_unused_2090_ = lean_ctor_get(v___x_2056_, 5);
lean_dec(v_unused_2090_);
v___x_2067_ = v___x_2056_;
v_isShared_2068_ = v_isSharedCheck_2089_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_snapshotTasks_2065_);
lean_inc(v_infoState_2064_);
lean_inc(v_messages_2063_);
lean_inc(v_recordedDeps_2062_);
lean_inc(v_traceState_2061_);
lean_inc(v_auxDeclNGen_2060_);
lean_inc(v_ngen_2059_);
lean_inc(v_nextMacroScope_2058_);
lean_inc(v_env_2057_);
lean_dec(v___x_2056_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2089_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
lean_inc(v___x_1985_);
v___x_2069_ = l_Lean_addProtected(v_env_2057_, v___x_1985_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 5, v___x_2012_);
lean_ctor_set(v___x_2067_, 0, v___x_2069_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_nextMacroScope_2058_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_ngen_2059_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_auxDeclNGen_2060_);
lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_traceState_2061_);
lean_ctor_set(v_reuseFailAlloc_2088_, 5, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2088_, 6, v_recordedDeps_2062_);
lean_ctor_set(v_reuseFailAlloc_2088_, 7, v_messages_2063_);
lean_ctor_set(v_reuseFailAlloc_2088_, 8, v_infoState_2064_);
lean_ctor_set(v_reuseFailAlloc_2088_, 9, v_snapshotTasks_2065_);
v___x_2071_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v_mctx_2074_; lean_object* v_zetaDeltaFVarIds_2075_; lean_object* v_postponed_2076_; lean_object* v_diag_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2086_; 
v___x_2072_ = lean_st_ref_put(v_a_1965_, v___x_2071_);
v___x_2073_ = lean_st_ref_take(v_a_1963_);
v_mctx_2074_ = lean_ctor_get(v___x_2073_, 0);
v_zetaDeltaFVarIds_2075_ = lean_ctor_get(v___x_2073_, 2);
v_postponed_2076_ = lean_ctor_get(v___x_2073_, 3);
v_diag_2077_ = lean_ctor_get(v___x_2073_, 4);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2073_, 1);
lean_dec(v_unused_2087_);
v___x_2079_ = v___x_2073_;
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_diag_2077_);
lean_inc(v_postponed_2076_);
lean_inc(v_zetaDeltaFVarIds_2075_);
lean_inc(v_mctx_2074_);
lean_dec(v___x_2073_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_2024_);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_mctx_2074_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_zetaDeltaFVarIds_2075_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_postponed_2076_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_diag_2077_);
v___x_2082_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_st_ref_put(v_a_1963_, v___x_2082_);
v___x_2084_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_1985_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_2084_;
}
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1985_);
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v___x_1985_);
lean_dec(v_a_1984_);
lean_dec(v_levelParams_1976_);
v_a_2105_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_1986_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_1986_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_levelParams_1976_);
lean_dec(v_indName_1961_);
v_a_2113_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_1983_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_1983_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec(v___x_1979_);
lean_dec_ref(v_type_1977_);
lean_dec(v_levelParams_1976_);
lean_dec(v_name_1975_);
lean_dec(v___x_1971_);
lean_dec_ref(v_val_1970_);
lean_dec(v_indName_1961_);
v___x_2121_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2);
v___x_2122_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2121_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_2122_;
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v___x_1971_);
lean_dec_ref(v_val_1970_);
lean_dec(v_indName_1961_);
v_a_2123_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_1973_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_1973_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v_a_1969_);
lean_dec(v_indName_1961_);
v___x_2131_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3);
v___x_2132_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2131_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_2132_;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_indName_1961_);
v_a_2133_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_1968_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_1968_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_1961_ = stack[0].m_obj;
lean_object* v_a_1962_ = stack[1].m_obj;
lean_object* v_a_1963_ = stack[2].m_obj;
lean_object* v_a_1964_ = stack[3].m_obj;
lean_object* v_a_1965_ = stack[4].m_obj;
lean_object* v_res_2141_;
v_res_2141_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
stack->m_obj
 = v_res_2141_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___boxed(lean_object* v_indName_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
return v_res_2148_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(lean_object* v___x_2149_, lean_object* v_k_2150_, lean_object* v_ctorIdx_2151_, lean_object* v_tail_2152_, lean_object* v___x_2153_, lean_object* v_as_2154_, size_t v_sz_2155_, size_t v_i_2156_, lean_object* v_bs_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_2149_, v_k_2150_, v_ctorIdx_2151_, v_tail_2152_, v___x_2153_, v_sz_2155_, v_i_2156_, v_bs_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
return v___x_2163_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2149_ = stack[0].m_obj;
lean_object* v_k_2150_ = stack[1].m_obj;
lean_object* v_ctorIdx_2151_ = stack[2].m_obj;
lean_object* v_tail_2152_ = stack[3].m_obj;
lean_object* v___x_2153_ = stack[4].m_obj;
lean_object* v_as_2154_ = stack[5].m_obj;
size_t v_sz_2155_ = stack[6].m_num;
size_t v_i_2156_ = stack[7].m_num;
lean_object* v_bs_2157_ = stack[8].m_obj;
lean_object* v___y_2158_ = stack[9].m_obj;
lean_object* v___y_2159_ = stack[10].m_obj;
lean_object* v___y_2160_ = stack[11].m_obj;
lean_object* v___y_2161_ = stack[12].m_obj;
lean_object* v_res_2164_;
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(v___x_2149_, v_k_2150_, v_ctorIdx_2151_, v_tail_2152_, v___x_2153_, v_as_2154_, v_sz_2155_, v_i_2156_, v_bs_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
stack->m_obj
 = v_res_2164_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___boxed(lean_object* v___x_2165_, lean_object* v_k_2166_, lean_object* v_ctorIdx_2167_, lean_object* v_tail_2168_, lean_object* v___x_2169_, lean_object* v_as_2170_, lean_object* v_sz_2171_, lean_object* v_i_2172_, lean_object* v_bs_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
size_t v_sz_boxed_2179_; size_t v_i_boxed_2180_; lean_object* v_res_2181_; 
v_sz_boxed_2179_ = lean_unbox_usize(v_sz_2171_);
lean_dec(v_sz_2171_);
v_i_boxed_2180_ = lean_unbox_usize(v_i_2172_);
lean_dec(v_i_2172_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(v___x_2165_, v_k_2166_, v_ctorIdx_2167_, v_tail_2168_, v___x_2169_, v_as_2170_, v_sz_boxed_2179_, v_i_boxed_2180_, v_bs_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec_ref(v_as_2170_);
lean_dec_ref(v___x_2169_);
return v_res_2181_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(lean_object* v___x_2182_, lean_object* v___x_2183_, lean_object* v___x_2184_, lean_object* v___x_2185_, lean_object* v___x_2186_, lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v___f_2189_, lean_object* v___x_2190_, lean_object* v___y_2191_, uint8_t v___x_2192_, lean_object* v_h_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_inc(v___x_2183_);
v___x_2199_ = l_Lean_mkConst(v___x_2182_, v___x_2183_);
v___x_2200_ = l_Lean_mkAppN(v___x_2199_, v___x_2184_);
lean_inc_ref(v___x_2185_);
v___x_2201_ = l_Lean_Expr_app___override(v___x_2200_, v___x_2185_);
lean_inc_ref(v___x_2186_);
v___x_2202_ = l_Lean_Expr_app___override(v___x_2201_, v___x_2186_);
v___x_2203_ = l_Lean_mkAppN(v___x_2202_, v___x_2187_);
lean_inc_ref(v_h_2193_);
v___x_2204_ = l_Lean_Meta_mkEqSymm(v_h_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2206_ = l_Lean_Expr_app___override(v___x_2203_, v_a_2205_);
v___x_2207_ = l_Lean_mkConst(v___x_2188_, v___x_2183_);
lean_inc_ref(v___x_2185_);
lean_inc_ref(v___x_2184_);
v___x_2208_ = lean_array_push(v___x_2184_, v___x_2185_);
v___x_2209_ = lean_array_push(v___x_2208_, v___x_2186_);
v___x_2210_ = l_Lean_mkAppN(v___x_2207_, v___x_2209_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v___x_2210_, v___f_2189_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2213_ = l_Lean_Expr_app___override(v___x_2206_, v_a_2212_);
v___x_2214_ = lean_mk_empty_array_with_capacity(v___x_2190_);
v___x_2215_ = lean_array_push(v___x_2214_, v___x_2185_);
v___x_2216_ = l_Array_append___redArg(v___x_2184_, v___x_2215_);
lean_dec_ref(v___x_2215_);
v___x_2217_ = l_Array_append___redArg(v___x_2216_, v___x_2187_);
v___x_2218_ = lean_unsigned_to_nat(2u);
v___x_2219_ = lean_mk_empty_array_with_capacity(v___x_2218_);
v___x_2220_ = lean_array_push(v___x_2219_, v_h_2193_);
v___x_2221_ = lean_array_push(v___x_2220_, v___y_2191_);
v___x_2222_ = l_Array_append___redArg(v___x_2217_, v___x_2221_);
lean_dec_ref(v___x_2221_);
v___x_2223_ = 0;
v___x_2224_ = 1;
v___x_2225_ = l_Lean_Meta_mkLambdaFVars(v___x_2222_, v___x_2213_, v___x_2223_, v___x_2192_, v___x_2223_, v___x_2192_, v___x_2224_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec_ref(v___x_2222_);
return v___x_2225_;
}
else
{
lean_dec_ref(v___x_2206_);
lean_dec_ref(v_h_2193_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v___x_2185_);
lean_dec_ref(v___x_2184_);
return v___x_2211_;
}
}
else
{
lean_dec_ref(v___x_2203_);
lean_dec_ref(v_h_2193_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v___f_2189_);
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2186_);
lean_dec_ref(v___x_2185_);
lean_dec_ref(v___x_2184_);
lean_dec(v___x_2183_);
return v___x_2204_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2182_ = stack[0].m_obj;
lean_object* v___x_2183_ = stack[1].m_obj;
lean_object* v___x_2184_ = stack[2].m_obj;
lean_object* v___x_2185_ = stack[3].m_obj;
lean_object* v___x_2186_ = stack[4].m_obj;
lean_object* v___x_2187_ = stack[5].m_obj;
lean_object* v___x_2188_ = stack[6].m_obj;
lean_object* v___f_2189_ = stack[7].m_obj;
lean_object* v___x_2190_ = stack[8].m_obj;
lean_object* v___y_2191_ = stack[9].m_obj;
uint8_t v___x_2192_ = stack[10].m_num;
lean_object* v_h_2193_ = stack[11].m_obj;
lean_object* v___y_2194_ = stack[12].m_obj;
lean_object* v___y_2195_ = stack[13].m_obj;
lean_object* v___y_2196_ = stack[14].m_obj;
lean_object* v___y_2197_ = stack[15].m_obj;
lean_object* v_res_2226_;
v_res_2226_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(v___x_2182_, v___x_2183_, v___x_2184_, v___x_2185_, v___x_2186_, v___x_2187_, v___x_2188_, v___f_2189_, v___x_2190_, v___y_2191_, v___x_2192_, v_h_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_2227_ = _args[0];
lean_object* v___x_2228_ = _args[1];
lean_object* v___x_2229_ = _args[2];
lean_object* v___x_2230_ = _args[3];
lean_object* v___x_2231_ = _args[4];
lean_object* v___x_2232_ = _args[5];
lean_object* v___x_2233_ = _args[6];
lean_object* v___f_2234_ = _args[7];
lean_object* v___x_2235_ = _args[8];
lean_object* v___y_2236_ = _args[9];
lean_object* v___x_2237_ = _args[10];
lean_object* v_h_2238_ = _args[11];
lean_object* v___y_2239_ = _args[12];
lean_object* v___y_2240_ = _args[13];
lean_object* v___y_2241_ = _args[14];
lean_object* v___y_2242_ = _args[15];
lean_object* v___y_2243_ = _args[16];
_start:
{
uint8_t v___x_9997__boxed_2244_; lean_object* v_res_2245_; 
v___x_9997__boxed_2244_ = lean_unbox(v___x_2237_);
v_res_2245_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(v___x_2227_, v___x_2228_, v___x_2229_, v___x_2230_, v___x_2231_, v___x_2232_, v___x_2233_, v___f_2234_, v___x_2235_, v___y_2236_, v___x_9997__boxed_2244_, v_h_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___x_2235_);
lean_dec_ref(v___x_2232_);
return v_res_2245_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(lean_object* v___y_2246_, lean_object* v_x_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___y_2246_);
return v___x_2253_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2246_ = stack[0].m_obj;
lean_object* v_x_2247_ = stack[1].m_obj;
lean_object* v___y_2248_ = stack[2].m_obj;
lean_object* v___y_2249_ = stack[3].m_obj;
lean_object* v___y_2250_ = stack[4].m_obj;
lean_object* v___y_2251_ = stack[5].m_obj;
lean_object* v_res_2254_;
v_res_2254_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(v___y_2246_, v_x_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
stack->m_obj
 = v_res_2254_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2255_, lean_object* v_x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(v___y_2255_, v_x_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v_x_2256_);
return v_res_2262_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(lean_object* v___x_2263_, lean_object* v_numParams_2264_, lean_object* v___x_2265_, lean_object* v___x_2266_, lean_object* v_numIndices_2267_, lean_object* v_indName_2268_, lean_object* v_tail_2269_, lean_object* v_i_2270_, lean_object* v___x_2271_, lean_object* v___x_2272_, lean_object* v___x_2273_, uint8_t v___x_2274_, lean_object* v_xs_2275_, lean_object* v_x_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_start_2291_; lean_object* v_stop_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___y_2297_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
lean_inc(v_numParams_2264_);
lean_inc_ref_n(v_xs_2275_, 2);
v___x_2282_ = l_Array_toSubarray___redArg(v_xs_2275_, v___x_2263_, v_numParams_2264_);
v___x_2283_ = lean_array_get(v___x_2265_, v_xs_2275_, v_numParams_2264_);
v___x_2284_ = lean_nat_add(v_numParams_2264_, v___x_2266_);
lean_dec(v_numParams_2264_);
v___x_2285_ = lean_nat_add(v___x_2284_, v_numIndices_2267_);
lean_inc(v___x_2285_);
v___x_2286_ = l_Array_toSubarray___redArg(v_xs_2275_, v___x_2284_, v___x_2285_);
v___x_2287_ = lean_array_get(v___x_2265_, v_xs_2275_, v___x_2285_);
v___x_2288_ = lean_nat_add(v___x_2285_, v___x_2266_);
lean_dec(v___x_2285_);
v___x_2289_ = lean_array_get_size(v_xs_2275_);
v___x_2290_ = l_Array_toSubarray___redArg(v_xs_2275_, v___x_2288_, v___x_2289_);
v_start_2291_ = lean_ctor_get(v___x_2290_, 1);
v_stop_2292_ = lean_ctor_get(v___x_2290_, 2);
v___x_2293_ = l_Subarray_copy___redArg(v___x_2282_);
v___x_2294_ = l_Subarray_copy___redArg(v___x_2286_);
v___x_2295_ = lean_array_push(v___x_2294_, v___x_2287_);
v___x_2310_ = lean_nat_sub(v_stop_2292_, v_start_2291_);
v___x_2311_ = lean_nat_dec_lt(v_i_2270_, v___x_2310_);
lean_dec(v___x_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; 
lean_dec_ref(v___x_2290_);
v___x_2312_ = l_outOfBounds___redArg(v___x_2265_);
v___y_2297_ = v___x_2312_;
goto v___jp_2296_;
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Subarray_get___redArg(v___x_2290_, v_i_2270_);
lean_dec_ref(v___x_2290_);
v___y_2297_ = v___x_2313_;
goto v___jp_2296_;
}
v___jp_2296_:
{
lean_object* v___f_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; 
lean_inc_ref(v___y_2297_);
v___f_2298_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2298_, 0, v___y_2297_);
v___x_2299_ = l_Lean_mkCtorIdxName(v_indName_2268_);
v___x_2300_ = l_Lean_mkConst(v___x_2299_, v_tail_2269_);
lean_inc_ref(v___x_2293_);
v___x_2301_ = l_Array_append___redArg(v___x_2293_, v___x_2295_);
v___x_2302_ = l_Lean_mkAppN(v___x_2300_, v___x_2301_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = l_Lean_mkRawNatLit(v_i_2270_);
v___x_2304_ = lean_box(v___x_2274_);
lean_inc_ref(v___x_2303_);
v___f_2305_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed), 17, 11);
lean_closure_set(v___f_2305_, 0, v___x_2271_);
lean_closure_set(v___f_2305_, 1, v___x_2272_);
lean_closure_set(v___f_2305_, 2, v___x_2293_);
lean_closure_set(v___f_2305_, 3, v___x_2283_);
lean_closure_set(v___f_2305_, 4, v___x_2303_);
lean_closure_set(v___f_2305_, 5, v___x_2295_);
lean_closure_set(v___f_2305_, 6, v___x_2273_);
lean_closure_set(v___f_2305_, 7, v___f_2298_);
lean_closure_set(v___f_2305_, 8, v___x_2266_);
lean_closure_set(v___f_2305_, 9, v___y_2297_);
lean_closure_set(v___f_2305_, 10, v___x_2304_);
v___x_2306_ = l_Lean_Meta_mkEq(v___x_2302_, v___x_2303_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_2309_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_2308_, v_a_2307_, v___f_2305_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
return v___x_2309_;
}
else
{
lean_dec_ref(v___f_2305_);
return v___x_2306_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2263_ = stack[0].m_obj;
lean_object* v_numParams_2264_ = stack[1].m_obj;
lean_object* v___x_2265_ = stack[2].m_obj;
lean_object* v___x_2266_ = stack[3].m_obj;
lean_object* v_numIndices_2267_ = stack[4].m_obj;
lean_object* v_indName_2268_ = stack[5].m_obj;
lean_object* v_tail_2269_ = stack[6].m_obj;
lean_object* v_i_2270_ = stack[7].m_obj;
lean_object* v___x_2271_ = stack[8].m_obj;
lean_object* v___x_2272_ = stack[9].m_obj;
lean_object* v___x_2273_ = stack[10].m_obj;
uint8_t v___x_2274_ = stack[11].m_num;
lean_object* v_xs_2275_ = stack[12].m_obj;
lean_object* v_x_2276_ = stack[13].m_obj;
lean_object* v___y_2277_ = stack[14].m_obj;
lean_object* v___y_2278_ = stack[15].m_obj;
lean_object* v___y_2279_ = stack[16].m_obj;
lean_object* v___y_2280_ = stack[17].m_obj;
lean_object* v_res_2314_;
v_res_2314_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(v___x_2263_, v_numParams_2264_, v___x_2265_, v___x_2266_, v_numIndices_2267_, v_indName_2268_, v_tail_2269_, v_i_2270_, v___x_2271_, v___x_2272_, v___x_2273_, v___x_2274_, v_xs_2275_, v_x_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
stack->m_obj
 = v_res_2314_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2315_ = _args[0];
lean_object* v_numParams_2316_ = _args[1];
lean_object* v___x_2317_ = _args[2];
lean_object* v___x_2318_ = _args[3];
lean_object* v_numIndices_2319_ = _args[4];
lean_object* v_indName_2320_ = _args[5];
lean_object* v_tail_2321_ = _args[6];
lean_object* v_i_2322_ = _args[7];
lean_object* v___x_2323_ = _args[8];
lean_object* v___x_2324_ = _args[9];
lean_object* v___x_2325_ = _args[10];
lean_object* v___x_2326_ = _args[11];
lean_object* v_xs_2327_ = _args[12];
lean_object* v_x_2328_ = _args[13];
lean_object* v___y_2329_ = _args[14];
lean_object* v___y_2330_ = _args[15];
lean_object* v___y_2331_ = _args[16];
lean_object* v___y_2332_ = _args[17];
lean_object* v___y_2333_ = _args[18];
_start:
{
uint8_t v___x_10198__boxed_2334_; lean_object* v_res_2335_; 
v___x_10198__boxed_2334_ = lean_unbox(v___x_2326_);
v_res_2335_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(v___x_2315_, v_numParams_2316_, v___x_2317_, v___x_2318_, v_numIndices_2319_, v_indName_2320_, v_tail_2321_, v_i_2322_, v___x_2323_, v___x_2324_, v___x_2325_, v___x_10198__boxed_2334_, v_xs_2327_, v_x_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_x_2328_);
lean_dec(v_numIndices_2319_);
lean_dec_ref(v___x_2317_);
return v_res_2335_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0));
v___x_2338_ = l_Lean_stringToMessageData(v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(lean_object* v_attrName_2345_, lean_object* v_declName_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2352_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2353_ = l_Lean_MessageData_ofName(v_attrName_2345_);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = 0;
v___x_2358_ = l_Lean_MessageData_ofConstName(v_declName_2346_, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2356_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2361_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
return v___x_2362_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2345_ = stack[0].m_obj;
lean_object* v_declName_2346_ = stack[1].m_obj;
lean_object* v___y_2347_ = stack[2].m_obj;
lean_object* v___y_2348_ = stack[3].m_obj;
lean_object* v___y_2349_ = stack[4].m_obj;
lean_object* v___y_2350_ = stack[5].m_obj;
lean_object* v_res_2363_;
v_res_2363_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2345_, v_declName_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
stack->m_obj
 = v_res_2363_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_2364_, lean_object* v_declName_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2364_, v_declName_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
return v_res_2371_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2));
v___x_2377_ = l_Lean_stringToMessageData(v___x_2376_);
return v___x_2377_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(lean_object* v_attrName_2378_, lean_object* v_declName_2379_, lean_object* v_asyncPrefix_x3f_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___y_2387_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2380_) == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_MessageData_nil;
v___y_2387_ = v___x_2400_;
goto v___jp_2386_;
}
else
{
lean_object* v_val_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_val_2401_ = lean_ctor_get(v_asyncPrefix_x3f_2380_, 0);
lean_inc(v_val_2401_);
lean_dec_ref_known(v_asyncPrefix_x3f_2380_, 1);
v___x_2402_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3);
v___x_2403_ = l_Lean_MessageData_ofName(v_val_2401_);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___y_2387_ = v___x_2406_;
goto v___jp_2386_;
}
v___jp_2386_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2388_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2389_ = l_Lean_MessageData_ofName(v_attrName_2378_);
v___x_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = 0;
v___x_2394_ = l_Lean_MessageData_ofConstName(v_declName_2379_, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2392_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v___y_2387_);
v___x_2399_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2398_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
return v___x_2399_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2378_ = stack[0].m_obj;
lean_object* v_declName_2379_ = stack[1].m_obj;
lean_object* v_asyncPrefix_x3f_2380_ = stack[2].m_obj;
lean_object* v___y_2381_ = stack[3].m_obj;
lean_object* v___y_2382_ = stack[4].m_obj;
lean_object* v___y_2383_ = stack[5].m_obj;
lean_object* v___y_2384_ = stack[6].m_obj;
lean_object* v_res_2407_;
v_res_2407_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2378_, v_declName_2379_, v_asyncPrefix_x3f_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
stack->m_obj
 = v_res_2407_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_2408_, lean_object* v_declName_2409_, lean_object* v_asyncPrefix_x3f_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2408_, v_declName_2409_, v_asyncPrefix_x3f_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0(lean_object* v_addEntryFn_2417_, lean_object* v_decl_2418_, lean_object* v_s_2419_){
_start:
{
lean_object* v_importedEntries_2420_; lean_object* v_state_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2429_; 
v_importedEntries_2420_ = lean_ctor_get(v_s_2419_, 0);
v_state_2421_ = lean_ctor_get(v_s_2419_, 1);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_s_2419_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2423_ = v_s_2419_;
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_state_2421_);
lean_inc(v_importedEntries_2420_);
lean_dec(v_s_2419_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v_state_2425_; lean_object* v___x_2427_; 
v_state_2425_ = lean_apply_2(v_addEntryFn_2417_, v_state_2421_, v_decl_2418_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v_state_2425_);
v___x_2427_ = v___x_2423_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_importedEntries_2420_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_state_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(lean_object* v_attr_2430_, lean_object* v_decl_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___x_2492_; lean_object* v_env_2493_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___x_2508_; 
v___x_2492_ = lean_st_ref_get(v___y_2435_);
v_env_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc_ref(v_env_2493_);
lean_dec(v___x_2492_);
v___x_2508_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2493_, v_decl_2431_);
if (lean_obj_tag(v___x_2508_) == 0)
{
v___y_2495_ = v___y_2432_;
v___y_2496_ = v___y_2433_;
v___y_2497_ = v___y_2434_;
v___y_2498_ = v___y_2435_;
goto v___jp_2494_;
}
else
{
lean_object* v_attr_2509_; lean_object* v_toAttributeImplCore_2510_; lean_object* v_name_2511_; lean_object* v___x_2512_; 
lean_dec_ref_known(v___x_2508_, 1);
lean_dec_ref(v_env_2493_);
v_attr_2509_ = lean_ctor_get(v_attr_2430_, 0);
lean_inc_ref(v_attr_2509_);
lean_dec_ref(v_attr_2430_);
v_toAttributeImplCore_2510_ = lean_ctor_get(v_attr_2509_, 0);
lean_inc_ref(v_toAttributeImplCore_2510_);
lean_dec_ref(v_attr_2509_);
v_name_2511_ = lean_ctor_get(v_toAttributeImplCore_2510_, 1);
lean_inc(v_name_2511_);
lean_dec_ref(v_toAttributeImplCore_2510_);
v___x_2512_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_name_2511_, v_decl_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
return v___x_2512_;
}
v___jp_2437_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v_mctx_2453_; lean_object* v_zetaDeltaFVarIds_2454_; lean_object* v_postponed_2455_; lean_object* v_diag_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2467_; 
v___x_2449_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
v___x_2450_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2450_, 0, v___y_2448_);
lean_ctor_set(v___x_2450_, 1, v___y_2443_);
lean_ctor_set(v___x_2450_, 2, v___y_2447_);
lean_ctor_set(v___x_2450_, 3, v___y_2444_);
lean_ctor_set(v___x_2450_, 4, v___y_2445_);
lean_ctor_set(v___x_2450_, 5, v___x_2449_);
lean_ctor_set(v___x_2450_, 6, v___y_2440_);
lean_ctor_set(v___x_2450_, 7, v___y_2442_);
lean_ctor_set(v___x_2450_, 8, v___y_2439_);
lean_ctor_set(v___x_2450_, 9, v___y_2438_);
v___x_2451_ = lean_st_ref_put(v___y_2446_, v___x_2450_);
v___x_2452_ = lean_st_ref_take(v___y_2441_);
v_mctx_2453_ = lean_ctor_get(v___x_2452_, 0);
v_zetaDeltaFVarIds_2454_ = lean_ctor_get(v___x_2452_, 2);
v_postponed_2455_ = lean_ctor_get(v___x_2452_, 3);
v_diag_2456_ = lean_ctor_get(v___x_2452_, 4);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v___x_2452_, 1);
lean_dec(v_unused_2468_);
v___x_2458_ = v___x_2452_;
v_isShared_2459_ = v_isSharedCheck_2467_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_diag_2456_);
lean_inc(v_postponed_2455_);
lean_inc(v_zetaDeltaFVarIds_2454_);
lean_inc(v_mctx_2453_);
lean_dec(v___x_2452_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2467_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2460_ = lean_box(0);
v___x_2461_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v___x_2461_);
v___x_2463_ = v___x_2458_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_mctx_2453_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v_zetaDeltaFVarIds_2454_);
lean_ctor_set(v_reuseFailAlloc_2466_, 3, v_postponed_2455_);
lean_ctor_set(v_reuseFailAlloc_2466_, 4, v_diag_2456_);
v___x_2463_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_st_ref_put(v___y_2441_, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2460_);
return v___x_2465_;
}
}
}
v___jp_2469_:
{
lean_object* v___x_2472_; lean_object* v_ext_2473_; lean_object* v_toEnvExtension_2474_; lean_object* v_env_2475_; lean_object* v_nextMacroScope_2476_; lean_object* v_ngen_2477_; lean_object* v_auxDeclNGen_2478_; lean_object* v_traceState_2479_; lean_object* v_recordedDeps_2480_; lean_object* v_messages_2481_; lean_object* v_infoState_2482_; lean_object* v_snapshotTasks_2483_; lean_object* v_addEntryFn_2484_; lean_object* v_asyncMode_2485_; uint8_t v_logWrites_2486_; lean_object* v___f_2487_; uint8_t v___x_2488_; 
v___x_2472_ = lean_st_ref_take(v___y_2471_);
v_ext_2473_ = lean_ctor_get(v_attr_2430_, 1);
lean_inc_ref(v_ext_2473_);
lean_dec_ref(v_attr_2430_);
v_toEnvExtension_2474_ = lean_ctor_get(v_ext_2473_, 0);
lean_inc_ref(v_toEnvExtension_2474_);
v_env_2475_ = lean_ctor_get(v___x_2472_, 0);
lean_inc_ref(v_env_2475_);
v_nextMacroScope_2476_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_nextMacroScope_2476_);
v_ngen_2477_ = lean_ctor_get(v___x_2472_, 2);
lean_inc_ref(v_ngen_2477_);
v_auxDeclNGen_2478_ = lean_ctor_get(v___x_2472_, 3);
lean_inc_ref(v_auxDeclNGen_2478_);
v_traceState_2479_ = lean_ctor_get(v___x_2472_, 4);
lean_inc_ref(v_traceState_2479_);
v_recordedDeps_2480_ = lean_ctor_get(v___x_2472_, 6);
lean_inc_ref(v_recordedDeps_2480_);
v_messages_2481_ = lean_ctor_get(v___x_2472_, 7);
lean_inc_ref(v_messages_2481_);
v_infoState_2482_ = lean_ctor_get(v___x_2472_, 8);
lean_inc_ref(v_infoState_2482_);
v_snapshotTasks_2483_ = lean_ctor_get(v___x_2472_, 9);
lean_inc_ref(v_snapshotTasks_2483_);
lean_dec(v___x_2472_);
v_addEntryFn_2484_ = lean_ctor_get(v_ext_2473_, 3);
lean_inc(v_addEntryFn_2484_);
lean_dec_ref(v_ext_2473_);
v_asyncMode_2485_ = lean_ctor_get(v_toEnvExtension_2474_, 2);
lean_inc(v_asyncMode_2485_);
v_logWrites_2486_ = lean_ctor_get_uint8(v_toEnvExtension_2474_, sizeof(void*)*6);
lean_inc(v_decl_2431_);
v___f_2487_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2487_, 0, v_addEntryFn_2484_);
lean_closure_set(v___f_2487_, 1, v_decl_2431_);
v___x_2488_ = 1;
if (v_logWrites_2486_ == 0)
{
lean_object* v___x_2489_; 
v___x_2489_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2474_, v_env_2475_, v___f_2487_, v_asyncMode_2485_, v_decl_2431_, v___x_2488_);
lean_dec(v_asyncMode_2485_);
v___y_2438_ = v_snapshotTasks_2483_;
v___y_2439_ = v_infoState_2482_;
v___y_2440_ = v_recordedDeps_2480_;
v___y_2441_ = v___y_2470_;
v___y_2442_ = v_messages_2481_;
v___y_2443_ = v_nextMacroScope_2476_;
v___y_2444_ = v_auxDeclNGen_2478_;
v___y_2445_ = v_traceState_2479_;
v___y_2446_ = v___y_2471_;
v___y_2447_ = v_ngen_2477_;
v___y_2448_ = v___x_2489_;
goto v___jp_2437_;
}
else
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_inc_ref(v_toEnvExtension_2474_);
v___x_2490_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2474_, v_env_2475_);
lean_dec_ref(v_env_2475_);
v___x_2491_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2474_, v___x_2490_, v___f_2487_, v_asyncMode_2485_, v_decl_2431_, v___x_2488_);
lean_dec(v_asyncMode_2485_);
v___y_2438_ = v_snapshotTasks_2483_;
v___y_2439_ = v_infoState_2482_;
v___y_2440_ = v_recordedDeps_2480_;
v___y_2441_ = v___y_2470_;
v___y_2442_ = v_messages_2481_;
v___y_2443_ = v_nextMacroScope_2476_;
v___y_2444_ = v_auxDeclNGen_2478_;
v___y_2445_ = v_traceState_2479_;
v___y_2446_ = v___y_2471_;
v___y_2447_ = v_ngen_2477_;
v___y_2448_ = v___x_2491_;
goto v___jp_2437_;
}
}
v___jp_2494_:
{
lean_object* v_ext_2499_; lean_object* v_toEnvExtension_2500_; lean_object* v_attr_2501_; lean_object* v_asyncMode_2502_; uint8_t v___x_2503_; 
v_ext_2499_ = lean_ctor_get(v_attr_2430_, 1);
v_toEnvExtension_2500_ = lean_ctor_get(v_ext_2499_, 0);
v_attr_2501_ = lean_ctor_get(v_attr_2430_, 0);
v_asyncMode_2502_ = lean_ctor_get(v_toEnvExtension_2500_, 2);
lean_inc(v_decl_2431_);
lean_inc_ref(v_env_2493_);
v___x_2503_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2493_, v_decl_2431_, v_asyncMode_2502_);
if (v___x_2503_ == 0)
{
lean_object* v_toAttributeImplCore_2504_; lean_object* v_name_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_inc_ref(v_attr_2501_);
lean_dec_ref(v_attr_2430_);
v_toAttributeImplCore_2504_ = lean_ctor_get(v_attr_2501_, 0);
lean_inc_ref(v_toAttributeImplCore_2504_);
lean_dec_ref(v_attr_2501_);
v_name_2505_ = lean_ctor_get(v_toAttributeImplCore_2504_, 1);
lean_inc(v_name_2505_);
lean_dec_ref(v_toAttributeImplCore_2504_);
v___x_2506_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2493_);
v___x_2507_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_name_2505_, v_decl_2431_, v___x_2506_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2507_;
}
else
{
lean_dec_ref(v_env_2493_);
v___y_2470_ = v___y_2496_;
v___y_2471_ = v___y_2498_;
goto v___jp_2469_;
}
}
}
}
LEAN_EXPORT void l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_attr_2430_ = stack[0].m_obj;
lean_object* v_decl_2431_ = stack[1].m_obj;
lean_object* v___y_2432_ = stack[2].m_obj;
lean_object* v___y_2433_ = stack[3].m_obj;
lean_object* v___y_2434_ = stack[4].m_obj;
lean_object* v___y_2435_ = stack[5].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v_attr_2430_, v_decl_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___boxed(lean_object* v_attr_2514_, lean_object* v_decl_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v_attr_2514_, v_decl_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2521_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(lean_object* v_val_2522_, lean_object* v_indName_2523_, lean_object* v_tail_2524_, lean_object* v___x_2525_, lean_object* v___x_2526_, lean_object* v___x_2527_, lean_object* v_a_2528_, lean_object* v_range_2529_, lean_object* v_b_2530_, lean_object* v_i_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_stop_2537_; lean_object* v_step_2538_; uint8_t v___x_2539_; 
v_stop_2537_ = lean_ctor_get(v_range_2529_, 1);
v_step_2538_ = lean_ctor_get(v_range_2529_, 2);
v___x_2539_ = lean_nat_dec_lt(v_i_2531_, v_stop_2537_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; 
lean_dec(v_i_2531_);
lean_dec_ref(v_a_2528_);
lean_dec(v___x_2527_);
lean_dec(v___x_2526_);
lean_dec(v___x_2525_);
lean_dec(v_tail_2524_);
lean_dec(v_indName_2523_);
lean_dec_ref(v_val_2522_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_b_2530_);
return v___x_2540_;
}
else
{
lean_object* v_numParams_2541_; lean_object* v_numIndices_2542_; lean_object* v_ctors_2543_; lean_object* v_levelParams_2544_; lean_object* v_type_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; 
v_numParams_2541_ = lean_ctor_get(v_val_2522_, 1);
v_numIndices_2542_ = lean_ctor_get(v_val_2522_, 2);
v_ctors_2543_ = lean_ctor_get(v_val_2522_, 4);
v_levelParams_2544_ = lean_ctor_get(v_a_2528_, 1);
v_type_2545_ = lean_ctor_get(v_a_2528_, 2);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = l_Lean_instInhabitedExpr;
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_box(0);
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_box(v___x_2539_);
lean_inc(v___x_2527_);
lean_inc(v___x_2526_);
lean_inc(v___x_2525_);
lean_inc_n(v_i_2531_, 2);
lean_inc(v_tail_2524_);
lean_inc(v_indName_2523_);
lean_inc(v_numIndices_2542_);
lean_inc(v_numParams_2541_);
v___f_2552_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed), 19, 12);
lean_closure_set(v___f_2552_, 0, v___x_2546_);
lean_closure_set(v___f_2552_, 1, v_numParams_2541_);
lean_closure_set(v___f_2552_, 2, v___x_2547_);
lean_closure_set(v___f_2552_, 3, v___x_2548_);
lean_closure_set(v___f_2552_, 4, v_numIndices_2542_);
lean_closure_set(v___f_2552_, 5, v_indName_2523_);
lean_closure_set(v___f_2552_, 6, v_tail_2524_);
lean_closure_set(v___f_2552_, 7, v_i_2531_);
lean_closure_set(v___f_2552_, 8, v___x_2525_);
lean_closure_set(v___f_2552_, 9, v___x_2526_);
lean_closure_set(v___f_2552_, 10, v___x_2527_);
lean_closure_set(v___f_2552_, 11, v___x_2551_);
v___x_2553_ = l_List_get_x21Internal___redArg(v___x_2549_, v_ctors_2543_, v_i_2531_);
v___x_2554_ = l_Lean_mkConstructorElimName(v_indName_2523_, v___x_2553_);
v___x_2555_ = 0;
lean_inc_ref(v_type_2545_);
v___x_2556_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_2545_, v___f_2552_, v___x_2555_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_n(v_a_2557_, 2);
lean_dec_ref_known(v___x_2556_, 1);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
v___x_2558_ = lean_infer_type(v_a_2557_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2713_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = lean_box(1);
lean_inc(v_levelParams_2544_);
lean_inc(v___x_2554_);
v___x_2561_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_2554_, v_levelParams_2544_, v_a_2559_, v_a_2557_, v___x_2560_, v___y_2535_);
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2713_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2713_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 1);
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_addAndCompile(v___x_2567_, v___x_2539_, v___x_2555_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2569_; lean_object* v_env_2570_; lean_object* v_nextMacroScope_2571_; lean_object* v_ngen_2572_; lean_object* v_auxDeclNGen_2573_; lean_object* v_traceState_2574_; lean_object* v_recordedDeps_2575_; lean_object* v_messages_2576_; lean_object* v_infoState_2577_; lean_object* v_snapshotTasks_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref_known(v___x_2568_, 1);
v___x_2569_ = lean_st_ref_take(v___y_2535_);
v_env_2570_ = lean_ctor_get(v___x_2569_, 0);
v_nextMacroScope_2571_ = lean_ctor_get(v___x_2569_, 1);
v_ngen_2572_ = lean_ctor_get(v___x_2569_, 2);
v_auxDeclNGen_2573_ = lean_ctor_get(v___x_2569_, 3);
v_traceState_2574_ = lean_ctor_get(v___x_2569_, 4);
v_recordedDeps_2575_ = lean_ctor_get(v___x_2569_, 6);
v_messages_2576_ = lean_ctor_get(v___x_2569_, 7);
v_infoState_2577_ = lean_ctor_get(v___x_2569_, 8);
v_snapshotTasks_2578_ = lean_ctor_get(v___x_2569_, 9);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; 
v_unused_2711_ = lean_ctor_get(v___x_2569_, 5);
lean_dec(v_unused_2711_);
v___x_2580_ = v___x_2569_;
v_isShared_2581_ = v_isSharedCheck_2710_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_snapshotTasks_2578_);
lean_inc(v_infoState_2577_);
lean_inc(v_messages_2576_);
lean_inc(v_recordedDeps_2575_);
lean_inc(v_traceState_2574_);
lean_inc(v_auxDeclNGen_2573_);
lean_inc(v_ngen_2572_);
lean_inc(v_nextMacroScope_2571_);
lean_inc(v_env_2570_);
lean_dec(v___x_2569_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2710_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_inc(v___x_2554_);
v___x_2582_ = l_Lean_markAuxRecursor(v_env_2570_, v___x_2554_);
v___x_2583_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 5, v___x_2583_);
lean_ctor_set(v___x_2580_, 0, v___x_2582_);
v___x_2585_ = v___x_2580_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_nextMacroScope_2571_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_ngen_2572_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_auxDeclNGen_2573_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_traceState_2574_);
lean_ctor_set(v_reuseFailAlloc_2709_, 5, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2709_, 6, v_recordedDeps_2575_);
lean_ctor_set(v_reuseFailAlloc_2709_, 7, v_messages_2576_);
lean_ctor_set(v_reuseFailAlloc_2709_, 8, v_infoState_2577_);
lean_ctor_set(v_reuseFailAlloc_2709_, 9, v_snapshotTasks_2578_);
v___x_2585_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v_mctx_2588_; lean_object* v_zetaDeltaFVarIds_2589_; lean_object* v_postponed_2590_; lean_object* v_diag_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2707_; 
v___x_2586_ = lean_st_ref_put(v___y_2535_, v___x_2585_);
v___x_2587_ = lean_st_ref_take(v___y_2533_);
v_mctx_2588_ = lean_ctor_get(v___x_2587_, 0);
v_zetaDeltaFVarIds_2589_ = lean_ctor_get(v___x_2587_, 2);
v_postponed_2590_ = lean_ctor_get(v___x_2587_, 3);
v_diag_2591_ = lean_ctor_get(v___x_2587_, 4);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v___x_2587_, 1);
lean_dec(v_unused_2708_);
v___x_2593_ = v___x_2587_;
v_isShared_2594_ = v_isSharedCheck_2707_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_diag_2591_);
lean_inc(v_postponed_2590_);
lean_inc(v_zetaDeltaFVarIds_2589_);
lean_inc(v_mctx_2588_);
lean_dec(v___x_2587_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2707_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_mctx_2588_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_zetaDeltaFVarIds_2589_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v_postponed_2590_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_diag_2591_);
v___x_2597_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v_env_2600_; lean_object* v_nextMacroScope_2601_; lean_object* v_ngen_2602_; lean_object* v_auxDeclNGen_2603_; lean_object* v_traceState_2604_; lean_object* v_recordedDeps_2605_; lean_object* v_messages_2606_; lean_object* v_infoState_2607_; lean_object* v_snapshotTasks_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2704_; 
v___x_2598_ = lean_st_ref_put(v___y_2533_, v___x_2597_);
v___x_2599_ = lean_st_ref_take(v___y_2535_);
v_env_2600_ = lean_ctor_get(v___x_2599_, 0);
v_nextMacroScope_2601_ = lean_ctor_get(v___x_2599_, 1);
v_ngen_2602_ = lean_ctor_get(v___x_2599_, 2);
v_auxDeclNGen_2603_ = lean_ctor_get(v___x_2599_, 3);
v_traceState_2604_ = lean_ctor_get(v___x_2599_, 4);
v_recordedDeps_2605_ = lean_ctor_get(v___x_2599_, 6);
v_messages_2606_ = lean_ctor_get(v___x_2599_, 7);
v_infoState_2607_ = lean_ctor_get(v___x_2599_, 8);
v_snapshotTasks_2608_ = lean_ctor_get(v___x_2599_, 9);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v___x_2599_, 5);
lean_dec(v_unused_2705_);
v___x_2610_ = v___x_2599_;
v_isShared_2611_ = v_isSharedCheck_2704_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_snapshotTasks_2608_);
lean_inc(v_infoState_2607_);
lean_inc(v_messages_2606_);
lean_inc(v_recordedDeps_2605_);
lean_inc(v_traceState_2604_);
lean_inc(v_auxDeclNGen_2603_);
lean_inc(v_ngen_2602_);
lean_inc(v_nextMacroScope_2601_);
lean_inc(v_env_2600_);
lean_dec(v___x_2599_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2704_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_inc(v___x_2554_);
v___x_2612_ = l_Lean_markSparseCasesOn(v_env_2600_, v___x_2554_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 5, v___x_2583_);
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_nextMacroScope_2601_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_ngen_2602_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_auxDeclNGen_2603_);
lean_ctor_set(v_reuseFailAlloc_2703_, 4, v_traceState_2604_);
lean_ctor_set(v_reuseFailAlloc_2703_, 5, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2703_, 6, v_recordedDeps_2605_);
lean_ctor_set(v_reuseFailAlloc_2703_, 7, v_messages_2606_);
lean_ctor_set(v_reuseFailAlloc_2703_, 8, v_infoState_2607_);
lean_ctor_set(v_reuseFailAlloc_2703_, 9, v_snapshotTasks_2608_);
v___x_2614_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v_mctx_2617_; lean_object* v_zetaDeltaFVarIds_2618_; lean_object* v_postponed_2619_; lean_object* v_diag_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2701_; 
v___x_2615_ = lean_st_ref_put(v___y_2535_, v___x_2614_);
v___x_2616_ = lean_st_ref_take(v___y_2533_);
v_mctx_2617_ = lean_ctor_get(v___x_2616_, 0);
v_zetaDeltaFVarIds_2618_ = lean_ctor_get(v___x_2616_, 2);
v_postponed_2619_ = lean_ctor_get(v___x_2616_, 3);
v_diag_2620_ = lean_ctor_get(v___x_2616_, 4);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v___x_2616_, 1);
lean_dec(v_unused_2702_);
v___x_2622_ = v___x_2616_;
v_isShared_2623_ = v_isSharedCheck_2701_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_diag_2620_);
lean_inc(v_postponed_2619_);
lean_inc(v_zetaDeltaFVarIds_2618_);
lean_inc(v_mctx_2617_);
lean_dec(v___x_2616_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2701_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 1, v___x_2595_);
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_mctx_2617_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_zetaDeltaFVarIds_2618_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_postponed_2619_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_diag_2620_);
v___x_2625_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v_env_2628_; lean_object* v_nextMacroScope_2629_; lean_object* v_ngen_2630_; lean_object* v_auxDeclNGen_2631_; lean_object* v_traceState_2632_; lean_object* v_recordedDeps_2633_; lean_object* v_messages_2634_; lean_object* v_infoState_2635_; lean_object* v_snapshotTasks_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2698_; 
v___x_2626_ = lean_st_ref_put(v___y_2533_, v___x_2625_);
v___x_2627_ = lean_st_ref_take(v___y_2535_);
v_env_2628_ = lean_ctor_get(v___x_2627_, 0);
v_nextMacroScope_2629_ = lean_ctor_get(v___x_2627_, 1);
v_ngen_2630_ = lean_ctor_get(v___x_2627_, 2);
v_auxDeclNGen_2631_ = lean_ctor_get(v___x_2627_, 3);
v_traceState_2632_ = lean_ctor_get(v___x_2627_, 4);
v_recordedDeps_2633_ = lean_ctor_get(v___x_2627_, 6);
v_messages_2634_ = lean_ctor_get(v___x_2627_, 7);
v_infoState_2635_ = lean_ctor_get(v___x_2627_, 8);
v_snapshotTasks_2636_ = lean_ctor_get(v___x_2627_, 9);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2627_, 5);
lean_dec(v_unused_2699_);
v___x_2638_ = v___x_2627_;
v_isShared_2639_ = v_isSharedCheck_2698_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_snapshotTasks_2636_);
lean_inc(v_infoState_2635_);
lean_inc(v_messages_2634_);
lean_inc(v_recordedDeps_2633_);
lean_inc(v_traceState_2632_);
lean_inc(v_auxDeclNGen_2631_);
lean_inc(v_ngen_2630_);
lean_inc(v_nextMacroScope_2629_);
lean_inc(v_env_2628_);
lean_dec(v___x_2627_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2698_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
lean_inc(v___x_2554_);
v___x_2640_ = l_Lean_Meta_addToCompletionBlackList(v_env_2628_, v___x_2554_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 5, v___x_2583_);
lean_ctor_set(v___x_2638_, 0, v___x_2640_);
v___x_2642_ = v___x_2638_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_nextMacroScope_2629_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_ngen_2630_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_auxDeclNGen_2631_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v_traceState_2632_);
lean_ctor_set(v_reuseFailAlloc_2697_, 5, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2697_, 6, v_recordedDeps_2633_);
lean_ctor_set(v_reuseFailAlloc_2697_, 7, v_messages_2634_);
lean_ctor_set(v_reuseFailAlloc_2697_, 8, v_infoState_2635_);
lean_ctor_set(v_reuseFailAlloc_2697_, 9, v_snapshotTasks_2636_);
v___x_2642_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v_mctx_2645_; lean_object* v_zetaDeltaFVarIds_2646_; lean_object* v_postponed_2647_; lean_object* v_diag_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2695_; 
v___x_2643_ = lean_st_ref_put(v___y_2535_, v___x_2642_);
v___x_2644_ = lean_st_ref_take(v___y_2533_);
v_mctx_2645_ = lean_ctor_get(v___x_2644_, 0);
v_zetaDeltaFVarIds_2646_ = lean_ctor_get(v___x_2644_, 2);
v_postponed_2647_ = lean_ctor_get(v___x_2644_, 3);
v_diag_2648_ = lean_ctor_get(v___x_2644_, 4);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v___x_2644_, 1);
lean_dec(v_unused_2696_);
v___x_2650_ = v___x_2644_;
v_isShared_2651_ = v_isSharedCheck_2695_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_diag_2648_);
lean_inc(v_postponed_2647_);
lean_inc(v_zetaDeltaFVarIds_2646_);
lean_inc(v_mctx_2645_);
lean_dec(v___x_2644_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2695_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v___x_2595_);
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_mctx_2645_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_zetaDeltaFVarIds_2646_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_postponed_2647_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v_diag_2648_);
v___x_2653_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v_env_2656_; lean_object* v_nextMacroScope_2657_; lean_object* v_ngen_2658_; lean_object* v_auxDeclNGen_2659_; lean_object* v_traceState_2660_; lean_object* v_recordedDeps_2661_; lean_object* v_messages_2662_; lean_object* v_infoState_2663_; lean_object* v_snapshotTasks_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2692_; 
v___x_2654_ = lean_st_ref_put(v___y_2533_, v___x_2653_);
v___x_2655_ = lean_st_ref_take(v___y_2535_);
v_env_2656_ = lean_ctor_get(v___x_2655_, 0);
v_nextMacroScope_2657_ = lean_ctor_get(v___x_2655_, 1);
v_ngen_2658_ = lean_ctor_get(v___x_2655_, 2);
v_auxDeclNGen_2659_ = lean_ctor_get(v___x_2655_, 3);
v_traceState_2660_ = lean_ctor_get(v___x_2655_, 4);
v_recordedDeps_2661_ = lean_ctor_get(v___x_2655_, 6);
v_messages_2662_ = lean_ctor_get(v___x_2655_, 7);
v_infoState_2663_ = lean_ctor_get(v___x_2655_, 8);
v_snapshotTasks_2664_ = lean_ctor_get(v___x_2655_, 9);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v___x_2655_, 5);
lean_dec(v_unused_2693_);
v___x_2666_ = v___x_2655_;
v_isShared_2667_ = v_isSharedCheck_2692_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_snapshotTasks_2664_);
lean_inc(v_infoState_2663_);
lean_inc(v_messages_2662_);
lean_inc(v_recordedDeps_2661_);
lean_inc(v_traceState_2660_);
lean_inc(v_auxDeclNGen_2659_);
lean_inc(v_ngen_2658_);
lean_inc(v_nextMacroScope_2657_);
lean_inc(v_env_2656_);
lean_dec(v___x_2655_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2692_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_inc(v___x_2554_);
v___x_2668_ = l_Lean_addProtected(v_env_2656_, v___x_2554_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 5, v___x_2583_);
lean_ctor_set(v___x_2666_, 0, v___x_2668_);
v___x_2670_ = v___x_2666_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_nextMacroScope_2657_);
lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_ngen_2658_);
lean_ctor_set(v_reuseFailAlloc_2691_, 3, v_auxDeclNGen_2659_);
lean_ctor_set(v_reuseFailAlloc_2691_, 4, v_traceState_2660_);
lean_ctor_set(v_reuseFailAlloc_2691_, 5, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2691_, 6, v_recordedDeps_2661_);
lean_ctor_set(v_reuseFailAlloc_2691_, 7, v_messages_2662_);
lean_ctor_set(v_reuseFailAlloc_2691_, 8, v_infoState_2663_);
lean_ctor_set(v_reuseFailAlloc_2691_, 9, v_snapshotTasks_2664_);
v___x_2670_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v_mctx_2673_; lean_object* v_zetaDeltaFVarIds_2674_; lean_object* v_postponed_2675_; lean_object* v_diag_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2689_; 
v___x_2671_ = lean_st_ref_put(v___y_2535_, v___x_2670_);
v___x_2672_ = lean_st_ref_take(v___y_2533_);
v_mctx_2673_ = lean_ctor_get(v___x_2672_, 0);
v_zetaDeltaFVarIds_2674_ = lean_ctor_get(v___x_2672_, 2);
v_postponed_2675_ = lean_ctor_get(v___x_2672_, 3);
v_diag_2676_ = lean_ctor_get(v___x_2672_, 4);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v___x_2672_, 1);
lean_dec(v_unused_2690_);
v___x_2678_ = v___x_2672_;
v_isShared_2679_ = v_isSharedCheck_2689_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_diag_2676_);
lean_inc(v_postponed_2675_);
lean_inc(v_zetaDeltaFVarIds_2674_);
lean_inc(v_mctx_2673_);
lean_dec(v___x_2672_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2689_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2595_);
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_mctx_2673_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v_zetaDeltaFVarIds_2674_);
lean_ctor_set(v_reuseFailAlloc_2688_, 3, v_postponed_2675_);
lean_ctor_set(v_reuseFailAlloc_2688_, 4, v_diag_2676_);
v___x_2681_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_st_ref_put(v___y_2533_, v___x_2681_);
v___x_2683_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v___x_2554_);
v___x_2684_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v___x_2683_, v___x_2554_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_dec_ref_known(v___x_2684_, 1);
v___x_2685_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_2554_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec_ref(v___x_2685_);
v___x_2686_ = lean_nat_add(v_i_2531_, v_step_2538_);
lean_dec(v_i_2531_);
v_b_2530_ = v___x_2550_;
v_i_2531_ = v___x_2686_;
goto _start;
}
else
{
lean_dec(v___x_2554_);
lean_dec(v_i_2531_);
lean_dec_ref(v_a_2528_);
lean_dec(v___x_2527_);
lean_dec(v___x_2526_);
lean_dec(v___x_2525_);
lean_dec(v_tail_2524_);
lean_dec(v_indName_2523_);
lean_dec_ref(v_val_2522_);
return v___x_2684_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2554_);
lean_dec(v_i_2531_);
lean_dec_ref(v_a_2528_);
lean_dec(v___x_2527_);
lean_dec(v___x_2526_);
lean_dec(v___x_2525_);
lean_dec(v_tail_2524_);
lean_dec(v_indName_2523_);
lean_dec_ref(v_val_2522_);
return v___x_2568_;
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2557_);
lean_dec(v___x_2554_);
lean_dec(v_i_2531_);
lean_dec_ref(v_a_2528_);
lean_dec(v___x_2527_);
lean_dec(v___x_2526_);
lean_dec(v___x_2525_);
lean_dec(v_tail_2524_);
lean_dec(v_indName_2523_);
lean_dec_ref(v_val_2522_);
v_a_2714_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2558_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2558_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___x_2554_);
lean_dec(v_i_2531_);
lean_dec_ref(v_a_2528_);
lean_dec(v___x_2527_);
lean_dec(v___x_2526_);
lean_dec(v___x_2525_);
lean_dec(v_tail_2524_);
lean_dec(v_indName_2523_);
lean_dec_ref(v_val_2522_);
v_a_2722_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2556_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2556_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2522_ = stack[0].m_obj;
lean_object* v_indName_2523_ = stack[1].m_obj;
lean_object* v_tail_2524_ = stack[2].m_obj;
lean_object* v___x_2525_ = stack[3].m_obj;
lean_object* v___x_2526_ = stack[4].m_obj;
lean_object* v___x_2527_ = stack[5].m_obj;
lean_object* v_a_2528_ = stack[6].m_obj;
lean_object* v_range_2529_ = stack[7].m_obj;
lean_object* v_b_2530_ = stack[8].m_obj;
lean_object* v_i_2531_ = stack[9].m_obj;
lean_object* v___y_2532_ = stack[10].m_obj;
lean_object* v___y_2533_ = stack[11].m_obj;
lean_object* v___y_2534_ = stack[12].m_obj;
lean_object* v___y_2535_ = stack[13].m_obj;
lean_object* v_res_2730_;
v_res_2730_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2522_, v_indName_2523_, v_tail_2524_, v___x_2525_, v___x_2526_, v___x_2527_, v_a_2528_, v_range_2529_, v_b_2530_, v_i_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
stack->m_obj
 = v_res_2730_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___boxed(lean_object* v_val_2731_, lean_object* v_indName_2732_, lean_object* v_tail_2733_, lean_object* v___x_2734_, lean_object* v___x_2735_, lean_object* v___x_2736_, lean_object* v_a_2737_, lean_object* v_range_2738_, lean_object* v_b_2739_, lean_object* v_i_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2731_, v_indName_2732_, v_tail_2733_, v___x_2734_, v___x_2735_, v___x_2736_, v_a_2737_, v_range_2738_, v_b_2739_, v_i_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec_ref(v_range_2738_);
return v_res_2746_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_2749_ = lean_unsigned_to_nat(58u);
v___x_2750_ = lean_unsigned_to_nat(169u);
v___x_2751_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2752_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2753_ = l_mkPanicMessageWithDecl(v___x_2752_, v___x_2751_, v___x_2750_, v___x_2749_, v___x_2748_);
return v___x_2753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_2755_ = lean_unsigned_to_nat(60u);
v___x_2756_ = lean_unsigned_to_nat(166u);
v___x_2757_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2758_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2759_ = l_mkPanicMessageWithDecl(v___x_2758_, v___x_2757_, v___x_2756_, v___x_2755_, v___x_2754_);
return v___x_2759_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(lean_object* v_indName_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2766_; 
lean_inc(v_indName_2760_);
v___x_2766_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
if (lean_obj_tag(v_a_2767_) == 5)
{
lean_object* v_val_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_val_2768_ = lean_ctor_get(v_a_2767_, 0);
lean_inc_ref(v_val_2768_);
lean_dec_ref_known(v_a_2767_, 1);
lean_inc(v_indName_2760_);
v___x_2769_ = l_Lean_mkCasesOnName(v_indName_2760_);
lean_inc(v___x_2769_);
v___x_2770_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2769_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v_levelParams_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2809_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v_levelParams_2772_ = lean_ctor_get(v_a_2771_, 1);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_a_2771_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; lean_object* v_unused_2811_; 
v_unused_2810_ = lean_ctor_get(v_a_2771_, 2);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_a_2771_, 0);
lean_dec(v_unused_2811_);
v___x_2774_ = v_a_2771_;
v_isShared_2775_ = v_isSharedCheck_2809_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_levelParams_2772_);
lean_dec(v_a_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2809_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_box(0);
v___x_2777_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_2772_, v___x_2776_);
if (lean_obj_tag(v___x_2777_) == 1)
{
lean_object* v_tail_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_tail_2778_ = lean_ctor_get(v___x_2777_, 1);
lean_inc(v_tail_2778_);
lean_inc_n(v_indName_2760_, 2);
v___x_2779_ = l_Lean_mkCtorElimName(v_indName_2760_);
v___x_2780_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_2760_);
v___x_2781_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2769_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = l_Lean_InductiveVal_numCtors(v_val_2768_);
v___x_2785_ = lean_unsigned_to_nat(1u);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 2, v___x_2785_);
lean_ctor_set(v___x_2774_, 1, v___x_2784_);
lean_ctor_set(v___x_2774_, 0, v___x_2783_);
v___x_2787_ = v___x_2774_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_box(0);
v___x_2789_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2768_, v_indName_2760_, v_tail_2778_, v___x_2779_, v___x_2777_, v___x_2780_, v_a_2782_, v___x_2787_, v___x_2788_, v___x_2783_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec_ref(v___x_2787_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; 
v_unused_2797_ = lean_ctor_get(v___x_2789_, 0);
lean_dec(v_unused_2797_);
v___x_2791_ = v___x_2789_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_dec(v___x_2789_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2788_);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2788_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
else
{
return v___x_2789_;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v___x_2780_);
lean_dec(v___x_2779_);
lean_dec(v_tail_2778_);
lean_dec_ref_known(v___x_2777_, 2);
lean_del_object(v___x_2774_);
lean_dec_ref(v_val_2768_);
lean_dec(v_indName_2760_);
v_a_2799_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2781_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2781_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_dec(v___x_2777_);
lean_del_object(v___x_2774_);
lean_dec(v___x_2769_);
lean_dec_ref(v_val_2768_);
lean_dec(v_indName_2760_);
v___x_2807_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1);
v___x_2808_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2807_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v___x_2769_);
lean_dec_ref(v_val_2768_);
lean_dec(v_indName_2760_);
v_a_2812_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2770_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2770_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_dec(v_a_2767_);
lean_dec(v_indName_2760_);
v___x_2820_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2);
v___x_2821_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2820_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
return v___x_2821_;
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_indName_2760_);
v_a_2822_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2766_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2766_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_2760_ = stack[0].m_obj;
lean_object* v_a_2761_ = stack[1].m_obj;
lean_object* v_a_2762_ = stack[2].m_obj;
lean_object* v_a_2763_ = stack[3].m_obj;
lean_object* v_a_2764_ = stack[4].m_obj;
lean_object* v_res_2830_;
v_res_2830_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
stack->m_obj
 = v_res_2830_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___boxed(lean_object* v_indName_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
return v_res_2837_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(lean_object* v_val_2838_, lean_object* v_indName_2839_, lean_object* v_tail_2840_, lean_object* v___x_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v_a_2844_, lean_object* v_range_2845_, lean_object* v_b_2846_, lean_object* v_i_2847_, lean_object* v_hs_2848_, lean_object* v_hl_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2838_, v_indName_2839_, v_tail_2840_, v___x_2841_, v___x_2842_, v___x_2843_, v_a_2844_, v_range_2845_, v_b_2846_, v_i_2847_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2838_ = stack[0].m_obj;
lean_object* v_indName_2839_ = stack[1].m_obj;
lean_object* v_tail_2840_ = stack[2].m_obj;
lean_object* v___x_2841_ = stack[3].m_obj;
lean_object* v___x_2842_ = stack[4].m_obj;
lean_object* v___x_2843_ = stack[5].m_obj;
lean_object* v_a_2844_ = stack[6].m_obj;
lean_object* v_range_2845_ = stack[7].m_obj;
lean_object* v_b_2846_ = stack[8].m_obj;
lean_object* v_i_2847_ = stack[9].m_obj;
lean_object* v___y_2850_ = stack[12].m_obj;
lean_object* v___y_2851_ = stack[13].m_obj;
lean_object* v___y_2852_ = stack[14].m_obj;
lean_object* v___y_2853_ = stack[15].m_obj;
lean_object* v_res_2856_;
v_res_2856_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(v_val_2838_, v_indName_2839_, v_tail_2840_, v___x_2841_, v___x_2842_, v___x_2843_, v_a_2844_, v_range_2845_, v_b_2846_, v_i_2847_, lean_box(0), lean_box(0), v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
stack->m_obj
 = v_res_2856_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___boxed(lean_object** _args){
lean_object* v_val_2857_ = _args[0];
lean_object* v_indName_2858_ = _args[1];
lean_object* v_tail_2859_ = _args[2];
lean_object* v___x_2860_ = _args[3];
lean_object* v___x_2861_ = _args[4];
lean_object* v___x_2862_ = _args[5];
lean_object* v_a_2863_ = _args[6];
lean_object* v_range_2864_ = _args[7];
lean_object* v_b_2865_ = _args[8];
lean_object* v_i_2866_ = _args[9];
lean_object* v_hs_2867_ = _args[10];
lean_object* v_hl_2868_ = _args[11];
lean_object* v___y_2869_ = _args[12];
lean_object* v___y_2870_ = _args[13];
lean_object* v___y_2871_ = _args[14];
lean_object* v___y_2872_ = _args[15];
lean_object* v___y_2873_ = _args[16];
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(v_val_2857_, v_indName_2858_, v_tail_2859_, v___x_2860_, v___x_2861_, v___x_2862_, v_a_2863_, v_range_2864_, v_b_2865_, v_i_2866_, v_hs_2867_, v_hl_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec_ref(v_range_2864_);
return v_res_2874_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(lean_object* v_00_u03b1_2875_, lean_object* v_attrName_2876_, lean_object* v_declName_2877_, lean_object* v_asyncPrefix_x3f_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2876_, v_declName_2877_, v_asyncPrefix_x3f_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2876_ = stack[1].m_obj;
lean_object* v_declName_2877_ = stack[2].m_obj;
lean_object* v_asyncPrefix_x3f_2878_ = stack[3].m_obj;
lean_object* v___y_2879_ = stack[4].m_obj;
lean_object* v___y_2880_ = stack[5].m_obj;
lean_object* v___y_2881_ = stack[6].m_obj;
lean_object* v___y_2882_ = stack[7].m_obj;
lean_object* v_res_2885_;
v_res_2885_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(lean_box(0), v_attrName_2876_, v_declName_2877_, v_asyncPrefix_x3f_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
stack->m_obj
 = v_res_2885_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2886_, lean_object* v_attrName_2887_, lean_object* v_declName_2888_, lean_object* v_asyncPrefix_x3f_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(v_00_u03b1_2886_, v_attrName_2887_, v_declName_2888_, v_asyncPrefix_x3f_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2895_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(lean_object* v_00_u03b1_2896_, lean_object* v_attrName_2897_, lean_object* v_declName_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2897_, v_declName_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
return v___x_2904_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2897_ = stack[1].m_obj;
lean_object* v_declName_2898_ = stack[2].m_obj;
lean_object* v___y_2899_ = stack[3].m_obj;
lean_object* v___y_2900_ = stack[4].m_obj;
lean_object* v___y_2901_ = stack[5].m_obj;
lean_object* v___y_2902_ = stack[6].m_obj;
lean_object* v_res_2905_;
v_res_2905_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(lean_box(0), v_attrName_2897_, v_declName_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
stack->m_obj
 = v_res_2905_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_attrName_2907_, lean_object* v_declName_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(v_00_u03b1_2906_, v_attrName_2907_, v_declName_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2914_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(lean_object* v___y_2915_, uint8_t v_isExporting_2916_, lean_object* v___x_2917_, lean_object* v___y_2918_, lean_object* v___x_2919_, lean_object* v_a_x3f_2920_){
_start:
{
lean_object* v___x_2922_; lean_object* v_env_2923_; lean_object* v_nextMacroScope_2924_; lean_object* v_ngen_2925_; lean_object* v_auxDeclNGen_2926_; lean_object* v_traceState_2927_; lean_object* v_recordedDeps_2928_; lean_object* v_messages_2929_; lean_object* v_infoState_2930_; lean_object* v_snapshotTasks_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2956_; 
v___x_2922_ = lean_st_ref_take(v___y_2915_);
v_env_2923_ = lean_ctor_get(v___x_2922_, 0);
v_nextMacroScope_2924_ = lean_ctor_get(v___x_2922_, 1);
v_ngen_2925_ = lean_ctor_get(v___x_2922_, 2);
v_auxDeclNGen_2926_ = lean_ctor_get(v___x_2922_, 3);
v_traceState_2927_ = lean_ctor_get(v___x_2922_, 4);
v_recordedDeps_2928_ = lean_ctor_get(v___x_2922_, 6);
v_messages_2929_ = lean_ctor_get(v___x_2922_, 7);
v_infoState_2930_ = lean_ctor_get(v___x_2922_, 8);
v_snapshotTasks_2931_ = lean_ctor_get(v___x_2922_, 9);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; 
v_unused_2957_ = lean_ctor_get(v___x_2922_, 5);
lean_dec(v_unused_2957_);
v___x_2933_ = v___x_2922_;
v_isShared_2934_ = v_isSharedCheck_2956_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_snapshotTasks_2931_);
lean_inc(v_infoState_2930_);
lean_inc(v_messages_2929_);
lean_inc(v_recordedDeps_2928_);
lean_inc(v_traceState_2927_);
lean_inc(v_auxDeclNGen_2926_);
lean_inc(v_ngen_2925_);
lean_inc(v_nextMacroScope_2924_);
lean_inc(v_env_2923_);
lean_dec(v___x_2922_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2956_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2935_ = l_Lean_Environment_setExporting(v_env_2923_, v_isExporting_2916_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 5, v___x_2917_);
lean_ctor_set(v___x_2933_, 0, v___x_2935_);
v___x_2937_ = v___x_2933_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_nextMacroScope_2924_);
lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_ngen_2925_);
lean_ctor_set(v_reuseFailAlloc_2955_, 3, v_auxDeclNGen_2926_);
lean_ctor_set(v_reuseFailAlloc_2955_, 4, v_traceState_2927_);
lean_ctor_set(v_reuseFailAlloc_2955_, 5, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2955_, 6, v_recordedDeps_2928_);
lean_ctor_set(v_reuseFailAlloc_2955_, 7, v_messages_2929_);
lean_ctor_set(v_reuseFailAlloc_2955_, 8, v_infoState_2930_);
lean_ctor_set(v_reuseFailAlloc_2955_, 9, v_snapshotTasks_2931_);
v___x_2937_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_mctx_2940_; lean_object* v_zetaDeltaFVarIds_2941_; lean_object* v_postponed_2942_; lean_object* v_diag_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2953_; 
v___x_2938_ = lean_st_ref_put(v___y_2915_, v___x_2937_);
v___x_2939_ = lean_st_ref_take(v___y_2918_);
v_mctx_2940_ = lean_ctor_get(v___x_2939_, 0);
v_zetaDeltaFVarIds_2941_ = lean_ctor_get(v___x_2939_, 2);
v_postponed_2942_ = lean_ctor_get(v___x_2939_, 3);
v_diag_2943_ = lean_ctor_get(v___x_2939_, 4);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; 
v_unused_2954_ = lean_ctor_get(v___x_2939_, 1);
lean_dec(v_unused_2954_);
v___x_2945_ = v___x_2939_;
v_isShared_2946_ = v_isSharedCheck_2953_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_diag_2943_);
lean_inc(v_postponed_2942_);
lean_inc(v_zetaDeltaFVarIds_2941_);
lean_inc(v_mctx_2940_);
lean_dec(v___x_2939_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2953_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = lean_box(0);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_2919_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_mctx_2940_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v_zetaDeltaFVarIds_2941_);
lean_ctor_set(v_reuseFailAlloc_2952_, 3, v_postponed_2942_);
lean_ctor_set(v_reuseFailAlloc_2952_, 4, v_diag_2943_);
v___x_2949_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_st_ref_put(v___y_2918_, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2947_);
return v___x_2951_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2915_ = stack[0].m_obj;
uint8_t v_isExporting_2916_ = stack[1].m_num;
lean_object* v___x_2917_ = stack[2].m_obj;
lean_object* v___y_2918_ = stack[3].m_obj;
lean_object* v___x_2919_ = stack[4].m_obj;
lean_object* v_a_x3f_2920_ = stack[5].m_obj;
lean_object* v_res_2958_;
v_res_2958_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2915_, v_isExporting_2916_, v___x_2917_, v___y_2918_, v___x_2919_, v_a_x3f_2920_);
stack->m_obj
 = v_res_2958_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2959_, lean_object* v_isExporting_2960_, lean_object* v___x_2961_, lean_object* v___y_2962_, lean_object* v___x_2963_, lean_object* v_a_x3f_2964_, lean_object* v___y_2965_){
_start:
{
uint8_t v_isExporting_boxed_2966_; lean_object* v_res_2967_; 
v_isExporting_boxed_2966_ = lean_unbox(v_isExporting_2960_);
v_res_2967_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2959_, v_isExporting_boxed_2966_, v___x_2961_, v___y_2962_, v___x_2963_, v_a_x3f_2964_);
lean_dec(v_a_x3f_2964_);
lean_dec(v___y_2962_);
lean_dec(v___y_2959_);
return v_res_2967_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(lean_object* v_x_2968_, uint8_t v_isExporting_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v_env_2976_; lean_object* v___x_2977_; uint8_t v_isModule_2978_; 
v___x_2975_ = lean_st_ref_get(v___y_2973_);
v_env_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc_ref(v_env_2976_);
lean_dec(v___x_2975_);
v___x_2977_ = l_Lean_Environment_header(v_env_2976_);
v_isModule_2978_ = lean_ctor_get_uint8(v___x_2977_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2977_);
if (v_isModule_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_dec_ref(v_env_2976_);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
v___x_2979_ = lean_apply_5(v_x_2968_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, lean_box(0));
return v___x_2979_;
}
else
{
uint8_t v_isExporting_2980_; 
v_isExporting_2980_ = lean_ctor_get_uint8(v_env_2976_, sizeof(void*)*13);
lean_dec_ref(v_env_2976_);
if (v_isExporting_2969_ == 0)
{
if (v_isExporting_2980_ == 0)
{
lean_object* v___x_3047_; 
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
v___x_3047_ = lean_apply_5(v_x_2968_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, lean_box(0));
return v___x_3047_;
}
else
{
goto v___jp_2981_;
}
}
else
{
if (v_isExporting_2980_ == 0)
{
goto v___jp_2981_;
}
else
{
lean_object* v___x_3048_; 
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
v___x_3048_ = lean_apply_5(v_x_2968_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, lean_box(0));
return v___x_3048_;
}
}
v___jp_2981_:
{
lean_object* v___x_2982_; lean_object* v_env_2983_; lean_object* v_nextMacroScope_2984_; lean_object* v_ngen_2985_; lean_object* v_auxDeclNGen_2986_; lean_object* v_traceState_2987_; lean_object* v_recordedDeps_2988_; lean_object* v_messages_2989_; lean_object* v_infoState_2990_; lean_object* v_snapshotTasks_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3045_; 
v___x_2982_ = lean_st_ref_take(v___y_2973_);
v_env_2983_ = lean_ctor_get(v___x_2982_, 0);
v_nextMacroScope_2984_ = lean_ctor_get(v___x_2982_, 1);
v_ngen_2985_ = lean_ctor_get(v___x_2982_, 2);
v_auxDeclNGen_2986_ = lean_ctor_get(v___x_2982_, 3);
v_traceState_2987_ = lean_ctor_get(v___x_2982_, 4);
v_recordedDeps_2988_ = lean_ctor_get(v___x_2982_, 6);
v_messages_2989_ = lean_ctor_get(v___x_2982_, 7);
v_infoState_2990_ = lean_ctor_get(v___x_2982_, 8);
v_snapshotTasks_2991_ = lean_ctor_get(v___x_2982_, 9);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; 
v_unused_3046_ = lean_ctor_get(v___x_2982_, 5);
lean_dec(v_unused_3046_);
v___x_2993_ = v___x_2982_;
v_isShared_2994_ = v_isSharedCheck_3045_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_snapshotTasks_2991_);
lean_inc(v_infoState_2990_);
lean_inc(v_messages_2989_);
lean_inc(v_recordedDeps_2988_);
lean_inc(v_traceState_2987_);
lean_inc(v_auxDeclNGen_2986_);
lean_inc(v_ngen_2985_);
lean_inc(v_nextMacroScope_2984_);
lean_inc(v_env_2983_);
lean_dec(v___x_2982_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3045_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2995_ = l_Lean_Environment_setExporting(v_env_2983_, v_isExporting_2969_);
v___x_2996_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 5, v___x_2996_);
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2998_ = v___x_2993_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_nextMacroScope_2984_);
lean_ctor_set(v_reuseFailAlloc_3044_, 2, v_ngen_2985_);
lean_ctor_set(v_reuseFailAlloc_3044_, 3, v_auxDeclNGen_2986_);
lean_ctor_set(v_reuseFailAlloc_3044_, 4, v_traceState_2987_);
lean_ctor_set(v_reuseFailAlloc_3044_, 5, v___x_2996_);
lean_ctor_set(v_reuseFailAlloc_3044_, 6, v_recordedDeps_2988_);
lean_ctor_set(v_reuseFailAlloc_3044_, 7, v_messages_2989_);
lean_ctor_set(v_reuseFailAlloc_3044_, 8, v_infoState_2990_);
lean_ctor_set(v_reuseFailAlloc_3044_, 9, v_snapshotTasks_2991_);
v___x_2998_ = v_reuseFailAlloc_3044_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_mctx_3001_; lean_object* v_zetaDeltaFVarIds_3002_; lean_object* v_postponed_3003_; lean_object* v_diag_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3042_; 
v___x_2999_ = lean_st_ref_put(v___y_2973_, v___x_2998_);
v___x_3000_ = lean_st_ref_take(v___y_2971_);
v_mctx_3001_ = lean_ctor_get(v___x_3000_, 0);
v_zetaDeltaFVarIds_3002_ = lean_ctor_get(v___x_3000_, 2);
v_postponed_3003_ = lean_ctor_get(v___x_3000_, 3);
v_diag_3004_ = lean_ctor_get(v___x_3000_, 4);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3042_ == 0)
{
lean_object* v_unused_3043_; 
v_unused_3043_ = lean_ctor_get(v___x_3000_, 1);
lean_dec(v_unused_3043_);
v___x_3006_ = v___x_3000_;
v_isShared_3007_ = v_isSharedCheck_3042_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_diag_3004_);
lean_inc(v_postponed_3003_);
lean_inc(v_zetaDeltaFVarIds_3002_);
lean_inc(v_mctx_3001_);
lean_dec(v___x_3000_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3042_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3008_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___x_3008_);
v___x_3010_ = v___x_3006_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_mctx_3001_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3041_, 2, v_zetaDeltaFVarIds_3002_);
lean_ctor_set(v_reuseFailAlloc_3041_, 3, v_postponed_3003_);
lean_ctor_set(v_reuseFailAlloc_3041_, 4, v_diag_3004_);
v___x_3010_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; lean_object* v_r_3012_; 
v___x_3011_ = lean_st_ref_put(v___y_2971_, v___x_3010_);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
v_r_3012_ = lean_apply_5(v_x_2968_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, lean_box(0));
if (lean_obj_tag(v_r_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3029_; 
v_a_3013_ = lean_ctor_get(v_r_3012_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_r_3012_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3015_ = v_r_3012_;
v_isShared_3016_ = v_isSharedCheck_3029_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v_r_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3029_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
lean_inc(v_a_3013_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set_tag(v___x_3015_, 1);
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v___x_3019_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2973_, v_isExporting_2980_, v___x_2996_, v___y_2971_, v___x_3008_, v___x_3018_);
lean_dec_ref(v___x_3018_);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v___x_3019_, 0);
lean_dec(v_unused_3027_);
v___x_3021_ = v___x_3019_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v___x_3019_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v_a_3013_);
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3013_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3030_ = lean_ctor_get(v_r_3012_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v_r_3012_, 1);
v___x_3031_ = lean_box(0);
v___x_3032_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2973_, v_isExporting_2980_, v___x_2996_, v___y_2971_, v___x_3008_, v___x_3031_);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v___x_3032_, 0);
lean_dec(v_unused_3040_);
v___x_3034_ = v___x_3032_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_dec(v___x_3032_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
lean_ctor_set_tag(v___x_3034_, 1);
lean_ctor_set(v___x_3034_, 0, v_a_3030_);
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3030_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2968_ = stack[0].m_obj;
uint8_t v_isExporting_2969_ = stack[1].m_num;
lean_object* v___y_2970_ = stack[2].m_obj;
lean_object* v___y_2971_ = stack[3].m_obj;
lean_object* v___y_2972_ = stack[4].m_obj;
lean_object* v___y_2973_ = stack[5].m_obj;
lean_object* v_res_3049_;
v_res_3049_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_2968_, v_isExporting_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
stack->m_obj
 = v_res_3049_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___boxed(lean_object* v_x_3050_, lean_object* v_isExporting_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v_isExporting_boxed_3057_; lean_object* v_res_3058_; 
v_isExporting_boxed_3057_ = lean_unbox(v_isExporting_3051_);
v_res_3058_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_3050_, v_isExporting_boxed_3057_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
return v_res_3058_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(lean_object* v_00_u03b1_3059_, lean_object* v_x_3060_, uint8_t v_isExporting_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_3060_, v_isExporting_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v___x_3067_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3060_ = stack[1].m_obj;
uint8_t v_isExporting_3061_ = stack[2].m_num;
lean_object* v___y_3062_ = stack[3].m_obj;
lean_object* v___y_3063_ = stack[4].m_obj;
lean_object* v___y_3064_ = stack[5].m_obj;
lean_object* v___y_3065_ = stack[6].m_obj;
lean_object* v_res_3068_;
v_res_3068_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(lean_box(0), v_x_3060_, v_isExporting_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
stack->m_obj
 = v_res_3068_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___boxed(lean_object* v_00_u03b1_3069_, lean_object* v_x_3070_, lean_object* v_isExporting_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
uint8_t v_isExporting_boxed_3077_; lean_object* v_res_3078_; 
v_isExporting_boxed_3077_ = lean_unbox(v_isExporting_3071_);
v_res_3078_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(v_00_u03b1_3069_, v_x_3070_, v_isExporting_boxed_3077_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
return v_res_3078_;
}
}
lean_object* l_Lean_mkCtorElim___lam__0(lean_object* v_indName_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
lean_inc(v_indName_3079_);
v___x_3085_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3086_; 
lean_dec_ref_known(v___x_3085_, 1);
lean_inc(v_indName_3079_);
v___x_3086_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v___x_3087_; 
lean_dec_ref_known(v___x_3086_, 1);
v___x_3087_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
return v___x_3087_;
}
else
{
lean_dec(v_indName_3079_);
return v___x_3086_;
}
}
else
{
lean_dec(v_indName_3079_);
return v___x_3085_;
}
}
}
LEAN_EXPORT void l_Lean_mkCtorElim___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_3079_ = stack[0].m_obj;
lean_object* v___y_3080_ = stack[1].m_obj;
lean_object* v___y_3081_ = stack[2].m_obj;
lean_object* v___y_3082_ = stack[3].m_obj;
lean_object* v___y_3083_ = stack[4].m_obj;
lean_object* v_res_3088_;
v_res_3088_ = l_Lean_mkCtorElim___lam__0(v_indName_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
stack->m_obj
 = v_res_3088_;
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object* v_indName_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_mkCtorElim___lam__0(v_indName_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
return v_res_3095_;
}
}
lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(lean_object* v_declName_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; 
lean_inc(v_declName_3096_);
v___x_3102_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_declName_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3138_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3138_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3138_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
if (lean_obj_tag(v_a_3103_) == 5)
{
lean_object* v_val_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_del_object(v___x_3105_);
v_val_3107_ = lean_ctor_get(v_a_3103_, 0);
lean_inc_ref(v_val_3107_);
lean_dec_ref_known(v_a_3103_, 1);
v___x_3108_ = l_Lean_mkRecName(v_declName_3096_);
v___x_3109_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v___x_3108_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_toConstantVal_3110_; lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3124_; 
v_toConstantVal_3110_ = lean_ctor_get(v_val_3107_, 0);
lean_inc_ref(v_toConstantVal_3110_);
lean_dec_ref(v_val_3107_);
v_a_3111_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3113_ = v___x_3109_;
v_isShared_3114_ = v_isSharedCheck_3124_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3109_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3124_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_levelParams_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
v_levelParams_3115_ = lean_ctor_get(v_toConstantVal_3110_, 1);
lean_inc(v_levelParams_3115_);
lean_dec_ref(v_toConstantVal_3110_);
v___x_3116_ = l_List_lengthTR___redArg(v_levelParams_3115_);
lean_dec(v_levelParams_3115_);
v___x_3117_ = l_Lean_ConstantInfo_levelParams(v_a_3111_);
lean_dec(v_a_3111_);
v___x_3118_ = l_List_lengthTR___redArg(v___x_3117_);
lean_dec(v___x_3117_);
v___x_3119_ = lean_nat_dec_lt(v___x_3116_, v___x_3118_);
lean_dec(v___x_3118_);
lean_dec(v___x_3116_);
v___x_3120_ = lean_box(v___x_3119_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3120_);
v___x_3122_ = v___x_3113_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref(v_val_3107_);
v_a_3125_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3109_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3109_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
uint8_t v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_dec(v_a_3103_);
lean_dec(v_declName_3096_);
v___x_3133_ = 0;
v___x_3134_ = lean_box(v___x_3133_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3134_);
v___x_3136_ = v___x_3105_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_declName_3096_);
v_a_3139_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3102_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3102_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3096_ = stack[0].m_obj;
lean_object* v___y_3097_ = stack[1].m_obj;
lean_object* v___y_3098_ = stack[2].m_obj;
lean_object* v___y_3099_ = stack[3].m_obj;
lean_object* v___y_3100_ = stack[4].m_obj;
lean_object* v_res_3147_;
v_res_3147_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_declName_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
stack->m_obj
 = v_res_3147_;
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0___boxed(lean_object* v_declName_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_declName_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
return v_res_3154_;
}
}
lean_object* l_Lean_mkCtorElim(lean_object* v_indName_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
lean_object* v___f_3161_; lean_object* v___x_3162_; lean_object* v_env_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; uint8_t v___x_3166_; 
lean_inc_n(v_indName_3155_, 2);
v___f_3161_ = lean_alloc_closure((void*)(l_Lean_mkCtorElim___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3161_, 0, v_indName_3155_);
v___x_3162_ = lean_st_ref_get(v_a_3159_);
v_env_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc_ref(v_env_3163_);
lean_dec(v___x_3162_);
v___x_3164_ = l_Lean_mkCtorIdxName(v_indName_3155_);
v___x_3165_ = 1;
v___x_3166_ = l_Lean_Environment_contains(v_env_3163_, v___x_3164_, v___x_3165_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_dec_ref(v___f_3161_);
lean_dec(v_indName_3155_);
v___x_3167_ = lean_box(0);
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
else
{
lean_object* v___x_3169_; 
lean_inc(v_indName_3155_);
v___x_3169_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3231_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3231_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3231_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
if (lean_obj_tag(v_a_3170_) == 5)
{
lean_object* v_val_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_val_3174_ = lean_ctor_get(v_a_3170_, 0);
lean_inc_ref(v_val_3174_);
lean_dec_ref_known(v_a_3170_, 1);
v___x_3175_ = lean_unsigned_to_nat(1u);
v___x_3176_ = l_Lean_InductiveVal_numCtors(v_val_3174_);
v___x_3177_ = lean_nat_dec_lt(v___x_3175_, v___x_3176_);
lean_dec(v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
lean_dec_ref(v_val_3174_);
lean_dec_ref(v___f_3161_);
lean_dec(v_indName_3155_);
v___x_3178_ = lean_box(0);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3178_);
v___x_3180_ = v___x_3172_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
else
{
lean_object* v_toConstantVal_3182_; lean_object* v_type_3183_; lean_object* v___x_3184_; 
lean_del_object(v___x_3172_);
v_toConstantVal_3182_ = lean_ctor_get(v_val_3174_, 0);
lean_inc_ref(v_toConstantVal_3182_);
lean_dec_ref(v_val_3174_);
v_type_3183_ = lean_ctor_get(v_toConstantVal_3182_, 2);
lean_inc_ref(v_type_3183_);
lean_dec_ref(v_toConstantVal_3182_);
v___x_3184_ = l_Lean_Meta_isPropFormerType(v_type_3183_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3218_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3218_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3218_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
uint8_t v___x_3189_; 
v___x_3189_ = lean_unbox(v_a_3185_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; 
lean_del_object(v___x_3187_);
lean_inc(v_indName_3155_);
v___x_3190_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_indName_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3205_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3205_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3205_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_unbox(v_a_3191_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3198_; 
lean_dec(v_a_3191_);
lean_dec(v_a_3185_);
lean_dec_ref(v___f_3161_);
lean_dec(v_indName_3155_);
v___x_3196_ = lean_box(0);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3196_);
v___x_3198_ = v___x_3193_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
else
{
uint8_t v___x_3200_; 
lean_del_object(v___x_3193_);
v___x_3200_ = l_Lean_isPrivateName(v_indName_3155_);
lean_dec(v_indName_3155_);
if (v___x_3200_ == 0)
{
uint8_t v___x_3201_; lean_object* v___x_3202_; 
lean_dec(v_a_3185_);
v___x_3201_ = lean_unbox(v_a_3191_);
lean_dec(v_a_3191_);
v___x_3202_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3161_, v___x_3201_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
return v___x_3202_;
}
else
{
uint8_t v___x_3203_; lean_object* v___x_3204_; 
lean_dec(v_a_3191_);
v___x_3203_ = lean_unbox(v_a_3185_);
lean_dec(v_a_3185_);
v___x_3204_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3161_, v___x_3203_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_a_3185_);
lean_dec_ref(v___f_3161_);
lean_dec(v_indName_3155_);
v_a_3206_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3190_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3190_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
lean_dec(v_a_3185_);
lean_dec_ref(v___f_3161_);
lean_dec(v_indName_3155_);
v___x_3214_ = lean_box(0);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3214_);
v___x_3216_ = v___x_3187_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v___f_3161_);
lean_dec(v_indName_3155_);
v_a_3219_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3184_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3184_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
lean_dec(v_a_3170_);
lean_dec_ref(v___f_3161_);
lean_dec(v_indName_3155_);
v___x_3227_ = lean_box(0);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3227_);
v___x_3229_ = v___x_3172_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v___f_3161_);
lean_dec(v_indName_3155_);
v_a_3232_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3169_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3169_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCtorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_3155_ = stack[0].m_obj;
lean_object* v_a_3156_ = stack[1].m_obj;
lean_object* v_a_3157_ = stack[2].m_obj;
lean_object* v_a_3158_ = stack[3].m_obj;
lean_object* v_a_3159_ = stack[4].m_obj;
lean_object* v_res_3240_;
v_res_3240_ = l_Lean_mkCtorElim(v_indName_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
stack->m_obj
 = v_res_3240_;
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___boxed(lean_object* v_indName_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_mkCtorElim(v_indName_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
return v_res_3247_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v_decl_3248_, lean_object* v_____r_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v___x_3255_; 
lean_inc(v_decl_3248_);
v___x_3255_ = l_Lean_mkCtorIdx(v_decl_3248_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v___x_3256_; 
lean_dec_ref_known(v___x_3255_, 1);
v___x_3256_ = l_Lean_mkCtorElim(v_decl_3248_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
return v___x_3256_;
}
else
{
lean_dec(v_decl_3248_);
return v___x_3255_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3248_ = stack[0].m_obj;
lean_object* v_____r_3249_ = stack[1].m_obj;
lean_object* v___y_3250_ = stack[2].m_obj;
lean_object* v___y_3251_ = stack[3].m_obj;
lean_object* v___y_3252_ = stack[4].m_obj;
lean_object* v___y_3253_ = stack[5].m_obj;
lean_object* v_res_3257_;
v_res_3257_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3248_, v_____r_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
stack->m_obj
 = v_res_3257_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_decl_3258_, lean_object* v_____r_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3258_, v_____r_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
return v_res_3265_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_3268_ = l_Lean_stringToMessageData(v___x_3267_);
return v___x_3268_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_3271_ = l_Lean_stringToMessageData(v___x_3270_);
return v___x_3271_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_3275_, uint8_t v_kind_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___y_3288_; 
v___x_3282_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_3283_ = l_Lean_MessageData_ofName(v_name_3275_);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
switch(v_kind_3276_)
{
case 0:
{
lean_object* v___x_3295_; 
v___x_3295_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_3288_ = v___x_3295_;
goto v___jp_3287_;
}
case 1:
{
lean_object* v___x_3296_; 
v___x_3296_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_3288_ = v___x_3296_;
goto v___jp_3287_;
}
default: 
{
lean_object* v___x_3297_; 
v___x_3297_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_3288_ = v___x_3297_;
goto v___jp_3287_;
}
}
v___jp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_inc_ref(v___y_3288_);
v___x_3289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___y_3288_);
v___x_3290_ = l_Lean_MessageData_ofFormat(v___x_3289_);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3286_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_3293_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3294_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3275_ = stack[0].m_obj;
uint8_t v_kind_3276_ = stack[1].m_num;
lean_object* v___y_3277_ = stack[2].m_obj;
lean_object* v___y_3278_ = stack[3].m_obj;
lean_object* v___y_3279_ = stack[4].m_obj;
lean_object* v___y_3280_ = stack[5].m_obj;
lean_object* v_res_3298_;
v_res_3298_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3275_, v_kind_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
stack->m_obj
 = v_res_3298_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_3299_, lean_object* v_kind_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
uint8_t v_kind_boxed_3306_; lean_object* v_res_3307_; 
v_kind_boxed_3306_ = lean_unbox(v_kind_3300_);
v_res_3307_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3299_, v_kind_boxed_3306_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
return v_res_3307_;
}
}
static uint64_t _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3314_; uint64_t v___x_3315_; 
v___x_3314_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3315_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3314_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_uint64_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3318_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set_uint64(v___x_3318_, sizeof(void*)*1, v___x_3316_);
return v___x_3318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3322_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
lean_ctor_set(v___x_3322_, 2, v___x_3321_);
lean_ctor_set(v___x_3322_, 3, v___x_3321_);
lean_ctor_set(v___x_3322_, 4, v___x_3321_);
lean_ctor_set(v___x_3322_, 5, v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
lean_ctor_set(v___x_3324_, 2, v___x_3323_);
lean_ctor_set(v___x_3324_, 3, v___x_3323_);
lean_ctor_set(v___x_3324_, 4, v___x_3323_);
return v___x_3324_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3325_, lean_object* v___x_3326_, lean_object* v___x_3327_, lean_object* v_decl_3328_, lean_object* v___stx_3329_, uint8_t v_kind_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
uint8_t v___x_3334_; uint8_t v___x_3335_; uint8_t v___x_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; size_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___y_3357_; 
v___x_3334_ = 0;
v___x_3335_ = l_Lean_instBEqAttributeKind_beq(v_kind_3330_, v___x_3334_);
v___x_3336_ = 1;
v___x_3337_ = 0;
v___x_3338_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3339_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3340_ = lean_unsigned_to_nat(32u);
v___x_3341_ = lean_mk_empty_array_with_capacity(v___x_3340_);
v___x_3342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3343_ = ((size_t)5ULL);
lean_inc_n(v___x_3325_, 6);
v___x_3344_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3341_);
lean_ctor_set(v___x_3344_, 2, v___x_3325_);
lean_ctor_set(v___x_3344_, 3, v___x_3325_);
lean_ctor_set_usize(v___x_3344_, 4, v___x_3343_);
v___x_3345_ = lean_box(1);
lean_inc_ref(v___x_3344_);
v___x_3346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3339_);
lean_ctor_set(v___x_3346_, 1, v___x_3344_);
lean_ctor_set(v___x_3346_, 2, v___x_3345_);
v___x_3347_ = lean_mk_empty_array_with_capacity(v___x_3325_);
v___x_3348_ = lean_box(0);
lean_inc(v___x_3326_);
v___x_3349_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3349_, 0, v___x_3338_);
lean_ctor_set(v___x_3349_, 1, v___x_3326_);
lean_ctor_set(v___x_3349_, 2, v___x_3346_);
lean_ctor_set(v___x_3349_, 3, v___x_3347_);
lean_ctor_set(v___x_3349_, 4, v___x_3348_);
lean_ctor_set(v___x_3349_, 5, v___x_3325_);
lean_ctor_set(v___x_3349_, 6, v___x_3348_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*7, v___x_3337_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*7 + 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*7 + 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*7 + 3, v___x_3336_);
v___x_3350_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3351_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3325_);
lean_ctor_set(v___x_3351_, 1, v___x_3325_);
lean_ctor_set(v___x_3351_, 2, v___x_3325_);
lean_ctor_set(v___x_3351_, 3, v___x_3325_);
lean_ctor_set(v___x_3351_, 4, v___x_3339_);
lean_ctor_set(v___x_3351_, 5, v___x_3339_);
lean_ctor_set(v___x_3351_, 6, v___x_3339_);
lean_ctor_set(v___x_3351_, 7, v___x_3339_);
lean_ctor_set(v___x_3351_, 8, v___x_3339_);
lean_ctor_set(v___x_3351_, 9, v___x_3339_);
lean_ctor_set(v___x_3351_, 10, v___x_3339_);
lean_ctor_set(v___x_3351_, 11, v___x_3350_);
v___x_3352_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3353_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3351_);
lean_ctor_set(v___x_3354_, 1, v___x_3352_);
lean_ctor_set(v___x_3354_, 2, v___x_3326_);
lean_ctor_set(v___x_3354_, 3, v___x_3344_);
lean_ctor_set(v___x_3354_, 4, v___x_3353_);
v___x_3355_ = lean_st_mk_ref(v___x_3354_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3367_; 
lean_dec(v_decl_3328_);
v___x_3367_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v___x_3327_, v_kind_3330_, v___x_3349_, v___x_3355_, v___y_3331_, v___y_3332_);
lean_dec_ref_known(v___x_3349_, 7);
v___y_3357_ = v___x_3367_;
goto v___jp_3356_;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec(v___x_3327_);
v___x_3368_ = lean_box(0);
v___x_3369_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3328_, v___x_3368_, v___x_3349_, v___x_3355_, v___y_3331_, v___y_3332_);
lean_dec_ref_known(v___x_3349_, 7);
v___y_3357_ = v___x_3369_;
goto v___jp_3356_;
}
v___jp_3356_:
{
if (lean_obj_tag(v___y_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3366_; 
v_a_3358_ = lean_ctor_get(v___y_3357_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___y_3357_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3360_ = v___y_3357_;
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___y_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3362_ = lean_st_ref_get(v___x_3355_);
lean_dec(v___x_3355_);
lean_dec(v___x_3362_);
if (v_isShared_3361_ == 0)
{
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3358_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
else
{
lean_dec(v___x_3355_);
return v___y_3357_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3325_ = stack[0].m_obj;
lean_object* v___x_3326_ = stack[1].m_obj;
lean_object* v___x_3327_ = stack[2].m_obj;
lean_object* v_decl_3328_ = stack[3].m_obj;
lean_object* v___stx_3329_ = stack[4].m_obj;
uint8_t v_kind_3330_ = stack[5].m_num;
lean_object* v___y_3331_ = stack[6].m_obj;
lean_object* v___y_3332_ = stack[7].m_obj;
lean_object* v_res_3370_;
v_res_3370_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3325_, v___x_3326_, v___x_3327_, v_decl_3328_, v___stx_3329_, v_kind_3330_, v___y_3331_, v___y_3332_);
stack->m_obj
 = v_res_3370_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3371_, lean_object* v___x_3372_, lean_object* v___x_3373_, lean_object* v_decl_3374_, lean_object* v___stx_3375_, lean_object* v_kind_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
uint8_t v_kind_boxed_3380_; lean_object* v_res_3381_; 
v_kind_boxed_3380_ = lean_unbox(v_kind_3376_);
v_res_3381_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3371_, v___x_3372_, v___x_3373_, v_decl_3374_, v___stx_3375_, v_kind_boxed_3380_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___stx_3375_);
return v_res_3381_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; lean_object* v_toCold_3387_; lean_object* v_env_3388_; lean_object* v_options_3389_; uint8_t v___x_3390_; lean_object* v_env_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3386_ = lean_st_ref_get(v___y_3384_);
v_toCold_3387_ = lean_ctor_get(v___y_3383_, 0);
v_env_3388_ = lean_ctor_get(v___x_3386_, 0);
lean_inc_ref(v_env_3388_);
lean_dec(v___x_3386_);
v_options_3389_ = lean_ctor_get(v_toCold_3387_, 2);
v___x_3390_ = 0;
v_env_3391_ = l_Lean_Environment_setRecordingDeps(v_env_3388_, v___x_3390_);
v___x_3392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3393_ = lean_unsigned_to_nat(32u);
v___x_3394_ = lean_mk_empty_array_with_capacity(v___x_3393_);
lean_dec_ref(v___x_3394_);
v___x_3395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
lean_inc_ref(v_options_3389_);
v___x_3396_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3396_, 0, v_env_3391_);
lean_ctor_set(v___x_3396_, 1, v___x_3392_);
lean_ctor_set(v___x_3396_, 2, v___x_3395_);
lean_ctor_set(v___x_3396_, 3, v_options_3389_);
v___x_3397_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
lean_ctor_set(v___x_3397_, 1, v_msgData_3382_);
v___x_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3382_ = stack[0].m_obj;
lean_object* v___y_3383_ = stack[1].m_obj;
lean_object* v___y_3384_ = stack[2].m_obj;
lean_object* v_res_3399_;
v_res_3399_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3382_, v___y_3383_, v___y_3384_);
stack->m_obj
 = v_res_3399_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3404_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_ref_3409_; lean_object* v___x_3410_; lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3419_; 
v_ref_3409_ = lean_ctor_get(v___y_3406_, 2);
v___x_3410_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msg_3405_, v___y_3406_, v___y_3407_);
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
lean_inc(v_ref_3409_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_ref_3409_);
lean_ctor_set(v___x_3415_, 1, v_a_3411_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 1);
lean_ctor_set(v___x_3413_, 0, v___x_3415_);
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3405_ = stack[0].m_obj;
lean_object* v___y_3406_ = stack[1].m_obj;
lean_object* v___y_3407_ = stack[2].m_obj;
lean_object* v_res_3420_;
v_res_3420_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3405_, v___y_3406_, v___y_3407_);
stack->m_obj
 = v_res_3420_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3432_, lean_object* v_decl_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3437_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3438_ = l_Lean_MessageData_ofName(v___x_3432_);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v___x_3441_, v___y_3434_, v___y_3435_);
return v___x_3442_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3432_ = stack[0].m_obj;
lean_object* v_decl_3433_ = stack[1].m_obj;
lean_object* v___y_3434_ = stack[2].m_obj;
lean_object* v___y_3435_ = stack[3].m_obj;
lean_object* v_res_3443_;
v_res_3443_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3432_, v_decl_3433_, v___y_3434_, v___y_3435_);
stack->m_obj
 = v_res_3443_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3444_, lean_object* v_decl_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3444_, v_decl_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v_decl_3445_);
return v_res_3449_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3531_ = l_Lean_registerBuiltinAttribute(v___x_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3532_;
v_res_3532_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3532_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3534_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3535_, lean_object* v_msg_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3536_, v___y_3537_, v___y_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3536_ = stack[1].m_obj;
lean_object* v___y_3537_ = stack[2].m_obj;
lean_object* v___y_3538_ = stack[3].m_obj;
lean_object* v_res_3541_;
v_res_3541_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(lean_box(0), v_msg_3536_, v___y_3537_, v___y_3538_);
stack->m_obj
 = v_res_3541_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3542_, lean_object* v_msg_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(v_00_u03b1_3542_, v_msg_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3547_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_3548_, lean_object* v_name_3549_, uint8_t v_kind_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3549_, v_kind_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3549_ = stack[1].m_obj;
uint8_t v_kind_3550_ = stack[2].m_num;
lean_object* v___y_3551_ = stack[3].m_obj;
lean_object* v___y_3552_ = stack[4].m_obj;
lean_object* v___y_3553_ = stack[5].m_obj;
lean_object* v___y_3554_ = stack[6].m_obj;
lean_object* v_res_3557_;
v_res_3557_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(lean_box(0), v_name_3549_, v_kind_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
stack->m_obj
 = v_res_3557_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_3558_, lean_object* v_name_3559_, lean_object* v_kind_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
uint8_t v_kind_boxed_3566_; lean_object* v_res_3567_; 
v_kind_boxed_3566_ = lean_unbox(v_kind_3560_);
v_res_3567_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(v_00_u03b1_3558_, v_name_3559_, v_kind_boxed_3566_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
return v_res_3567_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3571_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3572_ = l_Lean_addBuiltinDocString(v___x_3570_, v___x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3573_;
v_res_3573_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3573_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3575_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatTable(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatTable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatTable(uint8_t builtin);
lean_object* initialize_Lean_Elab_App(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatTable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CtorElim(builtin);
}
#ifdef __cplusplus
}
#endif
