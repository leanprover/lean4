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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabAsElim;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkConstructorElimName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_mkConstructorElimName___closed__0 = (const lean_object*)&l_Lean_mkConstructorElimName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(lean_object* v_as_8_, size_t v_i_9_, size_t v_stop_10_, lean_object* v_b_11_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0___boxed(lean_object* v_as_18_, lean_object* v_i_19_, lean_object* v_stop_20_, lean_object* v_b_21_){
_start:
{
size_t v_i_boxed_22_; size_t v_stop_boxed_23_; lean_object* v_res_24_; 
v_i_boxed_22_ = lean_unbox_usize(v_i_19_);
lean_dec(v_i_19_);
v_stop_boxed_23_ = lean_unbox_usize(v_stop_20_);
lean_dec(v_stop_20_);
v_res_24_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(v_as_18_, v_i_boxed_22_, v_stop_boxed_23_, v_b_21_);
lean_dec_ref(v_as_18_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(lean_object* v_l_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v_lvls_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v_last_35_; lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_28_ = lean_box(0);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0));
v_lvls_31_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(v_l_27_, v___x_30_);
v___x_32_ = lean_array_get_size(v_lvls_31_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_sub(v___x_32_, v___x_33_);
v_last_35_ = lean_array_get(v___x_28_, v_lvls_31_, v___x_34_);
lean_dec(v___x_34_);
v___x_36_ = lean_array_pop(v_lvls_31_);
v___x_37_ = lean_array_get_size(v___x_36_);
v___x_38_ = lean_nat_dec_lt(v___x_29_, v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_36_);
return v_last_35_;
}
else
{
size_t v___x_39_; size_t v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_usize_of_nat(v___x_37_);
v___x_40_ = ((size_t)0ULL);
v___x_41_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(v___x_36_, v___x_39_, v___x_40_, v_last_35_);
lean_dec_ref(v___x_36_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_1562__overap_50_; lean_object* v___x_51_; 
v___f_49_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_1562__overap_50_ = lean_panic_fn_borrowed(v___f_49_, v_msg_43_);
lean_inc(v___y_47_);
lean_inc_ref(v___y_46_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
v___x_51_ = lean_apply_5(v___x_1562__overap_50_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, lean_box(0));
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(v_msg_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(lean_object* v_a_59_, lean_object* v_b_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_array_66_; lean_object* v_start_67_; lean_object* v_stop_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_84_; 
v_array_66_ = lean_ctor_get(v_a_59_, 0);
v_start_67_ = lean_ctor_get(v_a_59_, 1);
v_stop_68_ = lean_ctor_get(v_a_59_, 2);
v_isSharedCheck_84_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_84_ == 0)
{
v___x_70_ = v_a_59_;
v_isShared_71_ = v_isSharedCheck_84_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_stop_68_);
lean_inc(v_start_67_);
lean_inc(v_array_66_);
lean_dec(v_a_59_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_84_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; 
v___x_72_ = lean_nat_dec_lt(v_start_67_, v_stop_68_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_del_object(v___x_70_);
lean_dec(v_stop_68_);
lean_dec(v_start_67_);
lean_dec_ref(v_array_66_);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v_b_60_);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_start_67_, v___x_74_);
lean_inc_ref(v_array_66_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_75_);
v___x_77_ = v___x_70_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_array_66_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_stop_68_);
v___x_77_ = v_reuseFailAlloc_83_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_array_fget(v_array_66_, v_start_67_);
lean_dec(v_start_67_);
lean_dec_ref(v_array_66_);
v___x_79_ = l_Lean_Meta_getLevel(v___x_78_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_81_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_79_, 1);
v___x_81_ = l_Lean_mkLevelMax_x27(v_b_60_, v_a_80_);
v_a_59_ = v___x_77_;
v_b_60_ = v___x_81_;
goto _start;
}
else
{
lean_dec_ref(v___x_77_);
lean_dec(v_b_60_);
return v___x_79_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg___boxed(lean_object* v_a_85_, lean_object* v_b_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v_a_85_, v_b_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_92_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2));
v___x_97_ = lean_unsigned_to_nat(2u);
v___x_98_ = lean_unsigned_to_nat(32u);
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1));
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_101_ = l_mkPanicMessageWithDecl(v___x_100_, v___x_99_, v___x_98_, v___x_97_, v___x_96_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(lean_object* v_es_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_array_get_size(v_es_102_);
v___x_110_ = lean_nat_dec_lt(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec_ref(v_es_102_);
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3);
v___x_112_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(v___x_111_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = l_Lean_instInhabitedExpr;
v___x_114_ = lean_array_get_borrowed(v___x_113_, v_es_102_, v___x_108_);
lean_inc(v___x_114_);
v___x_115_ = l_Lean_Meta_getLevel(v___x_114_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = l_Array_toSubarray___redArg(v_es_102_, v___x_117_, v___x_109_);
v___x_119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v___x_118_, v_a_116_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_129_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_129_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_124_ = l_Lean_Level_normalize(v_a_120_);
lean_dec(v_a_120_);
v___x_125_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(v___x_124_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_125_);
v___x_127_ = v___x_122_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
return v___x_119_;
}
}
else
{
lean_dec_ref(v_es_102_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___boxed(lean_object* v_es_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(v_es_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1(lean_object* v_inst_137_, lean_object* v_R_138_, lean_object* v_a_139_, lean_object* v_b_140_, lean_object* v_c_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v_a_139_, v_b_140_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___boxed(lean_object* v_inst_148_, lean_object* v_R_149_, lean_object* v_a_150_, lean_object* v_b_151_, lean_object* v_c_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1(v_inst_148_, v_R_149_, v_a_150_, v_b_151_, v_c_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(lean_object* v_r_162_, lean_object* v_t_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; 
lean_inc_ref(v_t_163_);
v___x_169_ = l_Lean_Meta_getLevel(v_t_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_183_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_183_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_183_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_183_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v_a_170_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v_r_162_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = l_Lean_mkConst(v___x_174_, v___x_177_);
v___x_179_ = l_Lean_Expr_app___override(v___x_178_, v_t_163_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_179_);
v___x_181_ = v___x_172_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec_ref(v_t_163_);
lean_dec(v_r_162_);
v_a_184_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_169_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_169_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___boxed(lean_object* v_r_192_, lean_object* v_t_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(v_r_192_, v_t_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(lean_object* v_msgData_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_env_207_; uint8_t v___x_208_; lean_object* v_env_209_; lean_object* v___x_210_; lean_object* v_toCold_211_; lean_object* v_mctx_212_; lean_object* v_lctx_213_; lean_object* v_options_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_206_ = lean_st_ref_get(v___y_204_);
v_env_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc_ref(v_env_207_);
lean_dec(v___x_206_);
v___x_208_ = 0;
v_env_209_ = l_Lean_Environment_setRecordingDeps(v_env_207_, v___x_208_);
v___x_210_ = lean_st_ref_get(v___y_202_);
v_toCold_211_ = lean_ctor_get(v___y_203_, 0);
v_mctx_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_mctx_212_);
lean_dec(v___x_210_);
v_lctx_213_ = lean_ctor_get(v___y_201_, 2);
v_options_214_ = lean_ctor_get(v_toCold_211_, 2);
lean_inc_ref(v_options_214_);
lean_inc_ref(v_lctx_213_);
v___x_215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_215_, 0, v_env_209_);
lean_ctor_set(v___x_215_, 1, v_mctx_212_);
lean_ctor_set(v___x_215_, 2, v_lctx_213_);
lean_ctor_set(v___x_215_, 3, v_options_214_);
v___x_216_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_msgData_200_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0___boxed(lean_object* v_msgData_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msgData_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_ref_231_; lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_ref_231_ = lean_ctor_get(v___y_228_, 2);
v___x_232_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msg_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_inc(v_ref_231_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_ref_231_);
lean_ctor_set(v___x_237_, 1, v_a_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 1);
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg___boxed(lean_object* v_msg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(lean_object* v_t_256_, lean_object* v_k_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; 
lean_inc(v_a_261_);
lean_inc_ref(v_a_260_);
lean_inc(v_a_259_);
lean_inc_ref(v_a_258_);
v___x_263_ = lean_whnf(v_t_256_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = l_Lean_Expr_isAppOfArity(v_a_264_, v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref(v_k_257_);
v___x_268_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1);
v___x_269_ = l_Lean_MessageData_ofExpr(v_a_264_);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_270_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
return v___x_271_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = l_Lean_Expr_appArg_x21(v_a_264_);
lean_inc(v_a_261_);
lean_inc_ref(v_a_260_);
lean_inc(v_a_259_);
lean_inc_ref(v_a_258_);
lean_inc_ref(v___x_272_);
v___x_273_ = lean_apply_6(v_k_257_, v___x_272_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, lean_box(0));
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_286_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_286_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_286_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_286_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3));
v___x_279_ = l_Lean_Expr_appFn_x21(v_a_264_);
lean_dec(v_a_264_);
v___x_280_ = l_Lean_Expr_constLevels_x21(v___x_279_);
lean_dec_ref(v___x_279_);
v___x_281_ = l_Lean_mkConst(v___x_278_, v___x_280_);
v___x_282_ = l_Lean_mkAppB(v___x_281_, v___x_272_, v_a_274_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_282_);
v___x_284_ = v___x_276_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_dec_ref(v___x_272_);
lean_dec(v_a_264_);
return v___x_273_;
}
}
}
else
{
lean_dec_ref(v_k_257_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___boxed(lean_object* v_t_287_, lean_object* v_k_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v_t_287_, v_k_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(lean_object* v_00_u03b1_295_, lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___boxed(lean_object* v_00_u03b1_303_, lean_object* v_msg_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(v_00_u03b1_303_, v_msg_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0));
v___x_313_ = l_Lean_stringToMessageData(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(lean_object* v_e_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc_ref(v_e_318_);
v___x_324_ = lean_infer_type(v_e_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
v___x_326_ = lean_whnf(v_a_325_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_347_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_347_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_347_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_347_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = l_Lean_Expr_isAppOfArity(v_a_327_, v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_del_object(v___x_329_);
lean_dec_ref(v_e_318_);
v___x_334_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1);
v___x_335_ = l_Lean_MessageData_ofExpr(v_a_327_);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_336_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_338_ = l_Lean_Expr_appArg_x21(v_a_327_);
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3));
v___x_340_ = l_Lean_Expr_appFn_x21(v_a_327_);
lean_dec(v_a_327_);
v___x_341_ = l_Lean_Expr_constLevels_x21(v___x_340_);
lean_dec_ref(v___x_340_);
v___x_342_ = l_Lean_mkConst(v___x_339_, v___x_341_);
v___x_343_ = l_Lean_mkAppB(v___x_342_, v___x_338_, v_e_318_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_343_);
v___x_345_ = v___x_329_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_dec_ref(v_e_318_);
return v___x_326_;
}
}
else
{
lean_dec_ref(v_e_318_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___boxed(lean_object* v_e_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_e_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(lean_object* v_a_355_, size_t v_sz_356_, size_t v_i_357_, lean_object* v_bs_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = lean_usize_dec_lt(v_i_357_, v_sz_356_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec(v_a_355_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v_bs_358_);
return v___x_365_;
}
else
{
lean_object* v_v_366_; lean_object* v___x_367_; lean_object* v_bs_x27_368_; lean_object* v___x_369_; 
v_v_366_ = lean_array_uget(v_bs_358_, v_i_357_);
v___x_367_ = lean_unsigned_to_nat(0u);
v_bs_x27_368_ = lean_array_uset(v_bs_358_, v_i_357_, v___x_367_);
lean_inc(v_a_355_);
v___x_369_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(v_a_355_, v_v_366_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_add(v_i_357_, v___x_371_);
v___x_373_ = lean_array_uset(v_bs_x27_368_, v_i_357_, v_a_370_);
v_i_357_ = v___x_372_;
v_bs_358_ = v___x_373_;
goto _start;
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_bs_x27_368_);
lean_dec(v_a_355_);
v_a_375_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_369_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_369_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0___boxed(lean_object* v_a_383_, lean_object* v_sz_384_, lean_object* v_i_385_, lean_object* v_bs_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
size_t v_sz_boxed_392_; size_t v_i_boxed_393_; lean_object* v_res_394_; 
v_sz_boxed_392_ = lean_unbox_usize(v_sz_384_);
lean_dec(v_sz_384_);
v_i_boxed_393_ = lean_unbox_usize(v_i_385_);
lean_dec(v_i_385_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_383_, v_sz_boxed_392_, v_i_boxed_393_, v_bs_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = l_Lean_Level_ofNat(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(lean_object* v_n_397_, lean_object* v_es_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_404_; 
lean_inc_ref(v_es_398_);
v___x_404_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(v_es_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; size_t v_sz_410_; size_t v___x_411_; lean_object* v___x_412_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc_n(v_a_405_, 2);
lean_dec_ref_known(v___x_404_, 1);
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0);
v___x_407_ = l_Lean_mkLevelMax_x27(v_a_405_, v___x_406_);
v___x_408_ = l_Lean_Level_normalize(v___x_407_);
lean_dec(v___x_407_);
v___x_409_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(v___x_408_);
v_sz_410_ = lean_array_size(v_es_398_);
v___x_411_ = ((size_t)0ULL);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_405_, v_sz_410_, v___x_411_, v_es_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = l_Lean_Expr_sort___override(v___x_409_);
v___x_415_ = l_Lean_mkNatLookupTable(v_n_397_, v___x_414_, v_a_413_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
lean_dec(v_a_413_);
return v___x_415_;
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v___x_409_);
lean_dec_ref(v_n_397_);
v_a_416_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_412_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec_ref(v_es_398_);
lean_dec_ref(v_n_397_);
v_a_424_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_404_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_404_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___boxed(lean_object* v_n_432_, lean_object* v_es_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_n_432_, v_es_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(lean_object* v_indName_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0));
v___x_443_ = l_Lean_Name_str___override(v_indName_441_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElimName(lean_object* v_indName_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_mkCtorElimName___closed__0));
v___x_447_ = l_Lean_Name_str___override(v_indName_445_, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(lean_object* v_n1_448_, lean_object* v_n2_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_privatePrefix_x3f(v_n2_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_privateToUserName(v_n1_448_);
return v___x_451_;
}
else
{
lean_object* v_val_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_val_452_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v___x_450_, 1);
v___x_453_ = l_Lean_privateToUserName(v_n1_448_);
v___x_454_ = l_Lean_Name_appendCore(v_val_452_, v___x_453_);
lean_dec(v_val_452_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName(lean_object* v_indName_456_, lean_object* v_conName_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = ((lean_object*)(l_Lean_mkConstructorElimName___closed__0));
v___x_459_ = l_Lean_Name_str___override(v_conName_457_, v___x_458_);
v___x_460_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(v___x_459_, v_indName_456_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(lean_object* v_k_461_, lean_object* v_b_462_, lean_object* v_c_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; 
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
v___x_469_ = lean_apply_7(v_k_461_, v_b_462_, v_c_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, lean_box(0));
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed(lean_object* v_k_470_, lean_object* v_b_471_, lean_object* v_c_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(v_k_470_, v_b_471_, v_c_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(lean_object* v_type_479_, lean_object* v_k_480_, uint8_t v_cleanupAnnotations_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___f_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___f_487_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_487_, 0, v_k_480_);
v___x_488_ = 0;
v___x_489_ = lean_box(0);
v___x_490_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_488_, v___x_489_, v_type_479_, v___f_487_, v_cleanupAnnotations_481_, v___x_488_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_a_499_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_490_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_490_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___boxed(lean_object* v_type_507_, lean_object* v_k_508_, lean_object* v_cleanupAnnotations_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_515_; lean_object* v_res_516_; 
v_cleanupAnnotations_boxed_515_ = lean_unbox(v_cleanupAnnotations_509_);
v_res_516_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_507_, v_k_508_, v_cleanupAnnotations_boxed_515_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(lean_object* v_00_u03b1_517_, lean_object* v_type_518_, lean_object* v_k_519_, uint8_t v_cleanupAnnotations_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_518_, v_k_519_, v_cleanupAnnotations_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___boxed(lean_object* v_00_u03b1_527_, lean_object* v_type_528_, lean_object* v_k_529_, lean_object* v_cleanupAnnotations_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_536_; lean_object* v_res_537_; 
v_cleanupAnnotations_boxed_536_ = lean_unbox(v_cleanupAnnotations_530_);
v_res_537_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(v_00_u03b1_527_, v_type_528_, v_k_529_, v_cleanupAnnotations_boxed_536_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(lean_object* v_name_538_, lean_object* v_levelParams_539_, lean_object* v_type_540_, lean_object* v_value_541_, lean_object* v_hints_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; uint8_t v___y_547_; lean_object* v_env_555_; uint8_t v___x_556_; 
v___x_545_ = lean_st_ref_get(v___y_543_);
v_env_555_ = lean_ctor_get(v___x_545_, 0);
lean_inc_ref_n(v_env_555_, 2);
lean_dec(v___x_545_);
v___x_556_ = l_Lean_Environment_hasUnsafe(v_env_555_, v_type_540_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; 
v___x_557_ = l_Lean_Environment_hasUnsafe(v_env_555_, v_value_541_);
if (v___x_557_ == 0)
{
uint8_t v___x_558_; 
v___x_558_ = 1;
v___y_547_ = v___x_558_;
goto v___jp_546_;
}
else
{
goto v___jp_553_;
}
}
else
{
lean_dec_ref(v_env_555_);
goto v___jp_553_;
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc(v_name_538_);
v___x_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_548_, 0, v_name_538_);
lean_ctor_set(v___x_548_, 1, v_levelParams_539_);
lean_ctor_set(v___x_548_, 2, v_type_540_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_550_, 0, v_name_538_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_551_, 0, v___x_548_);
lean_ctor_set(v___x_551_, 1, v_value_541_);
lean_ctor_set(v___x_551_, 2, v_hints_542_);
lean_ctor_set(v___x_551_, 3, v___x_550_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*4, v___y_547_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
v___jp_553_:
{
uint8_t v___x_554_; 
v___x_554_ = 0;
v___y_547_ = v___x_554_;
goto v___jp_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg___boxed(lean_object* v_name_559_, lean_object* v_levelParams_560_, lean_object* v_type_561_, lean_object* v_value_562_, lean_object* v_hints_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_559_, v_levelParams_560_, v_type_561_, v_value_562_, v_hints_563_, v___y_564_);
lean_dec(v___y_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(lean_object* v_name_567_, lean_object* v_levelParams_568_, lean_object* v_type_569_, lean_object* v_value_570_, lean_object* v_hints_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_567_, v_levelParams_568_, v_type_569_, v_value_570_, v_hints_571_, v___y_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___boxed(lean_object* v_name_578_, lean_object* v_levelParams_579_, lean_object* v_type_580_, lean_object* v_value_581_, lean_object* v_hints_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(v_name_578_, v_levelParams_579_, v_type_580_, v_value_581_, v_hints_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___f_595_; lean_object* v___x_4617__overap_596_; lean_object* v___x_597_; 
v___f_595_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_4617__overap_596_ = lean_panic_fn_borrowed(v___f_595_, v_msg_589_);
lean_inc(v___y_593_);
lean_inc_ref(v___y_592_);
lean_inc(v___y_591_);
lean_inc_ref(v___y_590_);
v___x_597_ = lean_apply_5(v___x_4617__overap_596_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, lean_box(0));
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8___boxed(lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(size_t v_sz_605_, size_t v_i_606_, lean_object* v_bs_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = lean_usize_dec_lt(v_i_606_, v_sz_605_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_bs_607_);
return v___x_614_;
}
else
{
lean_object* v_v_615_; lean_object* v___x_616_; lean_object* v_bs_x27_617_; lean_object* v___x_618_; 
v_v_615_ = lean_array_uget(v_bs_607_, v_i_606_);
v___x_616_ = lean_unsigned_to_nat(0u);
v_bs_x27_617_ = lean_array_uset(v_bs_607_, v_i_606_, v___x_616_);
lean_inc(v___y_611_);
lean_inc_ref(v___y_610_);
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
v___x_618_ = lean_infer_type(v_v_615_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = ((size_t)1ULL);
v___x_621_ = lean_usize_add(v_i_606_, v___x_620_);
v___x_622_ = lean_array_uset(v_bs_x27_617_, v_i_606_, v_a_619_);
v_i_606_ = v___x_621_;
v_bs_607_ = v___x_622_;
goto _start;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_bs_x27_617_);
v_a_624_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_618_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_618_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1___boxed(lean_object* v_sz_632_, lean_object* v_i_633_, lean_object* v_bs_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
size_t v_sz_boxed_640_; size_t v_i_boxed_641_; lean_object* v_res_642_; 
v_sz_boxed_640_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_641_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_sz_boxed_640_, v_i_boxed_641_, v_bs_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v___x_645_, uint8_t v___x_646_, lean_object* v_ctorIdx_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
size_t v_sz_653_; size_t v___x_654_; lean_object* v___x_655_; 
v_sz_653_ = lean_array_size(v___x_643_);
v___x_654_ = ((size_t)0ULL);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_sz_653_, v___x_654_, v___x_643_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
lean_inc_ref(v_ctorIdx_647_);
v___x_657_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_ctorIdx_647_, v_a_656_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = lean_unsigned_to_nat(2u);
v___x_660_ = lean_mk_empty_array_with_capacity(v___x_659_);
v___x_661_ = lean_array_push(v___x_660_, v___x_644_);
v___x_662_ = lean_array_push(v___x_661_, v_ctorIdx_647_);
v___x_663_ = l_Array_append___redArg(v___x_645_, v___x_662_);
lean_dec_ref(v___x_662_);
v___x_664_ = 1;
v___x_665_ = 1;
v___x_666_ = l_Lean_Meta_mkLambdaFVars(v___x_663_, v_a_658_, v___x_646_, v___x_664_, v___x_646_, v___x_664_, v___x_665_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec_ref(v___x_663_);
return v___x_666_;
}
else
{
lean_dec_ref(v_ctorIdx_647_);
lean_dec_ref(v___x_645_);
lean_dec_ref(v___x_644_);
return v___x_657_;
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_ctorIdx_647_);
lean_dec_ref(v___x_645_);
lean_dec_ref(v___x_644_);
v_a_667_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_655_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_655_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed(lean_object* v___x_675_, lean_object* v___x_676_, lean_object* v___x_677_, lean_object* v___x_678_, lean_object* v_ctorIdx_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v___x_7333__boxed_685_; lean_object* v_res_686_; 
v___x_7333__boxed_685_ = lean_unbox(v___x_678_);
v_res_686_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(v___x_675_, v___x_676_, v___x_677_, v___x_7333__boxed_685_, v_ctorIdx_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0(lean_object* v_k_687_, lean_object* v_b_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
v___x_694_ = lean_apply_6(v_k_687_, v_b_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, lean_box(0));
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0(v_k_695_, v_b_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(lean_object* v_name_703_, uint8_t v_bi_704_, lean_object* v_type_705_, lean_object* v_k_706_, uint8_t v_kind_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___f_713_; lean_object* v___x_714_; 
v___f_713_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_713_, 0, v_k_706_);
v___x_714_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_703_, v_bi_704_, v_type_705_, v___f_713_, v_kind_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v_a_723_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_714_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_714_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___boxed(lean_object* v_name_731_, lean_object* v_bi_732_, lean_object* v_type_733_, lean_object* v_k_734_, lean_object* v_kind_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v_bi_boxed_741_; uint8_t v_kind_boxed_742_; lean_object* v_res_743_; 
v_bi_boxed_741_ = lean_unbox(v_bi_732_);
v_kind_boxed_742_ = lean_unbox(v_kind_735_);
v_res_743_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_731_, v_bi_boxed_741_, v_type_733_, v_k_734_, v_kind_boxed_742_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(lean_object* v_name_744_, lean_object* v_type_745_, lean_object* v_k_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; 
v___x_752_ = 0;
v___x_753_ = 0;
v___x_754_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_744_, v___x_752_, v_type_745_, v_k_746_, v___x_753_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg___boxed(lean_object* v_name_755_, lean_object* v_type_756_, lean_object* v_k_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v_name_755_, v_type_756_, v_k_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_box(0);
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_772_ = l_Lean_mkConst(v___x_771_, v___x_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(lean_object* v_val_773_, lean_object* v___x_774_, lean_object* v___x_775_, uint8_t v___x_776_, lean_object* v_xs_777_, lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_numParams_784_; lean_object* v_numIndices_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_numParams_784_ = lean_ctor_get(v_val_773_, 1);
lean_inc_n(v_numParams_784_, 2);
v_numIndices_785_ = lean_ctor_get(v_val_773_, 2);
lean_inc(v_numIndices_785_);
lean_dec_ref(v_val_773_);
lean_inc_ref(v_xs_777_);
v___x_786_ = l_Array_toSubarray___redArg(v_xs_777_, v___x_774_, v_numParams_784_);
v___x_787_ = l_Subarray_copy___redArg(v___x_786_);
v___x_788_ = lean_array_get(v___x_775_, v_xs_777_, v_numParams_784_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_numParams_784_, v___x_789_);
lean_dec(v_numParams_784_);
v___x_791_ = lean_nat_add(v___x_790_, v_numIndices_785_);
lean_dec(v_numIndices_785_);
lean_dec(v___x_790_);
v___x_792_ = lean_nat_add(v___x_791_, v___x_789_);
lean_dec(v___x_791_);
v___x_793_ = lean_array_get_size(v_xs_777_);
v___x_794_ = l_Array_toSubarray___redArg(v_xs_777_, v___x_792_, v___x_793_);
v___x_795_ = l_Subarray_copy___redArg(v___x_794_);
v___x_796_ = lean_box(v___x_776_);
v___f_797_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_797_, 0, v___x_795_);
lean_closure_set(v___f_797_, 1, v___x_788_);
lean_closure_set(v___f_797_, 2, v___x_787_);
lean_closure_set(v___f_797_, 3, v___x_796_);
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_799_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_800_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_798_, v___x_799_, v___f_797_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed(lean_object* v_val_801_, lean_object* v___x_802_, lean_object* v___x_803_, lean_object* v___x_804_, lean_object* v_xs_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
uint8_t v___x_7510__boxed_812_; lean_object* v_res_813_; 
v___x_7510__boxed_812_ = lean_unbox(v___x_804_);
v_res_813_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(v_val_801_, v___x_802_, v___x_803_, v___x_7510__boxed_812_, v_xs_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec_ref(v_x_806_);
lean_dec_ref(v___x_803_);
return v_res_813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
lean_ctor_set(v___x_819_, 2, v___x_818_);
lean_ctor_set(v___x_819_, 3, v___x_818_);
lean_ctor_set(v___x_819_, 4, v___x_817_);
lean_ctor_set(v___x_819_, 5, v___x_817_);
lean_ctor_set(v___x_819_, 6, v___x_817_);
lean_ctor_set(v___x_819_, 7, v___x_817_);
lean_ctor_set(v___x_819_, 8, v___x_817_);
lean_ctor_set(v___x_819_, 9, v___x_817_);
lean_ctor_set(v___x_819_, 10, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_unsigned_to_nat(32u);
v___x_821_ = lean_mk_empty_array_with_capacity(v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__4(void){
_start:
{
size_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_823_ = ((size_t)5ULL);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_unsigned_to_nat(32u);
v___x_826_ = lean_mk_empty_array_with_capacity(v___x_825_);
v___x_827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3);
v___x_828_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
lean_ctor_set(v___x_828_, 2, v___x_824_);
lean_ctor_set(v___x_828_, 3, v___x_824_);
lean_ctor_set_usize(v___x_828_, 4, v___x_823_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_box(1);
v___x_830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__4);
v___x_831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__1);
v___x_832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
lean_ctor_set(v___x_832_, 2, v___x_829_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__6));
v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__8));
v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__10));
v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__12));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__14));
v___x_847_ = l_Lean_stringToMessageData(v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__16));
v___x_850_ = l_Lean_stringToMessageData(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__18));
v___x_853_ = l_Lean_stringToMessageData(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__21(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__20));
v___x_856_ = l_Lean_stringToMessageData(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__23(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__22));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__25(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__24));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__27(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__26));
v___x_865_ = l_Lean_stringToMessageData(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(lean_object* v_msg_866_, lean_object* v_declHint_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v_env_872_; uint8_t v___x_873_; 
v___x_870_ = lean_box(0);
v___x_871_ = lean_st_ref_get(v___y_868_);
v_env_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc_ref(v_env_872_);
lean_dec(v___x_871_);
v___x_873_ = l_Lean_Name_isAnonymous(v_declHint_867_);
if (v___x_873_ == 0)
{
uint8_t v_isExporting_874_; 
v_isExporting_874_ = lean_ctor_get_uint8(v_env_872_, sizeof(void*)*13);
if (v_isExporting_874_ == 0)
{
lean_object* v___x_875_; 
lean_dec_ref(v_env_872_);
lean_dec(v_declHint_867_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v_msg_866_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; uint8_t v___x_877_; 
lean_inc_ref(v_env_872_);
v___x_876_ = l_Lean_Environment_setExporting(v_env_872_, v___x_873_);
lean_inc(v_declHint_867_);
lean_inc_ref(v___x_876_);
v___x_877_ = l_Lean_Environment_contains(v___x_876_, v_declHint_867_, v_isExporting_874_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec_ref(v___x_876_);
lean_dec_ref(v_env_872_);
lean_dec(v_declHint_867_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v_msg_866_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v_c_884_; lean_object* v___x_885_; 
v___x_879_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2);
v___x_880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5);
v___x_881_ = l_Lean_Options_empty;
lean_inc_ref(v___x_876_);
v___x_882_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_882_, 0, v___x_876_);
lean_ctor_set(v___x_882_, 1, v___x_879_);
lean_ctor_set(v___x_882_, 2, v___x_880_);
lean_ctor_set(v___x_882_, 3, v___x_881_);
lean_inc(v_declHint_867_);
v___x_883_ = l_Lean_MessageData_ofConstName(v_declHint_867_, v___x_873_);
v_c_884_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_884_, 0, v___x_882_);
lean_ctor_set(v_c_884_, 1, v___x_883_);
v___x_885_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_876_, v_declHint_867_);
lean_dec_ref(v___x_876_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref(v_env_872_);
lean_dec(v_declHint_867_);
v___x_886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v_c_884_);
v___x_888_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_MessageData_note(v___x_889_);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v_msg_866_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
else
{
lean_object* v_val_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_946_; 
v_val_893_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_946_ == 0)
{
v___x_895_ = v___x_885_;
v_isShared_896_ = v_isSharedCheck_946_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_val_893_);
lean_dec(v___x_885_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_946_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v_modules_898_; lean_object* v_moduleNames_899_; lean_object* v_mod_900_; uint8_t v___x_915_; 
v___x_897_ = l_Lean_Environment_header(v_env_872_);
lean_dec_ref(v_env_872_);
v_modules_898_ = lean_ctor_get(v___x_897_, 3);
lean_inc_ref(v_modules_898_);
v_moduleNames_899_ = lean_ctor_get(v___x_897_, 4);
lean_inc_ref(v_moduleNames_899_);
lean_dec_ref(v___x_897_);
v_mod_900_ = lean_array_get(v___x_870_, v_moduleNames_899_, v_val_893_);
lean_dec_ref(v_moduleNames_899_);
v___x_915_ = l_Lean_isPrivateName(v_declHint_867_);
lean_dec(v_declHint_867_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_array_get_size(v_modules_898_);
v___x_917_ = lean_nat_dec_lt(v_val_893_, v___x_916_);
if (v___x_917_ == 0)
{
lean_dec_ref(v_modules_898_);
lean_dec(v_val_893_);
goto v___jp_901_;
}
else
{
lean_object* v___x_918_; lean_object* v_toImport_919_; uint8_t v_isExported_920_; 
v___x_918_ = lean_array_fget(v_modules_898_, v_val_893_);
lean_dec(v_val_893_);
lean_dec_ref(v_modules_898_);
v_toImport_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_ref(v_toImport_919_);
lean_dec(v___x_918_);
v_isExported_920_ = lean_ctor_get_uint8(v_toImport_919_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_919_);
if (v_isExported_920_ == 0)
{
goto v___jp_901_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_del_object(v___x_895_);
v___x_921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v_c_884_);
v___x_923_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_MessageData_ofName(v_mod_900_);
lean_inc_ref(v___x_925_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__21);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_925_);
v___x_930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__23);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_MessageData_note(v___x_931_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v_msg_866_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec_ref(v_modules_898_);
lean_del_object(v___x_895_);
lean_dec(v_val_893_);
v___x_935_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v_c_884_);
v___x_937_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__25);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l_Lean_MessageData_ofName(v_mod_900_);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__27);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_MessageData_note(v___x_942_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v_msg_866_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
v___jp_901_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v_c_884_);
v___x_904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_MessageData_ofName(v_mod_900_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_MessageData_note(v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v_msg_866_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 0);
lean_ctor_set(v___x_895_, 0, v___x_911_);
v___x_913_ = v___x_895_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_947_; 
lean_dec_ref(v_env_872_);
lean_dec(v_declHint_867_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_msg_866_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___boxed(lean_object* v_msg_948_, lean_object* v_declHint_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(v_msg_948_, v_declHint_949_, v___y_950_);
lean_dec(v___y_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14(lean_object* v_msg_953_, lean_object* v_declHint_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_970_; 
v___x_960_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(v_msg_953_, v_declHint_954_, v___y_958_);
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_970_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_970_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_970_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_965_ = l_Lean_unknownIdentifierMessageTag;
v___x_966_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v_a_961_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_966_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14___boxed(lean_object* v_msg_971_, lean_object* v_declHint_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14(v_msg_971_, v_declHint_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(lean_object* v_ref_979_, lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_toCold_986_; lean_object* v_currRecDepth_987_; lean_object* v_ref_988_; uint16_t v_optionFlags_989_; uint8_t v_suppressElabErrors_990_; uint8_t v_checkDeprecated_991_; uint8_t v_isRecordingDeps_992_; lean_object* v_ref_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_toCold_986_ = lean_ctor_get(v___y_983_, 0);
v_currRecDepth_987_ = lean_ctor_get(v___y_983_, 1);
v_ref_988_ = lean_ctor_get(v___y_983_, 2);
v_optionFlags_989_ = lean_ctor_get_uint16(v___y_983_, sizeof(void*)*3);
v_suppressElabErrors_990_ = lean_ctor_get_uint8(v___y_983_, sizeof(void*)*3 + 2);
v_checkDeprecated_991_ = lean_ctor_get_uint8(v___y_983_, sizeof(void*)*3 + 3);
v_isRecordingDeps_992_ = lean_ctor_get_uint8(v___y_983_, sizeof(void*)*3 + 4);
v_ref_993_ = l_Lean_replaceRef(v_ref_979_, v_ref_988_);
lean_inc(v_currRecDepth_987_);
lean_inc_ref(v_toCold_986_);
v___x_994_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_994_, 0, v_toCold_986_);
lean_ctor_set(v___x_994_, 1, v_currRecDepth_987_);
lean_ctor_set(v___x_994_, 2, v_ref_993_);
lean_ctor_set_uint16(v___x_994_, sizeof(void*)*3, v_optionFlags_989_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*3 + 2, v_suppressElabErrors_990_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*3 + 3, v_checkDeprecated_991_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*3 + 4, v_isRecordingDeps_992_);
v___x_995_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_980_, v___y_981_, v___y_982_, v___x_994_, v___y_984_);
lean_dec_ref_known(v___x_994_, 3);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_ref_996_, lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(v_ref_996_, v_msg_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v_ref_996_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(lean_object* v_ref_1004_, lean_object* v_msg_1005_, lean_object* v_declHint_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1014_; 
v___x_1012_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14(v_msg_1005_, v_declHint_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(v_ref_1004_, v_a_1013_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg___boxed(lean_object* v_ref_1015_, lean_object* v_msg_1016_, lean_object* v_declHint_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(v_ref_1015_, v_msg_1016_, v_declHint_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v_ref_1015_);
return v_res_1023_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1030_, lean_object* v_constName_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1037_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_1038_ = 0;
lean_inc(v_constName_1031_);
v___x_1039_ = l_Lean_MessageData_ofConstName(v_constName_1031_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(v_ref_1030_, v___x_1042_, v_constName_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1044_, lean_object* v_constName_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1044_, v_constName_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v_ref_1044_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(lean_object* v_constName_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_ref_1058_; lean_object* v___x_1059_; 
v_ref_1058_ = lean_ctor_get(v___y_1055_, 2);
v___x_1059_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1058_, v_constName_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(lean_object* v_constName_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_env_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = lean_st_ref_get(v___y_1071_);
v_env_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_env_1074_);
lean_dec(v___x_1073_);
v___x_1075_ = 0;
lean_inc(v_constName_1067_);
v___x_1076_ = l_Lean_Environment_find_x3f(v_env_1074_, v_constName_1067_, v___x_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1077_;
}
else
{
lean_object* v_val_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_constName_1067_);
v_val_1078_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1076_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_val_1078_);
lean_dec(v___x_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 0);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_val_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(lean_object* v_constName_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_constName_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1092_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object* v___dummy_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg();
return v_res_1098_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg();
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0);
v___x_1108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
lean_ctor_set(v___x_1108_, 2, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1109_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4);
v___x_1110_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3);
v___x_1111_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0);
v___x_1112_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
v___x_1113_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
lean_ctor_set(v___x_1113_, 2, v___x_1110_);
lean_ctor_set(v___x_1113_, 3, v___x_1111_);
lean_ctor_set(v___x_1113_, 4, v___x_1111_);
lean_ctor_set(v___x_1113_, 5, v___x_1111_);
lean_ctor_set(v___x_1113_, 6, v___x_1109_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(lean_object* v_declName_1114_, uint8_t v_s_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v_env_1120_; lean_object* v_nextMacroScope_1121_; lean_object* v_ngen_1122_; lean_object* v_auxDeclNGen_1123_; lean_object* v_traceState_1124_; lean_object* v_recordedDeps_1125_; lean_object* v_messages_1126_; lean_object* v_infoState_1127_; lean_object* v_snapshotTasks_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1157_; 
v___x_1119_ = lean_st_ref_take(v___y_1117_);
v_env_1120_ = lean_ctor_get(v___x_1119_, 0);
v_nextMacroScope_1121_ = lean_ctor_get(v___x_1119_, 1);
v_ngen_1122_ = lean_ctor_get(v___x_1119_, 2);
v_auxDeclNGen_1123_ = lean_ctor_get(v___x_1119_, 3);
v_traceState_1124_ = lean_ctor_get(v___x_1119_, 4);
v_recordedDeps_1125_ = lean_ctor_get(v___x_1119_, 6);
v_messages_1126_ = lean_ctor_get(v___x_1119_, 7);
v_infoState_1127_ = lean_ctor_get(v___x_1119_, 8);
v_snapshotTasks_1128_ = lean_ctor_get(v___x_1119_, 9);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v___x_1119_, 5);
lean_dec(v_unused_1158_);
v___x_1130_ = v___x_1119_;
v_isShared_1131_ = v_isSharedCheck_1157_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snapshotTasks_1128_);
lean_inc(v_infoState_1127_);
lean_inc(v_messages_1126_);
lean_inc(v_recordedDeps_1125_);
lean_inc(v_traceState_1124_);
lean_inc(v_auxDeclNGen_1123_);
lean_inc(v_ngen_1122_);
lean_inc(v_nextMacroScope_1121_);
lean_inc(v_env_1120_);
lean_dec(v___x_1119_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1157_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1132_ = 0;
v___x_1133_ = lean_box(0);
v___x_1134_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1120_, v_declName_1114_, v_s_1115_, v___x_1132_, v___x_1133_);
v___x_1135_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 5, v___x_1135_);
lean_ctor_set(v___x_1130_, 0, v___x_1134_);
v___x_1137_ = v___x_1130_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_nextMacroScope_1121_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_ngen_1122_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_auxDeclNGen_1123_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_traceState_1124_);
lean_ctor_set(v_reuseFailAlloc_1156_, 5, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1156_, 6, v_recordedDeps_1125_);
lean_ctor_set(v_reuseFailAlloc_1156_, 7, v_messages_1126_);
lean_ctor_set(v_reuseFailAlloc_1156_, 8, v_infoState_1127_);
lean_ctor_set(v_reuseFailAlloc_1156_, 9, v_snapshotTasks_1128_);
v___x_1137_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_mctx_1140_; lean_object* v_zetaDeltaFVarIds_1141_; lean_object* v_postponed_1142_; lean_object* v_diag_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1154_; 
v___x_1138_ = lean_st_ref_put(v___y_1117_, v___x_1137_);
v___x_1139_ = lean_st_ref_take(v___y_1116_);
v_mctx_1140_ = lean_ctor_get(v___x_1139_, 0);
v_zetaDeltaFVarIds_1141_ = lean_ctor_get(v___x_1139_, 2);
v_postponed_1142_ = lean_ctor_get(v___x_1139_, 3);
v_diag_1143_ = lean_ctor_get(v___x_1139_, 4);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v___x_1139_, 1);
lean_dec(v_unused_1155_);
v___x_1145_ = v___x_1139_;
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_diag_1143_);
lean_inc(v_postponed_1142_);
lean_inc(v_zetaDeltaFVarIds_1141_);
lean_inc(v_mctx_1140_);
lean_dec(v___x_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1148_);
v___x_1150_ = v___x_1145_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_mctx_1140_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_zetaDeltaFVarIds_1141_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_postponed_1142_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v_diag_1143_);
v___x_1150_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_st_ref_put(v___y_1116_, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1147_);
return v___x_1152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___boxed(lean_object* v_declName_1159_, lean_object* v_s_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v_s_boxed_1164_; lean_object* v_res_1165_; 
v_s_boxed_1164_ = lean_unbox(v_s_1160_);
v_res_1165_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(v_declName_1159_, v_s_boxed_1164_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec(v___y_1161_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(lean_object* v_declName_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = 0;
v___x_1173_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(v_declName_1166_, v___x_1172_, v___y_1168_, v___y_1170_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(lean_object* v_declName_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v_declName_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(lean_object* v_constName_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v_env_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1187_ = lean_st_ref_get(v___y_1185_);
v_env_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_ref(v_env_1188_);
lean_dec(v___x_1187_);
v___x_1189_ = 0;
lean_inc(v_constName_1181_);
v___x_1190_ = l_Lean_Environment_findConstVal_x3f(v_env_1188_, v_constName_1181_, v___x_1189_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1191_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_constName_1181_);
v_val_1192_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1190_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_val_1192_);
lean_dec(v___x_1190_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 0);
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_val_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(lean_object* v_constName_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v_constName_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1210_ = lean_unsigned_to_nat(60u);
v___x_1211_ = lean_unsigned_to_nat(81u);
v___x_1212_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0));
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1214_ = l_mkPanicMessageWithDecl(v___x_1213_, v___x_1212_, v___x_1211_, v___x_1210_, v___x_1209_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(lean_object* v_indName_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1215_);
v___x_1222_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1356_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1356_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1356_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
if (lean_obj_tag(v_a_1223_) == 5)
{
lean_object* v_val_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_val_1227_ = lean_ctor_get(v_a_1223_, 0);
lean_inc_ref(v_val_1227_);
lean_dec_ref_known(v_a_1223_, 1);
v___x_1228_ = l_Lean_InductiveVal_numCtors(v_val_1227_);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_nat_dec_eq(v___x_1228_, v___x_1229_);
lean_dec(v___x_1228_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_del_object(v___x_1225_);
v___x_1231_ = lean_box(v___x_1230_);
v___f_1232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1232_, 0, v_val_1227_);
lean_closure_set(v___f_1232_, 1, v___x_1229_);
lean_closure_set(v___f_1232_, 2, v___x_1221_);
lean_closure_set(v___f_1232_, 3, v___x_1231_);
lean_inc(v_indName_1215_);
v___x_1233_ = l_Lean_mkCasesOnName(v_indName_1215_);
v___x_1234_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1233_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v_levelParams_1236_; lean_object* v_type_1237_; lean_object* v___x_1238_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v_levelParams_1236_ = lean_ctor_get(v_a_1235_, 1);
lean_inc(v_levelParams_1236_);
v_type_1237_ = lean_ctor_get(v_a_1235_, 2);
lean_inc_ref(v_type_1237_);
lean_dec(v_a_1235_);
v___x_1238_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1237_, v___f_1232_, v___x_1230_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_n(v_a_1239_, 2);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1215_);
lean_inc(v_a_1219_);
lean_inc_ref(v_a_1218_);
lean_inc(v_a_1217_);
lean_inc_ref(v_a_1216_);
v___x_1241_ = lean_infer_type(v_a_1239_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1325_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = lean_box(1);
lean_inc(v___x_1240_);
v___x_1244_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1240_, v_levelParams_1236_, v_a_1242_, v_a_1239_, v___x_1243_, v_a_1219_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1325_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1325_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 1);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
uint8_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = 1;
v___x_1252_ = l_Lean_addAndCompile(v___x_1250_, v___x_1251_, v___x_1230_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v___x_1253_; lean_object* v_env_1254_; lean_object* v_nextMacroScope_1255_; lean_object* v_ngen_1256_; lean_object* v_auxDeclNGen_1257_; lean_object* v_traceState_1258_; lean_object* v_recordedDeps_1259_; lean_object* v_messages_1260_; lean_object* v_infoState_1261_; lean_object* v_snapshotTasks_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref_known(v___x_1252_, 1);
v___x_1253_ = lean_st_ref_take(v_a_1219_);
v_env_1254_ = lean_ctor_get(v___x_1253_, 0);
v_nextMacroScope_1255_ = lean_ctor_get(v___x_1253_, 1);
v_ngen_1256_ = lean_ctor_get(v___x_1253_, 2);
v_auxDeclNGen_1257_ = lean_ctor_get(v___x_1253_, 3);
v_traceState_1258_ = lean_ctor_get(v___x_1253_, 4);
v_recordedDeps_1259_ = lean_ctor_get(v___x_1253_, 6);
v_messages_1260_ = lean_ctor_get(v___x_1253_, 7);
v_infoState_1261_ = lean_ctor_get(v___x_1253_, 8);
v_snapshotTasks_1262_ = lean_ctor_get(v___x_1253_, 9);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v___x_1253_, 5);
lean_dec(v_unused_1323_);
v___x_1264_ = v___x_1253_;
v_isShared_1265_ = v_isSharedCheck_1322_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_snapshotTasks_1262_);
lean_inc(v_infoState_1261_);
lean_inc(v_messages_1260_);
lean_inc(v_recordedDeps_1259_);
lean_inc(v_traceState_1258_);
lean_inc(v_auxDeclNGen_1257_);
lean_inc(v_ngen_1256_);
lean_inc(v_nextMacroScope_1255_);
lean_inc(v_env_1254_);
lean_dec(v___x_1253_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1322_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
lean_inc(v___x_1240_);
v___x_1266_ = l_Lean_Meta_addToCompletionBlackList(v_env_1254_, v___x_1240_);
v___x_1267_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 5, v___x_1267_);
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_nextMacroScope_1255_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_ngen_1256_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_auxDeclNGen_1257_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_traceState_1258_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v_recordedDeps_1259_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_messages_1260_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v_infoState_1261_);
lean_ctor_set(v_reuseFailAlloc_1321_, 9, v_snapshotTasks_1262_);
v___x_1269_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_mctx_1272_; lean_object* v_zetaDeltaFVarIds_1273_; lean_object* v_postponed_1274_; lean_object* v_diag_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1319_; 
v___x_1270_ = lean_st_ref_put(v_a_1219_, v___x_1269_);
v___x_1271_ = lean_st_ref_take(v_a_1217_);
v_mctx_1272_ = lean_ctor_get(v___x_1271_, 0);
v_zetaDeltaFVarIds_1273_ = lean_ctor_get(v___x_1271_, 2);
v_postponed_1274_ = lean_ctor_get(v___x_1271_, 3);
v_diag_1275_ = lean_ctor_get(v___x_1271_, 4);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v___x_1271_, 1);
lean_dec(v_unused_1320_);
v___x_1277_ = v___x_1271_;
v_isShared_1278_ = v_isSharedCheck_1319_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_diag_1275_);
lean_inc(v_postponed_1274_);
lean_inc(v_zetaDeltaFVarIds_1273_);
lean_inc(v_mctx_1272_);
lean_dec(v___x_1271_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1319_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_mctx_1272_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_zetaDeltaFVarIds_1273_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_postponed_1274_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_diag_1275_);
v___x_1281_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_env_1284_; lean_object* v_nextMacroScope_1285_; lean_object* v_ngen_1286_; lean_object* v_auxDeclNGen_1287_; lean_object* v_traceState_1288_; lean_object* v_recordedDeps_1289_; lean_object* v_messages_1290_; lean_object* v_infoState_1291_; lean_object* v_snapshotTasks_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1316_; 
v___x_1282_ = lean_st_ref_put(v_a_1217_, v___x_1281_);
v___x_1283_ = lean_st_ref_take(v_a_1219_);
v_env_1284_ = lean_ctor_get(v___x_1283_, 0);
v_nextMacroScope_1285_ = lean_ctor_get(v___x_1283_, 1);
v_ngen_1286_ = lean_ctor_get(v___x_1283_, 2);
v_auxDeclNGen_1287_ = lean_ctor_get(v___x_1283_, 3);
v_traceState_1288_ = lean_ctor_get(v___x_1283_, 4);
v_recordedDeps_1289_ = lean_ctor_get(v___x_1283_, 6);
v_messages_1290_ = lean_ctor_get(v___x_1283_, 7);
v_infoState_1291_ = lean_ctor_get(v___x_1283_, 8);
v_snapshotTasks_1292_ = lean_ctor_get(v___x_1283_, 9);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1283_, 5);
lean_dec(v_unused_1317_);
v___x_1294_ = v___x_1283_;
v_isShared_1295_ = v_isSharedCheck_1316_;
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
v_isShared_1295_ = v_isSharedCheck_1316_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_inc(v___x_1240_);
v___x_1296_ = l_Lean_addProtected(v_env_1284_, v___x_1240_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 5, v___x_1267_);
lean_ctor_set(v___x_1294_, 0, v___x_1296_);
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_nextMacroScope_1285_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_ngen_1286_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v_auxDeclNGen_1287_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_traceState_1288_);
lean_ctor_set(v_reuseFailAlloc_1315_, 5, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1315_, 6, v_recordedDeps_1289_);
lean_ctor_set(v_reuseFailAlloc_1315_, 7, v_messages_1290_);
lean_ctor_set(v_reuseFailAlloc_1315_, 8, v_infoState_1291_);
lean_ctor_set(v_reuseFailAlloc_1315_, 9, v_snapshotTasks_1292_);
v___x_1298_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_mctx_1301_; lean_object* v_zetaDeltaFVarIds_1302_; lean_object* v_postponed_1303_; lean_object* v_diag_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1313_; 
v___x_1299_ = lean_st_ref_put(v_a_1219_, v___x_1298_);
v___x_1300_ = lean_st_ref_take(v_a_1217_);
v_mctx_1301_ = lean_ctor_get(v___x_1300_, 0);
v_zetaDeltaFVarIds_1302_ = lean_ctor_get(v___x_1300_, 2);
v_postponed_1303_ = lean_ctor_get(v___x_1300_, 3);
v_diag_1304_ = lean_ctor_get(v___x_1300_, 4);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1300_, 1);
lean_dec(v_unused_1314_);
v___x_1306_ = v___x_1300_;
v_isShared_1307_ = v_isSharedCheck_1313_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_diag_1304_);
lean_inc(v_postponed_1303_);
lean_inc(v_zetaDeltaFVarIds_1302_);
lean_inc(v_mctx_1301_);
lean_dec(v___x_1300_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1313_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1279_);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_mctx_1301_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_zetaDeltaFVarIds_1302_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v_postponed_1303_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_diag_1304_);
v___x_1309_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_st_ref_put(v_a_1217_, v___x_1309_);
v___x_1311_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_1240_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1311_;
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
lean_dec(v___x_1240_);
return v___x_1252_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___x_1240_);
lean_dec(v_a_1239_);
lean_dec(v_levelParams_1236_);
v_a_1326_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1241_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1241_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_levelParams_1236_);
lean_dec(v_indName_1215_);
v_a_1334_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1238_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1238_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v___f_1232_);
lean_dec(v_indName_1215_);
v_a_1342_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1234_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1234_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec_ref(v_val_1227_);
lean_dec(v_indName_1215_);
v___x_1350_ = lean_box(0);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1350_);
v___x_1352_ = v___x_1225_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_del_object(v___x_1225_);
lean_dec(v_a_1223_);
lean_dec(v_indName_1215_);
v___x_1354_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2);
v___x_1355_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_1354_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1355_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_indName_1215_);
v_a_1357_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1222_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1222_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___boxed(lean_object* v_indName_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(lean_object* v_00_u03b1_1372_, lean_object* v_name_1373_, uint8_t v_bi_1374_, lean_object* v_type_1375_, lean_object* v_k_1376_, uint8_t v_kind_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_1373_, v_bi_1374_, v_type_1375_, v_k_1376_, v_kind_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_name_1385_, lean_object* v_bi_1386_, lean_object* v_type_1387_, lean_object* v_k_1388_, lean_object* v_kind_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v_bi_boxed_1395_; uint8_t v_kind_boxed_1396_; lean_object* v_res_1397_; 
v_bi_boxed_1395_ = lean_unbox(v_bi_1386_);
v_kind_boxed_1396_ = lean_unbox(v_kind_1389_);
v_res_1397_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(v_00_u03b1_1384_, v_name_1385_, v_bi_boxed_1395_, v_type_1387_, v_k_1388_, v_kind_boxed_1396_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(lean_object* v_00_u03b1_1398_, lean_object* v_name_1399_, lean_object* v_type_1400_, lean_object* v_k_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v_name_1399_, v_type_1400_, v_k_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___boxed(lean_object* v_00_u03b1_1408_, lean_object* v_name_1409_, lean_object* v_type_1410_, lean_object* v_k_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(v_00_u03b1_1408_, v_name_1409_, v_type_1410_, v_k_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(lean_object* v_00_u03b2_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___redArg(){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___redArg___boxed(lean_object* v___dummy_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___redArg();
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object* v_00_u03b2_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(lean_object* v_00_u03b1_1426_, lean_object* v_constName_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_constName_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(v_00_u03b1_1434_, v_constName_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10(lean_object* v_declName_1442_, uint8_t v_s_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(v_declName_1442_, v_s_1443_, v___y_1445_, v___y_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___boxed(lean_object* v_declName_1450_, lean_object* v_s_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v_s_boxed_1457_; lean_object* v_res_1458_; 
v_s_boxed_1457_ = lean_unbox(v_s_1451_);
v_res_1458_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10(v_declName_1450_, v_s_boxed_1457_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_1459_, lean_object* v_ref_1460_, lean_object* v_constName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1460_, v_constName_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_ref_1469_, lean_object* v_constName_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(v_00_u03b1_1468_, v_ref_1469_, v_constName_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_ref_1469_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12(lean_object* v_00_u03b1_1477_, lean_object* v_ref_1478_, lean_object* v_msg_1479_, lean_object* v_declHint_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(v_ref_1478_, v_msg_1479_, v_declHint_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___boxed(lean_object* v_00_u03b1_1487_, lean_object* v_ref_1488_, lean_object* v_msg_1489_, lean_object* v_declHint_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12(v_00_u03b1_1487_, v_ref_1488_, v_msg_1489_, v_declHint_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v_ref_1488_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15(lean_object* v_msg_1497_, lean_object* v_declHint_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(v_msg_1497_, v_declHint_1498_, v___y_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_1505_, lean_object* v_declHint_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15(v_msg_1505_, v_declHint_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1513_, lean_object* v_ref_1514_, lean_object* v_msg_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(v_ref_1514_, v_msg_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15(v_00_u03b1_1522_, v_ref_1523_, v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v_ref_1523_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(lean_object* v___x_1531_, lean_object* v_k_1532_, lean_object* v_zs_1533_, uint8_t v___x_1534_, uint8_t v___x_1535_, uint8_t v___x_1536_, lean_object* v_h_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
lean_inc_ref(v_h_1537_);
v___x_1543_ = l_Lean_Meta_mkEqNDRec(v___x_1531_, v_k_1532_, v_h_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_a_1544_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = l_Lean_mkAppN(v_a_1546_, v_zs_1533_);
v___x_1548_ = lean_array_push(v_zs_1533_, v_h_1537_);
v___x_1549_ = l_Lean_Meta_mkLambdaFVars(v___x_1548_, v___x_1547_, v___x_1534_, v___x_1535_, v___x_1534_, v___x_1535_, v___x_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec_ref(v___x_1548_);
return v___x_1549_;
}
else
{
lean_dec_ref(v_h_1537_);
lean_dec_ref(v_zs_1533_);
return v___x_1545_;
}
}
else
{
lean_dec_ref(v_h_1537_);
lean_dec_ref(v_zs_1533_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___x_1550_, lean_object* v_k_1551_, lean_object* v_zs_1552_, lean_object* v___x_1553_, lean_object* v___x_1554_, lean_object* v___x_1555_, lean_object* v_h_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v___x_6659__boxed_1562_; uint8_t v___x_6660__boxed_1563_; uint8_t v___x_6661__boxed_1564_; lean_object* v_res_1565_; 
v___x_6659__boxed_1562_ = lean_unbox(v___x_1553_);
v___x_6660__boxed_1563_ = lean_unbox(v___x_1554_);
v___x_6661__boxed_1564_ = lean_unbox(v___x_1555_);
v_res_1565_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(v___x_1550_, v_k_1551_, v_zs_1552_, v___x_6659__boxed_1562_, v___x_6660__boxed_1563_, v___x_6661__boxed_1564_, v_h_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(lean_object* v___x_1569_, lean_object* v_k_1570_, uint8_t v___x_1571_, uint8_t v___x_1572_, uint8_t v___x_1573_, lean_object* v___x_1574_, lean_object* v___x_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, lean_object* v_ctorIdx_1578_, lean_object* v___x_1579_, lean_object* v_zs_1580_, lean_object* v___ctorRet_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1587_ = lean_box(v___x_1571_);
v___x_1588_ = lean_box(v___x_1572_);
v___x_1589_ = lean_box(v___x_1573_);
v___f_1590_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1590_, 0, v___x_1569_);
lean_closure_set(v___f_1590_, 1, v_k_1570_);
lean_closure_set(v___f_1590_, 2, v_zs_1580_);
lean_closure_set(v___f_1590_, 3, v___x_1587_);
lean_closure_set(v___f_1590_, 4, v___x_1588_);
lean_closure_set(v___f_1590_, 5, v___x_1589_);
v___x_1591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1));
v___x_1592_ = l_Lean_Level_ofNat(v___x_1574_);
v___x_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v___x_1575_);
v___x_1594_ = l_Lean_mkConst(v___x_1591_, v___x_1593_);
v___x_1595_ = l_Lean_mkRawNatLit(v___x_1576_);
v___x_1596_ = l_Lean_mkApp3(v___x_1594_, v___x_1577_, v_ctorIdx_1578_, v___x_1595_);
v___x_1597_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1579_, v___x_1596_, v___f_1590_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1598_ = _args[0];
lean_object* v_k_1599_ = _args[1];
lean_object* v___x_1600_ = _args[2];
lean_object* v___x_1601_ = _args[3];
lean_object* v___x_1602_ = _args[4];
lean_object* v___x_1603_ = _args[5];
lean_object* v___x_1604_ = _args[6];
lean_object* v___x_1605_ = _args[7];
lean_object* v___x_1606_ = _args[8];
lean_object* v_ctorIdx_1607_ = _args[9];
lean_object* v___x_1608_ = _args[10];
lean_object* v_zs_1609_ = _args[11];
lean_object* v___ctorRet_1610_ = _args[12];
lean_object* v___y_1611_ = _args[13];
lean_object* v___y_1612_ = _args[14];
lean_object* v___y_1613_ = _args[15];
lean_object* v___y_1614_ = _args[16];
lean_object* v___y_1615_ = _args[17];
_start:
{
uint8_t v___x_6708__boxed_1616_; uint8_t v___x_6709__boxed_1617_; uint8_t v___x_6710__boxed_1618_; lean_object* v_res_1619_; 
v___x_6708__boxed_1616_ = lean_unbox(v___x_1600_);
v___x_6709__boxed_1617_ = lean_unbox(v___x_1601_);
v___x_6710__boxed_1618_ = lean_unbox(v___x_1602_);
v_res_1619_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(v___x_1598_, v_k_1599_, v___x_6708__boxed_1616_, v___x_6709__boxed_1617_, v___x_6710__boxed_1618_, v___x_1603_, v___x_1604_, v___x_1605_, v___x_1606_, v_ctorIdx_1607_, v___x_1608_, v_zs_1609_, v___ctorRet_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec_ref(v___ctorRet_1610_);
lean_dec(v___x_1603_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(lean_object* v___x_1623_, lean_object* v_k_1624_, lean_object* v_ctorIdx_1625_, lean_object* v_tail_1626_, lean_object* v___x_1627_, size_t v_sz_1628_, size_t v_i_1629_, lean_object* v_bs_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_lt(v_i_1629_, v_sz_1628_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_dec(v_tail_1626_);
lean_dec_ref(v_ctorIdx_1625_);
lean_dec_ref(v_k_1624_);
lean_dec_ref(v___x_1623_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_bs_1630_);
return v___x_1637_;
}
else
{
uint8_t v___x_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_v_1644_; lean_object* v___x_1645_; lean_object* v_bs_x27_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1638_ = 0;
v___x_1639_ = 1;
v___x_1640_ = lean_unsigned_to_nat(1u);
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_1643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v_v_1644_ = lean_array_uget(v_bs_1630_, v_i_1629_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v_bs_x27_1646_ = lean_array_uset(v_bs_1630_, v_i_1629_, v___x_1645_);
v___x_1647_ = lean_usize_to_nat(v_i_1629_);
v___x_1648_ = lean_box(v___x_1638_);
v___x_1649_ = lean_box(v___x_1636_);
v___x_1650_ = lean_box(v___x_1639_);
lean_inc_ref(v_ctorIdx_1625_);
lean_inc_ref(v_k_1624_);
lean_inc_ref(v___x_1623_);
v___f_1651_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed), 18, 11);
lean_closure_set(v___f_1651_, 0, v___x_1623_);
lean_closure_set(v___f_1651_, 1, v_k_1624_);
lean_closure_set(v___f_1651_, 2, v___x_1648_);
lean_closure_set(v___f_1651_, 3, v___x_1649_);
lean_closure_set(v___f_1651_, 4, v___x_1650_);
lean_closure_set(v___f_1651_, 5, v___x_1640_);
lean_closure_set(v___f_1651_, 6, v___x_1641_);
lean_closure_set(v___f_1651_, 7, v___x_1647_);
lean_closure_set(v___f_1651_, 8, v___x_1642_);
lean_closure_set(v___f_1651_, 9, v_ctorIdx_1625_);
lean_closure_set(v___f_1651_, 10, v___x_1643_);
lean_inc(v_tail_1626_);
v___x_1652_ = l_Lean_mkConst(v_v_1644_, v_tail_1626_);
v___x_1653_ = l_Lean_mkAppN(v___x_1652_, v___x_1627_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
v___x_1654_ = lean_infer_type(v___x_1653_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_a_1655_, v___f_1651_, v___x_1638_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; size_t v___x_1658_; size_t v___x_1659_; lean_object* v___x_1660_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = ((size_t)1ULL);
v___x_1659_ = lean_usize_add(v_i_1629_, v___x_1658_);
v___x_1660_ = lean_array_uset(v_bs_x27_1646_, v_i_1629_, v_a_1657_);
v_i_1629_ = v___x_1659_;
v_bs_1630_ = v___x_1660_;
goto _start;
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_bs_x27_1646_);
lean_dec(v_tail_1626_);
lean_dec_ref(v_ctorIdx_1625_);
lean_dec_ref(v_k_1624_);
lean_dec_ref(v___x_1623_);
v_a_1662_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1656_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1656_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v___f_1651_);
lean_dec_ref(v_bs_x27_1646_);
lean_dec(v_tail_1626_);
lean_dec_ref(v_ctorIdx_1625_);
lean_dec_ref(v_k_1624_);
lean_dec_ref(v___x_1623_);
v_a_1670_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1654_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1654_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___boxed(lean_object* v___x_1678_, lean_object* v_k_1679_, lean_object* v_ctorIdx_1680_, lean_object* v_tail_1681_, lean_object* v___x_1682_, lean_object* v_sz_1683_, lean_object* v_i_1684_, lean_object* v_bs_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
size_t v_sz_boxed_1691_; size_t v_i_boxed_1692_; lean_object* v_res_1693_; 
v_sz_boxed_1691_ = lean_unbox_usize(v_sz_1683_);
lean_dec(v_sz_1683_);
v_i_boxed_1692_ = lean_unbox_usize(v_i_1684_);
lean_dec(v_i_1684_);
v_res_1693_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1678_, v_k_1679_, v_ctorIdx_1680_, v_tail_1681_, v___x_1682_, v_sz_boxed_1691_, v_i_boxed_1692_, v_bs_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec_ref(v___x_1682_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(lean_object* v___x_1694_, lean_object* v___x_1695_, lean_object* v_a_1696_, lean_object* v_name_1697_, lean_object* v___x_1698_, lean_object* v___x_1699_, lean_object* v_ctors_1700_, lean_object* v___x_1701_, lean_object* v_ctorIdx_1702_, lean_object* v_tail_1703_, lean_object* v_h_1704_, lean_object* v_k_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_inc_ref(v___x_1694_);
v___x_1711_ = l_Lean_mkAppN(v___x_1694_, v___x_1695_);
v___x_1712_ = l_Lean_mkArrow(v_a_1696_, v___x_1711_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; uint8_t v___x_1714_; uint8_t v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = 0;
v___x_1715_ = 1;
v___x_1716_ = 1;
v___x_1717_ = l_Lean_Meta_mkLambdaFVars(v___x_1695_, v_a_1713_, v___x_1714_, v___x_1715_, v___x_1714_, v___x_1715_, v___x_1716_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; size_t v_sz_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = l_Lean_mkConst(v_name_1697_, v___x_1698_);
v___x_1720_ = l_Lean_mkAppN(v___x_1719_, v___x_1699_);
v___x_1721_ = l_Lean_Expr_app___override(v___x_1720_, v_a_1718_);
v___x_1722_ = l_Lean_mkAppN(v___x_1721_, v___x_1695_);
v___x_1723_ = lean_array_mk(v_ctors_1700_);
v_sz_1724_ = lean_array_size(v___x_1723_);
v___x_1725_ = ((size_t)0ULL);
lean_inc_ref(v_ctorIdx_1702_);
lean_inc_ref(v_k_1705_);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1701_, v_k_1705_, v_ctorIdx_1702_, v_tail_1703_, v___x_1699_, v_sz_1724_, v___x_1725_, v___x_1723_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = l_Lean_mkAppN(v___x_1722_, v_a_1727_);
lean_dec(v_a_1727_);
lean_inc_ref(v_h_1704_);
v___x_1729_ = l_Lean_Expr_app___override(v___x_1728_, v_h_1704_);
v___x_1730_ = lean_unsigned_to_nat(2u);
v___x_1731_ = lean_mk_empty_array_with_capacity(v___x_1730_);
lean_inc_ref(v___x_1731_);
v___x_1732_ = lean_array_push(v___x_1731_, v___x_1694_);
v___x_1733_ = lean_array_push(v___x_1732_, v_ctorIdx_1702_);
v___x_1734_ = l_Array_append___redArg(v___x_1699_, v___x_1733_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = l_Array_append___redArg(v___x_1734_, v___x_1695_);
v___x_1736_ = lean_array_push(v___x_1731_, v_h_1704_);
v___x_1737_ = lean_array_push(v___x_1736_, v_k_1705_);
v___x_1738_ = l_Array_append___redArg(v___x_1735_, v___x_1737_);
lean_dec_ref(v___x_1737_);
v___x_1739_ = l_Lean_Meta_mkLambdaFVars(v___x_1738_, v___x_1729_, v___x_1714_, v___x_1715_, v___x_1714_, v___x_1715_, v___x_1716_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec_ref(v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v___x_1722_);
lean_dec_ref(v_k_1705_);
lean_dec_ref(v_h_1704_);
lean_dec_ref(v_ctorIdx_1702_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1694_);
v_a_1740_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1726_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1726_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_dec_ref(v_k_1705_);
lean_dec_ref(v_h_1704_);
lean_dec(v_tail_1703_);
lean_dec_ref(v_ctorIdx_1702_);
lean_dec_ref(v___x_1701_);
lean_dec(v_ctors_1700_);
lean_dec_ref(v___x_1699_);
lean_dec(v___x_1698_);
lean_dec(v_name_1697_);
lean_dec_ref(v___x_1694_);
return v___x_1717_;
}
}
else
{
lean_dec_ref(v_k_1705_);
lean_dec_ref(v_h_1704_);
lean_dec(v_tail_1703_);
lean_dec_ref(v_ctorIdx_1702_);
lean_dec_ref(v___x_1701_);
lean_dec(v_ctors_1700_);
lean_dec_ref(v___x_1699_);
lean_dec(v___x_1698_);
lean_dec(v_name_1697_);
lean_dec_ref(v___x_1694_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed(lean_object** _args){
lean_object* v___x_1748_ = _args[0];
lean_object* v___x_1749_ = _args[1];
lean_object* v_a_1750_ = _args[2];
lean_object* v_name_1751_ = _args[3];
lean_object* v___x_1752_ = _args[4];
lean_object* v___x_1753_ = _args[5];
lean_object* v_ctors_1754_ = _args[6];
lean_object* v___x_1755_ = _args[7];
lean_object* v_ctorIdx_1756_ = _args[8];
lean_object* v_tail_1757_ = _args[9];
lean_object* v_h_1758_ = _args[10];
lean_object* v_k_1759_ = _args[11];
lean_object* v___y_1760_ = _args[12];
lean_object* v___y_1761_ = _args[13];
lean_object* v___y_1762_ = _args[14];
lean_object* v___y_1763_ = _args[15];
lean_object* v___y_1764_ = _args[16];
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(v___x_1748_, v___x_1749_, v_a_1750_, v_name_1751_, v___x_1752_, v___x_1753_, v_ctors_1754_, v___x_1755_, v_ctorIdx_1756_, v_tail_1757_, v_h_1758_, v_k_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v___x_1749_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(lean_object* v___x_1769_, lean_object* v___x_1770_, lean_object* v_a_1771_, lean_object* v_name_1772_, lean_object* v___x_1773_, lean_object* v___x_1774_, lean_object* v_ctors_1775_, lean_object* v___x_1776_, lean_object* v_ctorIdx_1777_, lean_object* v_tail_1778_, lean_object* v___x_1779_, lean_object* v_h_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___f_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___f_1786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1786_, 0, v___x_1769_);
lean_closure_set(v___f_1786_, 1, v___x_1770_);
lean_closure_set(v___f_1786_, 2, v_a_1771_);
lean_closure_set(v___f_1786_, 3, v_name_1772_);
lean_closure_set(v___f_1786_, 4, v___x_1773_);
lean_closure_set(v___f_1786_, 5, v___x_1774_);
lean_closure_set(v___f_1786_, 6, v_ctors_1775_);
lean_closure_set(v___f_1786_, 7, v___x_1776_);
lean_closure_set(v___f_1786_, 8, v_ctorIdx_1777_);
lean_closure_set(v___f_1786_, 9, v_tail_1778_);
lean_closure_set(v___f_1786_, 10, v_h_1780_);
v___x_1787_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1));
v___x_1788_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1787_, v___x_1779_, v___f_1786_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed(lean_object** _args){
lean_object* v___x_1789_ = _args[0];
lean_object* v___x_1790_ = _args[1];
lean_object* v_a_1791_ = _args[2];
lean_object* v_name_1792_ = _args[3];
lean_object* v___x_1793_ = _args[4];
lean_object* v___x_1794_ = _args[5];
lean_object* v_ctors_1795_ = _args[6];
lean_object* v___x_1796_ = _args[7];
lean_object* v_ctorIdx_1797_ = _args[8];
lean_object* v_tail_1798_ = _args[9];
lean_object* v___x_1799_ = _args[10];
lean_object* v_h_1800_ = _args[11];
lean_object* v___y_1801_ = _args[12];
lean_object* v___y_1802_ = _args[13];
lean_object* v___y_1803_ = _args[14];
lean_object* v___y_1804_ = _args[15];
lean_object* v___y_1805_ = _args[16];
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(v___x_1789_, v___x_1790_, v_a_1791_, v_name_1792_, v___x_1793_, v___x_1794_, v_ctors_1795_, v___x_1796_, v_ctorIdx_1797_, v_tail_1798_, v___x_1799_, v_h_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(lean_object* v___x_1807_, lean_object* v___x_1808_, lean_object* v___x_1809_, lean_object* v___x_1810_, lean_object* v_indName_1811_, lean_object* v_tail_1812_, lean_object* v___x_1813_, lean_object* v_name_1814_, lean_object* v_ctors_1815_, lean_object* v_ctorIdx_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_inc(v___x_1808_);
v___x_1822_ = l_Lean_mkConst(v___x_1807_, v___x_1808_);
lean_inc_ref(v___x_1810_);
lean_inc_ref_n(v___x_1809_, 2);
v___x_1823_ = lean_array_push(v___x_1809_, v___x_1810_);
v___x_1824_ = l_Lean_mkAppN(v___x_1822_, v___x_1823_);
lean_dec_ref(v___x_1823_);
lean_inc_ref_n(v_ctorIdx_1816_, 2);
lean_inc_ref(v___x_1824_);
v___x_1825_ = l_Lean_Expr_app___override(v___x_1824_, v_ctorIdx_1816_);
v___x_1826_ = l_Lean_mkCtorIdxName(v_indName_1811_);
lean_inc(v_tail_1812_);
v___x_1827_ = l_Lean_mkConst(v___x_1826_, v_tail_1812_);
v___x_1828_ = l_Array_append___redArg(v___x_1809_, v___x_1813_);
v___x_1829_ = l_Lean_mkAppN(v___x_1827_, v___x_1828_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = l_Lean_Meta_mkEq(v_ctorIdx_1816_, v___x_1829_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc_n(v_a_1831_, 2);
lean_dec_ref_known(v___x_1830_, 1);
v___f_1832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed), 17, 11);
lean_closure_set(v___f_1832_, 0, v___x_1810_);
lean_closure_set(v___f_1832_, 1, v___x_1813_);
lean_closure_set(v___f_1832_, 2, v_a_1831_);
lean_closure_set(v___f_1832_, 3, v_name_1814_);
lean_closure_set(v___f_1832_, 4, v___x_1808_);
lean_closure_set(v___f_1832_, 5, v___x_1809_);
lean_closure_set(v___f_1832_, 6, v_ctors_1815_);
lean_closure_set(v___f_1832_, 7, v___x_1824_);
lean_closure_set(v___f_1832_, 8, v_ctorIdx_1816_);
lean_closure_set(v___f_1832_, 9, v_tail_1812_);
lean_closure_set(v___f_1832_, 10, v___x_1825_);
v___x_1833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_1834_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1833_, v_a_1831_, v___f_1832_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1834_;
}
else
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1824_);
lean_dec_ref(v_ctorIdx_1816_);
lean_dec(v_ctors_1815_);
lean_dec(v_name_1814_);
lean_dec_ref(v___x_1813_);
lean_dec(v_tail_1812_);
lean_dec_ref(v___x_1810_);
lean_dec_ref(v___x_1809_);
lean_dec(v___x_1808_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed(lean_object* v___x_1835_, lean_object* v___x_1836_, lean_object* v___x_1837_, lean_object* v___x_1838_, lean_object* v_indName_1839_, lean_object* v_tail_1840_, lean_object* v___x_1841_, lean_object* v_name_1842_, lean_object* v_ctors_1843_, lean_object* v_ctorIdx_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(v___x_1835_, v___x_1836_, v___x_1837_, v___x_1838_, v_indName_1839_, v_tail_1840_, v___x_1841_, v_name_1842_, v_ctors_1843_, v_ctorIdx_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(lean_object* v_val_1851_, lean_object* v___x_1852_, lean_object* v___x_1853_, lean_object* v___x_1854_, lean_object* v_indName_1855_, lean_object* v_tail_1856_, lean_object* v_name_1857_, lean_object* v___x_1858_, lean_object* v_xs_1859_, lean_object* v_x_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_numParams_1866_; lean_object* v_numIndices_1867_; lean_object* v_ctors_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_numParams_1866_ = lean_ctor_get(v_val_1851_, 1);
lean_inc_n(v_numParams_1866_, 2);
v_numIndices_1867_ = lean_ctor_get(v_val_1851_, 2);
lean_inc(v_numIndices_1867_);
v_ctors_1868_ = lean_ctor_get(v_val_1851_, 4);
lean_inc(v_ctors_1868_);
lean_dec_ref(v_val_1851_);
v___x_1869_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_1859_, 2);
v___x_1870_ = l_Array_toSubarray___redArg(v_xs_1859_, v___x_1869_, v_numParams_1866_);
v___x_1871_ = l_Subarray_copy___redArg(v___x_1870_);
v___x_1872_ = lean_array_get(v___x_1852_, v_xs_1859_, v_numParams_1866_);
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = lean_nat_add(v_numParams_1866_, v___x_1873_);
lean_dec(v_numParams_1866_);
v___x_1875_ = lean_nat_add(v___x_1874_, v_numIndices_1867_);
lean_dec(v_numIndices_1867_);
lean_inc(v___x_1875_);
v___x_1876_ = l_Array_toSubarray___redArg(v_xs_1859_, v___x_1874_, v___x_1875_);
v___x_1877_ = l_Subarray_copy___redArg(v___x_1876_);
v___x_1878_ = lean_array_get(v___x_1852_, v_xs_1859_, v___x_1875_);
lean_dec(v___x_1875_);
lean_dec_ref(v_xs_1859_);
v___x_1879_ = lean_array_push(v___x_1877_, v___x_1878_);
v___f_1880_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed), 15, 9);
lean_closure_set(v___f_1880_, 0, v___x_1853_);
lean_closure_set(v___f_1880_, 1, v___x_1854_);
lean_closure_set(v___f_1880_, 2, v___x_1871_);
lean_closure_set(v___f_1880_, 3, v___x_1872_);
lean_closure_set(v___f_1880_, 4, v_indName_1855_);
lean_closure_set(v___f_1880_, 5, v_tail_1856_);
lean_closure_set(v___f_1880_, 6, v___x_1879_);
lean_closure_set(v___f_1880_, 7, v_name_1857_);
lean_closure_set(v___f_1880_, 8, v_ctors_1868_);
v___x_1881_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_1882_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_1883_ = l_Lean_mkConst(v___x_1882_, v___x_1858_);
v___x_1884_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1881_, v___x_1883_, v___f_1880_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed(lean_object* v_val_1885_, lean_object* v___x_1886_, lean_object* v___x_1887_, lean_object* v___x_1888_, lean_object* v_indName_1889_, lean_object* v_tail_1890_, lean_object* v_name_1891_, lean_object* v___x_1892_, lean_object* v_xs_1893_, lean_object* v_x_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(v_val_1885_, v___x_1886_, v___x_1887_, v___x_1888_, v_indName_1889_, v_tail_1890_, v_name_1891_, v___x_1892_, v_xs_1893_, v_x_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec_ref(v_x_1894_);
lean_dec_ref(v___x_1886_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
if (lean_obj_tag(v_a_1901_) == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = l_List_reverse___redArg(v_a_1902_);
return v___x_1903_;
}
else
{
lean_object* v_head_1904_; lean_object* v_tail_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1914_; 
v_head_1904_ = lean_ctor_get(v_a_1901_, 0);
v_tail_1905_ = lean_ctor_get(v_a_1901_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_a_1901_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1907_ = v_a_1901_;
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_tail_1905_);
lean_inc(v_head_1904_);
lean_dec(v_a_1901_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = l_Lean_mkLevelParam(v_head_1904_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v_a_1902_);
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_a_1902_);
v___x_1911_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
v_a_1901_ = v_tail_1905_;
v_a_1902_ = v___x_1911_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1917_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_1918_ = lean_unsigned_to_nat(58u);
v___x_1919_ = lean_unsigned_to_nat(113u);
v___x_1920_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1921_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1922_ = l_mkPanicMessageWithDecl(v___x_1921_, v___x_1920_, v___x_1919_, v___x_1918_, v___x_1917_);
return v___x_1922_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1923_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1924_ = lean_unsigned_to_nat(60u);
v___x_1925_ = lean_unsigned_to_nat(109u);
v___x_1926_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1927_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1928_ = l_mkPanicMessageWithDecl(v___x_1927_, v___x_1926_, v___x_1925_, v___x_1924_, v___x_1923_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(lean_object* v_indName_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1929_);
v___x_1936_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
if (lean_obj_tag(v_a_1937_) == 5)
{
lean_object* v_val_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_val_1938_ = lean_ctor_get(v_a_1937_, 0);
lean_inc_ref(v_val_1938_);
lean_dec_ref_known(v_a_1937_, 1);
lean_inc_n(v_indName_1929_, 2);
v___x_1939_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1929_);
v___x_1940_ = l_Lean_mkCasesOnName(v_indName_1929_);
v___x_1941_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1940_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_name_1943_; lean_object* v_levelParams_1944_; lean_object* v_type_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v_name_1943_ = lean_ctor_get(v_a_1942_, 0);
lean_inc(v_name_1943_);
v_levelParams_1944_ = lean_ctor_get(v_a_1942_, 1);
lean_inc_n(v_levelParams_1944_, 2);
v_type_1945_ = lean_ctor_get(v_a_1942_, 2);
lean_inc_ref(v_type_1945_);
lean_dec(v_a_1942_);
v___x_1946_ = lean_box(0);
v___x_1947_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_1944_, v___x_1946_);
if (lean_obj_tag(v___x_1947_) == 1)
{
lean_object* v_tail_1948_; lean_object* v___f_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; 
v_tail_1948_ = lean_ctor_get(v___x_1947_, 1);
lean_inc(v_tail_1948_);
lean_inc(v_indName_1929_);
v___f_1949_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed), 15, 8);
lean_closure_set(v___f_1949_, 0, v_val_1938_);
lean_closure_set(v___f_1949_, 1, v___x_1935_);
lean_closure_set(v___f_1949_, 2, v___x_1939_);
lean_closure_set(v___f_1949_, 3, v___x_1947_);
lean_closure_set(v___f_1949_, 4, v_indName_1929_);
lean_closure_set(v___f_1949_, 5, v_tail_1948_);
lean_closure_set(v___f_1949_, 6, v_name_1943_);
lean_closure_set(v___f_1949_, 7, v___x_1946_);
v___x_1950_ = 0;
v___x_1951_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1945_, v___f_1949_, v___x_1950_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc_n(v_a_1952_, 2);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = l_Lean_mkCtorElimName(v_indName_1929_);
lean_inc(v_a_1933_);
lean_inc_ref(v_a_1932_);
lean_inc(v_a_1931_);
lean_inc_ref(v_a_1930_);
v___x_1954_ = lean_infer_type(v_a_1952_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_2072_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = lean_box(1);
lean_inc(v___x_1953_);
v___x_1957_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1953_, v_levelParams_1944_, v_a_1955_, v_a_1952_, v___x_1956_, v_a_1933_);
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_2072_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_2072_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 1);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_2071_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
uint8_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = 1;
v___x_1965_ = l_Lean_addAndCompile(v___x_1963_, v___x_1964_, v___x_1950_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; lean_object* v_env_1967_; lean_object* v_nextMacroScope_1968_; lean_object* v_ngen_1969_; lean_object* v_auxDeclNGen_1970_; lean_object* v_traceState_1971_; lean_object* v_recordedDeps_1972_; lean_object* v_messages_1973_; lean_object* v_infoState_1974_; lean_object* v_snapshotTasks_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref_known(v___x_1965_, 1);
v___x_1966_ = lean_st_ref_take(v_a_1933_);
v_env_1967_ = lean_ctor_get(v___x_1966_, 0);
v_nextMacroScope_1968_ = lean_ctor_get(v___x_1966_, 1);
v_ngen_1969_ = lean_ctor_get(v___x_1966_, 2);
v_auxDeclNGen_1970_ = lean_ctor_get(v___x_1966_, 3);
v_traceState_1971_ = lean_ctor_get(v___x_1966_, 4);
v_recordedDeps_1972_ = lean_ctor_get(v___x_1966_, 6);
v_messages_1973_ = lean_ctor_get(v___x_1966_, 7);
v_infoState_1974_ = lean_ctor_get(v___x_1966_, 8);
v_snapshotTasks_1975_ = lean_ctor_get(v___x_1966_, 9);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; 
v_unused_2070_ = lean_ctor_get(v___x_1966_, 5);
lean_dec(v_unused_2070_);
v___x_1977_ = v___x_1966_;
v_isShared_1978_ = v_isSharedCheck_2069_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_snapshotTasks_1975_);
lean_inc(v_infoState_1974_);
lean_inc(v_messages_1973_);
lean_inc(v_recordedDeps_1972_);
lean_inc(v_traceState_1971_);
lean_inc(v_auxDeclNGen_1970_);
lean_inc(v_ngen_1969_);
lean_inc(v_nextMacroScope_1968_);
lean_inc(v_env_1967_);
lean_dec(v___x_1966_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2069_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
lean_inc(v___x_1953_);
v___x_1979_ = l_Lean_markAuxRecursor(v_env_1967_, v___x_1953_);
v___x_1980_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 5, v___x_1980_);
lean_ctor_set(v___x_1977_, 0, v___x_1979_);
v___x_1982_ = v___x_1977_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_nextMacroScope_1968_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_ngen_1969_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_auxDeclNGen_1970_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_traceState_1971_);
lean_ctor_set(v_reuseFailAlloc_2068_, 5, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2068_, 6, v_recordedDeps_1972_);
lean_ctor_set(v_reuseFailAlloc_2068_, 7, v_messages_1973_);
lean_ctor_set(v_reuseFailAlloc_2068_, 8, v_infoState_1974_);
lean_ctor_set(v_reuseFailAlloc_2068_, 9, v_snapshotTasks_1975_);
v___x_1982_ = v_reuseFailAlloc_2068_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_mctx_1985_; lean_object* v_zetaDeltaFVarIds_1986_; lean_object* v_postponed_1987_; lean_object* v_diag_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2066_; 
v___x_1983_ = lean_st_ref_put(v_a_1933_, v___x_1982_);
v___x_1984_ = lean_st_ref_take(v_a_1931_);
v_mctx_1985_ = lean_ctor_get(v___x_1984_, 0);
v_zetaDeltaFVarIds_1986_ = lean_ctor_get(v___x_1984_, 2);
v_postponed_1987_ = lean_ctor_get(v___x_1984_, 3);
v_diag_1988_ = lean_ctor_get(v___x_1984_, 4);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; 
v_unused_2067_ = lean_ctor_get(v___x_1984_, 1);
lean_dec(v_unused_2067_);
v___x_1990_ = v___x_1984_;
v_isShared_1991_ = v_isSharedCheck_2066_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_diag_1988_);
lean_inc(v_postponed_1987_);
lean_inc(v_zetaDeltaFVarIds_1986_);
lean_inc(v_mctx_1985_);
lean_dec(v___x_1984_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2066_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 1, v___x_1992_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_mctx_1985_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_zetaDeltaFVarIds_1986_);
lean_ctor_set(v_reuseFailAlloc_2065_, 3, v_postponed_1987_);
lean_ctor_set(v_reuseFailAlloc_2065_, 4, v_diag_1988_);
v___x_1994_ = v_reuseFailAlloc_2065_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v_env_1997_; lean_object* v_nextMacroScope_1998_; lean_object* v_ngen_1999_; lean_object* v_auxDeclNGen_2000_; lean_object* v_traceState_2001_; lean_object* v_recordedDeps_2002_; lean_object* v_messages_2003_; lean_object* v_infoState_2004_; lean_object* v_snapshotTasks_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2063_; 
v___x_1995_ = lean_st_ref_put(v_a_1931_, v___x_1994_);
v___x_1996_ = lean_st_ref_take(v_a_1933_);
v_env_1997_ = lean_ctor_get(v___x_1996_, 0);
v_nextMacroScope_1998_ = lean_ctor_get(v___x_1996_, 1);
v_ngen_1999_ = lean_ctor_get(v___x_1996_, 2);
v_auxDeclNGen_2000_ = lean_ctor_get(v___x_1996_, 3);
v_traceState_2001_ = lean_ctor_get(v___x_1996_, 4);
v_recordedDeps_2002_ = lean_ctor_get(v___x_1996_, 6);
v_messages_2003_ = lean_ctor_get(v___x_1996_, 7);
v_infoState_2004_ = lean_ctor_get(v___x_1996_, 8);
v_snapshotTasks_2005_ = lean_ctor_get(v___x_1996_, 9);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_1996_, 5);
lean_dec(v_unused_2064_);
v___x_2007_ = v___x_1996_;
v_isShared_2008_ = v_isSharedCheck_2063_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snapshotTasks_2005_);
lean_inc(v_infoState_2004_);
lean_inc(v_messages_2003_);
lean_inc(v_recordedDeps_2002_);
lean_inc(v_traceState_2001_);
lean_inc(v_auxDeclNGen_2000_);
lean_inc(v_ngen_1999_);
lean_inc(v_nextMacroScope_1998_);
lean_inc(v_env_1997_);
lean_dec(v___x_1996_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2063_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_inc(v___x_1953_);
v___x_2009_ = l_Lean_Meta_addToCompletionBlackList(v_env_1997_, v___x_1953_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 5, v___x_1980_);
lean_ctor_set(v___x_2007_, 0, v___x_2009_);
v___x_2011_ = v___x_2007_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_nextMacroScope_1998_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_ngen_1999_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v_auxDeclNGen_2000_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v_traceState_2001_);
lean_ctor_set(v_reuseFailAlloc_2062_, 5, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2062_, 6, v_recordedDeps_2002_);
lean_ctor_set(v_reuseFailAlloc_2062_, 7, v_messages_2003_);
lean_ctor_set(v_reuseFailAlloc_2062_, 8, v_infoState_2004_);
lean_ctor_set(v_reuseFailAlloc_2062_, 9, v_snapshotTasks_2005_);
v___x_2011_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v_mctx_2014_; lean_object* v_zetaDeltaFVarIds_2015_; lean_object* v_postponed_2016_; lean_object* v_diag_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2060_; 
v___x_2012_ = lean_st_ref_put(v_a_1933_, v___x_2011_);
v___x_2013_ = lean_st_ref_take(v_a_1931_);
v_mctx_2014_ = lean_ctor_get(v___x_2013_, 0);
v_zetaDeltaFVarIds_2015_ = lean_ctor_get(v___x_2013_, 2);
v_postponed_2016_ = lean_ctor_get(v___x_2013_, 3);
v_diag_2017_ = lean_ctor_get(v___x_2013_, 4);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v___x_2013_, 1);
lean_dec(v_unused_2061_);
v___x_2019_ = v___x_2013_;
v_isShared_2020_ = v_isSharedCheck_2060_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_diag_2017_);
lean_inc(v_postponed_2016_);
lean_inc(v_zetaDeltaFVarIds_2015_);
lean_inc(v_mctx_2014_);
lean_dec(v___x_2013_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2060_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v___x_1992_);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_mctx_2014_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_zetaDeltaFVarIds_2015_);
lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_postponed_2016_);
lean_ctor_set(v_reuseFailAlloc_2059_, 4, v_diag_2017_);
v___x_2022_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v_env_2025_; lean_object* v_nextMacroScope_2026_; lean_object* v_ngen_2027_; lean_object* v_auxDeclNGen_2028_; lean_object* v_traceState_2029_; lean_object* v_recordedDeps_2030_; lean_object* v_messages_2031_; lean_object* v_infoState_2032_; lean_object* v_snapshotTasks_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2057_; 
v___x_2023_ = lean_st_ref_put(v_a_1931_, v___x_2022_);
v___x_2024_ = lean_st_ref_take(v_a_1933_);
v_env_2025_ = lean_ctor_get(v___x_2024_, 0);
v_nextMacroScope_2026_ = lean_ctor_get(v___x_2024_, 1);
v_ngen_2027_ = lean_ctor_get(v___x_2024_, 2);
v_auxDeclNGen_2028_ = lean_ctor_get(v___x_2024_, 3);
v_traceState_2029_ = lean_ctor_get(v___x_2024_, 4);
v_recordedDeps_2030_ = lean_ctor_get(v___x_2024_, 6);
v_messages_2031_ = lean_ctor_get(v___x_2024_, 7);
v_infoState_2032_ = lean_ctor_get(v___x_2024_, 8);
v_snapshotTasks_2033_ = lean_ctor_get(v___x_2024_, 9);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2024_, 5);
lean_dec(v_unused_2058_);
v___x_2035_ = v___x_2024_;
v_isShared_2036_ = v_isSharedCheck_2057_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_snapshotTasks_2033_);
lean_inc(v_infoState_2032_);
lean_inc(v_messages_2031_);
lean_inc(v_recordedDeps_2030_);
lean_inc(v_traceState_2029_);
lean_inc(v_auxDeclNGen_2028_);
lean_inc(v_ngen_2027_);
lean_inc(v_nextMacroScope_2026_);
lean_inc(v_env_2025_);
lean_dec(v___x_2024_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2057_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_inc(v___x_1953_);
v___x_2037_ = l_Lean_addProtected(v_env_2025_, v___x_1953_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 5, v___x_1980_);
lean_ctor_set(v___x_2035_, 0, v___x_2037_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_nextMacroScope_2026_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_ngen_2027_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_auxDeclNGen_2028_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_traceState_2029_);
lean_ctor_set(v_reuseFailAlloc_2056_, 5, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2056_, 6, v_recordedDeps_2030_);
lean_ctor_set(v_reuseFailAlloc_2056_, 7, v_messages_2031_);
lean_ctor_set(v_reuseFailAlloc_2056_, 8, v_infoState_2032_);
lean_ctor_set(v_reuseFailAlloc_2056_, 9, v_snapshotTasks_2033_);
v___x_2039_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v_mctx_2042_; lean_object* v_zetaDeltaFVarIds_2043_; lean_object* v_postponed_2044_; lean_object* v_diag_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2054_; 
v___x_2040_ = lean_st_ref_put(v_a_1933_, v___x_2039_);
v___x_2041_ = lean_st_ref_take(v_a_1931_);
v_mctx_2042_ = lean_ctor_get(v___x_2041_, 0);
v_zetaDeltaFVarIds_2043_ = lean_ctor_get(v___x_2041_, 2);
v_postponed_2044_ = lean_ctor_get(v___x_2041_, 3);
v_diag_2045_ = lean_ctor_get(v___x_2041_, 4);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v___x_2041_, 1);
lean_dec(v_unused_2055_);
v___x_2047_ = v___x_2041_;
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_diag_2045_);
lean_inc(v_postponed_2044_);
lean_inc(v_zetaDeltaFVarIds_2043_);
lean_inc(v_mctx_2042_);
lean_dec(v___x_2041_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v___x_1992_);
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_mctx_2042_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_zetaDeltaFVarIds_2043_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_postponed_2044_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_diag_2045_);
v___x_2050_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_st_ref_put(v_a_1931_, v___x_2050_);
v___x_2052_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_1953_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_2052_;
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
lean_dec(v___x_1953_);
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v___x_1953_);
lean_dec(v_a_1952_);
lean_dec(v_levelParams_1944_);
v_a_2073_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_1954_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_1954_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_levelParams_1944_);
lean_dec(v_indName_1929_);
v_a_2081_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_1951_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_1951_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v___x_1947_);
lean_dec_ref(v_type_1945_);
lean_dec(v_levelParams_1944_);
lean_dec(v_name_1943_);
lean_dec(v___x_1939_);
lean_dec_ref(v_val_1938_);
lean_dec(v_indName_1929_);
v___x_2089_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2);
v___x_2090_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_2089_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_2090_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v___x_1939_);
lean_dec_ref(v_val_1938_);
lean_dec(v_indName_1929_);
v_a_2091_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_1941_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_1941_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v_a_1937_);
lean_dec(v_indName_1929_);
v___x_2099_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3);
v___x_2100_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_2099_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_2100_;
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v_indName_1929_);
v_a_2101_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_1936_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_1936_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___boxed(lean_object* v_indName_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(lean_object* v___x_2116_, lean_object* v_k_2117_, lean_object* v_ctorIdx_2118_, lean_object* v_tail_2119_, lean_object* v___x_2120_, lean_object* v_as_2121_, size_t v_sz_2122_, size_t v_i_2123_, lean_object* v_bs_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_2116_, v_k_2117_, v_ctorIdx_2118_, v_tail_2119_, v___x_2120_, v_sz_2122_, v_i_2123_, v_bs_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___boxed(lean_object* v___x_2131_, lean_object* v_k_2132_, lean_object* v_ctorIdx_2133_, lean_object* v_tail_2134_, lean_object* v___x_2135_, lean_object* v_as_2136_, lean_object* v_sz_2137_, lean_object* v_i_2138_, lean_object* v_bs_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
size_t v_sz_boxed_2145_; size_t v_i_boxed_2146_; lean_object* v_res_2147_; 
v_sz_boxed_2145_ = lean_unbox_usize(v_sz_2137_);
lean_dec(v_sz_2137_);
v_i_boxed_2146_ = lean_unbox_usize(v_i_2138_);
lean_dec(v_i_2138_);
v_res_2147_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(v___x_2131_, v_k_2132_, v_ctorIdx_2133_, v_tail_2134_, v___x_2135_, v_as_2136_, v_sz_boxed_2145_, v_i_boxed_2146_, v_bs_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v_as_2136_);
lean_dec_ref(v___x_2135_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(lean_object* v___x_2148_, lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v___x_2151_, lean_object* v___x_2152_, lean_object* v___x_2153_, lean_object* v___x_2154_, lean_object* v___f_2155_, lean_object* v___x_2156_, lean_object* v___y_2157_, uint8_t v___x_2158_, lean_object* v_h_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_inc(v___x_2149_);
v___x_2165_ = l_Lean_mkConst(v___x_2148_, v___x_2149_);
v___x_2166_ = l_Lean_mkAppN(v___x_2165_, v___x_2150_);
lean_inc_ref(v___x_2151_);
v___x_2167_ = l_Lean_Expr_app___override(v___x_2166_, v___x_2151_);
lean_inc_ref(v___x_2152_);
v___x_2168_ = l_Lean_Expr_app___override(v___x_2167_, v___x_2152_);
v___x_2169_ = l_Lean_mkAppN(v___x_2168_, v___x_2153_);
lean_inc_ref(v_h_2159_);
v___x_2170_ = l_Lean_Meta_mkEqSymm(v_h_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = l_Lean_Expr_app___override(v___x_2169_, v_a_2171_);
v___x_2173_ = l_Lean_mkConst(v___x_2154_, v___x_2149_);
lean_inc_ref(v___x_2151_);
lean_inc_ref(v___x_2150_);
v___x_2174_ = lean_array_push(v___x_2150_, v___x_2151_);
v___x_2175_ = lean_array_push(v___x_2174_, v___x_2152_);
v___x_2176_ = l_Lean_mkAppN(v___x_2173_, v___x_2175_);
lean_dec_ref(v___x_2175_);
v___x_2177_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v___x_2176_, v___f_2155_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l_Lean_Expr_app___override(v___x_2172_, v_a_2178_);
v___x_2180_ = lean_mk_empty_array_with_capacity(v___x_2156_);
v___x_2181_ = lean_array_push(v___x_2180_, v___x_2151_);
v___x_2182_ = l_Array_append___redArg(v___x_2150_, v___x_2181_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = l_Array_append___redArg(v___x_2182_, v___x_2153_);
v___x_2184_ = lean_unsigned_to_nat(2u);
v___x_2185_ = lean_mk_empty_array_with_capacity(v___x_2184_);
v___x_2186_ = lean_array_push(v___x_2185_, v_h_2159_);
v___x_2187_ = lean_array_push(v___x_2186_, v___y_2157_);
v___x_2188_ = l_Array_append___redArg(v___x_2183_, v___x_2187_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = 0;
v___x_2190_ = 1;
v___x_2191_ = l_Lean_Meta_mkLambdaFVars(v___x_2188_, v___x_2179_, v___x_2189_, v___x_2158_, v___x_2189_, v___x_2158_, v___x_2190_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec_ref(v___x_2188_);
return v___x_2191_;
}
else
{
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_h_2159_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v___x_2150_);
return v___x_2177_;
}
}
else
{
lean_dec_ref(v___x_2169_);
lean_dec_ref(v_h_2159_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v___f_2155_);
lean_dec(v___x_2154_);
lean_dec_ref(v___x_2152_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v___x_2150_);
lean_dec(v___x_2149_);
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_2192_ = _args[0];
lean_object* v___x_2193_ = _args[1];
lean_object* v___x_2194_ = _args[2];
lean_object* v___x_2195_ = _args[3];
lean_object* v___x_2196_ = _args[4];
lean_object* v___x_2197_ = _args[5];
lean_object* v___x_2198_ = _args[6];
lean_object* v___f_2199_ = _args[7];
lean_object* v___x_2200_ = _args[8];
lean_object* v___y_2201_ = _args[9];
lean_object* v___x_2202_ = _args[10];
lean_object* v_h_2203_ = _args[11];
lean_object* v___y_2204_ = _args[12];
lean_object* v___y_2205_ = _args[13];
lean_object* v___y_2206_ = _args[14];
lean_object* v___y_2207_ = _args[15];
lean_object* v___y_2208_ = _args[16];
_start:
{
uint8_t v___x_11101__boxed_2209_; lean_object* v_res_2210_; 
v___x_11101__boxed_2209_ = lean_unbox(v___x_2202_);
v_res_2210_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(v___x_2192_, v___x_2193_, v___x_2194_, v___x_2195_, v___x_2196_, v___x_2197_, v___x_2198_, v___f_2199_, v___x_2200_, v___y_2201_, v___x_11101__boxed_2209_, v_h_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___x_2200_);
lean_dec_ref(v___x_2197_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(lean_object* v___y_2211_, lean_object* v_x_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___y_2211_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2219_, lean_object* v_x_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(v___y_2219_, v_x_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v_x_2220_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(lean_object* v___x_2227_, lean_object* v_numParams_2228_, lean_object* v___x_2229_, lean_object* v___x_2230_, lean_object* v_numIndices_2231_, lean_object* v_indName_2232_, lean_object* v_tail_2233_, lean_object* v_i_2234_, lean_object* v___x_2235_, lean_object* v___x_2236_, lean_object* v___x_2237_, uint8_t v___x_2238_, lean_object* v_xs_2239_, lean_object* v_x_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_start_2255_; lean_object* v_stop_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___y_2261_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
lean_inc(v_numParams_2228_);
lean_inc_ref_n(v_xs_2239_, 2);
v___x_2246_ = l_Array_toSubarray___redArg(v_xs_2239_, v___x_2227_, v_numParams_2228_);
v___x_2247_ = lean_array_get(v___x_2229_, v_xs_2239_, v_numParams_2228_);
v___x_2248_ = lean_nat_add(v_numParams_2228_, v___x_2230_);
lean_dec(v_numParams_2228_);
v___x_2249_ = lean_nat_add(v___x_2248_, v_numIndices_2231_);
lean_inc(v___x_2249_);
v___x_2250_ = l_Array_toSubarray___redArg(v_xs_2239_, v___x_2248_, v___x_2249_);
v___x_2251_ = lean_array_get(v___x_2229_, v_xs_2239_, v___x_2249_);
v___x_2252_ = lean_nat_add(v___x_2249_, v___x_2230_);
lean_dec(v___x_2249_);
v___x_2253_ = lean_array_get_size(v_xs_2239_);
v___x_2254_ = l_Array_toSubarray___redArg(v_xs_2239_, v___x_2252_, v___x_2253_);
v_start_2255_ = lean_ctor_get(v___x_2254_, 1);
v_stop_2256_ = lean_ctor_get(v___x_2254_, 2);
v___x_2257_ = l_Subarray_copy___redArg(v___x_2246_);
v___x_2258_ = l_Subarray_copy___redArg(v___x_2250_);
v___x_2259_ = lean_array_push(v___x_2258_, v___x_2251_);
v___x_2274_ = lean_nat_sub(v_stop_2256_, v_start_2255_);
v___x_2275_ = lean_nat_dec_lt(v_i_2234_, v___x_2274_);
lean_dec(v___x_2274_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; 
lean_dec_ref(v___x_2254_);
v___x_2276_ = l_outOfBounds___redArg(v___x_2229_);
v___y_2261_ = v___x_2276_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Subarray_get___redArg(v___x_2254_, v_i_2234_);
lean_dec_ref(v___x_2254_);
v___y_2261_ = v___x_2277_;
goto v___jp_2260_;
}
v___jp_2260_:
{
lean_object* v___f_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; 
lean_inc_ref(v___y_2261_);
v___f_2262_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2262_, 0, v___y_2261_);
v___x_2263_ = l_Lean_mkCtorIdxName(v_indName_2232_);
v___x_2264_ = l_Lean_mkConst(v___x_2263_, v_tail_2233_);
lean_inc_ref(v___x_2257_);
v___x_2265_ = l_Array_append___redArg(v___x_2257_, v___x_2259_);
v___x_2266_ = l_Lean_mkAppN(v___x_2264_, v___x_2265_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = l_Lean_mkRawNatLit(v_i_2234_);
v___x_2268_ = lean_box(v___x_2238_);
lean_inc_ref(v___x_2267_);
v___f_2269_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed), 17, 11);
lean_closure_set(v___f_2269_, 0, v___x_2235_);
lean_closure_set(v___f_2269_, 1, v___x_2236_);
lean_closure_set(v___f_2269_, 2, v___x_2257_);
lean_closure_set(v___f_2269_, 3, v___x_2247_);
lean_closure_set(v___f_2269_, 4, v___x_2267_);
lean_closure_set(v___f_2269_, 5, v___x_2259_);
lean_closure_set(v___f_2269_, 6, v___x_2237_);
lean_closure_set(v___f_2269_, 7, v___f_2262_);
lean_closure_set(v___f_2269_, 8, v___x_2230_);
lean_closure_set(v___f_2269_, 9, v___y_2261_);
lean_closure_set(v___f_2269_, 10, v___x_2268_);
v___x_2270_ = l_Lean_Meta_mkEq(v___x_2266_, v___x_2267_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_2273_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_2272_, v_a_2271_, v___f_2269_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2273_;
}
else
{
lean_dec_ref(v___f_2269_);
return v___x_2270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2278_ = _args[0];
lean_object* v_numParams_2279_ = _args[1];
lean_object* v___x_2280_ = _args[2];
lean_object* v___x_2281_ = _args[3];
lean_object* v_numIndices_2282_ = _args[4];
lean_object* v_indName_2283_ = _args[5];
lean_object* v_tail_2284_ = _args[6];
lean_object* v_i_2285_ = _args[7];
lean_object* v___x_2286_ = _args[8];
lean_object* v___x_2287_ = _args[9];
lean_object* v___x_2288_ = _args[10];
lean_object* v___x_2289_ = _args[11];
lean_object* v_xs_2290_ = _args[12];
lean_object* v_x_2291_ = _args[13];
lean_object* v___y_2292_ = _args[14];
lean_object* v___y_2293_ = _args[15];
lean_object* v___y_2294_ = _args[16];
lean_object* v___y_2295_ = _args[17];
lean_object* v___y_2296_ = _args[18];
_start:
{
uint8_t v___x_11228__boxed_2297_; lean_object* v_res_2298_; 
v___x_11228__boxed_2297_ = lean_unbox(v___x_2289_);
v_res_2298_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(v___x_2278_, v_numParams_2279_, v___x_2280_, v___x_2281_, v_numIndices_2282_, v_indName_2283_, v_tail_2284_, v_i_2285_, v___x_2286_, v___x_2287_, v___x_2288_, v___x_11228__boxed_2297_, v_xs_2290_, v_x_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec_ref(v_x_2291_);
lean_dec(v_numIndices_2282_);
lean_dec_ref(v___x_2280_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0));
v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4));
v___x_2307_ = l_Lean_stringToMessageData(v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(lean_object* v_attrName_2308_, lean_object* v_declName_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2315_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2316_ = l_Lean_MessageData_ofName(v_attrName_2308_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = 0;
v___x_2321_ = l_Lean_MessageData_ofConstName(v_declName_2309_, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2319_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2324_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_2326_, lean_object* v_declName_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2326_, v_declName_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2333_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0));
v___x_2336_ = l_Lean_stringToMessageData(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(lean_object* v_attrName_2340_, lean_object* v_declName_2341_, lean_object* v_asyncPrefix_x3f_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___y_2349_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2342_) == 0)
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_MessageData_nil;
v___y_2349_ = v___x_2362_;
goto v___jp_2348_;
}
else
{
lean_object* v_val_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_val_2363_ = lean_ctor_get(v_asyncPrefix_x3f_2342_, 0);
lean_inc(v_val_2363_);
lean_dec_ref_known(v_asyncPrefix_x3f_2342_, 1);
v___x_2364_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3);
v___x_2365_ = l_Lean_MessageData_ofName(v_val_2363_);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___y_2349_ = v___x_2368_;
goto v___jp_2348_;
}
v___jp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2350_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2351_ = l_Lean_MessageData_ofName(v_attrName_2340_);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = 0;
v___x_2356_ = l_Lean_MessageData_ofConstName(v_declName_2341_, v___x_2355_);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2354_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
lean_ctor_set(v___x_2360_, 1, v___y_2349_);
v___x_2361_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2360_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_2369_, lean_object* v_declName_2370_, lean_object* v_asyncPrefix_x3f_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2369_, v_declName_2370_, v_asyncPrefix_x3f_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0(lean_object* v_addEntryFn_2378_, lean_object* v_decl_2379_, lean_object* v_s_2380_){
_start:
{
lean_object* v_importedEntries_2381_; lean_object* v_state_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2390_; 
v_importedEntries_2381_ = lean_ctor_get(v_s_2380_, 0);
v_state_2382_ = lean_ctor_get(v_s_2380_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_s_2380_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2384_ = v_s_2380_;
v_isShared_2385_ = v_isSharedCheck_2390_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_state_2382_);
lean_inc(v_importedEntries_2381_);
lean_dec(v_s_2380_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2390_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_state_2386_; lean_object* v___x_2388_; 
v_state_2386_ = lean_apply_2(v_addEntryFn_2378_, v_state_2382_, v_decl_2379_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v_state_2386_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_importedEntries_2381_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_state_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(lean_object* v_attr_2391_, lean_object* v_decl_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___x_2453_; lean_object* v_env_2454_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___x_2469_; 
v___x_2453_ = lean_st_ref_get(v___y_2396_);
v_env_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_ref(v_env_2454_);
lean_dec(v___x_2453_);
v___x_2469_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2454_, v_decl_2392_);
if (lean_obj_tag(v___x_2469_) == 0)
{
v___y_2456_ = v___y_2393_;
v___y_2457_ = v___y_2394_;
v___y_2458_ = v___y_2395_;
v___y_2459_ = v___y_2396_;
goto v___jp_2455_;
}
else
{
lean_object* v_attr_2470_; lean_object* v_toAttributeImplCore_2471_; lean_object* v_name_2472_; lean_object* v___x_2473_; 
lean_dec_ref_known(v___x_2469_, 1);
lean_dec_ref(v_env_2454_);
v_attr_2470_ = lean_ctor_get(v_attr_2391_, 0);
lean_inc_ref(v_attr_2470_);
lean_dec_ref(v_attr_2391_);
v_toAttributeImplCore_2471_ = lean_ctor_get(v_attr_2470_, 0);
lean_inc_ref(v_toAttributeImplCore_2471_);
lean_dec_ref(v_attr_2470_);
v_name_2472_ = lean_ctor_get(v_toAttributeImplCore_2471_, 1);
lean_inc(v_name_2472_);
lean_dec_ref(v_toAttributeImplCore_2471_);
v___x_2473_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_name_2472_, v_decl_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2473_;
}
v___jp_2398_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v_mctx_2414_; lean_object* v_zetaDeltaFVarIds_2415_; lean_object* v_postponed_2416_; lean_object* v_diag_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2428_; 
v___x_2410_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
v___x_2411_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2411_, 0, v___y_2409_);
lean_ctor_set(v___x_2411_, 1, v___y_2407_);
lean_ctor_set(v___x_2411_, 2, v___y_2404_);
lean_ctor_set(v___x_2411_, 3, v___y_2403_);
lean_ctor_set(v___x_2411_, 4, v___y_2406_);
lean_ctor_set(v___x_2411_, 5, v___x_2410_);
lean_ctor_set(v___x_2411_, 6, v___y_2405_);
lean_ctor_set(v___x_2411_, 7, v___y_2401_);
lean_ctor_set(v___x_2411_, 8, v___y_2408_);
lean_ctor_set(v___x_2411_, 9, v___y_2402_);
v___x_2412_ = lean_st_ref_put(v___y_2399_, v___x_2411_);
v___x_2413_ = lean_st_ref_take(v___y_2400_);
v_mctx_2414_ = lean_ctor_get(v___x_2413_, 0);
v_zetaDeltaFVarIds_2415_ = lean_ctor_get(v___x_2413_, 2);
v_postponed_2416_ = lean_ctor_get(v___x_2413_, 3);
v_diag_2417_ = lean_ctor_get(v___x_2413_, 4);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; 
v_unused_2429_ = lean_ctor_get(v___x_2413_, 1);
lean_dec(v_unused_2429_);
v___x_2419_ = v___x_2413_;
v_isShared_2420_ = v_isSharedCheck_2428_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_diag_2417_);
lean_inc(v_postponed_2416_);
lean_inc(v_zetaDeltaFVarIds_2415_);
lean_inc(v_mctx_2414_);
lean_dec(v___x_2413_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2428_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2421_ = lean_box(0);
v___x_2422_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 1, v___x_2422_);
v___x_2424_ = v___x_2419_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_mctx_2414_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_zetaDeltaFVarIds_2415_);
lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_postponed_2416_);
lean_ctor_set(v_reuseFailAlloc_2427_, 4, v_diag_2417_);
v___x_2424_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_st_ref_put(v___y_2400_, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2421_);
return v___x_2426_;
}
}
}
v___jp_2430_:
{
lean_object* v___x_2433_; lean_object* v_ext_2434_; lean_object* v_toEnvExtension_2435_; lean_object* v_env_2436_; lean_object* v_nextMacroScope_2437_; lean_object* v_ngen_2438_; lean_object* v_auxDeclNGen_2439_; lean_object* v_traceState_2440_; lean_object* v_recordedDeps_2441_; lean_object* v_messages_2442_; lean_object* v_infoState_2443_; lean_object* v_snapshotTasks_2444_; lean_object* v_addEntryFn_2445_; lean_object* v_asyncMode_2446_; uint8_t v_logWrites_2447_; lean_object* v___f_2448_; uint8_t v___x_2449_; 
v___x_2433_ = lean_st_ref_take(v___y_2432_);
v_ext_2434_ = lean_ctor_get(v_attr_2391_, 1);
lean_inc_ref(v_ext_2434_);
lean_dec_ref(v_attr_2391_);
v_toEnvExtension_2435_ = lean_ctor_get(v_ext_2434_, 0);
lean_inc_ref(v_toEnvExtension_2435_);
v_env_2436_ = lean_ctor_get(v___x_2433_, 0);
lean_inc_ref(v_env_2436_);
v_nextMacroScope_2437_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_nextMacroScope_2437_);
v_ngen_2438_ = lean_ctor_get(v___x_2433_, 2);
lean_inc_ref(v_ngen_2438_);
v_auxDeclNGen_2439_ = lean_ctor_get(v___x_2433_, 3);
lean_inc_ref(v_auxDeclNGen_2439_);
v_traceState_2440_ = lean_ctor_get(v___x_2433_, 4);
lean_inc_ref(v_traceState_2440_);
v_recordedDeps_2441_ = lean_ctor_get(v___x_2433_, 6);
lean_inc_ref(v_recordedDeps_2441_);
v_messages_2442_ = lean_ctor_get(v___x_2433_, 7);
lean_inc_ref(v_messages_2442_);
v_infoState_2443_ = lean_ctor_get(v___x_2433_, 8);
lean_inc_ref(v_infoState_2443_);
v_snapshotTasks_2444_ = lean_ctor_get(v___x_2433_, 9);
lean_inc_ref(v_snapshotTasks_2444_);
lean_dec(v___x_2433_);
v_addEntryFn_2445_ = lean_ctor_get(v_ext_2434_, 3);
lean_inc(v_addEntryFn_2445_);
lean_dec_ref(v_ext_2434_);
v_asyncMode_2446_ = lean_ctor_get(v_toEnvExtension_2435_, 2);
lean_inc(v_asyncMode_2446_);
v_logWrites_2447_ = lean_ctor_get_uint8(v_toEnvExtension_2435_, sizeof(void*)*6);
lean_inc(v_decl_2392_);
v___f_2448_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2448_, 0, v_addEntryFn_2445_);
lean_closure_set(v___f_2448_, 1, v_decl_2392_);
v___x_2449_ = 1;
if (v_logWrites_2447_ == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2435_, v_env_2436_, v___f_2448_, v_asyncMode_2446_, v_decl_2392_, v___x_2449_);
lean_dec(v_asyncMode_2446_);
v___y_2399_ = v___y_2432_;
v___y_2400_ = v___y_2431_;
v___y_2401_ = v_messages_2442_;
v___y_2402_ = v_snapshotTasks_2444_;
v___y_2403_ = v_auxDeclNGen_2439_;
v___y_2404_ = v_ngen_2438_;
v___y_2405_ = v_recordedDeps_2441_;
v___y_2406_ = v_traceState_2440_;
v___y_2407_ = v_nextMacroScope_2437_;
v___y_2408_ = v_infoState_2443_;
v___y_2409_ = v___x_2450_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_inc_ref(v_toEnvExtension_2435_);
v___x_2451_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2435_, v_env_2436_);
lean_dec_ref(v_env_2436_);
v___x_2452_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2435_, v___x_2451_, v___f_2448_, v_asyncMode_2446_, v_decl_2392_, v___x_2449_);
lean_dec(v_asyncMode_2446_);
v___y_2399_ = v___y_2432_;
v___y_2400_ = v___y_2431_;
v___y_2401_ = v_messages_2442_;
v___y_2402_ = v_snapshotTasks_2444_;
v___y_2403_ = v_auxDeclNGen_2439_;
v___y_2404_ = v_ngen_2438_;
v___y_2405_ = v_recordedDeps_2441_;
v___y_2406_ = v_traceState_2440_;
v___y_2407_ = v_nextMacroScope_2437_;
v___y_2408_ = v_infoState_2443_;
v___y_2409_ = v___x_2452_;
goto v___jp_2398_;
}
}
v___jp_2455_:
{
lean_object* v_ext_2460_; lean_object* v_toEnvExtension_2461_; lean_object* v_attr_2462_; lean_object* v_asyncMode_2463_; uint8_t v___x_2464_; 
v_ext_2460_ = lean_ctor_get(v_attr_2391_, 1);
v_toEnvExtension_2461_ = lean_ctor_get(v_ext_2460_, 0);
v_attr_2462_ = lean_ctor_get(v_attr_2391_, 0);
v_asyncMode_2463_ = lean_ctor_get(v_toEnvExtension_2461_, 2);
lean_inc(v_decl_2392_);
lean_inc_ref(v_env_2454_);
v___x_2464_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2454_, v_decl_2392_, v_asyncMode_2463_);
if (v___x_2464_ == 0)
{
lean_object* v_toAttributeImplCore_2465_; lean_object* v_name_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_inc_ref(v_attr_2462_);
lean_dec_ref(v_attr_2391_);
v_toAttributeImplCore_2465_ = lean_ctor_get(v_attr_2462_, 0);
lean_inc_ref(v_toAttributeImplCore_2465_);
lean_dec_ref(v_attr_2462_);
v_name_2466_ = lean_ctor_get(v_toAttributeImplCore_2465_, 1);
lean_inc(v_name_2466_);
lean_dec_ref(v_toAttributeImplCore_2465_);
v___x_2467_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2454_);
v___x_2468_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_name_2466_, v_decl_2392_, v___x_2467_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
return v___x_2468_;
}
else
{
lean_dec_ref(v_env_2454_);
v___y_2431_ = v___y_2457_;
v___y_2432_ = v___y_2459_;
goto v___jp_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___boxed(lean_object* v_attr_2474_, lean_object* v_decl_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v_attr_2474_, v_decl_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(lean_object* v_val_2482_, lean_object* v_indName_2483_, lean_object* v_tail_2484_, lean_object* v___x_2485_, lean_object* v___x_2486_, lean_object* v___x_2487_, lean_object* v_a_2488_, lean_object* v_range_2489_, lean_object* v_b_2490_, lean_object* v_i_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_stop_2497_; lean_object* v_step_2498_; uint8_t v___x_2499_; 
v_stop_2497_ = lean_ctor_get(v_range_2489_, 1);
v_step_2498_ = lean_ctor_get(v_range_2489_, 2);
v___x_2499_ = lean_nat_dec_lt(v_i_2491_, v_stop_2497_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
lean_dec(v_i_2491_);
lean_dec_ref(v_a_2488_);
lean_dec(v___x_2487_);
lean_dec(v___x_2486_);
lean_dec(v___x_2485_);
lean_dec(v_tail_2484_);
lean_dec(v_indName_2483_);
lean_dec_ref(v_val_2482_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_b_2490_);
return v___x_2500_;
}
else
{
lean_object* v_numParams_2501_; lean_object* v_numIndices_2502_; lean_object* v_ctors_2503_; lean_object* v_levelParams_2504_; lean_object* v_type_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___f_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; lean_object* v___x_2516_; 
v_numParams_2501_ = lean_ctor_get(v_val_2482_, 1);
v_numIndices_2502_ = lean_ctor_get(v_val_2482_, 2);
v_ctors_2503_ = lean_ctor_get(v_val_2482_, 4);
v_levelParams_2504_ = lean_ctor_get(v_a_2488_, 1);
v_type_2505_ = lean_ctor_get(v_a_2488_, 2);
v___x_2506_ = lean_unsigned_to_nat(0u);
v___x_2507_ = l_Lean_instInhabitedExpr;
v___x_2508_ = lean_unsigned_to_nat(1u);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_box(v___x_2499_);
lean_inc(v___x_2487_);
lean_inc(v___x_2486_);
lean_inc(v___x_2485_);
lean_inc_n(v_i_2491_, 2);
lean_inc(v_tail_2484_);
lean_inc_n(v_indName_2483_, 2);
lean_inc(v_numIndices_2502_);
lean_inc(v_numParams_2501_);
v___f_2512_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed), 19, 12);
lean_closure_set(v___f_2512_, 0, v___x_2506_);
lean_closure_set(v___f_2512_, 1, v_numParams_2501_);
lean_closure_set(v___f_2512_, 2, v___x_2507_);
lean_closure_set(v___f_2512_, 3, v___x_2508_);
lean_closure_set(v___f_2512_, 4, v_numIndices_2502_);
lean_closure_set(v___f_2512_, 5, v_indName_2483_);
lean_closure_set(v___f_2512_, 6, v_tail_2484_);
lean_closure_set(v___f_2512_, 7, v_i_2491_);
lean_closure_set(v___f_2512_, 8, v___x_2485_);
lean_closure_set(v___f_2512_, 9, v___x_2486_);
lean_closure_set(v___f_2512_, 10, v___x_2487_);
lean_closure_set(v___f_2512_, 11, v___x_2511_);
v___x_2513_ = l_List_get_x21Internal___redArg(v___x_2509_, v_ctors_2503_, v_i_2491_);
v___x_2514_ = l_Lean_mkConstructorElimName(v_indName_2483_, v___x_2513_);
v___x_2515_ = 0;
lean_inc_ref(v_type_2505_);
v___x_2516_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_2505_, v___f_2512_, v___x_2515_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2518_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_n(v_a_2517_, 2);
lean_dec_ref_known(v___x_2516_, 1);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
v___x_2518_ = lean_infer_type(v_a_2517_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2673_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2520_ = lean_box(1);
lean_inc(v_levelParams_2504_);
lean_inc(v___x_2514_);
v___x_2521_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_2514_, v_levelParams_2504_, v_a_2519_, v_a_2517_, v___x_2520_, v___y_2495_);
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2673_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2673_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set_tag(v___x_2524_, 1);
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_addAndCompile(v___x_2527_, v___x_2499_, v___x_2515_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v___x_2529_; lean_object* v_env_2530_; lean_object* v_nextMacroScope_2531_; lean_object* v_ngen_2532_; lean_object* v_auxDeclNGen_2533_; lean_object* v_traceState_2534_; lean_object* v_recordedDeps_2535_; lean_object* v_messages_2536_; lean_object* v_infoState_2537_; lean_object* v_snapshotTasks_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref_known(v___x_2528_, 1);
v___x_2529_ = lean_st_ref_take(v___y_2495_);
v_env_2530_ = lean_ctor_get(v___x_2529_, 0);
v_nextMacroScope_2531_ = lean_ctor_get(v___x_2529_, 1);
v_ngen_2532_ = lean_ctor_get(v___x_2529_, 2);
v_auxDeclNGen_2533_ = lean_ctor_get(v___x_2529_, 3);
v_traceState_2534_ = lean_ctor_get(v___x_2529_, 4);
v_recordedDeps_2535_ = lean_ctor_get(v___x_2529_, 6);
v_messages_2536_ = lean_ctor_get(v___x_2529_, 7);
v_infoState_2537_ = lean_ctor_get(v___x_2529_, 8);
v_snapshotTasks_2538_ = lean_ctor_get(v___x_2529_, 9);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v___x_2529_, 5);
lean_dec(v_unused_2671_);
v___x_2540_ = v___x_2529_;
v_isShared_2541_ = v_isSharedCheck_2670_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_snapshotTasks_2538_);
lean_inc(v_infoState_2537_);
lean_inc(v_messages_2536_);
lean_inc(v_recordedDeps_2535_);
lean_inc(v_traceState_2534_);
lean_inc(v_auxDeclNGen_2533_);
lean_inc(v_ngen_2532_);
lean_inc(v_nextMacroScope_2531_);
lean_inc(v_env_2530_);
lean_dec(v___x_2529_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2670_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_inc(v___x_2514_);
v___x_2542_ = l_Lean_markAuxRecursor(v_env_2530_, v___x_2514_);
v___x_2543_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 5, v___x_2543_);
lean_ctor_set(v___x_2540_, 0, v___x_2542_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_nextMacroScope_2531_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_ngen_2532_);
lean_ctor_set(v_reuseFailAlloc_2669_, 3, v_auxDeclNGen_2533_);
lean_ctor_set(v_reuseFailAlloc_2669_, 4, v_traceState_2534_);
lean_ctor_set(v_reuseFailAlloc_2669_, 5, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2669_, 6, v_recordedDeps_2535_);
lean_ctor_set(v_reuseFailAlloc_2669_, 7, v_messages_2536_);
lean_ctor_set(v_reuseFailAlloc_2669_, 8, v_infoState_2537_);
lean_ctor_set(v_reuseFailAlloc_2669_, 9, v_snapshotTasks_2538_);
v___x_2545_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v_mctx_2548_; lean_object* v_zetaDeltaFVarIds_2549_; lean_object* v_postponed_2550_; lean_object* v_diag_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2667_; 
v___x_2546_ = lean_st_ref_put(v___y_2495_, v___x_2545_);
v___x_2547_ = lean_st_ref_take(v___y_2493_);
v_mctx_2548_ = lean_ctor_get(v___x_2547_, 0);
v_zetaDeltaFVarIds_2549_ = lean_ctor_get(v___x_2547_, 2);
v_postponed_2550_ = lean_ctor_get(v___x_2547_, 3);
v_diag_2551_ = lean_ctor_get(v___x_2547_, 4);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v___x_2547_, 1);
lean_dec(v_unused_2668_);
v___x_2553_ = v___x_2547_;
v_isShared_2554_ = v_isSharedCheck_2667_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_diag_2551_);
lean_inc(v_postponed_2550_);
lean_inc(v_zetaDeltaFVarIds_2549_);
lean_inc(v_mctx_2548_);
lean_dec(v___x_2547_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2667_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 1, v___x_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_mctx_2548_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v_zetaDeltaFVarIds_2549_);
lean_ctor_set(v_reuseFailAlloc_2666_, 3, v_postponed_2550_);
lean_ctor_set(v_reuseFailAlloc_2666_, 4, v_diag_2551_);
v___x_2557_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_env_2560_; lean_object* v_nextMacroScope_2561_; lean_object* v_ngen_2562_; lean_object* v_auxDeclNGen_2563_; lean_object* v_traceState_2564_; lean_object* v_recordedDeps_2565_; lean_object* v_messages_2566_; lean_object* v_infoState_2567_; lean_object* v_snapshotTasks_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2664_; 
v___x_2558_ = lean_st_ref_put(v___y_2493_, v___x_2557_);
v___x_2559_ = lean_st_ref_take(v___y_2495_);
v_env_2560_ = lean_ctor_get(v___x_2559_, 0);
v_nextMacroScope_2561_ = lean_ctor_get(v___x_2559_, 1);
v_ngen_2562_ = lean_ctor_get(v___x_2559_, 2);
v_auxDeclNGen_2563_ = lean_ctor_get(v___x_2559_, 3);
v_traceState_2564_ = lean_ctor_get(v___x_2559_, 4);
v_recordedDeps_2565_ = lean_ctor_get(v___x_2559_, 6);
v_messages_2566_ = lean_ctor_get(v___x_2559_, 7);
v_infoState_2567_ = lean_ctor_get(v___x_2559_, 8);
v_snapshotTasks_2568_ = lean_ctor_get(v___x_2559_, 9);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2559_, 5);
lean_dec(v_unused_2665_);
v___x_2570_ = v___x_2559_;
v_isShared_2571_ = v_isSharedCheck_2664_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snapshotTasks_2568_);
lean_inc(v_infoState_2567_);
lean_inc(v_messages_2566_);
lean_inc(v_recordedDeps_2565_);
lean_inc(v_traceState_2564_);
lean_inc(v_auxDeclNGen_2563_);
lean_inc(v_ngen_2562_);
lean_inc(v_nextMacroScope_2561_);
lean_inc(v_env_2560_);
lean_dec(v___x_2559_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2664_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
lean_inc(v___x_2514_);
v___x_2572_ = l_Lean_markSparseCasesOn(v_env_2560_, v___x_2514_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 5, v___x_2543_);
lean_ctor_set(v___x_2570_, 0, v___x_2572_);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_nextMacroScope_2561_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_ngen_2562_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_auxDeclNGen_2563_);
lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_traceState_2564_);
lean_ctor_set(v_reuseFailAlloc_2663_, 5, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2663_, 6, v_recordedDeps_2565_);
lean_ctor_set(v_reuseFailAlloc_2663_, 7, v_messages_2566_);
lean_ctor_set(v_reuseFailAlloc_2663_, 8, v_infoState_2567_);
lean_ctor_set(v_reuseFailAlloc_2663_, 9, v_snapshotTasks_2568_);
v___x_2574_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v_mctx_2577_; lean_object* v_zetaDeltaFVarIds_2578_; lean_object* v_postponed_2579_; lean_object* v_diag_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2661_; 
v___x_2575_ = lean_st_ref_put(v___y_2495_, v___x_2574_);
v___x_2576_ = lean_st_ref_take(v___y_2493_);
v_mctx_2577_ = lean_ctor_get(v___x_2576_, 0);
v_zetaDeltaFVarIds_2578_ = lean_ctor_get(v___x_2576_, 2);
v_postponed_2579_ = lean_ctor_get(v___x_2576_, 3);
v_diag_2580_ = lean_ctor_get(v___x_2576_, 4);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; 
v_unused_2662_ = lean_ctor_get(v___x_2576_, 1);
lean_dec(v_unused_2662_);
v___x_2582_ = v___x_2576_;
v_isShared_2583_ = v_isSharedCheck_2661_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_diag_2580_);
lean_inc(v_postponed_2579_);
lean_inc(v_zetaDeltaFVarIds_2578_);
lean_inc(v_mctx_2577_);
lean_dec(v___x_2576_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2661_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 1, v___x_2555_);
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_mctx_2577_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_zetaDeltaFVarIds_2578_);
lean_ctor_set(v_reuseFailAlloc_2660_, 3, v_postponed_2579_);
lean_ctor_set(v_reuseFailAlloc_2660_, 4, v_diag_2580_);
v___x_2585_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v_env_2588_; lean_object* v_nextMacroScope_2589_; lean_object* v_ngen_2590_; lean_object* v_auxDeclNGen_2591_; lean_object* v_traceState_2592_; lean_object* v_recordedDeps_2593_; lean_object* v_messages_2594_; lean_object* v_infoState_2595_; lean_object* v_snapshotTasks_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2658_; 
v___x_2586_ = lean_st_ref_put(v___y_2493_, v___x_2585_);
v___x_2587_ = lean_st_ref_take(v___y_2495_);
v_env_2588_ = lean_ctor_get(v___x_2587_, 0);
v_nextMacroScope_2589_ = lean_ctor_get(v___x_2587_, 1);
v_ngen_2590_ = lean_ctor_get(v___x_2587_, 2);
v_auxDeclNGen_2591_ = lean_ctor_get(v___x_2587_, 3);
v_traceState_2592_ = lean_ctor_get(v___x_2587_, 4);
v_recordedDeps_2593_ = lean_ctor_get(v___x_2587_, 6);
v_messages_2594_ = lean_ctor_get(v___x_2587_, 7);
v_infoState_2595_ = lean_ctor_get(v___x_2587_, 8);
v_snapshotTasks_2596_ = lean_ctor_get(v___x_2587_, 9);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2658_ == 0)
{
lean_object* v_unused_2659_; 
v_unused_2659_ = lean_ctor_get(v___x_2587_, 5);
lean_dec(v_unused_2659_);
v___x_2598_ = v___x_2587_;
v_isShared_2599_ = v_isSharedCheck_2658_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_snapshotTasks_2596_);
lean_inc(v_infoState_2595_);
lean_inc(v_messages_2594_);
lean_inc(v_recordedDeps_2593_);
lean_inc(v_traceState_2592_);
lean_inc(v_auxDeclNGen_2591_);
lean_inc(v_ngen_2590_);
lean_inc(v_nextMacroScope_2589_);
lean_inc(v_env_2588_);
lean_dec(v___x_2587_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2658_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_inc(v___x_2514_);
v___x_2600_ = l_Lean_Meta_addToCompletionBlackList(v_env_2588_, v___x_2514_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 5, v___x_2543_);
lean_ctor_set(v___x_2598_, 0, v___x_2600_);
v___x_2602_ = v___x_2598_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_nextMacroScope_2589_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v_ngen_2590_);
lean_ctor_set(v_reuseFailAlloc_2657_, 3, v_auxDeclNGen_2591_);
lean_ctor_set(v_reuseFailAlloc_2657_, 4, v_traceState_2592_);
lean_ctor_set(v_reuseFailAlloc_2657_, 5, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2657_, 6, v_recordedDeps_2593_);
lean_ctor_set(v_reuseFailAlloc_2657_, 7, v_messages_2594_);
lean_ctor_set(v_reuseFailAlloc_2657_, 8, v_infoState_2595_);
lean_ctor_set(v_reuseFailAlloc_2657_, 9, v_snapshotTasks_2596_);
v___x_2602_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v_mctx_2605_; lean_object* v_zetaDeltaFVarIds_2606_; lean_object* v_postponed_2607_; lean_object* v_diag_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2655_; 
v___x_2603_ = lean_st_ref_put(v___y_2495_, v___x_2602_);
v___x_2604_ = lean_st_ref_take(v___y_2493_);
v_mctx_2605_ = lean_ctor_get(v___x_2604_, 0);
v_zetaDeltaFVarIds_2606_ = lean_ctor_get(v___x_2604_, 2);
v_postponed_2607_ = lean_ctor_get(v___x_2604_, 3);
v_diag_2608_ = lean_ctor_get(v___x_2604_, 4);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v___x_2604_, 1);
lean_dec(v_unused_2656_);
v___x_2610_ = v___x_2604_;
v_isShared_2611_ = v_isSharedCheck_2655_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_diag_2608_);
lean_inc(v_postponed_2607_);
lean_inc(v_zetaDeltaFVarIds_2606_);
lean_inc(v_mctx_2605_);
lean_dec(v___x_2604_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2655_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 1, v___x_2555_);
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_mctx_2605_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_zetaDeltaFVarIds_2606_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_postponed_2607_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v_diag_2608_);
v___x_2613_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v_env_2616_; lean_object* v_nextMacroScope_2617_; lean_object* v_ngen_2618_; lean_object* v_auxDeclNGen_2619_; lean_object* v_traceState_2620_; lean_object* v_recordedDeps_2621_; lean_object* v_messages_2622_; lean_object* v_infoState_2623_; lean_object* v_snapshotTasks_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2652_; 
v___x_2614_ = lean_st_ref_put(v___y_2493_, v___x_2613_);
v___x_2615_ = lean_st_ref_take(v___y_2495_);
v_env_2616_ = lean_ctor_get(v___x_2615_, 0);
v_nextMacroScope_2617_ = lean_ctor_get(v___x_2615_, 1);
v_ngen_2618_ = lean_ctor_get(v___x_2615_, 2);
v_auxDeclNGen_2619_ = lean_ctor_get(v___x_2615_, 3);
v_traceState_2620_ = lean_ctor_get(v___x_2615_, 4);
v_recordedDeps_2621_ = lean_ctor_get(v___x_2615_, 6);
v_messages_2622_ = lean_ctor_get(v___x_2615_, 7);
v_infoState_2623_ = lean_ctor_get(v___x_2615_, 8);
v_snapshotTasks_2624_ = lean_ctor_get(v___x_2615_, 9);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v___x_2615_, 5);
lean_dec(v_unused_2653_);
v___x_2626_ = v___x_2615_;
v_isShared_2627_ = v_isSharedCheck_2652_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_snapshotTasks_2624_);
lean_inc(v_infoState_2623_);
lean_inc(v_messages_2622_);
lean_inc(v_recordedDeps_2621_);
lean_inc(v_traceState_2620_);
lean_inc(v_auxDeclNGen_2619_);
lean_inc(v_ngen_2618_);
lean_inc(v_nextMacroScope_2617_);
lean_inc(v_env_2616_);
lean_dec(v___x_2615_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2652_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
lean_inc(v___x_2514_);
v___x_2628_ = l_Lean_addProtected(v_env_2616_, v___x_2514_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 5, v___x_2543_);
lean_ctor_set(v___x_2626_, 0, v___x_2628_);
v___x_2630_ = v___x_2626_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_nextMacroScope_2617_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_ngen_2618_);
lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_auxDeclNGen_2619_);
lean_ctor_set(v_reuseFailAlloc_2651_, 4, v_traceState_2620_);
lean_ctor_set(v_reuseFailAlloc_2651_, 5, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2651_, 6, v_recordedDeps_2621_);
lean_ctor_set(v_reuseFailAlloc_2651_, 7, v_messages_2622_);
lean_ctor_set(v_reuseFailAlloc_2651_, 8, v_infoState_2623_);
lean_ctor_set(v_reuseFailAlloc_2651_, 9, v_snapshotTasks_2624_);
v___x_2630_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_mctx_2633_; lean_object* v_zetaDeltaFVarIds_2634_; lean_object* v_postponed_2635_; lean_object* v_diag_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2649_; 
v___x_2631_ = lean_st_ref_put(v___y_2495_, v___x_2630_);
v___x_2632_ = lean_st_ref_take(v___y_2493_);
v_mctx_2633_ = lean_ctor_get(v___x_2632_, 0);
v_zetaDeltaFVarIds_2634_ = lean_ctor_get(v___x_2632_, 2);
v_postponed_2635_ = lean_ctor_get(v___x_2632_, 3);
v_diag_2636_ = lean_ctor_get(v___x_2632_, 4);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; 
v_unused_2650_ = lean_ctor_get(v___x_2632_, 1);
lean_dec(v_unused_2650_);
v___x_2638_ = v___x_2632_;
v_isShared_2639_ = v_isSharedCheck_2649_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_diag_2636_);
lean_inc(v_postponed_2635_);
lean_inc(v_zetaDeltaFVarIds_2634_);
lean_inc(v_mctx_2633_);
lean_dec(v___x_2632_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2649_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 1, v___x_2555_);
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_mctx_2633_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_zetaDeltaFVarIds_2634_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_postponed_2635_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_diag_2636_);
v___x_2641_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_st_ref_put(v___y_2493_, v___x_2641_);
v___x_2643_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v___x_2514_);
v___x_2644_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v___x_2643_, v___x_2514_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec_ref_known(v___x_2644_, 1);
v___x_2645_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2514_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec_ref(v___x_2645_);
v___x_2646_ = lean_nat_add(v_i_2491_, v_step_2498_);
lean_dec(v_i_2491_);
v_b_2490_ = v___x_2510_;
v_i_2491_ = v___x_2646_;
goto _start;
}
else
{
lean_dec(v___x_2514_);
lean_dec(v_i_2491_);
lean_dec_ref(v_a_2488_);
lean_dec(v___x_2487_);
lean_dec(v___x_2486_);
lean_dec(v___x_2485_);
lean_dec(v_tail_2484_);
lean_dec(v_indName_2483_);
lean_dec_ref(v_val_2482_);
return v___x_2644_;
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
lean_dec(v___x_2514_);
lean_dec(v_i_2491_);
lean_dec_ref(v_a_2488_);
lean_dec(v___x_2487_);
lean_dec(v___x_2486_);
lean_dec(v___x_2485_);
lean_dec(v_tail_2484_);
lean_dec(v_indName_2483_);
lean_dec_ref(v_val_2482_);
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec(v_a_2517_);
lean_dec(v___x_2514_);
lean_dec(v_i_2491_);
lean_dec_ref(v_a_2488_);
lean_dec(v___x_2487_);
lean_dec(v___x_2486_);
lean_dec(v___x_2485_);
lean_dec(v_tail_2484_);
lean_dec(v_indName_2483_);
lean_dec_ref(v_val_2482_);
v_a_2674_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2518_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2518_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v___x_2514_);
lean_dec(v_i_2491_);
lean_dec_ref(v_a_2488_);
lean_dec(v___x_2487_);
lean_dec(v___x_2486_);
lean_dec(v___x_2485_);
lean_dec(v_tail_2484_);
lean_dec(v_indName_2483_);
lean_dec_ref(v_val_2482_);
v_a_2682_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2516_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2516_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___boxed(lean_object* v_val_2690_, lean_object* v_indName_2691_, lean_object* v_tail_2692_, lean_object* v___x_2693_, lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v_a_2696_, lean_object* v_range_2697_, lean_object* v_b_2698_, lean_object* v_i_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2690_, v_indName_2691_, v_tail_2692_, v___x_2693_, v___x_2694_, v___x_2695_, v_a_2696_, v_range_2697_, v_b_2698_, v_i_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec_ref(v_range_2697_);
return v_res_2705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_2708_ = lean_unsigned_to_nat(58u);
v___x_2709_ = lean_unsigned_to_nat(169u);
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2712_ = l_mkPanicMessageWithDecl(v___x_2711_, v___x_2710_, v___x_2709_, v___x_2708_, v___x_2707_);
return v___x_2712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_2714_ = lean_unsigned_to_nat(60u);
v___x_2715_ = lean_unsigned_to_nat(166u);
v___x_2716_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2717_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2718_ = l_mkPanicMessageWithDecl(v___x_2717_, v___x_2716_, v___x_2715_, v___x_2714_, v___x_2713_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(lean_object* v_indName_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v___x_2725_; 
lean_inc(v_indName_2719_);
v___x_2725_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
if (lean_obj_tag(v_a_2726_) == 5)
{
lean_object* v_val_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_val_2727_ = lean_ctor_get(v_a_2726_, 0);
lean_inc_ref(v_val_2727_);
lean_dec_ref_known(v_a_2726_, 1);
lean_inc(v_indName_2719_);
v___x_2728_ = l_Lean_mkCasesOnName(v_indName_2719_);
lean_inc(v___x_2728_);
v___x_2729_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2728_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v_levelParams_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2768_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v_levelParams_2731_ = lean_ctor_get(v_a_2730_, 1);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_a_2730_);
if (v_isSharedCheck_2768_ == 0)
{
lean_object* v_unused_2769_; lean_object* v_unused_2770_; 
v_unused_2769_ = lean_ctor_get(v_a_2730_, 2);
lean_dec(v_unused_2769_);
v_unused_2770_ = lean_ctor_get(v_a_2730_, 0);
lean_dec(v_unused_2770_);
v___x_2733_ = v_a_2730_;
v_isShared_2734_ = v_isSharedCheck_2768_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_levelParams_2731_);
lean_dec(v_a_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2768_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_box(0);
v___x_2736_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_2731_, v___x_2735_);
if (lean_obj_tag(v___x_2736_) == 1)
{
lean_object* v_tail_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_tail_2737_ = lean_ctor_get(v___x_2736_, 1);
lean_inc(v_tail_2737_);
lean_inc_n(v_indName_2719_, 2);
v___x_2738_ = l_Lean_mkCtorElimName(v_indName_2719_);
v___x_2739_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_2719_);
v___x_2740_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2728_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = l_Lean_InductiveVal_numCtors(v_val_2727_);
v___x_2744_ = lean_unsigned_to_nat(1u);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 2, v___x_2744_);
lean_ctor_set(v___x_2733_, 1, v___x_2743_);
lean_ctor_set(v___x_2733_, 0, v___x_2742_);
v___x_2746_ = v___x_2733_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2743_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = lean_box(0);
v___x_2748_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2727_, v_indName_2719_, v_tail_2737_, v___x_2738_, v___x_2736_, v___x_2739_, v_a_2741_, v___x_2746_, v___x_2747_, v___x_2742_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec_ref(v___x_2746_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v___x_2748_, 0);
lean_dec(v_unused_2756_);
v___x_2750_ = v___x_2748_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_dec(v___x_2748_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2747_);
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2747_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
else
{
return v___x_2748_;
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v___x_2739_);
lean_dec(v___x_2738_);
lean_dec(v_tail_2737_);
lean_dec_ref_known(v___x_2736_, 2);
lean_del_object(v___x_2733_);
lean_dec_ref(v_val_2727_);
lean_dec(v_indName_2719_);
v_a_2758_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2740_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2740_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec(v___x_2736_);
lean_del_object(v___x_2733_);
lean_dec(v___x_2728_);
lean_dec_ref(v_val_2727_);
lean_dec(v_indName_2719_);
v___x_2766_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1);
v___x_2767_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_2766_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
return v___x_2767_;
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v___x_2728_);
lean_dec_ref(v_val_2727_);
lean_dec(v_indName_2719_);
v_a_2771_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2729_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2729_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec(v_a_2726_);
lean_dec(v_indName_2719_);
v___x_2779_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2);
v___x_2780_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_2779_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
return v___x_2780_;
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_indName_2719_);
v_a_2781_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2725_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2725_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___boxed(lean_object* v_indName_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(lean_object* v_val_2796_, lean_object* v_indName_2797_, lean_object* v_tail_2798_, lean_object* v___x_2799_, lean_object* v___x_2800_, lean_object* v___x_2801_, lean_object* v_a_2802_, lean_object* v_range_2803_, lean_object* v_b_2804_, lean_object* v_i_2805_, lean_object* v_hs_2806_, lean_object* v_hl_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2796_, v_indName_2797_, v_tail_2798_, v___x_2799_, v___x_2800_, v___x_2801_, v_a_2802_, v_range_2803_, v_b_2804_, v_i_2805_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___boxed(lean_object** _args){
lean_object* v_val_2814_ = _args[0];
lean_object* v_indName_2815_ = _args[1];
lean_object* v_tail_2816_ = _args[2];
lean_object* v___x_2817_ = _args[3];
lean_object* v___x_2818_ = _args[4];
lean_object* v___x_2819_ = _args[5];
lean_object* v_a_2820_ = _args[6];
lean_object* v_range_2821_ = _args[7];
lean_object* v_b_2822_ = _args[8];
lean_object* v_i_2823_ = _args[9];
lean_object* v_hs_2824_ = _args[10];
lean_object* v_hl_2825_ = _args[11];
lean_object* v___y_2826_ = _args[12];
lean_object* v___y_2827_ = _args[13];
lean_object* v___y_2828_ = _args[14];
lean_object* v___y_2829_ = _args[15];
lean_object* v___y_2830_ = _args[16];
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(v_val_2814_, v_indName_2815_, v_tail_2816_, v___x_2817_, v___x_2818_, v___x_2819_, v_a_2820_, v_range_2821_, v_b_2822_, v_i_2823_, v_hs_2824_, v_hl_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec_ref(v_range_2821_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(lean_object* v_00_u03b1_2832_, lean_object* v_attrName_2833_, lean_object* v_declName_2834_, lean_object* v_asyncPrefix_x3f_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2833_, v_declName_2834_, v_asyncPrefix_x3f_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_attrName_2843_, lean_object* v_declName_2844_, lean_object* v_asyncPrefix_x3f_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(v_00_u03b1_2842_, v_attrName_2843_, v_declName_2844_, v_asyncPrefix_x3f_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(lean_object* v_00_u03b1_2852_, lean_object* v_attrName_2853_, lean_object* v_declName_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2853_, v_declName_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2861_, lean_object* v_attrName_2862_, lean_object* v_declName_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(v_00_u03b1_2861_, v_attrName_2862_, v_declName_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0(lean_object* v_indName_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; 
lean_inc(v_indName_2870_);
v___x_2876_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v___x_2877_; 
lean_dec_ref_known(v___x_2876_, 1);
lean_inc(v_indName_2870_);
v___x_2877_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v___x_2878_; 
lean_dec_ref_known(v___x_2877_, 1);
v___x_2878_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_2878_;
}
else
{
lean_dec(v_indName_2870_);
return v___x_2877_;
}
}
else
{
lean_dec(v_indName_2870_);
return v___x_2876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object* v_indName_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_mkCtorElim___lam__0(v_indName_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(lean_object* v_declName_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; 
lean_inc(v_declName_2886_);
v___x_2892_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_declName_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2928_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2928_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2928_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
if (lean_obj_tag(v_a_2893_) == 5)
{
lean_object* v_val_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_del_object(v___x_2895_);
v_val_2897_ = lean_ctor_get(v_a_2893_, 0);
lean_inc_ref(v_val_2897_);
lean_dec_ref_known(v_a_2893_, 1);
v___x_2898_ = l_Lean_mkRecName(v_declName_2886_);
v___x_2899_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v___x_2898_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_toConstantVal_2900_; lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2914_; 
v_toConstantVal_2900_ = lean_ctor_get(v_val_2897_, 0);
lean_inc_ref(v_toConstantVal_2900_);
lean_dec_ref(v_val_2897_);
v_a_2901_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2903_ = v___x_2899_;
v_isShared_2904_ = v_isSharedCheck_2914_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2899_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2914_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_levelParams_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v_levelParams_2905_ = lean_ctor_get(v_toConstantVal_2900_, 1);
lean_inc(v_levelParams_2905_);
lean_dec_ref(v_toConstantVal_2900_);
v___x_2906_ = l_List_lengthTR___redArg(v_levelParams_2905_);
lean_dec(v_levelParams_2905_);
v___x_2907_ = l_Lean_ConstantInfo_levelParams(v_a_2901_);
lean_dec(v_a_2901_);
v___x_2908_ = l_List_lengthTR___redArg(v___x_2907_);
lean_dec(v___x_2907_);
v___x_2909_ = lean_nat_dec_lt(v___x_2906_, v___x_2908_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
v___x_2910_ = lean_box(v___x_2909_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2910_);
v___x_2912_ = v___x_2903_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref(v_val_2897_);
v_a_2915_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2899_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2899_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
lean_dec(v_a_2893_);
lean_dec(v_declName_2886_);
v___x_2923_ = 0;
v___x_2924_ = lean_box(v___x_2923_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2924_);
v___x_2926_ = v___x_2895_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_declName_2886_);
v_a_2929_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2892_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2892_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0___boxed(lean_object* v_declName_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_declName_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(lean_object* v___y_2944_, uint8_t v_isExporting_2945_, lean_object* v___x_2946_, lean_object* v___y_2947_, lean_object* v___x_2948_, lean_object* v_a_x3f_2949_){
_start:
{
lean_object* v___x_2951_; lean_object* v_env_2952_; lean_object* v_nextMacroScope_2953_; lean_object* v_ngen_2954_; lean_object* v_auxDeclNGen_2955_; lean_object* v_traceState_2956_; lean_object* v_recordedDeps_2957_; lean_object* v_messages_2958_; lean_object* v_infoState_2959_; lean_object* v_snapshotTasks_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2985_; 
v___x_2951_ = lean_st_ref_take(v___y_2944_);
v_env_2952_ = lean_ctor_get(v___x_2951_, 0);
v_nextMacroScope_2953_ = lean_ctor_get(v___x_2951_, 1);
v_ngen_2954_ = lean_ctor_get(v___x_2951_, 2);
v_auxDeclNGen_2955_ = lean_ctor_get(v___x_2951_, 3);
v_traceState_2956_ = lean_ctor_get(v___x_2951_, 4);
v_recordedDeps_2957_ = lean_ctor_get(v___x_2951_, 6);
v_messages_2958_ = lean_ctor_get(v___x_2951_, 7);
v_infoState_2959_ = lean_ctor_get(v___x_2951_, 8);
v_snapshotTasks_2960_ = lean_ctor_get(v___x_2951_, 9);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v___x_2951_, 5);
lean_dec(v_unused_2986_);
v___x_2962_ = v___x_2951_;
v_isShared_2963_ = v_isSharedCheck_2985_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_snapshotTasks_2960_);
lean_inc(v_infoState_2959_);
lean_inc(v_messages_2958_);
lean_inc(v_recordedDeps_2957_);
lean_inc(v_traceState_2956_);
lean_inc(v_auxDeclNGen_2955_);
lean_inc(v_ngen_2954_);
lean_inc(v_nextMacroScope_2953_);
lean_inc(v_env_2952_);
lean_dec(v___x_2951_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2985_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = l_Lean_Environment_setExporting(v_env_2952_, v_isExporting_2945_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 5, v___x_2946_);
lean_ctor_set(v___x_2962_, 0, v___x_2964_);
v___x_2966_ = v___x_2962_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_nextMacroScope_2953_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_ngen_2954_);
lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_auxDeclNGen_2955_);
lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_traceState_2956_);
lean_ctor_set(v_reuseFailAlloc_2984_, 5, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2984_, 6, v_recordedDeps_2957_);
lean_ctor_set(v_reuseFailAlloc_2984_, 7, v_messages_2958_);
lean_ctor_set(v_reuseFailAlloc_2984_, 8, v_infoState_2959_);
lean_ctor_set(v_reuseFailAlloc_2984_, 9, v_snapshotTasks_2960_);
v___x_2966_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_mctx_2969_; lean_object* v_zetaDeltaFVarIds_2970_; lean_object* v_postponed_2971_; lean_object* v_diag_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2982_; 
v___x_2967_ = lean_st_ref_put(v___y_2944_, v___x_2966_);
v___x_2968_ = lean_st_ref_take(v___y_2947_);
v_mctx_2969_ = lean_ctor_get(v___x_2968_, 0);
v_zetaDeltaFVarIds_2970_ = lean_ctor_get(v___x_2968_, 2);
v_postponed_2971_ = lean_ctor_get(v___x_2968_, 3);
v_diag_2972_ = lean_ctor_get(v___x_2968_, 4);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v___x_2968_, 1);
lean_dec(v_unused_2983_);
v___x_2974_ = v___x_2968_;
v_isShared_2975_ = v_isSharedCheck_2982_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_diag_2972_);
lean_inc(v_postponed_2971_);
lean_inc(v_zetaDeltaFVarIds_2970_);
lean_inc(v_mctx_2969_);
lean_dec(v___x_2968_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2982_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = lean_box(0);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 1, v___x_2948_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_mctx_2969_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_zetaDeltaFVarIds_2970_);
lean_ctor_set(v_reuseFailAlloc_2981_, 3, v_postponed_2971_);
lean_ctor_set(v_reuseFailAlloc_2981_, 4, v_diag_2972_);
v___x_2978_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_st_ref_put(v___y_2947_, v___x_2978_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2976_);
return v___x_2980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2987_, lean_object* v_isExporting_2988_, lean_object* v___x_2989_, lean_object* v___y_2990_, lean_object* v___x_2991_, lean_object* v_a_x3f_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v_isExporting_boxed_2994_; lean_object* v_res_2995_; 
v_isExporting_boxed_2994_ = lean_unbox(v_isExporting_2988_);
v_res_2995_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2987_, v_isExporting_boxed_2994_, v___x_2989_, v___y_2990_, v___x_2991_, v_a_x3f_2992_);
lean_dec(v_a_x3f_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2987_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(lean_object* v_x_2996_, uint8_t v_isExporting_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___x_3003_; lean_object* v_env_3004_; lean_object* v___x_3005_; uint8_t v_isModule_3006_; 
v___x_3003_ = lean_st_ref_get(v___y_3001_);
v_env_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc_ref(v_env_3004_);
lean_dec(v___x_3003_);
v___x_3005_ = l_Lean_Environment_header(v_env_3004_);
v_isModule_3006_ = lean_ctor_get_uint8(v___x_3005_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3005_);
if (v_isModule_3006_ == 0)
{
lean_object* v___x_3007_; 
lean_dec_ref(v_env_3004_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
v___x_3007_ = lean_apply_5(v_x_2996_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, lean_box(0));
return v___x_3007_;
}
else
{
uint8_t v_isExporting_3008_; 
v_isExporting_3008_ = lean_ctor_get_uint8(v_env_3004_, sizeof(void*)*13);
lean_dec_ref(v_env_3004_);
if (v_isExporting_2997_ == 0)
{
if (v_isExporting_3008_ == 0)
{
lean_object* v___x_3075_; 
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
v___x_3075_ = lean_apply_5(v_x_2996_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, lean_box(0));
return v___x_3075_;
}
else
{
goto v___jp_3009_;
}
}
else
{
if (v_isExporting_3008_ == 0)
{
goto v___jp_3009_;
}
else
{
lean_object* v___x_3076_; 
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
v___x_3076_ = lean_apply_5(v_x_2996_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, lean_box(0));
return v___x_3076_;
}
}
v___jp_3009_:
{
lean_object* v___x_3010_; lean_object* v_env_3011_; lean_object* v_nextMacroScope_3012_; lean_object* v_ngen_3013_; lean_object* v_auxDeclNGen_3014_; lean_object* v_traceState_3015_; lean_object* v_recordedDeps_3016_; lean_object* v_messages_3017_; lean_object* v_infoState_3018_; lean_object* v_snapshotTasks_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3073_; 
v___x_3010_ = lean_st_ref_take(v___y_3001_);
v_env_3011_ = lean_ctor_get(v___x_3010_, 0);
v_nextMacroScope_3012_ = lean_ctor_get(v___x_3010_, 1);
v_ngen_3013_ = lean_ctor_get(v___x_3010_, 2);
v_auxDeclNGen_3014_ = lean_ctor_get(v___x_3010_, 3);
v_traceState_3015_ = lean_ctor_get(v___x_3010_, 4);
v_recordedDeps_3016_ = lean_ctor_get(v___x_3010_, 6);
v_messages_3017_ = lean_ctor_get(v___x_3010_, 7);
v_infoState_3018_ = lean_ctor_get(v___x_3010_, 8);
v_snapshotTasks_3019_ = lean_ctor_get(v___x_3010_, 9);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v___x_3010_, 5);
lean_dec(v_unused_3074_);
v___x_3021_ = v___x_3010_;
v_isShared_3022_ = v_isSharedCheck_3073_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_snapshotTasks_3019_);
lean_inc(v_infoState_3018_);
lean_inc(v_messages_3017_);
lean_inc(v_recordedDeps_3016_);
lean_inc(v_traceState_3015_);
lean_inc(v_auxDeclNGen_3014_);
lean_inc(v_ngen_3013_);
lean_inc(v_nextMacroScope_3012_);
lean_inc(v_env_3011_);
lean_dec(v___x_3010_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3073_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3023_ = l_Lean_Environment_setExporting(v_env_3011_, v_isExporting_2997_);
v___x_3024_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 5, v___x_3024_);
lean_ctor_set(v___x_3021_, 0, v___x_3023_);
v___x_3026_ = v___x_3021_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_nextMacroScope_3012_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_ngen_3013_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_auxDeclNGen_3014_);
lean_ctor_set(v_reuseFailAlloc_3072_, 4, v_traceState_3015_);
lean_ctor_set(v_reuseFailAlloc_3072_, 5, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3072_, 6, v_recordedDeps_3016_);
lean_ctor_set(v_reuseFailAlloc_3072_, 7, v_messages_3017_);
lean_ctor_set(v_reuseFailAlloc_3072_, 8, v_infoState_3018_);
lean_ctor_set(v_reuseFailAlloc_3072_, 9, v_snapshotTasks_3019_);
v___x_3026_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_mctx_3029_; lean_object* v_zetaDeltaFVarIds_3030_; lean_object* v_postponed_3031_; lean_object* v_diag_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3070_; 
v___x_3027_ = lean_st_ref_put(v___y_3001_, v___x_3026_);
v___x_3028_ = lean_st_ref_take(v___y_2999_);
v_mctx_3029_ = lean_ctor_get(v___x_3028_, 0);
v_zetaDeltaFVarIds_3030_ = lean_ctor_get(v___x_3028_, 2);
v_postponed_3031_ = lean_ctor_get(v___x_3028_, 3);
v_diag_3032_ = lean_ctor_get(v___x_3028_, 4);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v___x_3028_, 1);
lean_dec(v_unused_3071_);
v___x_3034_ = v___x_3028_;
v_isShared_3035_ = v_isSharedCheck_3070_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_diag_3032_);
lean_inc(v_postponed_3031_);
lean_inc(v_zetaDeltaFVarIds_3030_);
lean_inc(v_mctx_3029_);
lean_dec(v___x_3028_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3070_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3036_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 1, v___x_3036_);
v___x_3038_ = v___x_3034_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_mctx_3029_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_zetaDeltaFVarIds_3030_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_postponed_3031_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v_diag_3032_);
v___x_3038_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; lean_object* v_r_3040_; 
v___x_3039_ = lean_st_ref_put(v___y_2999_, v___x_3038_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
v_r_3040_ = lean_apply_5(v_x_2996_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, lean_box(0));
if (lean_obj_tag(v_r_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3057_; 
v_a_3041_ = lean_ctor_get(v_r_3040_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_r_3040_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3043_ = v_r_3040_;
v_isShared_3044_ = v_isSharedCheck_3057_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v_r_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3057_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
lean_inc(v_a_3041_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set_tag(v___x_3043_, 1);
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
v___x_3047_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_3001_, v_isExporting_3008_, v___x_3024_, v___y_2999_, v___x_3036_, v___x_3046_);
lean_dec_ref(v___x_3046_);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v___x_3047_, 0);
lean_dec(v_unused_3055_);
v___x_3049_ = v___x_3047_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v___x_3047_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v_a_3041_);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3041_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
v_a_3058_ = lean_ctor_get(v_r_3040_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v_r_3040_, 1);
v___x_3059_ = lean_box(0);
v___x_3060_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_3001_, v_isExporting_3008_, v___x_3024_, v___y_2999_, v___x_3036_, v___x_3059_);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; 
v_unused_3068_ = lean_ctor_get(v___x_3060_, 0);
lean_dec(v_unused_3068_);
v___x_3062_ = v___x_3060_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_dec(v___x_3060_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set_tag(v___x_3062_, 1);
lean_ctor_set(v___x_3062_, 0, v_a_3058_);
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3058_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___boxed(lean_object* v_x_3077_, lean_object* v_isExporting_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
uint8_t v_isExporting_boxed_3084_; lean_object* v_res_3085_; 
v_isExporting_boxed_3084_ = lean_unbox(v_isExporting_3078_);
v_res_3085_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_3077_, v_isExporting_boxed_3084_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim(lean_object* v_indName_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v___f_3092_; lean_object* v___x_3093_; lean_object* v_env_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; uint8_t v___x_3097_; 
lean_inc_n(v_indName_3086_, 2);
v___f_3092_ = lean_alloc_closure((void*)(l_Lean_mkCtorElim___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3092_, 0, v_indName_3086_);
v___x_3093_ = lean_st_ref_get(v_a_3090_);
v_env_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc_ref(v_env_3094_);
lean_dec(v___x_3093_);
v___x_3095_ = l_Lean_mkCtorIdxName(v_indName_3086_);
v___x_3096_ = 1;
v___x_3097_ = l_Lean_Environment_contains(v_env_3094_, v___x_3095_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref(v___f_3092_);
lean_dec(v_indName_3086_);
v___x_3098_ = lean_box(0);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; 
lean_inc(v_indName_3086_);
v___x_3100_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3162_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3162_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3162_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
if (lean_obj_tag(v_a_3101_) == 5)
{
lean_object* v_val_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v_val_3105_ = lean_ctor_get(v_a_3101_, 0);
lean_inc_ref(v_val_3105_);
lean_dec_ref_known(v_a_3101_, 1);
v___x_3106_ = lean_unsigned_to_nat(1u);
v___x_3107_ = l_Lean_InductiveVal_numCtors(v_val_3105_);
v___x_3108_ = lean_nat_dec_lt(v___x_3106_, v___x_3107_);
lean_dec(v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
lean_dec_ref(v_val_3105_);
lean_dec_ref(v___f_3092_);
lean_dec(v_indName_3086_);
v___x_3109_ = lean_box(0);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3109_);
v___x_3111_ = v___x_3103_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
else
{
lean_object* v_toConstantVal_3113_; lean_object* v_type_3114_; lean_object* v___x_3115_; 
lean_del_object(v___x_3103_);
v_toConstantVal_3113_ = lean_ctor_get(v_val_3105_, 0);
lean_inc_ref(v_toConstantVal_3113_);
lean_dec_ref(v_val_3105_);
v_type_3114_ = lean_ctor_get(v_toConstantVal_3113_, 2);
lean_inc_ref(v_type_3114_);
lean_dec_ref(v_toConstantVal_3113_);
v___x_3115_ = l_Lean_Meta_isPropFormerType(v_type_3114_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3149_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3149_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3149_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
uint8_t v___x_3120_; 
v___x_3120_ = lean_unbox(v_a_3116_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_del_object(v___x_3118_);
lean_inc(v_indName_3086_);
v___x_3121_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_indName_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3136_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3136_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3136_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
uint8_t v___x_3126_; 
v___x_3126_ = lean_unbox(v_a_3122_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
lean_dec(v_a_3122_);
lean_dec(v_a_3116_);
lean_dec_ref(v___f_3092_);
lean_dec(v_indName_3086_);
v___x_3127_ = lean_box(0);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3127_);
v___x_3129_ = v___x_3124_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
else
{
uint8_t v___x_3131_; 
lean_del_object(v___x_3124_);
v___x_3131_ = l_Lean_isPrivateName(v_indName_3086_);
lean_dec(v_indName_3086_);
if (v___x_3131_ == 0)
{
uint8_t v___x_3132_; lean_object* v___x_3133_; 
lean_dec(v_a_3116_);
v___x_3132_ = lean_unbox(v_a_3122_);
lean_dec(v_a_3122_);
v___x_3133_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3092_, v___x_3132_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
return v___x_3133_;
}
else
{
uint8_t v___x_3134_; lean_object* v___x_3135_; 
lean_dec(v_a_3122_);
v___x_3134_ = lean_unbox(v_a_3116_);
lean_dec(v_a_3116_);
v___x_3135_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3092_, v___x_3134_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
return v___x_3135_;
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_a_3116_);
lean_dec_ref(v___f_3092_);
lean_dec(v_indName_3086_);
v_a_3137_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3121_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3121_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
lean_dec(v_a_3116_);
lean_dec_ref(v___f_3092_);
lean_dec(v_indName_3086_);
v___x_3145_ = lean_box(0);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3145_);
v___x_3147_ = v___x_3118_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v___f_3092_);
lean_dec(v_indName_3086_);
v_a_3150_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3115_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3115_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3160_; 
lean_dec(v_a_3101_);
lean_dec_ref(v___f_3092_);
lean_dec(v_indName_3086_);
v___x_3158_ = lean_box(0);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3158_);
v___x_3160_ = v___x_3103_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v___f_3092_);
lean_dec(v_indName_3086_);
v_a_3163_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3100_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3100_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___boxed(lean_object* v_indName_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lean_mkCtorElim(v_indName_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3172_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(lean_object* v_00_u03b1_3178_, lean_object* v_x_3179_, uint8_t v_isExporting_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_3179_, v_isExporting_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___boxed(lean_object* v_00_u03b1_3187_, lean_object* v_x_3188_, lean_object* v_isExporting_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
uint8_t v_isExporting_boxed_3195_; lean_object* v_res_3196_; 
v_isExporting_boxed_3195_ = lean_unbox(v_isExporting_3189_);
v_res_3196_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(v_00_u03b1_3187_, v_x_3188_, v_isExporting_boxed_3195_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v_decl_3197_, lean_object* v_____r_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
lean_inc(v_decl_3197_);
v___x_3204_ = l_Lean_mkCtorIdx(v_decl_3197_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3205_; 
lean_dec_ref_known(v___x_3204_, 1);
v___x_3205_ = l_Lean_mkCtorElim(v_decl_3197_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3205_;
}
else
{
lean_dec(v_decl_3197_);
return v___x_3204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_decl_3206_, lean_object* v_____r_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3206_, v_____r_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3213_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_3216_ = l_Lean_stringToMessageData(v___x_3215_);
return v___x_3216_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_3219_ = l_Lean_stringToMessageData(v___x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_3223_, uint8_t v_kind_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___y_3236_; 
v___x_3230_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_3231_ = l_Lean_MessageData_ofName(v_name_3223_);
v___x_3232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
switch(v_kind_3224_)
{
case 0:
{
lean_object* v___x_3243_; 
v___x_3243_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_3236_ = v___x_3243_;
goto v___jp_3235_;
}
case 1:
{
lean_object* v___x_3244_; 
v___x_3244_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_3236_ = v___x_3244_;
goto v___jp_3235_;
}
default: 
{
lean_object* v___x_3245_; 
v___x_3245_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_3236_ = v___x_3245_;
goto v___jp_3235_;
}
}
v___jp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_inc_ref(v___y_3236_);
v___x_3237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___y_3236_);
v___x_3238_ = l_Lean_MessageData_ofFormat(v___x_3237_);
v___x_3239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3234_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_3241_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_3246_, lean_object* v_kind_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
uint8_t v_kind_boxed_3253_; lean_object* v_res_3254_; 
v_kind_boxed_3253_ = lean_unbox(v_kind_3247_);
v_res_3254_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3246_, v_kind_boxed_3253_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
return v_res_3254_;
}
}
static uint64_t _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3261_; uint64_t v___x_3262_; 
v___x_3261_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3262_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3261_);
return v___x_3262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_uint64_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3264_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3265_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set_uint64(v___x_3265_, sizeof(void*)*1, v___x_3263_);
return v___x_3265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
return v___x_3267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
return v___x_3269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
lean_ctor_set(v___x_3271_, 2, v___x_3270_);
lean_ctor_set(v___x_3271_, 3, v___x_3270_);
lean_ctor_set(v___x_3271_, 4, v___x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3272_, lean_object* v___x_3273_, lean_object* v___x_3274_, lean_object* v_decl_3275_, lean_object* v___stx_3276_, uint8_t v_kind_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v___x_3281_; uint8_t v___x_3282_; uint8_t v___x_3283_; uint8_t v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; size_t v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___y_3306_; 
v___x_3281_ = 0;
v___x_3282_ = l_Lean_instBEqAttributeKind_beq(v_kind_3277_, v___x_3281_);
v___x_3283_ = 1;
v___x_3284_ = 0;
v___x_3285_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3286_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3287_ = lean_unsigned_to_nat(32u);
v___x_3288_ = lean_mk_empty_array_with_capacity(v___x_3287_);
v___x_3289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3);
v___x_3290_ = ((size_t)5ULL);
lean_inc_n(v___x_3272_, 7);
v___x_3291_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3288_);
lean_ctor_set(v___x_3291_, 2, v___x_3272_);
lean_ctor_set(v___x_3291_, 3, v___x_3272_);
lean_ctor_set_usize(v___x_3291_, 4, v___x_3290_);
v___x_3292_ = lean_box(1);
lean_inc_ref(v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3286_);
lean_ctor_set(v___x_3293_, 1, v___x_3291_);
lean_ctor_set(v___x_3293_, 2, v___x_3292_);
v___x_3294_ = lean_mk_empty_array_with_capacity(v___x_3272_);
v___x_3295_ = lean_box(0);
lean_inc(v___x_3273_);
v___x_3296_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3296_, 0, v___x_3285_);
lean_ctor_set(v___x_3296_, 1, v___x_3273_);
lean_ctor_set(v___x_3296_, 2, v___x_3293_);
lean_ctor_set(v___x_3296_, 3, v___x_3294_);
lean_ctor_set(v___x_3296_, 4, v___x_3295_);
lean_ctor_set(v___x_3296_, 5, v___x_3272_);
lean_ctor_set(v___x_3296_, 6, v___x_3295_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*7, v___x_3284_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*7 + 1, v___x_3284_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*7 + 2, v___x_3284_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*7 + 3, v___x_3283_);
v___x_3297_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3272_);
lean_ctor_set(v___x_3297_, 1, v___x_3272_);
lean_ctor_set(v___x_3297_, 2, v___x_3272_);
lean_ctor_set(v___x_3297_, 3, v___x_3272_);
lean_ctor_set(v___x_3297_, 4, v___x_3286_);
lean_ctor_set(v___x_3297_, 5, v___x_3286_);
lean_ctor_set(v___x_3297_, 6, v___x_3286_);
lean_ctor_set(v___x_3297_, 7, v___x_3286_);
lean_ctor_set(v___x_3297_, 8, v___x_3286_);
lean_ctor_set(v___x_3297_, 9, v___x_3286_);
lean_ctor_set(v___x_3297_, 10, v___x_3286_);
v___x_3298_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
v___x_3299_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3286_);
lean_ctor_set(v___x_3300_, 1, v___x_3286_);
lean_ctor_set(v___x_3300_, 2, v___x_3272_);
v___x_3301_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3298_);
lean_ctor_set(v___x_3301_, 1, v___x_3286_);
lean_ctor_set(v___x_3301_, 2, v___x_3299_);
lean_ctor_set(v___x_3301_, 3, v___x_3286_);
lean_ctor_set(v___x_3301_, 4, v___x_3286_);
lean_ctor_set(v___x_3301_, 5, v___x_3286_);
lean_ctor_set(v___x_3301_, 6, v___x_3300_);
v___x_3302_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3297_);
lean_ctor_set(v___x_3303_, 1, v___x_3301_);
lean_ctor_set(v___x_3303_, 2, v___x_3273_);
lean_ctor_set(v___x_3303_, 3, v___x_3291_);
lean_ctor_set(v___x_3303_, 4, v___x_3302_);
v___x_3304_ = lean_st_mk_ref(v___x_3303_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3316_; 
lean_dec(v_decl_3275_);
v___x_3316_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v___x_3274_, v_kind_3277_, v___x_3296_, v___x_3304_, v___y_3278_, v___y_3279_);
lean_dec(v___x_3304_);
lean_dec_ref_known(v___x_3296_, 7);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec(v___x_3274_);
v___x_3317_ = lean_box(0);
v___x_3318_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3275_, v___x_3317_, v___x_3296_, v___x_3304_, v___y_3278_, v___y_3279_);
lean_dec_ref_known(v___x_3296_, 7);
v___y_3306_ = v___x_3318_;
goto v___jp_3305_;
}
v___jp_3305_:
{
if (lean_obj_tag(v___y_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3315_; 
v_a_3307_ = lean_ctor_get(v___y_3306_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___y_3306_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3309_ = v___y_3306_;
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___y_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_st_ref_get(v___x_3304_);
lean_dec(v___x_3304_);
lean_dec(v___x_3311_);
if (v_isShared_3310_ == 0)
{
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3307_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
else
{
lean_dec(v___x_3304_);
return v___y_3306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3319_, lean_object* v___x_3320_, lean_object* v___x_3321_, lean_object* v_decl_3322_, lean_object* v___stx_3323_, lean_object* v_kind_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
uint8_t v_kind_boxed_3328_; lean_object* v_res_3329_; 
v_kind_boxed_3328_ = lean_unbox(v_kind_3324_);
v_res_3329_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3319_, v___x_3320_, v___x_3321_, v_decl_3322_, v___stx_3323_, v_kind_boxed_3328_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___stx_3323_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3334_; lean_object* v_toCold_3335_; lean_object* v_env_3336_; lean_object* v_options_3337_; uint8_t v___x_3338_; lean_object* v_env_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3334_ = lean_st_ref_get(v___y_3332_);
v_toCold_3335_ = lean_ctor_get(v___y_3331_, 0);
v_env_3336_ = lean_ctor_get(v___x_3334_, 0);
lean_inc_ref(v_env_3336_);
lean_dec(v___x_3334_);
v_options_3337_ = lean_ctor_get(v_toCold_3335_, 2);
v___x_3338_ = 0;
v_env_3339_ = l_Lean_Environment_setRecordingDeps(v_env_3336_, v___x_3338_);
v___x_3340_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2);
v___x_3341_ = lean_unsigned_to_nat(32u);
v___x_3342_ = lean_mk_empty_array_with_capacity(v___x_3341_);
lean_dec_ref(v___x_3342_);
v___x_3343_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5);
lean_inc_ref(v_options_3337_);
v___x_3344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3344_, 0, v_env_3339_);
lean_ctor_set(v___x_3344_, 1, v___x_3340_);
lean_ctor_set(v___x_3344_, 2, v___x_3343_);
lean_ctor_set(v___x_3344_, 3, v_options_3337_);
v___x_3345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
lean_ctor_set(v___x_3345_, 1, v_msgData_3330_);
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_ref_3356_; lean_object* v___x_3357_; lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3366_; 
v_ref_3356_ = lean_ctor_get(v___y_3353_, 2);
v___x_3357_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msg_3352_, v___y_3353_, v___y_3354_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3364_; 
lean_inc(v_ref_3356_);
v___x_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3362_, 0, v_ref_3356_);
lean_ctor_set(v___x_3362_, 1, v_a_3358_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 1);
lean_ctor_set(v___x_3360_, 0, v___x_3362_);
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
return v_res_3371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3374_ = l_Lean_stringToMessageData(v___x_3373_);
return v___x_3374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3377_ = l_Lean_stringToMessageData(v___x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3378_, lean_object* v_decl_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3383_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3384_ = l_Lean_MessageData_ofName(v___x_3378_);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v___x_3387_, v___y_3380_, v___y_3381_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3389_, lean_object* v_decl_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3389_, v_decl_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v_decl_3390_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3476_ = l_Lean_registerBuiltinAttribute(v___x_3475_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3479_, lean_object* v_msg_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3480_, v___y_3481_, v___y_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3485_, lean_object* v_msg_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(v_00_u03b1_3485_, v_msg_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_3491_, lean_object* v_name_3492_, uint8_t v_kind_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3492_, v_kind_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_3500_, lean_object* v_name_3501_, lean_object* v_kind_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
uint8_t v_kind_boxed_3508_; lean_object* v_res_3509_; 
v_kind_boxed_3508_ = lean_unbox(v_kind_3502_);
v_res_3509_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(v_00_u03b1_3500_, v_name_3501_, v_kind_boxed_3508_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3513_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3514_ = l_Lean_addBuiltinDocString(v___x_3512_, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3516_;
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
