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
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19;
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
lean_object* v___f_595_; lean_object* v___x_4725__overap_596_; lean_object* v___x_597_; 
v___f_595_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_4725__overap_596_ = lean_panic_fn_borrowed(v___f_595_, v_msg_589_);
lean_inc(v___y_593_);
lean_inc_ref(v___y_592_);
lean_inc(v___y_591_);
lean_inc_ref(v___y_590_);
v___x_597_ = lean_apply_5(v___x_4725__overap_596_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, lean_box(0));
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
uint8_t v___x_7352__boxed_685_; lean_object* v_res_686_; 
v___x_7352__boxed_685_ = lean_unbox(v___x_678_);
v_res_686_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(v___x_675_, v___x_676_, v___x_677_, v___x_7352__boxed_685_, v_ctorIdx_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
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
uint8_t v___x_7529__boxed_812_; lean_object* v_res_813_; 
v___x_7529__boxed_812_ = lean_unbox(v___x_804_);
v_res_813_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(v_val_801_, v___x_802_, v___x_803_, v___x_7529__boxed_812_, v_xs_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(lean_object* v_msg_854_, lean_object* v_declHint_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_env_860_; uint8_t v___x_861_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_st_ref_get(v___y_856_);
v_env_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_env_860_);
lean_dec(v___x_859_);
v___x_861_ = l_Lean_Name_isAnonymous(v_declHint_855_);
if (v___x_861_ == 0)
{
uint8_t v_isExporting_862_; 
v_isExporting_862_ = lean_ctor_get_uint8(v_env_860_, sizeof(void*)*13);
if (v_isExporting_862_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_env_860_);
lean_dec(v_declHint_855_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_msg_854_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; uint8_t v___x_865_; 
lean_inc_ref(v_env_860_);
v___x_864_ = l_Lean_Environment_setExporting(v_env_860_, v___x_861_);
lean_inc(v_declHint_855_);
lean_inc_ref(v___x_864_);
v___x_865_ = l_Lean_Environment_contains(v___x_864_, v_declHint_855_, v_isExporting_862_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; 
lean_dec_ref(v___x_864_);
lean_dec_ref(v_env_860_);
lean_dec(v_declHint_855_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v_msg_854_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v_c_872_; lean_object* v___x_873_; 
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2);
v___x_868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5);
v___x_869_ = l_Lean_Options_empty;
lean_inc_ref(v___x_864_);
v___x_870_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_870_, 0, v___x_864_);
lean_ctor_set(v___x_870_, 1, v___x_867_);
lean_ctor_set(v___x_870_, 2, v___x_868_);
lean_ctor_set(v___x_870_, 3, v___x_869_);
lean_inc(v_declHint_855_);
v___x_871_ = l_Lean_MessageData_ofConstName(v_declHint_855_, v___x_861_);
v_c_872_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_872_, 0, v___x_870_);
lean_ctor_set(v_c_872_, 1, v___x_871_);
v___x_873_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_864_, v_declHint_855_);
lean_dec_ref(v___x_864_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v_env_860_);
lean_dec(v_declHint_855_);
v___x_874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v_c_872_);
v___x_876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__9);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Lean_MessageData_note(v___x_877_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v_msg_854_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_915_; 
v_val_881_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_915_ == 0)
{
v___x_883_ = v___x_873_;
v_isShared_884_ = v_isSharedCheck_915_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_val_881_);
lean_dec(v___x_873_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_915_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v_moduleNames_886_; lean_object* v_mod_887_; uint8_t v___x_888_; 
v___x_885_ = l_Lean_Environment_header(v_env_860_);
lean_dec_ref(v_env_860_);
v_moduleNames_886_ = lean_ctor_get(v___x_885_, 4);
lean_inc_ref(v_moduleNames_886_);
lean_dec_ref(v___x_885_);
v_mod_887_ = lean_array_get(v___x_858_, v_moduleNames_886_, v_val_881_);
lean_dec(v_val_881_);
lean_dec_ref(v_moduleNames_886_);
v___x_888_ = l_Lean_isPrivateName(v_declHint_855_);
lean_dec(v_declHint_855_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__11);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_c_872_);
v___x_891_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__13);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_MessageData_ofName(v_mod_887_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__15);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Lean_MessageData_note(v___x_896_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v_msg_854_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 0);
lean_ctor_set(v___x_883_, 0, v___x_898_);
v___x_900_ = v___x_883_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__7);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v_c_872_);
v___x_904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__17);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_MessageData_ofName(v_mod_887_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__19);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_MessageData_note(v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v_msg_854_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 0);
lean_ctor_set(v___x_883_, 0, v___x_911_);
v___x_913_ = v___x_883_;
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
lean_object* v___x_916_; 
lean_dec_ref(v_env_860_);
lean_dec(v_declHint_855_);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v_msg_854_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___boxed(lean_object* v_msg_917_, lean_object* v_declHint_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(v_msg_917_, v_declHint_918_, v___y_919_);
lean_dec(v___y_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14(lean_object* v_msg_922_, lean_object* v_declHint_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_939_; 
v___x_929_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(v_msg_922_, v_declHint_923_, v___y_927_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_939_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_934_ = l_Lean_unknownIdentifierMessageTag;
v___x_935_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_a_930_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14___boxed(lean_object* v_msg_940_, lean_object* v_declHint_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14(v_msg_940_, v_declHint_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(lean_object* v_ref_948_, lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_toCold_955_; lean_object* v_currRecDepth_956_; lean_object* v_ref_957_; uint16_t v_optionFlags_958_; uint8_t v_suppressElabErrors_959_; uint8_t v_checkDeprecated_960_; uint8_t v_isRecordingDeps_961_; lean_object* v_ref_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_toCold_955_ = lean_ctor_get(v___y_952_, 0);
v_currRecDepth_956_ = lean_ctor_get(v___y_952_, 1);
v_ref_957_ = lean_ctor_get(v___y_952_, 2);
v_optionFlags_958_ = lean_ctor_get_uint16(v___y_952_, sizeof(void*)*3);
v_suppressElabErrors_959_ = lean_ctor_get_uint8(v___y_952_, sizeof(void*)*3 + 2);
v_checkDeprecated_960_ = lean_ctor_get_uint8(v___y_952_, sizeof(void*)*3 + 3);
v_isRecordingDeps_961_ = lean_ctor_get_uint8(v___y_952_, sizeof(void*)*3 + 4);
v_ref_962_ = l_Lean_replaceRef(v_ref_948_, v_ref_957_);
lean_inc(v_currRecDepth_956_);
lean_inc_ref(v_toCold_955_);
v___x_963_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_963_, 0, v_toCold_955_);
lean_ctor_set(v___x_963_, 1, v_currRecDepth_956_);
lean_ctor_set(v___x_963_, 2, v_ref_962_);
lean_ctor_set_uint16(v___x_963_, sizeof(void*)*3, v_optionFlags_958_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*3 + 2, v_suppressElabErrors_959_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*3 + 3, v_checkDeprecated_960_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*3 + 4, v_isRecordingDeps_961_);
v___x_964_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_949_, v___y_950_, v___y_951_, v___x_963_, v___y_953_);
lean_dec_ref_known(v___x_963_, 3);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_ref_965_, lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(v_ref_965_, v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v_ref_965_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(lean_object* v_ref_973_, lean_object* v_msg_974_, lean_object* v_declHint_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; lean_object* v_a_982_; lean_object* v___x_983_; 
v___x_981_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14(v_msg_974_, v_declHint_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
v___x_983_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(v_ref_973_, v_a_982_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg___boxed(lean_object* v_ref_984_, lean_object* v_msg_985_, lean_object* v_declHint_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(v_ref_984_, v_msg_985_, v_declHint_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v_ref_984_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_999_, lean_object* v_constName_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1006_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_1007_ = 0;
lean_inc(v_constName_1000_);
v___x_1008_ = l_Lean_MessageData_ofConstName(v_constName_1000_, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(v_ref_999_, v___x_1011_, v_constName_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1013_, lean_object* v_constName_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1013_, v_constName_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v_ref_1013_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(lean_object* v_constName_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_ref_1027_; lean_object* v___x_1028_; 
v_ref_1027_ = lean_ctor_get(v___y_1024_, 2);
v___x_1028_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1027_, v_constName_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(lean_object* v_constName_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v_env_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_st_ref_get(v___y_1040_);
v_env_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc_ref(v_env_1043_);
lean_dec(v___x_1042_);
v___x_1044_ = 0;
lean_inc(v_constName_1036_);
v___x_1045_ = l_Lean_Environment_find_x3f(v_env_1043_, v_constName_1036_, v___x_1044_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1046_;
}
else
{
lean_object* v_val_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_constName_1036_);
v_val_1047_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1045_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_val_1047_);
lean_dec(v___x_1045_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 0);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_val_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(lean_object* v_constName_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_constName_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1061_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object* v___dummy_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg();
return v_res_1067_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg();
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0);
v___x_1077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
lean_ctor_set(v___x_1077_, 2, v___x_1075_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1078_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__4);
v___x_1079_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__3);
v___x_1080_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__0);
v___x_1081_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
v___x_1082_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1080_);
lean_ctor_set(v___x_1082_, 2, v___x_1079_);
lean_ctor_set(v___x_1082_, 3, v___x_1080_);
lean_ctor_set(v___x_1082_, 4, v___x_1080_);
lean_ctor_set(v___x_1082_, 5, v___x_1080_);
lean_ctor_set(v___x_1082_, 6, v___x_1080_);
lean_ctor_set(v___x_1082_, 7, v___x_1078_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(lean_object* v_declName_1083_, uint8_t v_s_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; lean_object* v_env_1089_; lean_object* v_nextMacroScope_1090_; lean_object* v_ngen_1091_; lean_object* v_auxDeclNGen_1092_; lean_object* v_traceState_1093_; lean_object* v_recordedDeps_1094_; lean_object* v_messages_1095_; lean_object* v_infoState_1096_; lean_object* v_snapshotTasks_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1126_; 
v___x_1088_ = lean_st_ref_take(v___y_1086_);
v_env_1089_ = lean_ctor_get(v___x_1088_, 0);
v_nextMacroScope_1090_ = lean_ctor_get(v___x_1088_, 1);
v_ngen_1091_ = lean_ctor_get(v___x_1088_, 2);
v_auxDeclNGen_1092_ = lean_ctor_get(v___x_1088_, 3);
v_traceState_1093_ = lean_ctor_get(v___x_1088_, 4);
v_recordedDeps_1094_ = lean_ctor_get(v___x_1088_, 6);
v_messages_1095_ = lean_ctor_get(v___x_1088_, 7);
v_infoState_1096_ = lean_ctor_get(v___x_1088_, 8);
v_snapshotTasks_1097_ = lean_ctor_get(v___x_1088_, 9);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1088_, 5);
lean_dec(v_unused_1127_);
v___x_1099_ = v___x_1088_;
v_isShared_1100_ = v_isSharedCheck_1126_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snapshotTasks_1097_);
lean_inc(v_infoState_1096_);
lean_inc(v_messages_1095_);
lean_inc(v_recordedDeps_1094_);
lean_inc(v_traceState_1093_);
lean_inc(v_auxDeclNGen_1092_);
lean_inc(v_ngen_1091_);
lean_inc(v_nextMacroScope_1090_);
lean_inc(v_env_1089_);
lean_dec(v___x_1088_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1126_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1101_ = 0;
v___x_1102_ = lean_box(0);
v___x_1103_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1089_, v_declName_1083_, v_s_1084_, v___x_1101_, v___x_1102_);
v___x_1104_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 5, v___x_1104_);
lean_ctor_set(v___x_1099_, 0, v___x_1103_);
v___x_1106_ = v___x_1099_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_nextMacroScope_1090_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_ngen_1091_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v_auxDeclNGen_1092_);
lean_ctor_set(v_reuseFailAlloc_1125_, 4, v_traceState_1093_);
lean_ctor_set(v_reuseFailAlloc_1125_, 5, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1125_, 6, v_recordedDeps_1094_);
lean_ctor_set(v_reuseFailAlloc_1125_, 7, v_messages_1095_);
lean_ctor_set(v_reuseFailAlloc_1125_, 8, v_infoState_1096_);
lean_ctor_set(v_reuseFailAlloc_1125_, 9, v_snapshotTasks_1097_);
v___x_1106_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_mctx_1109_; lean_object* v_zetaDeltaFVarIds_1110_; lean_object* v_postponed_1111_; lean_object* v_diag_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1123_; 
v___x_1107_ = lean_st_ref_put(v___y_1086_, v___x_1106_);
v___x_1108_ = lean_st_ref_take(v___y_1085_);
v_mctx_1109_ = lean_ctor_get(v___x_1108_, 0);
v_zetaDeltaFVarIds_1110_ = lean_ctor_get(v___x_1108_, 2);
v_postponed_1111_ = lean_ctor_get(v___x_1108_, 3);
v_diag_1112_ = lean_ctor_get(v___x_1108_, 4);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v___x_1108_, 1);
lean_dec(v_unused_1124_);
v___x_1114_ = v___x_1108_;
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_diag_1112_);
lean_inc(v_postponed_1111_);
lean_inc(v_zetaDeltaFVarIds_1110_);
lean_inc(v_mctx_1109_);
lean_dec(v___x_1108_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1117_);
v___x_1119_ = v___x_1114_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_mctx_1109_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_zetaDeltaFVarIds_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_postponed_1111_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_diag_1112_);
v___x_1119_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_st_ref_put(v___y_1085_, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1116_);
return v___x_1121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___boxed(lean_object* v_declName_1128_, lean_object* v_s_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v_s_boxed_1133_; lean_object* v_res_1134_; 
v_s_boxed_1133_ = lean_unbox(v_s_1129_);
v_res_1134_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(v_declName_1128_, v_s_boxed_1133_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec(v___y_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(lean_object* v_declName_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
uint8_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = 0;
v___x_1142_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(v_declName_1135_, v___x_1141_, v___y_1137_, v___y_1139_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(lean_object* v_declName_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v_declName_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(lean_object* v_constName_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v_env_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = lean_st_ref_get(v___y_1154_);
v_env_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc_ref(v_env_1157_);
lean_dec(v___x_1156_);
v___x_1158_ = 0;
lean_inc(v_constName_1150_);
v___x_1159_ = l_Lean_Environment_findConstVal_x3f(v_env_1157_, v_constName_1150_, v___x_1158_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1160_;
}
else
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec(v_constName_1150_);
v_val_1161_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1159_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v___x_1159_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set_tag(v___x_1163_, 0);
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_val_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(lean_object* v_constName_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v_constName_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1179_ = lean_unsigned_to_nat(60u);
v___x_1180_ = lean_unsigned_to_nat(81u);
v___x_1181_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0));
v___x_1182_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1183_ = l_mkPanicMessageWithDecl(v___x_1182_, v___x_1181_, v___x_1180_, v___x_1179_, v___x_1178_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(lean_object* v_indName_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1184_);
v___x_1191_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1325_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1325_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1325_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
if (lean_obj_tag(v_a_1192_) == 5)
{
lean_object* v_val_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_val_1196_ = lean_ctor_get(v_a_1192_, 0);
lean_inc_ref(v_val_1196_);
lean_dec_ref_known(v_a_1192_, 1);
v___x_1197_ = l_Lean_InductiveVal_numCtors(v_val_1196_);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_nat_dec_eq(v___x_1197_, v___x_1198_);
lean_dec(v___x_1197_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_del_object(v___x_1194_);
v___x_1200_ = lean_box(v___x_1199_);
v___f_1201_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1201_, 0, v_val_1196_);
lean_closure_set(v___f_1201_, 1, v___x_1198_);
lean_closure_set(v___f_1201_, 2, v___x_1190_);
lean_closure_set(v___f_1201_, 3, v___x_1200_);
lean_inc(v_indName_1184_);
v___x_1202_ = l_Lean_mkCasesOnName(v_indName_1184_);
v___x_1203_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1202_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v_levelParams_1205_; lean_object* v_type_1206_; lean_object* v___x_1207_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1203_, 1);
v_levelParams_1205_ = lean_ctor_get(v_a_1204_, 1);
lean_inc(v_levelParams_1205_);
v_type_1206_ = lean_ctor_get(v_a_1204_, 2);
lean_inc_ref(v_type_1206_);
lean_dec(v_a_1204_);
v___x_1207_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1206_, v___f_1201_, v___x_1199_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_n(v_a_1208_, 2);
lean_dec_ref_known(v___x_1207_, 1);
v___x_1209_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1184_);
lean_inc(v_a_1188_);
lean_inc_ref(v_a_1187_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
v___x_1210_ = lean_infer_type(v_a_1208_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1294_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = lean_box(1);
lean_inc(v___x_1209_);
v___x_1213_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1209_, v_levelParams_1205_, v_a_1211_, v_a_1208_, v___x_1212_, v_a_1188_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1294_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1294_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 1);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
uint8_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = 1;
v___x_1221_ = l_Lean_addAndCompile(v___x_1219_, v___x_1220_, v___x_1199_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v_nextMacroScope_1224_; lean_object* v_ngen_1225_; lean_object* v_auxDeclNGen_1226_; lean_object* v_traceState_1227_; lean_object* v_recordedDeps_1228_; lean_object* v_messages_1229_; lean_object* v_infoState_1230_; lean_object* v_snapshotTasks_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref_known(v___x_1221_, 1);
v___x_1222_ = lean_st_ref_take(v_a_1188_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
v_nextMacroScope_1224_ = lean_ctor_get(v___x_1222_, 1);
v_ngen_1225_ = lean_ctor_get(v___x_1222_, 2);
v_auxDeclNGen_1226_ = lean_ctor_get(v___x_1222_, 3);
v_traceState_1227_ = lean_ctor_get(v___x_1222_, 4);
v_recordedDeps_1228_ = lean_ctor_get(v___x_1222_, 6);
v_messages_1229_ = lean_ctor_get(v___x_1222_, 7);
v_infoState_1230_ = lean_ctor_get(v___x_1222_, 8);
v_snapshotTasks_1231_ = lean_ctor_get(v___x_1222_, 9);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v___x_1222_, 5);
lean_dec(v_unused_1292_);
v___x_1233_ = v___x_1222_;
v_isShared_1234_ = v_isSharedCheck_1291_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snapshotTasks_1231_);
lean_inc(v_infoState_1230_);
lean_inc(v_messages_1229_);
lean_inc(v_recordedDeps_1228_);
lean_inc(v_traceState_1227_);
lean_inc(v_auxDeclNGen_1226_);
lean_inc(v_ngen_1225_);
lean_inc(v_nextMacroScope_1224_);
lean_inc(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1291_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_inc(v___x_1209_);
v___x_1235_ = l_Lean_Meta_addToCompletionBlackList(v_env_1223_, v___x_1209_);
v___x_1236_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 5, v___x_1236_);
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1238_ = v___x_1233_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_nextMacroScope_1224_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_ngen_1225_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_auxDeclNGen_1226_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_traceState_1227_);
lean_ctor_set(v_reuseFailAlloc_1290_, 5, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1290_, 6, v_recordedDeps_1228_);
lean_ctor_set(v_reuseFailAlloc_1290_, 7, v_messages_1229_);
lean_ctor_set(v_reuseFailAlloc_1290_, 8, v_infoState_1230_);
lean_ctor_set(v_reuseFailAlloc_1290_, 9, v_snapshotTasks_1231_);
v___x_1238_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_mctx_1241_; lean_object* v_zetaDeltaFVarIds_1242_; lean_object* v_postponed_1243_; lean_object* v_diag_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1288_; 
v___x_1239_ = lean_st_ref_put(v_a_1188_, v___x_1238_);
v___x_1240_ = lean_st_ref_take(v_a_1186_);
v_mctx_1241_ = lean_ctor_get(v___x_1240_, 0);
v_zetaDeltaFVarIds_1242_ = lean_ctor_get(v___x_1240_, 2);
v_postponed_1243_ = lean_ctor_get(v___x_1240_, 3);
v_diag_1244_ = lean_ctor_get(v___x_1240_, 4);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v___x_1240_, 1);
lean_dec(v_unused_1289_);
v___x_1246_ = v___x_1240_;
v_isShared_1247_ = v_isSharedCheck_1288_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_diag_1244_);
lean_inc(v_postponed_1243_);
lean_inc(v_zetaDeltaFVarIds_1242_);
lean_inc(v_mctx_1241_);
lean_dec(v___x_1240_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1288_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_mctx_1241_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_zetaDeltaFVarIds_1242_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_postponed_1243_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_diag_1244_);
v___x_1250_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_env_1253_; lean_object* v_nextMacroScope_1254_; lean_object* v_ngen_1255_; lean_object* v_auxDeclNGen_1256_; lean_object* v_traceState_1257_; lean_object* v_recordedDeps_1258_; lean_object* v_messages_1259_; lean_object* v_infoState_1260_; lean_object* v_snapshotTasks_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1285_; 
v___x_1251_ = lean_st_ref_put(v_a_1186_, v___x_1250_);
v___x_1252_ = lean_st_ref_take(v_a_1188_);
v_env_1253_ = lean_ctor_get(v___x_1252_, 0);
v_nextMacroScope_1254_ = lean_ctor_get(v___x_1252_, 1);
v_ngen_1255_ = lean_ctor_get(v___x_1252_, 2);
v_auxDeclNGen_1256_ = lean_ctor_get(v___x_1252_, 3);
v_traceState_1257_ = lean_ctor_get(v___x_1252_, 4);
v_recordedDeps_1258_ = lean_ctor_get(v___x_1252_, 6);
v_messages_1259_ = lean_ctor_get(v___x_1252_, 7);
v_infoState_1260_ = lean_ctor_get(v___x_1252_, 8);
v_snapshotTasks_1261_ = lean_ctor_get(v___x_1252_, 9);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1252_, 5);
lean_dec(v_unused_1286_);
v___x_1263_ = v___x_1252_;
v_isShared_1264_ = v_isSharedCheck_1285_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_snapshotTasks_1261_);
lean_inc(v_infoState_1260_);
lean_inc(v_messages_1259_);
lean_inc(v_recordedDeps_1258_);
lean_inc(v_traceState_1257_);
lean_inc(v_auxDeclNGen_1256_);
lean_inc(v_ngen_1255_);
lean_inc(v_nextMacroScope_1254_);
lean_inc(v_env_1253_);
lean_dec(v___x_1252_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1285_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_inc(v___x_1209_);
v___x_1265_ = l_Lean_addProtected(v_env_1253_, v___x_1209_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 5, v___x_1236_);
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_nextMacroScope_1254_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_ngen_1255_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_auxDeclNGen_1256_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_traceState_1257_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1284_, 6, v_recordedDeps_1258_);
lean_ctor_set(v_reuseFailAlloc_1284_, 7, v_messages_1259_);
lean_ctor_set(v_reuseFailAlloc_1284_, 8, v_infoState_1260_);
lean_ctor_set(v_reuseFailAlloc_1284_, 9, v_snapshotTasks_1261_);
v___x_1267_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_mctx_1270_; lean_object* v_zetaDeltaFVarIds_1271_; lean_object* v_postponed_1272_; lean_object* v_diag_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1282_; 
v___x_1268_ = lean_st_ref_put(v_a_1188_, v___x_1267_);
v___x_1269_ = lean_st_ref_take(v_a_1186_);
v_mctx_1270_ = lean_ctor_get(v___x_1269_, 0);
v_zetaDeltaFVarIds_1271_ = lean_ctor_get(v___x_1269_, 2);
v_postponed_1272_ = lean_ctor_get(v___x_1269_, 3);
v_diag_1273_ = lean_ctor_get(v___x_1269_, 4);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v___x_1269_, 1);
lean_dec(v_unused_1283_);
v___x_1275_ = v___x_1269_;
v_isShared_1276_ = v_isSharedCheck_1282_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_diag_1273_);
lean_inc(v_postponed_1272_);
lean_inc(v_zetaDeltaFVarIds_1271_);
lean_inc(v_mctx_1270_);
lean_dec(v___x_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1282_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1248_);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_mctx_1270_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_zetaDeltaFVarIds_1271_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_postponed_1272_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v_diag_1273_);
v___x_1278_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_st_ref_put(v_a_1186_, v___x_1278_);
v___x_1280_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_1209_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1280_;
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
lean_dec(v___x_1209_);
return v___x_1221_;
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v___x_1209_);
lean_dec(v_a_1208_);
lean_dec(v_levelParams_1205_);
v_a_1295_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1210_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1210_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_levelParams_1205_);
lean_dec(v_indName_1184_);
v_a_1303_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1207_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1207_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v___f_1201_);
lean_dec(v_indName_1184_);
v_a_1311_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1203_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1203_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
lean_dec_ref(v_val_1196_);
lean_dec(v_indName_1184_);
v___x_1319_ = lean_box(0);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1319_);
v___x_1321_ = v___x_1194_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_del_object(v___x_1194_);
lean_dec(v_a_1192_);
lean_dec(v_indName_1184_);
v___x_1323_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2);
v___x_1324_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_1323_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1324_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_indName_1184_);
v_a_1326_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1191_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1191_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___boxed(lean_object* v_indName_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(lean_object* v_00_u03b1_1341_, lean_object* v_name_1342_, uint8_t v_bi_1343_, lean_object* v_type_1344_, lean_object* v_k_1345_, uint8_t v_kind_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_1342_, v_bi_1343_, v_type_1344_, v_k_1345_, v_kind_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_name_1354_, lean_object* v_bi_1355_, lean_object* v_type_1356_, lean_object* v_k_1357_, lean_object* v_kind_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v_bi_boxed_1364_; uint8_t v_kind_boxed_1365_; lean_object* v_res_1366_; 
v_bi_boxed_1364_ = lean_unbox(v_bi_1355_);
v_kind_boxed_1365_ = lean_unbox(v_kind_1358_);
v_res_1366_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(v_00_u03b1_1353_, v_name_1354_, v_bi_boxed_1364_, v_type_1356_, v_k_1357_, v_kind_boxed_1365_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(lean_object* v_00_u03b1_1367_, lean_object* v_name_1368_, lean_object* v_type_1369_, lean_object* v_k_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v_name_1368_, v_type_1369_, v_k_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_name_1378_, lean_object* v_type_1379_, lean_object* v_k_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(v_00_u03b1_1377_, v_name_1378_, v_type_1379_, v_k_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(lean_object* v_00_u03b2_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___redArg(){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___redArg___boxed(lean_object* v___dummy_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___redArg();
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object* v_00_u03b2_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(lean_object* v_00_u03b1_1395_, lean_object* v_constName_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_constName_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(v_00_u03b1_1403_, v_constName_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10(lean_object* v_declName_1411_, uint8_t v_s_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg(v_declName_1411_, v_s_1412_, v___y_1414_, v___y_1416_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___boxed(lean_object* v_declName_1419_, lean_object* v_s_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
uint8_t v_s_boxed_1426_; lean_object* v_res_1427_; 
v_s_boxed_1426_ = lean_unbox(v_s_1420_);
v_res_1427_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10(v_declName_1419_, v_s_boxed_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_1428_, lean_object* v_ref_1429_, lean_object* v_constName_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1429_, v_constName_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_ref_1438_, lean_object* v_constName_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(v_00_u03b1_1437_, v_ref_1438_, v_constName_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v_ref_1438_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12(lean_object* v_00_u03b1_1446_, lean_object* v_ref_1447_, lean_object* v_msg_1448_, lean_object* v_declHint_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___redArg(v_ref_1447_, v_msg_1448_, v_declHint_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_ref_1457_, lean_object* v_msg_1458_, lean_object* v_declHint_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12(v_00_u03b1_1456_, v_ref_1457_, v_msg_1458_, v_declHint_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_ref_1457_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15(lean_object* v_msg_1466_, lean_object* v_declHint_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg(v_msg_1466_, v_declHint_1467_, v___y_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_1474_, lean_object* v_declHint_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15(v_msg_1474_, v_declHint_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1482_, lean_object* v_ref_1483_, lean_object* v_msg_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___redArg(v_ref_1483_, v_msg_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1491_, lean_object* v_ref_1492_, lean_object* v_msg_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__15(v_00_u03b1_1491_, v_ref_1492_, v_msg_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v_ref_1492_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(lean_object* v___x_1500_, lean_object* v_k_1501_, lean_object* v_zs_1502_, uint8_t v___x_1503_, uint8_t v___x_1504_, uint8_t v___x_1505_, lean_object* v_h_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
lean_inc_ref(v_h_1506_);
v___x_1512_ = l_Lean_Meta_mkEqNDRec(v___x_1500_, v_k_1501_, v_h_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_a_1513_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = l_Lean_mkAppN(v_a_1515_, v_zs_1502_);
v___x_1517_ = lean_array_push(v_zs_1502_, v_h_1506_);
v___x_1518_ = l_Lean_Meta_mkLambdaFVars(v___x_1517_, v___x_1516_, v___x_1503_, v___x_1504_, v___x_1503_, v___x_1504_, v___x_1505_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec_ref(v___x_1517_);
return v___x_1518_;
}
else
{
lean_dec_ref(v_h_1506_);
lean_dec_ref(v_zs_1502_);
return v___x_1514_;
}
}
else
{
lean_dec_ref(v_h_1506_);
lean_dec_ref(v_zs_1502_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___x_1519_, lean_object* v_k_1520_, lean_object* v_zs_1521_, lean_object* v___x_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, lean_object* v_h_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v___x_6825__boxed_1531_; uint8_t v___x_6826__boxed_1532_; uint8_t v___x_6827__boxed_1533_; lean_object* v_res_1534_; 
v___x_6825__boxed_1531_ = lean_unbox(v___x_1522_);
v___x_6826__boxed_1532_ = lean_unbox(v___x_1523_);
v___x_6827__boxed_1533_ = lean_unbox(v___x_1524_);
v_res_1534_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(v___x_1519_, v_k_1520_, v_zs_1521_, v___x_6825__boxed_1531_, v___x_6826__boxed_1532_, v___x_6827__boxed_1533_, v_h_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(lean_object* v___x_1538_, lean_object* v_k_1539_, uint8_t v___x_1540_, uint8_t v___x_1541_, uint8_t v___x_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v___x_1545_, lean_object* v___x_1546_, lean_object* v_ctorIdx_1547_, lean_object* v___x_1548_, lean_object* v_zs_1549_, lean_object* v___ctorRet_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1556_ = lean_box(v___x_1540_);
v___x_1557_ = lean_box(v___x_1541_);
v___x_1558_ = lean_box(v___x_1542_);
v___f_1559_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1559_, 0, v___x_1538_);
lean_closure_set(v___f_1559_, 1, v_k_1539_);
lean_closure_set(v___f_1559_, 2, v_zs_1549_);
lean_closure_set(v___f_1559_, 3, v___x_1556_);
lean_closure_set(v___f_1559_, 4, v___x_1557_);
lean_closure_set(v___f_1559_, 5, v___x_1558_);
v___x_1560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1));
v___x_1561_ = l_Lean_Level_ofNat(v___x_1543_);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1544_);
v___x_1563_ = l_Lean_mkConst(v___x_1560_, v___x_1562_);
v___x_1564_ = l_Lean_mkRawNatLit(v___x_1545_);
v___x_1565_ = l_Lean_mkApp3(v___x_1563_, v___x_1546_, v_ctorIdx_1547_, v___x_1564_);
v___x_1566_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1548_, v___x_1565_, v___f_1559_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1567_ = _args[0];
lean_object* v_k_1568_ = _args[1];
lean_object* v___x_1569_ = _args[2];
lean_object* v___x_1570_ = _args[3];
lean_object* v___x_1571_ = _args[4];
lean_object* v___x_1572_ = _args[5];
lean_object* v___x_1573_ = _args[6];
lean_object* v___x_1574_ = _args[7];
lean_object* v___x_1575_ = _args[8];
lean_object* v_ctorIdx_1576_ = _args[9];
lean_object* v___x_1577_ = _args[10];
lean_object* v_zs_1578_ = _args[11];
lean_object* v___ctorRet_1579_ = _args[12];
lean_object* v___y_1580_ = _args[13];
lean_object* v___y_1581_ = _args[14];
lean_object* v___y_1582_ = _args[15];
lean_object* v___y_1583_ = _args[16];
lean_object* v___y_1584_ = _args[17];
_start:
{
uint8_t v___x_6874__boxed_1585_; uint8_t v___x_6875__boxed_1586_; uint8_t v___x_6876__boxed_1587_; lean_object* v_res_1588_; 
v___x_6874__boxed_1585_ = lean_unbox(v___x_1569_);
v___x_6875__boxed_1586_ = lean_unbox(v___x_1570_);
v___x_6876__boxed_1587_ = lean_unbox(v___x_1571_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(v___x_1567_, v_k_1568_, v___x_6874__boxed_1585_, v___x_6875__boxed_1586_, v___x_6876__boxed_1587_, v___x_1572_, v___x_1573_, v___x_1574_, v___x_1575_, v_ctorIdx_1576_, v___x_1577_, v_zs_1578_, v___ctorRet_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v___ctorRet_1579_);
lean_dec(v___x_1572_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(lean_object* v___x_1592_, lean_object* v_k_1593_, lean_object* v_ctorIdx_1594_, lean_object* v_tail_1595_, lean_object* v___x_1596_, size_t v_sz_1597_, size_t v_i_1598_, lean_object* v_bs_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_usize_dec_lt(v_i_1598_, v_sz_1597_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec(v_tail_1595_);
lean_dec_ref(v_ctorIdx_1594_);
lean_dec_ref(v_k_1593_);
lean_dec_ref(v___x_1592_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_bs_1599_);
return v___x_1606_;
}
else
{
uint8_t v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_v_1613_; lean_object* v___x_1614_; lean_object* v_bs_x27_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1607_ = 0;
v___x_1608_ = 1;
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_1612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v_v_1613_ = lean_array_uget(v_bs_1599_, v_i_1598_);
v___x_1614_ = lean_unsigned_to_nat(0u);
v_bs_x27_1615_ = lean_array_uset(v_bs_1599_, v_i_1598_, v___x_1614_);
v___x_1616_ = lean_usize_to_nat(v_i_1598_);
v___x_1617_ = lean_box(v___x_1607_);
v___x_1618_ = lean_box(v___x_1605_);
v___x_1619_ = lean_box(v___x_1608_);
lean_inc_ref(v_ctorIdx_1594_);
lean_inc_ref(v_k_1593_);
lean_inc_ref(v___x_1592_);
v___f_1620_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed), 18, 11);
lean_closure_set(v___f_1620_, 0, v___x_1592_);
lean_closure_set(v___f_1620_, 1, v_k_1593_);
lean_closure_set(v___f_1620_, 2, v___x_1617_);
lean_closure_set(v___f_1620_, 3, v___x_1618_);
lean_closure_set(v___f_1620_, 4, v___x_1619_);
lean_closure_set(v___f_1620_, 5, v___x_1609_);
lean_closure_set(v___f_1620_, 6, v___x_1610_);
lean_closure_set(v___f_1620_, 7, v___x_1616_);
lean_closure_set(v___f_1620_, 8, v___x_1611_);
lean_closure_set(v___f_1620_, 9, v_ctorIdx_1594_);
lean_closure_set(v___f_1620_, 10, v___x_1612_);
lean_inc(v_tail_1595_);
v___x_1621_ = l_Lean_mkConst(v_v_1613_, v_tail_1595_);
v___x_1622_ = l_Lean_mkAppN(v___x_1621_, v___x_1596_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
v___x_1623_ = lean_infer_type(v___x_1622_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_a_1624_, v___f_1620_, v___x_1607_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = ((size_t)1ULL);
v___x_1628_ = lean_usize_add(v_i_1598_, v___x_1627_);
v___x_1629_ = lean_array_uset(v_bs_x27_1615_, v_i_1598_, v_a_1626_);
v_i_1598_ = v___x_1628_;
v_bs_1599_ = v___x_1629_;
goto _start;
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_bs_x27_1615_);
lean_dec(v_tail_1595_);
lean_dec_ref(v_ctorIdx_1594_);
lean_dec_ref(v_k_1593_);
lean_dec_ref(v___x_1592_);
v_a_1631_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1625_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1625_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v___f_1620_);
lean_dec_ref(v_bs_x27_1615_);
lean_dec(v_tail_1595_);
lean_dec_ref(v_ctorIdx_1594_);
lean_dec_ref(v_k_1593_);
lean_dec_ref(v___x_1592_);
v_a_1639_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1623_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1623_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___boxed(lean_object* v___x_1647_, lean_object* v_k_1648_, lean_object* v_ctorIdx_1649_, lean_object* v_tail_1650_, lean_object* v___x_1651_, lean_object* v_sz_1652_, lean_object* v_i_1653_, lean_object* v_bs_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
size_t v_sz_boxed_1660_; size_t v_i_boxed_1661_; lean_object* v_res_1662_; 
v_sz_boxed_1660_ = lean_unbox_usize(v_sz_1652_);
lean_dec(v_sz_1652_);
v_i_boxed_1661_ = lean_unbox_usize(v_i_1653_);
lean_dec(v_i_1653_);
v_res_1662_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1647_, v_k_1648_, v_ctorIdx_1649_, v_tail_1650_, v___x_1651_, v_sz_boxed_1660_, v_i_boxed_1661_, v_bs_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v___x_1651_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v_a_1665_, lean_object* v_name_1666_, lean_object* v___x_1667_, lean_object* v___x_1668_, lean_object* v_ctors_1669_, lean_object* v___x_1670_, lean_object* v_ctorIdx_1671_, lean_object* v_tail_1672_, lean_object* v_h_1673_, lean_object* v_k_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_inc_ref(v___x_1663_);
v___x_1680_ = l_Lean_mkAppN(v___x_1663_, v___x_1664_);
v___x_1681_ = l_Lean_mkArrow(v_a_1665_, v___x_1680_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; uint8_t v___x_1683_; uint8_t v___x_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1683_ = 0;
v___x_1684_ = 1;
v___x_1685_ = 1;
v___x_1686_ = l_Lean_Meta_mkLambdaFVars(v___x_1664_, v_a_1682_, v___x_1683_, v___x_1684_, v___x_1683_, v___x_1684_, v___x_1685_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; size_t v_sz_1693_; size_t v___x_1694_; lean_object* v___x_1695_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = l_Lean_mkConst(v_name_1666_, v___x_1667_);
v___x_1689_ = l_Lean_mkAppN(v___x_1688_, v___x_1668_);
v___x_1690_ = l_Lean_Expr_app___override(v___x_1689_, v_a_1687_);
v___x_1691_ = l_Lean_mkAppN(v___x_1690_, v___x_1664_);
v___x_1692_ = lean_array_mk(v_ctors_1669_);
v_sz_1693_ = lean_array_size(v___x_1692_);
v___x_1694_ = ((size_t)0ULL);
lean_inc_ref(v_ctorIdx_1671_);
lean_inc_ref(v_k_1674_);
v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1670_, v_k_1674_, v_ctorIdx_1671_, v_tail_1672_, v___x_1668_, v_sz_1693_, v___x_1694_, v___x_1692_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v___x_1697_ = l_Lean_mkAppN(v___x_1691_, v_a_1696_);
lean_dec(v_a_1696_);
lean_inc_ref(v_h_1673_);
v___x_1698_ = l_Lean_Expr_app___override(v___x_1697_, v_h_1673_);
v___x_1699_ = lean_unsigned_to_nat(2u);
v___x_1700_ = lean_mk_empty_array_with_capacity(v___x_1699_);
lean_inc_ref(v___x_1700_);
v___x_1701_ = lean_array_push(v___x_1700_, v___x_1663_);
v___x_1702_ = lean_array_push(v___x_1701_, v_ctorIdx_1671_);
v___x_1703_ = l_Array_append___redArg(v___x_1668_, v___x_1702_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = l_Array_append___redArg(v___x_1703_, v___x_1664_);
v___x_1705_ = lean_array_push(v___x_1700_, v_h_1673_);
v___x_1706_ = lean_array_push(v___x_1705_, v_k_1674_);
v___x_1707_ = l_Array_append___redArg(v___x_1704_, v___x_1706_);
lean_dec_ref(v___x_1706_);
v___x_1708_ = l_Lean_Meta_mkLambdaFVars(v___x_1707_, v___x_1698_, v___x_1683_, v___x_1684_, v___x_1683_, v___x_1684_, v___x_1685_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec_ref(v___x_1707_);
return v___x_1708_;
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref(v___x_1691_);
lean_dec_ref(v_k_1674_);
lean_dec_ref(v_h_1673_);
lean_dec_ref(v_ctorIdx_1671_);
lean_dec_ref(v___x_1668_);
lean_dec_ref(v___x_1663_);
v_a_1709_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1695_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1695_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_dec_ref(v_k_1674_);
lean_dec_ref(v_h_1673_);
lean_dec(v_tail_1672_);
lean_dec_ref(v_ctorIdx_1671_);
lean_dec_ref(v___x_1670_);
lean_dec(v_ctors_1669_);
lean_dec_ref(v___x_1668_);
lean_dec(v___x_1667_);
lean_dec(v_name_1666_);
lean_dec_ref(v___x_1663_);
return v___x_1686_;
}
}
else
{
lean_dec_ref(v_k_1674_);
lean_dec_ref(v_h_1673_);
lean_dec(v_tail_1672_);
lean_dec_ref(v_ctorIdx_1671_);
lean_dec_ref(v___x_1670_);
lean_dec(v_ctors_1669_);
lean_dec_ref(v___x_1668_);
lean_dec(v___x_1667_);
lean_dec(v_name_1666_);
lean_dec_ref(v___x_1663_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed(lean_object** _args){
lean_object* v___x_1717_ = _args[0];
lean_object* v___x_1718_ = _args[1];
lean_object* v_a_1719_ = _args[2];
lean_object* v_name_1720_ = _args[3];
lean_object* v___x_1721_ = _args[4];
lean_object* v___x_1722_ = _args[5];
lean_object* v_ctors_1723_ = _args[6];
lean_object* v___x_1724_ = _args[7];
lean_object* v_ctorIdx_1725_ = _args[8];
lean_object* v_tail_1726_ = _args[9];
lean_object* v_h_1727_ = _args[10];
lean_object* v_k_1728_ = _args[11];
lean_object* v___y_1729_ = _args[12];
lean_object* v___y_1730_ = _args[13];
lean_object* v___y_1731_ = _args[14];
lean_object* v___y_1732_ = _args[15];
lean_object* v___y_1733_ = _args[16];
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(v___x_1717_, v___x_1718_, v_a_1719_, v_name_1720_, v___x_1721_, v___x_1722_, v_ctors_1723_, v___x_1724_, v_ctorIdx_1725_, v_tail_1726_, v_h_1727_, v_k_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec_ref(v___x_1718_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(lean_object* v___x_1738_, lean_object* v___x_1739_, lean_object* v_a_1740_, lean_object* v_name_1741_, lean_object* v___x_1742_, lean_object* v___x_1743_, lean_object* v_ctors_1744_, lean_object* v___x_1745_, lean_object* v_ctorIdx_1746_, lean_object* v_tail_1747_, lean_object* v___x_1748_, lean_object* v_h_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___f_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___f_1755_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1755_, 0, v___x_1738_);
lean_closure_set(v___f_1755_, 1, v___x_1739_);
lean_closure_set(v___f_1755_, 2, v_a_1740_);
lean_closure_set(v___f_1755_, 3, v_name_1741_);
lean_closure_set(v___f_1755_, 4, v___x_1742_);
lean_closure_set(v___f_1755_, 5, v___x_1743_);
lean_closure_set(v___f_1755_, 6, v_ctors_1744_);
lean_closure_set(v___f_1755_, 7, v___x_1745_);
lean_closure_set(v___f_1755_, 8, v_ctorIdx_1746_);
lean_closure_set(v___f_1755_, 9, v_tail_1747_);
lean_closure_set(v___f_1755_, 10, v_h_1749_);
v___x_1756_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1));
v___x_1757_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1756_, v___x_1748_, v___f_1755_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed(lean_object** _args){
lean_object* v___x_1758_ = _args[0];
lean_object* v___x_1759_ = _args[1];
lean_object* v_a_1760_ = _args[2];
lean_object* v_name_1761_ = _args[3];
lean_object* v___x_1762_ = _args[4];
lean_object* v___x_1763_ = _args[5];
lean_object* v_ctors_1764_ = _args[6];
lean_object* v___x_1765_ = _args[7];
lean_object* v_ctorIdx_1766_ = _args[8];
lean_object* v_tail_1767_ = _args[9];
lean_object* v___x_1768_ = _args[10];
lean_object* v_h_1769_ = _args[11];
lean_object* v___y_1770_ = _args[12];
lean_object* v___y_1771_ = _args[13];
lean_object* v___y_1772_ = _args[14];
lean_object* v___y_1773_ = _args[15];
lean_object* v___y_1774_ = _args[16];
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(v___x_1758_, v___x_1759_, v_a_1760_, v_name_1761_, v___x_1762_, v___x_1763_, v_ctors_1764_, v___x_1765_, v_ctorIdx_1766_, v_tail_1767_, v___x_1768_, v_h_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(lean_object* v___x_1776_, lean_object* v___x_1777_, lean_object* v___x_1778_, lean_object* v___x_1779_, lean_object* v_indName_1780_, lean_object* v_tail_1781_, lean_object* v___x_1782_, lean_object* v_name_1783_, lean_object* v_ctors_1784_, lean_object* v_ctorIdx_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_inc(v___x_1777_);
v___x_1791_ = l_Lean_mkConst(v___x_1776_, v___x_1777_);
lean_inc_ref(v___x_1779_);
lean_inc_ref_n(v___x_1778_, 2);
v___x_1792_ = lean_array_push(v___x_1778_, v___x_1779_);
v___x_1793_ = l_Lean_mkAppN(v___x_1791_, v___x_1792_);
lean_dec_ref(v___x_1792_);
lean_inc_ref_n(v_ctorIdx_1785_, 2);
lean_inc_ref(v___x_1793_);
v___x_1794_ = l_Lean_Expr_app___override(v___x_1793_, v_ctorIdx_1785_);
v___x_1795_ = l_Lean_mkCtorIdxName(v_indName_1780_);
lean_inc(v_tail_1781_);
v___x_1796_ = l_Lean_mkConst(v___x_1795_, v_tail_1781_);
v___x_1797_ = l_Array_append___redArg(v___x_1778_, v___x_1782_);
v___x_1798_ = l_Lean_mkAppN(v___x_1796_, v___x_1797_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = l_Lean_Meta_mkEq(v_ctorIdx_1785_, v___x_1798_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___f_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc_n(v_a_1800_, 2);
lean_dec_ref_known(v___x_1799_, 1);
v___f_1801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed), 17, 11);
lean_closure_set(v___f_1801_, 0, v___x_1779_);
lean_closure_set(v___f_1801_, 1, v___x_1782_);
lean_closure_set(v___f_1801_, 2, v_a_1800_);
lean_closure_set(v___f_1801_, 3, v_name_1783_);
lean_closure_set(v___f_1801_, 4, v___x_1777_);
lean_closure_set(v___f_1801_, 5, v___x_1778_);
lean_closure_set(v___f_1801_, 6, v_ctors_1784_);
lean_closure_set(v___f_1801_, 7, v___x_1793_);
lean_closure_set(v___f_1801_, 8, v_ctorIdx_1785_);
lean_closure_set(v___f_1801_, 9, v_tail_1781_);
lean_closure_set(v___f_1801_, 10, v___x_1794_);
v___x_1802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_1803_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1802_, v_a_1800_, v___f_1801_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1803_;
}
else
{
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___x_1793_);
lean_dec_ref(v_ctorIdx_1785_);
lean_dec(v_ctors_1784_);
lean_dec(v_name_1783_);
lean_dec_ref(v___x_1782_);
lean_dec(v_tail_1781_);
lean_dec_ref(v___x_1779_);
lean_dec_ref(v___x_1778_);
lean_dec(v___x_1777_);
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed(lean_object* v___x_1804_, lean_object* v___x_1805_, lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_indName_1808_, lean_object* v_tail_1809_, lean_object* v___x_1810_, lean_object* v_name_1811_, lean_object* v_ctors_1812_, lean_object* v_ctorIdx_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(v___x_1804_, v___x_1805_, v___x_1806_, v___x_1807_, v_indName_1808_, v_tail_1809_, v___x_1810_, v_name_1811_, v_ctors_1812_, v_ctorIdx_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(lean_object* v_val_1820_, lean_object* v___x_1821_, lean_object* v___x_1822_, lean_object* v___x_1823_, lean_object* v_indName_1824_, lean_object* v_tail_1825_, lean_object* v_name_1826_, lean_object* v___x_1827_, lean_object* v_xs_1828_, lean_object* v_x_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_numParams_1835_; lean_object* v_numIndices_1836_; lean_object* v_ctors_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___f_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_numParams_1835_ = lean_ctor_get(v_val_1820_, 1);
lean_inc_n(v_numParams_1835_, 2);
v_numIndices_1836_ = lean_ctor_get(v_val_1820_, 2);
lean_inc(v_numIndices_1836_);
v_ctors_1837_ = lean_ctor_get(v_val_1820_, 4);
lean_inc(v_ctors_1837_);
lean_dec_ref(v_val_1820_);
v___x_1838_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_1828_, 2);
v___x_1839_ = l_Array_toSubarray___redArg(v_xs_1828_, v___x_1838_, v_numParams_1835_);
v___x_1840_ = l_Subarray_copy___redArg(v___x_1839_);
v___x_1841_ = lean_array_get(v___x_1821_, v_xs_1828_, v_numParams_1835_);
v___x_1842_ = lean_unsigned_to_nat(1u);
v___x_1843_ = lean_nat_add(v_numParams_1835_, v___x_1842_);
lean_dec(v_numParams_1835_);
v___x_1844_ = lean_nat_add(v___x_1843_, v_numIndices_1836_);
lean_dec(v_numIndices_1836_);
lean_inc(v___x_1844_);
v___x_1845_ = l_Array_toSubarray___redArg(v_xs_1828_, v___x_1843_, v___x_1844_);
v___x_1846_ = l_Subarray_copy___redArg(v___x_1845_);
v___x_1847_ = lean_array_get(v___x_1821_, v_xs_1828_, v___x_1844_);
lean_dec(v___x_1844_);
lean_dec_ref(v_xs_1828_);
v___x_1848_ = lean_array_push(v___x_1846_, v___x_1847_);
v___f_1849_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed), 15, 9);
lean_closure_set(v___f_1849_, 0, v___x_1822_);
lean_closure_set(v___f_1849_, 1, v___x_1823_);
lean_closure_set(v___f_1849_, 2, v___x_1840_);
lean_closure_set(v___f_1849_, 3, v___x_1841_);
lean_closure_set(v___f_1849_, 4, v_indName_1824_);
lean_closure_set(v___f_1849_, 5, v_tail_1825_);
lean_closure_set(v___f_1849_, 6, v___x_1848_);
lean_closure_set(v___f_1849_, 7, v_name_1826_);
lean_closure_set(v___f_1849_, 8, v_ctors_1837_);
v___x_1850_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_1851_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_1852_ = l_Lean_mkConst(v___x_1851_, v___x_1827_);
v___x_1853_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1850_, v___x_1852_, v___f_1849_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed(lean_object* v_val_1854_, lean_object* v___x_1855_, lean_object* v___x_1856_, lean_object* v___x_1857_, lean_object* v_indName_1858_, lean_object* v_tail_1859_, lean_object* v_name_1860_, lean_object* v___x_1861_, lean_object* v_xs_1862_, lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(v_val_1854_, v___x_1855_, v___x_1856_, v___x_1857_, v_indName_1858_, v_tail_1859_, v_name_1860_, v___x_1861_, v_xs_1862_, v_x_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v_x_1863_);
lean_dec_ref(v___x_1855_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
if (lean_obj_tag(v_a_1870_) == 0)
{
lean_object* v___x_1872_; 
v___x_1872_ = l_List_reverse___redArg(v_a_1871_);
return v___x_1872_;
}
else
{
lean_object* v_head_1873_; lean_object* v_tail_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1883_; 
v_head_1873_ = lean_ctor_get(v_a_1870_, 0);
v_tail_1874_ = lean_ctor_get(v_a_1870_, 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_a_1870_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1876_ = v_a_1870_;
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_tail_1874_);
lean_inc(v_head_1873_);
lean_dec(v_a_1870_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_mkLevelParam(v_head_1873_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v_a_1871_);
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_a_1871_);
v___x_1880_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
v_a_1870_ = v_tail_1874_;
v_a_1871_ = v___x_1880_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_1887_ = lean_unsigned_to_nat(58u);
v___x_1888_ = lean_unsigned_to_nat(113u);
v___x_1889_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1890_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1891_ = l_mkPanicMessageWithDecl(v___x_1890_, v___x_1889_, v___x_1888_, v___x_1887_, v___x_1886_);
return v___x_1891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1893_ = lean_unsigned_to_nat(60u);
v___x_1894_ = lean_unsigned_to_nat(109u);
v___x_1895_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1896_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1897_ = l_mkPanicMessageWithDecl(v___x_1896_, v___x_1895_, v___x_1894_, v___x_1893_, v___x_1892_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(lean_object* v_indName_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1898_);
v___x_1905_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
if (lean_obj_tag(v_a_1906_) == 5)
{
lean_object* v_val_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_val_1907_ = lean_ctor_get(v_a_1906_, 0);
lean_inc_ref(v_val_1907_);
lean_dec_ref_known(v_a_1906_, 1);
lean_inc_n(v_indName_1898_, 2);
v___x_1908_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1898_);
v___x_1909_ = l_Lean_mkCasesOnName(v_indName_1898_);
v___x_1910_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1909_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_name_1912_; lean_object* v_levelParams_1913_; lean_object* v_type_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v_name_1912_ = lean_ctor_get(v_a_1911_, 0);
lean_inc(v_name_1912_);
v_levelParams_1913_ = lean_ctor_get(v_a_1911_, 1);
lean_inc_n(v_levelParams_1913_, 2);
v_type_1914_ = lean_ctor_get(v_a_1911_, 2);
lean_inc_ref(v_type_1914_);
lean_dec(v_a_1911_);
v___x_1915_ = lean_box(0);
v___x_1916_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_1913_, v___x_1915_);
if (lean_obj_tag(v___x_1916_) == 1)
{
lean_object* v_tail_1917_; lean_object* v___f_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; 
v_tail_1917_ = lean_ctor_get(v___x_1916_, 1);
lean_inc(v_tail_1917_);
lean_inc(v_indName_1898_);
v___f_1918_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed), 15, 8);
lean_closure_set(v___f_1918_, 0, v_val_1907_);
lean_closure_set(v___f_1918_, 1, v___x_1904_);
lean_closure_set(v___f_1918_, 2, v___x_1908_);
lean_closure_set(v___f_1918_, 3, v___x_1916_);
lean_closure_set(v___f_1918_, 4, v_indName_1898_);
lean_closure_set(v___f_1918_, 5, v_tail_1917_);
lean_closure_set(v___f_1918_, 6, v_name_1912_);
lean_closure_set(v___f_1918_, 7, v___x_1915_);
v___x_1919_ = 0;
v___x_1920_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1914_, v___f_1918_, v___x_1919_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc_n(v_a_1921_, 2);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = l_Lean_mkCtorElimName(v_indName_1898_);
lean_inc(v_a_1902_);
lean_inc_ref(v_a_1901_);
lean_inc(v_a_1900_);
lean_inc_ref(v_a_1899_);
v___x_1923_ = lean_infer_type(v_a_1921_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_2041_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = lean_box(1);
lean_inc(v___x_1922_);
v___x_1926_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1922_, v_levelParams_1913_, v_a_1924_, v_a_1921_, v___x_1925_, v_a_1902_);
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_2041_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_2041_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 1);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_2040_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
uint8_t v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = 1;
v___x_1934_ = l_Lean_addAndCompile(v___x_1932_, v___x_1933_, v___x_1919_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; lean_object* v_env_1936_; lean_object* v_nextMacroScope_1937_; lean_object* v_ngen_1938_; lean_object* v_auxDeclNGen_1939_; lean_object* v_traceState_1940_; lean_object* v_recordedDeps_1941_; lean_object* v_messages_1942_; lean_object* v_infoState_1943_; lean_object* v_snapshotTasks_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref_known(v___x_1934_, 1);
v___x_1935_ = lean_st_ref_take(v_a_1902_);
v_env_1936_ = lean_ctor_get(v___x_1935_, 0);
v_nextMacroScope_1937_ = lean_ctor_get(v___x_1935_, 1);
v_ngen_1938_ = lean_ctor_get(v___x_1935_, 2);
v_auxDeclNGen_1939_ = lean_ctor_get(v___x_1935_, 3);
v_traceState_1940_ = lean_ctor_get(v___x_1935_, 4);
v_recordedDeps_1941_ = lean_ctor_get(v___x_1935_, 6);
v_messages_1942_ = lean_ctor_get(v___x_1935_, 7);
v_infoState_1943_ = lean_ctor_get(v___x_1935_, 8);
v_snapshotTasks_1944_ = lean_ctor_get(v___x_1935_, 9);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v___x_1935_, 5);
lean_dec(v_unused_2039_);
v___x_1946_ = v___x_1935_;
v_isShared_1947_ = v_isSharedCheck_2038_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_snapshotTasks_1944_);
lean_inc(v_infoState_1943_);
lean_inc(v_messages_1942_);
lean_inc(v_recordedDeps_1941_);
lean_inc(v_traceState_1940_);
lean_inc(v_auxDeclNGen_1939_);
lean_inc(v_ngen_1938_);
lean_inc(v_nextMacroScope_1937_);
lean_inc(v_env_1936_);
lean_dec(v___x_1935_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2038_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_inc(v___x_1922_);
v___x_1948_ = l_Lean_markAuxRecursor(v_env_1936_, v___x_1922_);
v___x_1949_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 5, v___x_1949_);
lean_ctor_set(v___x_1946_, 0, v___x_1948_);
v___x_1951_ = v___x_1946_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_nextMacroScope_1937_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v_ngen_1938_);
lean_ctor_set(v_reuseFailAlloc_2037_, 3, v_auxDeclNGen_1939_);
lean_ctor_set(v_reuseFailAlloc_2037_, 4, v_traceState_1940_);
lean_ctor_set(v_reuseFailAlloc_2037_, 5, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2037_, 6, v_recordedDeps_1941_);
lean_ctor_set(v_reuseFailAlloc_2037_, 7, v_messages_1942_);
lean_ctor_set(v_reuseFailAlloc_2037_, 8, v_infoState_1943_);
lean_ctor_set(v_reuseFailAlloc_2037_, 9, v_snapshotTasks_1944_);
v___x_1951_ = v_reuseFailAlloc_2037_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v_mctx_1954_; lean_object* v_zetaDeltaFVarIds_1955_; lean_object* v_postponed_1956_; lean_object* v_diag_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2035_; 
v___x_1952_ = lean_st_ref_put(v_a_1902_, v___x_1951_);
v___x_1953_ = lean_st_ref_take(v_a_1900_);
v_mctx_1954_ = lean_ctor_get(v___x_1953_, 0);
v_zetaDeltaFVarIds_1955_ = lean_ctor_get(v___x_1953_, 2);
v_postponed_1956_ = lean_ctor_get(v___x_1953_, 3);
v_diag_1957_ = lean_ctor_get(v___x_1953_, 4);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_1953_, 1);
lean_dec(v_unused_2036_);
v___x_1959_ = v___x_1953_;
v_isShared_1960_ = v_isSharedCheck_2035_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_diag_1957_);
lean_inc(v_postponed_1956_);
lean_inc(v_zetaDeltaFVarIds_1955_);
lean_inc(v_mctx_1954_);
lean_dec(v___x_1953_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2035_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_mctx_1954_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_zetaDeltaFVarIds_1955_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_postponed_1956_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_diag_1957_);
v___x_1963_ = v_reuseFailAlloc_2034_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v_env_1966_; lean_object* v_nextMacroScope_1967_; lean_object* v_ngen_1968_; lean_object* v_auxDeclNGen_1969_; lean_object* v_traceState_1970_; lean_object* v_recordedDeps_1971_; lean_object* v_messages_1972_; lean_object* v_infoState_1973_; lean_object* v_snapshotTasks_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2032_; 
v___x_1964_ = lean_st_ref_put(v_a_1900_, v___x_1963_);
v___x_1965_ = lean_st_ref_take(v_a_1902_);
v_env_1966_ = lean_ctor_get(v___x_1965_, 0);
v_nextMacroScope_1967_ = lean_ctor_get(v___x_1965_, 1);
v_ngen_1968_ = lean_ctor_get(v___x_1965_, 2);
v_auxDeclNGen_1969_ = lean_ctor_get(v___x_1965_, 3);
v_traceState_1970_ = lean_ctor_get(v___x_1965_, 4);
v_recordedDeps_1971_ = lean_ctor_get(v___x_1965_, 6);
v_messages_1972_ = lean_ctor_get(v___x_1965_, 7);
v_infoState_1973_ = lean_ctor_get(v___x_1965_, 8);
v_snapshotTasks_1974_ = lean_ctor_get(v___x_1965_, 9);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v___x_1965_, 5);
lean_dec(v_unused_2033_);
v___x_1976_ = v___x_1965_;
v_isShared_1977_ = v_isSharedCheck_2032_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_snapshotTasks_1974_);
lean_inc(v_infoState_1973_);
lean_inc(v_messages_1972_);
lean_inc(v_recordedDeps_1971_);
lean_inc(v_traceState_1970_);
lean_inc(v_auxDeclNGen_1969_);
lean_inc(v_ngen_1968_);
lean_inc(v_nextMacroScope_1967_);
lean_inc(v_env_1966_);
lean_dec(v___x_1965_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2032_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_inc(v___x_1922_);
v___x_1978_ = l_Lean_Meta_addToCompletionBlackList(v_env_1966_, v___x_1922_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 5, v___x_1949_);
lean_ctor_set(v___x_1976_, 0, v___x_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_nextMacroScope_1967_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_ngen_1968_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v_auxDeclNGen_1969_);
lean_ctor_set(v_reuseFailAlloc_2031_, 4, v_traceState_1970_);
lean_ctor_set(v_reuseFailAlloc_2031_, 5, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2031_, 6, v_recordedDeps_1971_);
lean_ctor_set(v_reuseFailAlloc_2031_, 7, v_messages_1972_);
lean_ctor_set(v_reuseFailAlloc_2031_, 8, v_infoState_1973_);
lean_ctor_set(v_reuseFailAlloc_2031_, 9, v_snapshotTasks_1974_);
v___x_1980_ = v_reuseFailAlloc_2031_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v_mctx_1983_; lean_object* v_zetaDeltaFVarIds_1984_; lean_object* v_postponed_1985_; lean_object* v_diag_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2029_; 
v___x_1981_ = lean_st_ref_put(v_a_1902_, v___x_1980_);
v___x_1982_ = lean_st_ref_take(v_a_1900_);
v_mctx_1983_ = lean_ctor_get(v___x_1982_, 0);
v_zetaDeltaFVarIds_1984_ = lean_ctor_get(v___x_1982_, 2);
v_postponed_1985_ = lean_ctor_get(v___x_1982_, 3);
v_diag_1986_ = lean_ctor_get(v___x_1982_, 4);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_1982_, 1);
lean_dec(v_unused_2030_);
v___x_1988_ = v___x_1982_;
v_isShared_1989_ = v_isSharedCheck_2029_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_diag_1986_);
lean_inc(v_postponed_1985_);
lean_inc(v_zetaDeltaFVarIds_1984_);
lean_inc(v_mctx_1983_);
lean_dec(v___x_1982_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2029_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___x_1961_);
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_mctx_1983_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_zetaDeltaFVarIds_1984_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v_postponed_1985_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_diag_1986_);
v___x_1991_ = v_reuseFailAlloc_2028_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v_env_1994_; lean_object* v_nextMacroScope_1995_; lean_object* v_ngen_1996_; lean_object* v_auxDeclNGen_1997_; lean_object* v_traceState_1998_; lean_object* v_recordedDeps_1999_; lean_object* v_messages_2000_; lean_object* v_infoState_2001_; lean_object* v_snapshotTasks_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2026_; 
v___x_1992_ = lean_st_ref_put(v_a_1900_, v___x_1991_);
v___x_1993_ = lean_st_ref_take(v_a_1902_);
v_env_1994_ = lean_ctor_get(v___x_1993_, 0);
v_nextMacroScope_1995_ = lean_ctor_get(v___x_1993_, 1);
v_ngen_1996_ = lean_ctor_get(v___x_1993_, 2);
v_auxDeclNGen_1997_ = lean_ctor_get(v___x_1993_, 3);
v_traceState_1998_ = lean_ctor_get(v___x_1993_, 4);
v_recordedDeps_1999_ = lean_ctor_get(v___x_1993_, 6);
v_messages_2000_ = lean_ctor_get(v___x_1993_, 7);
v_infoState_2001_ = lean_ctor_get(v___x_1993_, 8);
v_snapshotTasks_2002_ = lean_ctor_get(v___x_1993_, 9);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v___x_1993_, 5);
lean_dec(v_unused_2027_);
v___x_2004_ = v___x_1993_;
v_isShared_2005_ = v_isSharedCheck_2026_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_snapshotTasks_2002_);
lean_inc(v_infoState_2001_);
lean_inc(v_messages_2000_);
lean_inc(v_recordedDeps_1999_);
lean_inc(v_traceState_1998_);
lean_inc(v_auxDeclNGen_1997_);
lean_inc(v_ngen_1996_);
lean_inc(v_nextMacroScope_1995_);
lean_inc(v_env_1994_);
lean_dec(v___x_1993_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2026_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
lean_inc(v___x_1922_);
v___x_2006_ = l_Lean_addProtected(v_env_1994_, v___x_1922_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 5, v___x_1949_);
lean_ctor_set(v___x_2004_, 0, v___x_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_nextMacroScope_1995_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_ngen_1996_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_auxDeclNGen_1997_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_traceState_1998_);
lean_ctor_set(v_reuseFailAlloc_2025_, 5, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2025_, 6, v_recordedDeps_1999_);
lean_ctor_set(v_reuseFailAlloc_2025_, 7, v_messages_2000_);
lean_ctor_set(v_reuseFailAlloc_2025_, 8, v_infoState_2001_);
lean_ctor_set(v_reuseFailAlloc_2025_, 9, v_snapshotTasks_2002_);
v___x_2008_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v_mctx_2011_; lean_object* v_zetaDeltaFVarIds_2012_; lean_object* v_postponed_2013_; lean_object* v_diag_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2023_; 
v___x_2009_ = lean_st_ref_put(v_a_1902_, v___x_2008_);
v___x_2010_ = lean_st_ref_take(v_a_1900_);
v_mctx_2011_ = lean_ctor_get(v___x_2010_, 0);
v_zetaDeltaFVarIds_2012_ = lean_ctor_get(v___x_2010_, 2);
v_postponed_2013_ = lean_ctor_get(v___x_2010_, 3);
v_diag_2014_ = lean_ctor_get(v___x_2010_, 4);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v___x_2010_, 1);
lean_dec(v_unused_2024_);
v___x_2016_ = v___x_2010_;
v_isShared_2017_ = v_isSharedCheck_2023_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_diag_2014_);
lean_inc(v_postponed_2013_);
lean_inc(v_zetaDeltaFVarIds_2012_);
lean_inc(v_mctx_2011_);
lean_dec(v___x_2010_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2023_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 1, v___x_1961_);
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_mctx_2011_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_zetaDeltaFVarIds_2012_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_postponed_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_diag_2014_);
v___x_2019_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_st_ref_put(v_a_1900_, v___x_2019_);
v___x_2021_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_1922_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_2021_;
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
lean_dec(v___x_1922_);
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v___x_1922_);
lean_dec(v_a_1921_);
lean_dec(v_levelParams_1913_);
v_a_2042_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_1923_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_1923_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_levelParams_1913_);
lean_dec(v_indName_1898_);
v_a_2050_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1920_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1920_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v___x_1916_);
lean_dec_ref(v_type_1914_);
lean_dec(v_levelParams_1913_);
lean_dec(v_name_1912_);
lean_dec(v___x_1908_);
lean_dec_ref(v_val_1907_);
lean_dec(v_indName_1898_);
v___x_2058_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2);
v___x_2059_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_2058_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_2059_;
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v___x_1908_);
lean_dec_ref(v_val_1907_);
lean_dec(v_indName_1898_);
v_a_2060_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_1910_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_1910_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v_a_1906_);
lean_dec(v_indName_1898_);
v___x_2068_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3);
v___x_2069_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_2068_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_2069_;
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_indName_1898_);
v_a_2070_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_1905_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_1905_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___boxed(lean_object* v_indName_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(lean_object* v___x_2085_, lean_object* v_k_2086_, lean_object* v_ctorIdx_2087_, lean_object* v_tail_2088_, lean_object* v___x_2089_, lean_object* v_as_2090_, size_t v_sz_2091_, size_t v_i_2092_, lean_object* v_bs_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_2085_, v_k_2086_, v_ctorIdx_2087_, v_tail_2088_, v___x_2089_, v_sz_2091_, v_i_2092_, v_bs_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___boxed(lean_object* v___x_2100_, lean_object* v_k_2101_, lean_object* v_ctorIdx_2102_, lean_object* v_tail_2103_, lean_object* v___x_2104_, lean_object* v_as_2105_, lean_object* v_sz_2106_, lean_object* v_i_2107_, lean_object* v_bs_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
size_t v_sz_boxed_2114_; size_t v_i_boxed_2115_; lean_object* v_res_2116_; 
v_sz_boxed_2114_ = lean_unbox_usize(v_sz_2106_);
lean_dec(v_sz_2106_);
v_i_boxed_2115_ = lean_unbox_usize(v_i_2107_);
lean_dec(v_i_2107_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(v___x_2100_, v_k_2101_, v_ctorIdx_2102_, v_tail_2103_, v___x_2104_, v_as_2105_, v_sz_boxed_2114_, v_i_boxed_2115_, v_bs_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec_ref(v_as_2105_);
lean_dec_ref(v___x_2104_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(lean_object* v___x_2117_, lean_object* v___x_2118_, lean_object* v___x_2119_, lean_object* v___x_2120_, lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v___x_2123_, lean_object* v___f_2124_, lean_object* v___x_2125_, lean_object* v___y_2126_, uint8_t v___x_2127_, lean_object* v_h_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_inc(v___x_2118_);
v___x_2134_ = l_Lean_mkConst(v___x_2117_, v___x_2118_);
v___x_2135_ = l_Lean_mkAppN(v___x_2134_, v___x_2119_);
lean_inc_ref(v___x_2120_);
v___x_2136_ = l_Lean_Expr_app___override(v___x_2135_, v___x_2120_);
lean_inc_ref(v___x_2121_);
v___x_2137_ = l_Lean_Expr_app___override(v___x_2136_, v___x_2121_);
v___x_2138_ = l_Lean_mkAppN(v___x_2137_, v___x_2122_);
lean_inc_ref(v_h_2128_);
v___x_2139_ = l_Lean_Meta_mkEqSymm(v_h_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_Expr_app___override(v___x_2138_, v_a_2140_);
v___x_2142_ = l_Lean_mkConst(v___x_2123_, v___x_2118_);
lean_inc_ref(v___x_2120_);
lean_inc_ref(v___x_2119_);
v___x_2143_ = lean_array_push(v___x_2119_, v___x_2120_);
v___x_2144_ = lean_array_push(v___x_2143_, v___x_2121_);
v___x_2145_ = l_Lean_mkAppN(v___x_2142_, v___x_2144_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v___x_2145_, v___f_2124_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = l_Lean_Expr_app___override(v___x_2141_, v_a_2147_);
v___x_2149_ = lean_mk_empty_array_with_capacity(v___x_2125_);
v___x_2150_ = lean_array_push(v___x_2149_, v___x_2120_);
v___x_2151_ = l_Array_append___redArg(v___x_2119_, v___x_2150_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = l_Array_append___redArg(v___x_2151_, v___x_2122_);
v___x_2153_ = lean_unsigned_to_nat(2u);
v___x_2154_ = lean_mk_empty_array_with_capacity(v___x_2153_);
v___x_2155_ = lean_array_push(v___x_2154_, v_h_2128_);
v___x_2156_ = lean_array_push(v___x_2155_, v___y_2126_);
v___x_2157_ = l_Array_append___redArg(v___x_2152_, v___x_2156_);
lean_dec_ref(v___x_2156_);
v___x_2158_ = 0;
v___x_2159_ = 1;
v___x_2160_ = l_Lean_Meta_mkLambdaFVars(v___x_2157_, v___x_2148_, v___x_2158_, v___x_2127_, v___x_2158_, v___x_2127_, v___x_2159_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec_ref(v___x_2157_);
return v___x_2160_;
}
else
{
lean_dec_ref(v___x_2141_);
lean_dec_ref(v_h_2128_);
lean_dec_ref(v___y_2126_);
lean_dec_ref(v___x_2120_);
lean_dec_ref(v___x_2119_);
return v___x_2146_;
}
}
else
{
lean_dec_ref(v___x_2138_);
lean_dec_ref(v_h_2128_);
lean_dec_ref(v___y_2126_);
lean_dec_ref(v___f_2124_);
lean_dec(v___x_2123_);
lean_dec_ref(v___x_2121_);
lean_dec_ref(v___x_2120_);
lean_dec_ref(v___x_2119_);
lean_dec(v___x_2118_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_2161_ = _args[0];
lean_object* v___x_2162_ = _args[1];
lean_object* v___x_2163_ = _args[2];
lean_object* v___x_2164_ = _args[3];
lean_object* v___x_2165_ = _args[4];
lean_object* v___x_2166_ = _args[5];
lean_object* v___x_2167_ = _args[6];
lean_object* v___f_2168_ = _args[7];
lean_object* v___x_2169_ = _args[8];
lean_object* v___y_2170_ = _args[9];
lean_object* v___x_2171_ = _args[10];
lean_object* v_h_2172_ = _args[11];
lean_object* v___y_2173_ = _args[12];
lean_object* v___y_2174_ = _args[13];
lean_object* v___y_2175_ = _args[14];
lean_object* v___y_2176_ = _args[15];
lean_object* v___y_2177_ = _args[16];
_start:
{
uint8_t v___x_11418__boxed_2178_; lean_object* v_res_2179_; 
v___x_11418__boxed_2178_ = lean_unbox(v___x_2171_);
v_res_2179_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(v___x_2161_, v___x_2162_, v___x_2163_, v___x_2164_, v___x_2165_, v___x_2166_, v___x_2167_, v___f_2168_, v___x_2169_, v___y_2170_, v___x_11418__boxed_2178_, v_h_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___x_2169_);
lean_dec_ref(v___x_2166_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(lean_object* v___y_2180_, lean_object* v_x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___y_2180_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(v___y_2188_, v_x_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec_ref(v_x_2189_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(lean_object* v___x_2196_, lean_object* v_numParams_2197_, lean_object* v___x_2198_, lean_object* v___x_2199_, lean_object* v_numIndices_2200_, lean_object* v_indName_2201_, lean_object* v_tail_2202_, lean_object* v_i_2203_, lean_object* v___x_2204_, lean_object* v___x_2205_, lean_object* v___x_2206_, uint8_t v___x_2207_, lean_object* v_xs_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v_start_2224_; lean_object* v_stop_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___y_2230_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
lean_inc(v_numParams_2197_);
lean_inc_ref_n(v_xs_2208_, 2);
v___x_2215_ = l_Array_toSubarray___redArg(v_xs_2208_, v___x_2196_, v_numParams_2197_);
v___x_2216_ = lean_array_get(v___x_2198_, v_xs_2208_, v_numParams_2197_);
v___x_2217_ = lean_nat_add(v_numParams_2197_, v___x_2199_);
lean_dec(v_numParams_2197_);
v___x_2218_ = lean_nat_add(v___x_2217_, v_numIndices_2200_);
lean_inc(v___x_2218_);
v___x_2219_ = l_Array_toSubarray___redArg(v_xs_2208_, v___x_2217_, v___x_2218_);
v___x_2220_ = lean_array_get(v___x_2198_, v_xs_2208_, v___x_2218_);
v___x_2221_ = lean_nat_add(v___x_2218_, v___x_2199_);
lean_dec(v___x_2218_);
v___x_2222_ = lean_array_get_size(v_xs_2208_);
v___x_2223_ = l_Array_toSubarray___redArg(v_xs_2208_, v___x_2221_, v___x_2222_);
v_start_2224_ = lean_ctor_get(v___x_2223_, 1);
v_stop_2225_ = lean_ctor_get(v___x_2223_, 2);
v___x_2226_ = l_Subarray_copy___redArg(v___x_2215_);
v___x_2227_ = l_Subarray_copy___redArg(v___x_2219_);
v___x_2228_ = lean_array_push(v___x_2227_, v___x_2220_);
v___x_2243_ = lean_nat_sub(v_stop_2225_, v_start_2224_);
v___x_2244_ = lean_nat_dec_lt(v_i_2203_, v___x_2243_);
lean_dec(v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
lean_dec_ref(v___x_2223_);
v___x_2245_ = l_outOfBounds___redArg(v___x_2198_);
v___y_2230_ = v___x_2245_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Subarray_get___redArg(v___x_2223_, v_i_2203_);
lean_dec_ref(v___x_2223_);
v___y_2230_ = v___x_2246_;
goto v___jp_2229_;
}
v___jp_2229_:
{
lean_object* v___f_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; 
lean_inc_ref(v___y_2230_);
v___f_2231_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2231_, 0, v___y_2230_);
v___x_2232_ = l_Lean_mkCtorIdxName(v_indName_2201_);
v___x_2233_ = l_Lean_mkConst(v___x_2232_, v_tail_2202_);
lean_inc_ref(v___x_2226_);
v___x_2234_ = l_Array_append___redArg(v___x_2226_, v___x_2228_);
v___x_2235_ = l_Lean_mkAppN(v___x_2233_, v___x_2234_);
lean_dec_ref(v___x_2234_);
v___x_2236_ = l_Lean_mkRawNatLit(v_i_2203_);
v___x_2237_ = lean_box(v___x_2207_);
lean_inc_ref(v___x_2236_);
v___f_2238_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed), 17, 11);
lean_closure_set(v___f_2238_, 0, v___x_2204_);
lean_closure_set(v___f_2238_, 1, v___x_2205_);
lean_closure_set(v___f_2238_, 2, v___x_2226_);
lean_closure_set(v___f_2238_, 3, v___x_2216_);
lean_closure_set(v___f_2238_, 4, v___x_2236_);
lean_closure_set(v___f_2238_, 5, v___x_2228_);
lean_closure_set(v___f_2238_, 6, v___x_2206_);
lean_closure_set(v___f_2238_, 7, v___f_2231_);
lean_closure_set(v___f_2238_, 8, v___x_2199_);
lean_closure_set(v___f_2238_, 9, v___y_2230_);
lean_closure_set(v___f_2238_, 10, v___x_2237_);
v___x_2239_ = l_Lean_Meta_mkEq(v___x_2235_, v___x_2236_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_2242_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_2241_, v_a_2240_, v___f_2238_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
return v___x_2242_;
}
else
{
lean_dec_ref(v___f_2238_);
return v___x_2239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2247_ = _args[0];
lean_object* v_numParams_2248_ = _args[1];
lean_object* v___x_2249_ = _args[2];
lean_object* v___x_2250_ = _args[3];
lean_object* v_numIndices_2251_ = _args[4];
lean_object* v_indName_2252_ = _args[5];
lean_object* v_tail_2253_ = _args[6];
lean_object* v_i_2254_ = _args[7];
lean_object* v___x_2255_ = _args[8];
lean_object* v___x_2256_ = _args[9];
lean_object* v___x_2257_ = _args[10];
lean_object* v___x_2258_ = _args[11];
lean_object* v_xs_2259_ = _args[12];
lean_object* v_x_2260_ = _args[13];
lean_object* v___y_2261_ = _args[14];
lean_object* v___y_2262_ = _args[15];
lean_object* v___y_2263_ = _args[16];
lean_object* v___y_2264_ = _args[17];
lean_object* v___y_2265_ = _args[18];
_start:
{
uint8_t v___x_11545__boxed_2266_; lean_object* v_res_2267_; 
v___x_11545__boxed_2266_ = lean_unbox(v___x_2258_);
v_res_2267_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(v___x_2247_, v_numParams_2248_, v___x_2249_, v___x_2250_, v_numIndices_2251_, v_indName_2252_, v_tail_2253_, v_i_2254_, v___x_2255_, v___x_2256_, v___x_2257_, v___x_11545__boxed_2266_, v_xs_2259_, v_x_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_x_2260_);
lean_dec(v_numIndices_2251_);
lean_dec_ref(v___x_2249_);
return v_res_2267_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0));
v___x_2270_ = l_Lean_stringToMessageData(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2));
v___x_2273_ = l_Lean_stringToMessageData(v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4));
v___x_2276_ = l_Lean_stringToMessageData(v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(lean_object* v_attrName_2277_, lean_object* v_declName_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2284_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2285_ = l_Lean_MessageData_ofName(v_attrName_2277_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = 0;
v___x_2290_ = l_Lean_MessageData_ofConstName(v_declName_2278_, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2288_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2293_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_2295_, lean_object* v_declName_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2295_, v_declName_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
return v_res_2302_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0));
v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
return v___x_2305_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2));
v___x_2308_ = l_Lean_stringToMessageData(v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(lean_object* v_attrName_2309_, lean_object* v_declName_2310_, lean_object* v_asyncPrefix_x3f_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___y_2318_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2311_) == 0)
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_MessageData_nil;
v___y_2318_ = v___x_2331_;
goto v___jp_2317_;
}
else
{
lean_object* v_val_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_val_2332_ = lean_ctor_get(v_asyncPrefix_x3f_2311_, 0);
lean_inc(v_val_2332_);
lean_dec_ref_known(v_asyncPrefix_x3f_2311_, 1);
v___x_2333_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3);
v___x_2334_ = l_Lean_MessageData_ofName(v_val_2332_);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___y_2318_ = v___x_2337_;
goto v___jp_2317_;
}
v___jp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2319_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2320_ = l_Lean_MessageData_ofName(v_attrName_2309_);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = 0;
v___x_2325_ = l_Lean_MessageData_ofConstName(v_declName_2310_, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2323_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___y_2318_);
v___x_2330_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2329_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_2338_, lean_object* v_declName_2339_, lean_object* v_asyncPrefix_x3f_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2338_, v_declName_2339_, v_asyncPrefix_x3f_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0(lean_object* v_addEntryFn_2347_, lean_object* v_decl_2348_, lean_object* v_s_2349_){
_start:
{
lean_object* v_importedEntries_2350_; lean_object* v_state_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2359_; 
v_importedEntries_2350_ = lean_ctor_get(v_s_2349_, 0);
v_state_2351_ = lean_ctor_get(v_s_2349_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_s_2349_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2353_ = v_s_2349_;
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_state_2351_);
lean_inc(v_importedEntries_2350_);
lean_dec(v_s_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_state_2355_; lean_object* v___x_2357_; 
v_state_2355_ = lean_apply_2(v_addEntryFn_2347_, v_state_2351_, v_decl_2348_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v_state_2355_);
v___x_2357_ = v___x_2353_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_importedEntries_2350_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_state_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(lean_object* v_attr_2360_, lean_object* v_decl_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___x_2422_; lean_object* v_env_2423_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___x_2438_; 
v___x_2422_ = lean_st_ref_get(v___y_2365_);
v_env_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc_ref(v_env_2423_);
lean_dec(v___x_2422_);
v___x_2438_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2423_, v_decl_2361_);
if (lean_obj_tag(v___x_2438_) == 0)
{
v___y_2425_ = v___y_2362_;
v___y_2426_ = v___y_2363_;
v___y_2427_ = v___y_2364_;
v___y_2428_ = v___y_2365_;
goto v___jp_2424_;
}
else
{
lean_object* v_attr_2439_; lean_object* v_toAttributeImplCore_2440_; lean_object* v_name_2441_; lean_object* v___x_2442_; 
lean_dec_ref_known(v___x_2438_, 1);
lean_dec_ref(v_env_2423_);
v_attr_2439_ = lean_ctor_get(v_attr_2360_, 0);
lean_inc_ref(v_attr_2439_);
lean_dec_ref(v_attr_2360_);
v_toAttributeImplCore_2440_ = lean_ctor_get(v_attr_2439_, 0);
lean_inc_ref(v_toAttributeImplCore_2440_);
lean_dec_ref(v_attr_2439_);
v_name_2441_ = lean_ctor_get(v_toAttributeImplCore_2440_, 1);
lean_inc(v_name_2441_);
lean_dec_ref(v_toAttributeImplCore_2440_);
v___x_2442_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_name_2441_, v_decl_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
return v___x_2442_;
}
v___jp_2367_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v_mctx_2383_; lean_object* v_zetaDeltaFVarIds_2384_; lean_object* v_postponed_2385_; lean_object* v_diag_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2397_; 
v___x_2379_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
v___x_2380_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2380_, 0, v___y_2378_);
lean_ctor_set(v___x_2380_, 1, v___y_2373_);
lean_ctor_set(v___x_2380_, 2, v___y_2371_);
lean_ctor_set(v___x_2380_, 3, v___y_2377_);
lean_ctor_set(v___x_2380_, 4, v___y_2375_);
lean_ctor_set(v___x_2380_, 5, v___x_2379_);
lean_ctor_set(v___x_2380_, 6, v___y_2370_);
lean_ctor_set(v___x_2380_, 7, v___y_2376_);
lean_ctor_set(v___x_2380_, 8, v___y_2369_);
lean_ctor_set(v___x_2380_, 9, v___y_2372_);
v___x_2381_ = lean_st_ref_put(v___y_2374_, v___x_2380_);
v___x_2382_ = lean_st_ref_take(v___y_2368_);
v_mctx_2383_ = lean_ctor_get(v___x_2382_, 0);
v_zetaDeltaFVarIds_2384_ = lean_ctor_get(v___x_2382_, 2);
v_postponed_2385_ = lean_ctor_get(v___x_2382_, 3);
v_diag_2386_ = lean_ctor_get(v___x_2382_, 4);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v___x_2382_, 1);
lean_dec(v_unused_2398_);
v___x_2388_ = v___x_2382_;
v_isShared_2389_ = v_isSharedCheck_2397_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_diag_2386_);
lean_inc(v_postponed_2385_);
lean_inc(v_zetaDeltaFVarIds_2384_);
lean_inc(v_mctx_2383_);
lean_dec(v___x_2382_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2397_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 1, v___x_2391_);
v___x_2393_ = v___x_2388_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_mctx_2383_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_zetaDeltaFVarIds_2384_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_postponed_2385_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v_diag_2386_);
v___x_2393_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_st_ref_put(v___y_2368_, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2390_);
return v___x_2395_;
}
}
}
v___jp_2399_:
{
lean_object* v___x_2402_; lean_object* v_ext_2403_; lean_object* v_toEnvExtension_2404_; lean_object* v_env_2405_; lean_object* v_nextMacroScope_2406_; lean_object* v_ngen_2407_; lean_object* v_auxDeclNGen_2408_; lean_object* v_traceState_2409_; lean_object* v_recordedDeps_2410_; lean_object* v_messages_2411_; lean_object* v_infoState_2412_; lean_object* v_snapshotTasks_2413_; lean_object* v_addEntryFn_2414_; lean_object* v_asyncMode_2415_; uint8_t v_logWrites_2416_; lean_object* v___f_2417_; uint8_t v___x_2418_; 
v___x_2402_ = lean_st_ref_take(v___y_2401_);
v_ext_2403_ = lean_ctor_get(v_attr_2360_, 1);
lean_inc_ref(v_ext_2403_);
lean_dec_ref(v_attr_2360_);
v_toEnvExtension_2404_ = lean_ctor_get(v_ext_2403_, 0);
lean_inc_ref(v_toEnvExtension_2404_);
v_env_2405_ = lean_ctor_get(v___x_2402_, 0);
lean_inc_ref(v_env_2405_);
v_nextMacroScope_2406_ = lean_ctor_get(v___x_2402_, 1);
lean_inc(v_nextMacroScope_2406_);
v_ngen_2407_ = lean_ctor_get(v___x_2402_, 2);
lean_inc_ref(v_ngen_2407_);
v_auxDeclNGen_2408_ = lean_ctor_get(v___x_2402_, 3);
lean_inc_ref(v_auxDeclNGen_2408_);
v_traceState_2409_ = lean_ctor_get(v___x_2402_, 4);
lean_inc_ref(v_traceState_2409_);
v_recordedDeps_2410_ = lean_ctor_get(v___x_2402_, 6);
lean_inc_ref(v_recordedDeps_2410_);
v_messages_2411_ = lean_ctor_get(v___x_2402_, 7);
lean_inc_ref(v_messages_2411_);
v_infoState_2412_ = lean_ctor_get(v___x_2402_, 8);
lean_inc_ref(v_infoState_2412_);
v_snapshotTasks_2413_ = lean_ctor_get(v___x_2402_, 9);
lean_inc_ref(v_snapshotTasks_2413_);
lean_dec(v___x_2402_);
v_addEntryFn_2414_ = lean_ctor_get(v_ext_2403_, 3);
lean_inc(v_addEntryFn_2414_);
lean_dec_ref(v_ext_2403_);
v_asyncMode_2415_ = lean_ctor_get(v_toEnvExtension_2404_, 2);
lean_inc(v_asyncMode_2415_);
v_logWrites_2416_ = lean_ctor_get_uint8(v_toEnvExtension_2404_, sizeof(void*)*6);
lean_inc(v_decl_2361_);
v___f_2417_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2417_, 0, v_addEntryFn_2414_);
lean_closure_set(v___f_2417_, 1, v_decl_2361_);
v___x_2418_ = 1;
if (v_logWrites_2416_ == 0)
{
lean_object* v___x_2419_; 
v___x_2419_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2404_, v_env_2405_, v___f_2417_, v_asyncMode_2415_, v_decl_2361_, v___x_2418_);
lean_dec(v_asyncMode_2415_);
v___y_2368_ = v___y_2400_;
v___y_2369_ = v_infoState_2412_;
v___y_2370_ = v_recordedDeps_2410_;
v___y_2371_ = v_ngen_2407_;
v___y_2372_ = v_snapshotTasks_2413_;
v___y_2373_ = v_nextMacroScope_2406_;
v___y_2374_ = v___y_2401_;
v___y_2375_ = v_traceState_2409_;
v___y_2376_ = v_messages_2411_;
v___y_2377_ = v_auxDeclNGen_2408_;
v___y_2378_ = v___x_2419_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_inc_ref(v_toEnvExtension_2404_);
v___x_2420_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2404_, v_env_2405_);
lean_dec_ref(v_env_2405_);
v___x_2421_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2404_, v___x_2420_, v___f_2417_, v_asyncMode_2415_, v_decl_2361_, v___x_2418_);
lean_dec(v_asyncMode_2415_);
v___y_2368_ = v___y_2400_;
v___y_2369_ = v_infoState_2412_;
v___y_2370_ = v_recordedDeps_2410_;
v___y_2371_ = v_ngen_2407_;
v___y_2372_ = v_snapshotTasks_2413_;
v___y_2373_ = v_nextMacroScope_2406_;
v___y_2374_ = v___y_2401_;
v___y_2375_ = v_traceState_2409_;
v___y_2376_ = v_messages_2411_;
v___y_2377_ = v_auxDeclNGen_2408_;
v___y_2378_ = v___x_2421_;
goto v___jp_2367_;
}
}
v___jp_2424_:
{
lean_object* v_ext_2429_; lean_object* v_toEnvExtension_2430_; lean_object* v_attr_2431_; lean_object* v_asyncMode_2432_; uint8_t v___x_2433_; 
v_ext_2429_ = lean_ctor_get(v_attr_2360_, 1);
v_toEnvExtension_2430_ = lean_ctor_get(v_ext_2429_, 0);
v_attr_2431_ = lean_ctor_get(v_attr_2360_, 0);
v_asyncMode_2432_ = lean_ctor_get(v_toEnvExtension_2430_, 2);
lean_inc(v_decl_2361_);
lean_inc_ref(v_env_2423_);
v___x_2433_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2423_, v_decl_2361_, v_asyncMode_2432_);
if (v___x_2433_ == 0)
{
lean_object* v_toAttributeImplCore_2434_; lean_object* v_name_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_inc_ref(v_attr_2431_);
lean_dec_ref(v_attr_2360_);
v_toAttributeImplCore_2434_ = lean_ctor_get(v_attr_2431_, 0);
lean_inc_ref(v_toAttributeImplCore_2434_);
lean_dec_ref(v_attr_2431_);
v_name_2435_ = lean_ctor_get(v_toAttributeImplCore_2434_, 1);
lean_inc(v_name_2435_);
lean_dec_ref(v_toAttributeImplCore_2434_);
v___x_2436_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2423_);
v___x_2437_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_name_2435_, v_decl_2361_, v___x_2436_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2437_;
}
else
{
lean_dec_ref(v_env_2423_);
v___y_2400_ = v___y_2426_;
v___y_2401_ = v___y_2428_;
goto v___jp_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___boxed(lean_object* v_attr_2443_, lean_object* v_decl_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v_attr_2443_, v_decl_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(lean_object* v_val_2451_, lean_object* v_indName_2452_, lean_object* v_tail_2453_, lean_object* v___x_2454_, lean_object* v___x_2455_, lean_object* v___x_2456_, lean_object* v_a_2457_, lean_object* v_range_2458_, lean_object* v_b_2459_, lean_object* v_i_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_stop_2466_; lean_object* v_step_2467_; uint8_t v___x_2468_; 
v_stop_2466_ = lean_ctor_get(v_range_2458_, 1);
v_step_2467_ = lean_ctor_get(v_range_2458_, 2);
v___x_2468_ = lean_nat_dec_lt(v_i_2460_, v_stop_2466_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
lean_dec(v_i_2460_);
lean_dec_ref(v_a_2457_);
lean_dec(v___x_2456_);
lean_dec(v___x_2455_);
lean_dec(v___x_2454_);
lean_dec(v_tail_2453_);
lean_dec(v_indName_2452_);
lean_dec_ref(v_val_2451_);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_b_2459_);
return v___x_2469_;
}
else
{
lean_object* v_numParams_2470_; lean_object* v_numIndices_2471_; lean_object* v_ctors_2472_; lean_object* v_levelParams_2473_; lean_object* v_type_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; 
v_numParams_2470_ = lean_ctor_get(v_val_2451_, 1);
v_numIndices_2471_ = lean_ctor_get(v_val_2451_, 2);
v_ctors_2472_ = lean_ctor_get(v_val_2451_, 4);
v_levelParams_2473_ = lean_ctor_get(v_a_2457_, 1);
v_type_2474_ = lean_ctor_get(v_a_2457_, 2);
v___x_2475_ = lean_unsigned_to_nat(0u);
v___x_2476_ = l_Lean_instInhabitedExpr;
v___x_2477_ = lean_unsigned_to_nat(1u);
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_box(0);
v___x_2480_ = lean_box(v___x_2468_);
lean_inc(v___x_2456_);
lean_inc(v___x_2455_);
lean_inc(v___x_2454_);
lean_inc_n(v_i_2460_, 2);
lean_inc(v_tail_2453_);
lean_inc_n(v_indName_2452_, 2);
lean_inc(v_numIndices_2471_);
lean_inc(v_numParams_2470_);
v___f_2481_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed), 19, 12);
lean_closure_set(v___f_2481_, 0, v___x_2475_);
lean_closure_set(v___f_2481_, 1, v_numParams_2470_);
lean_closure_set(v___f_2481_, 2, v___x_2476_);
lean_closure_set(v___f_2481_, 3, v___x_2477_);
lean_closure_set(v___f_2481_, 4, v_numIndices_2471_);
lean_closure_set(v___f_2481_, 5, v_indName_2452_);
lean_closure_set(v___f_2481_, 6, v_tail_2453_);
lean_closure_set(v___f_2481_, 7, v_i_2460_);
lean_closure_set(v___f_2481_, 8, v___x_2454_);
lean_closure_set(v___f_2481_, 9, v___x_2455_);
lean_closure_set(v___f_2481_, 10, v___x_2456_);
lean_closure_set(v___f_2481_, 11, v___x_2480_);
v___x_2482_ = l_List_get_x21Internal___redArg(v___x_2478_, v_ctors_2472_, v_i_2460_);
v___x_2483_ = l_Lean_mkConstructorElimName(v_indName_2452_, v___x_2482_);
v___x_2484_ = 0;
lean_inc_ref(v_type_2474_);
v___x_2485_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_2474_, v___f_2481_, v___x_2484_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2487_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc_n(v_a_2486_, 2);
lean_dec_ref_known(v___x_2485_, 1);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
v___x_2487_ = lean_infer_type(v_a_2486_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2642_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2489_ = lean_box(1);
lean_inc(v_levelParams_2473_);
lean_inc(v___x_2483_);
v___x_2490_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_2483_, v_levelParams_2473_, v_a_2488_, v_a_2486_, v___x_2489_, v___y_2464_);
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2642_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2642_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_addAndCompile(v___x_2496_, v___x_2468_, v___x_2484_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; lean_object* v_env_2499_; lean_object* v_nextMacroScope_2500_; lean_object* v_ngen_2501_; lean_object* v_auxDeclNGen_2502_; lean_object* v_traceState_2503_; lean_object* v_recordedDeps_2504_; lean_object* v_messages_2505_; lean_object* v_infoState_2506_; lean_object* v_snapshotTasks_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref_known(v___x_2497_, 1);
v___x_2498_ = lean_st_ref_take(v___y_2464_);
v_env_2499_ = lean_ctor_get(v___x_2498_, 0);
v_nextMacroScope_2500_ = lean_ctor_get(v___x_2498_, 1);
v_ngen_2501_ = lean_ctor_get(v___x_2498_, 2);
v_auxDeclNGen_2502_ = lean_ctor_get(v___x_2498_, 3);
v_traceState_2503_ = lean_ctor_get(v___x_2498_, 4);
v_recordedDeps_2504_ = lean_ctor_get(v___x_2498_, 6);
v_messages_2505_ = lean_ctor_get(v___x_2498_, 7);
v_infoState_2506_ = lean_ctor_get(v___x_2498_, 8);
v_snapshotTasks_2507_ = lean_ctor_get(v___x_2498_, 9);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; 
v_unused_2640_ = lean_ctor_get(v___x_2498_, 5);
lean_dec(v_unused_2640_);
v___x_2509_ = v___x_2498_;
v_isShared_2510_ = v_isSharedCheck_2639_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_snapshotTasks_2507_);
lean_inc(v_infoState_2506_);
lean_inc(v_messages_2505_);
lean_inc(v_recordedDeps_2504_);
lean_inc(v_traceState_2503_);
lean_inc(v_auxDeclNGen_2502_);
lean_inc(v_ngen_2501_);
lean_inc(v_nextMacroScope_2500_);
lean_inc(v_env_2499_);
lean_dec(v___x_2498_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2639_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
lean_inc(v___x_2483_);
v___x_2511_ = l_Lean_markAuxRecursor(v_env_2499_, v___x_2483_);
v___x_2512_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 5, v___x_2512_);
lean_ctor_set(v___x_2509_, 0, v___x_2511_);
v___x_2514_ = v___x_2509_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_nextMacroScope_2500_);
lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_ngen_2501_);
lean_ctor_set(v_reuseFailAlloc_2638_, 3, v_auxDeclNGen_2502_);
lean_ctor_set(v_reuseFailAlloc_2638_, 4, v_traceState_2503_);
lean_ctor_set(v_reuseFailAlloc_2638_, 5, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2638_, 6, v_recordedDeps_2504_);
lean_ctor_set(v_reuseFailAlloc_2638_, 7, v_messages_2505_);
lean_ctor_set(v_reuseFailAlloc_2638_, 8, v_infoState_2506_);
lean_ctor_set(v_reuseFailAlloc_2638_, 9, v_snapshotTasks_2507_);
v___x_2514_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v_mctx_2517_; lean_object* v_zetaDeltaFVarIds_2518_; lean_object* v_postponed_2519_; lean_object* v_diag_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2636_; 
v___x_2515_ = lean_st_ref_put(v___y_2464_, v___x_2514_);
v___x_2516_ = lean_st_ref_take(v___y_2462_);
v_mctx_2517_ = lean_ctor_get(v___x_2516_, 0);
v_zetaDeltaFVarIds_2518_ = lean_ctor_get(v___x_2516_, 2);
v_postponed_2519_ = lean_ctor_get(v___x_2516_, 3);
v_diag_2520_ = lean_ctor_get(v___x_2516_, 4);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v___x_2516_, 1);
lean_dec(v_unused_2637_);
v___x_2522_ = v___x_2516_;
v_isShared_2523_ = v_isSharedCheck_2636_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_diag_2520_);
lean_inc(v_postponed_2519_);
lean_inc(v_zetaDeltaFVarIds_2518_);
lean_inc(v_mctx_2517_);
lean_dec(v___x_2516_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2636_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2524_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 1, v___x_2524_);
v___x_2526_ = v___x_2522_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_mctx_2517_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v_zetaDeltaFVarIds_2518_);
lean_ctor_set(v_reuseFailAlloc_2635_, 3, v_postponed_2519_);
lean_ctor_set(v_reuseFailAlloc_2635_, 4, v_diag_2520_);
v___x_2526_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_env_2529_; lean_object* v_nextMacroScope_2530_; lean_object* v_ngen_2531_; lean_object* v_auxDeclNGen_2532_; lean_object* v_traceState_2533_; lean_object* v_recordedDeps_2534_; lean_object* v_messages_2535_; lean_object* v_infoState_2536_; lean_object* v_snapshotTasks_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2633_; 
v___x_2527_ = lean_st_ref_put(v___y_2462_, v___x_2526_);
v___x_2528_ = lean_st_ref_take(v___y_2464_);
v_env_2529_ = lean_ctor_get(v___x_2528_, 0);
v_nextMacroScope_2530_ = lean_ctor_get(v___x_2528_, 1);
v_ngen_2531_ = lean_ctor_get(v___x_2528_, 2);
v_auxDeclNGen_2532_ = lean_ctor_get(v___x_2528_, 3);
v_traceState_2533_ = lean_ctor_get(v___x_2528_, 4);
v_recordedDeps_2534_ = lean_ctor_get(v___x_2528_, 6);
v_messages_2535_ = lean_ctor_get(v___x_2528_, 7);
v_infoState_2536_ = lean_ctor_get(v___x_2528_, 8);
v_snapshotTasks_2537_ = lean_ctor_get(v___x_2528_, 9);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; 
v_unused_2634_ = lean_ctor_get(v___x_2528_, 5);
lean_dec(v_unused_2634_);
v___x_2539_ = v___x_2528_;
v_isShared_2540_ = v_isSharedCheck_2633_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_snapshotTasks_2537_);
lean_inc(v_infoState_2536_);
lean_inc(v_messages_2535_);
lean_inc(v_recordedDeps_2534_);
lean_inc(v_traceState_2533_);
lean_inc(v_auxDeclNGen_2532_);
lean_inc(v_ngen_2531_);
lean_inc(v_nextMacroScope_2530_);
lean_inc(v_env_2529_);
lean_dec(v___x_2528_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2633_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_inc(v___x_2483_);
v___x_2541_ = l_Lean_markSparseCasesOn(v_env_2529_, v___x_2483_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 5, v___x_2512_);
lean_ctor_set(v___x_2539_, 0, v___x_2541_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_nextMacroScope_2530_);
lean_ctor_set(v_reuseFailAlloc_2632_, 2, v_ngen_2531_);
lean_ctor_set(v_reuseFailAlloc_2632_, 3, v_auxDeclNGen_2532_);
lean_ctor_set(v_reuseFailAlloc_2632_, 4, v_traceState_2533_);
lean_ctor_set(v_reuseFailAlloc_2632_, 5, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2632_, 6, v_recordedDeps_2534_);
lean_ctor_set(v_reuseFailAlloc_2632_, 7, v_messages_2535_);
lean_ctor_set(v_reuseFailAlloc_2632_, 8, v_infoState_2536_);
lean_ctor_set(v_reuseFailAlloc_2632_, 9, v_snapshotTasks_2537_);
v___x_2543_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_mctx_2546_; lean_object* v_zetaDeltaFVarIds_2547_; lean_object* v_postponed_2548_; lean_object* v_diag_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2630_; 
v___x_2544_ = lean_st_ref_put(v___y_2464_, v___x_2543_);
v___x_2545_ = lean_st_ref_take(v___y_2462_);
v_mctx_2546_ = lean_ctor_get(v___x_2545_, 0);
v_zetaDeltaFVarIds_2547_ = lean_ctor_get(v___x_2545_, 2);
v_postponed_2548_ = lean_ctor_get(v___x_2545_, 3);
v_diag_2549_ = lean_ctor_get(v___x_2545_, 4);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v___x_2545_, 1);
lean_dec(v_unused_2631_);
v___x_2551_ = v___x_2545_;
v_isShared_2552_ = v_isSharedCheck_2630_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_diag_2549_);
lean_inc(v_postponed_2548_);
lean_inc(v_zetaDeltaFVarIds_2547_);
lean_inc(v_mctx_2546_);
lean_dec(v___x_2545_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2630_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 1, v___x_2524_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_mctx_2546_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_zetaDeltaFVarIds_2547_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v_postponed_2548_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_diag_2549_);
v___x_2554_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v_env_2557_; lean_object* v_nextMacroScope_2558_; lean_object* v_ngen_2559_; lean_object* v_auxDeclNGen_2560_; lean_object* v_traceState_2561_; lean_object* v_recordedDeps_2562_; lean_object* v_messages_2563_; lean_object* v_infoState_2564_; lean_object* v_snapshotTasks_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2627_; 
v___x_2555_ = lean_st_ref_put(v___y_2462_, v___x_2554_);
v___x_2556_ = lean_st_ref_take(v___y_2464_);
v_env_2557_ = lean_ctor_get(v___x_2556_, 0);
v_nextMacroScope_2558_ = lean_ctor_get(v___x_2556_, 1);
v_ngen_2559_ = lean_ctor_get(v___x_2556_, 2);
v_auxDeclNGen_2560_ = lean_ctor_get(v___x_2556_, 3);
v_traceState_2561_ = lean_ctor_get(v___x_2556_, 4);
v_recordedDeps_2562_ = lean_ctor_get(v___x_2556_, 6);
v_messages_2563_ = lean_ctor_get(v___x_2556_, 7);
v_infoState_2564_ = lean_ctor_get(v___x_2556_, 8);
v_snapshotTasks_2565_ = lean_ctor_get(v___x_2556_, 9);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v___x_2556_, 5);
lean_dec(v_unused_2628_);
v___x_2567_ = v___x_2556_;
v_isShared_2568_ = v_isSharedCheck_2627_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_snapshotTasks_2565_);
lean_inc(v_infoState_2564_);
lean_inc(v_messages_2563_);
lean_inc(v_recordedDeps_2562_);
lean_inc(v_traceState_2561_);
lean_inc(v_auxDeclNGen_2560_);
lean_inc(v_ngen_2559_);
lean_inc(v_nextMacroScope_2558_);
lean_inc(v_env_2557_);
lean_dec(v___x_2556_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2627_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
lean_inc(v___x_2483_);
v___x_2569_ = l_Lean_Meta_addToCompletionBlackList(v_env_2557_, v___x_2483_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 5, v___x_2512_);
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_nextMacroScope_2558_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_ngen_2559_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_auxDeclNGen_2560_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v_traceState_2561_);
lean_ctor_set(v_reuseFailAlloc_2626_, 5, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2626_, 6, v_recordedDeps_2562_);
lean_ctor_set(v_reuseFailAlloc_2626_, 7, v_messages_2563_);
lean_ctor_set(v_reuseFailAlloc_2626_, 8, v_infoState_2564_);
lean_ctor_set(v_reuseFailAlloc_2626_, 9, v_snapshotTasks_2565_);
v___x_2571_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_mctx_2574_; lean_object* v_zetaDeltaFVarIds_2575_; lean_object* v_postponed_2576_; lean_object* v_diag_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2624_; 
v___x_2572_ = lean_st_ref_put(v___y_2464_, v___x_2571_);
v___x_2573_ = lean_st_ref_take(v___y_2462_);
v_mctx_2574_ = lean_ctor_get(v___x_2573_, 0);
v_zetaDeltaFVarIds_2575_ = lean_ctor_get(v___x_2573_, 2);
v_postponed_2576_ = lean_ctor_get(v___x_2573_, 3);
v_diag_2577_ = lean_ctor_get(v___x_2573_, 4);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; 
v_unused_2625_ = lean_ctor_get(v___x_2573_, 1);
lean_dec(v_unused_2625_);
v___x_2579_ = v___x_2573_;
v_isShared_2580_ = v_isSharedCheck_2624_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_diag_2577_);
lean_inc(v_postponed_2576_);
lean_inc(v_zetaDeltaFVarIds_2575_);
lean_inc(v_mctx_2574_);
lean_dec(v___x_2573_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2624_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 1, v___x_2524_);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_mctx_2574_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_zetaDeltaFVarIds_2575_);
lean_ctor_set(v_reuseFailAlloc_2623_, 3, v_postponed_2576_);
lean_ctor_set(v_reuseFailAlloc_2623_, 4, v_diag_2577_);
v___x_2582_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_env_2585_; lean_object* v_nextMacroScope_2586_; lean_object* v_ngen_2587_; lean_object* v_auxDeclNGen_2588_; lean_object* v_traceState_2589_; lean_object* v_recordedDeps_2590_; lean_object* v_messages_2591_; lean_object* v_infoState_2592_; lean_object* v_snapshotTasks_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2621_; 
v___x_2583_ = lean_st_ref_put(v___y_2462_, v___x_2582_);
v___x_2584_ = lean_st_ref_take(v___y_2464_);
v_env_2585_ = lean_ctor_get(v___x_2584_, 0);
v_nextMacroScope_2586_ = lean_ctor_get(v___x_2584_, 1);
v_ngen_2587_ = lean_ctor_get(v___x_2584_, 2);
v_auxDeclNGen_2588_ = lean_ctor_get(v___x_2584_, 3);
v_traceState_2589_ = lean_ctor_get(v___x_2584_, 4);
v_recordedDeps_2590_ = lean_ctor_get(v___x_2584_, 6);
v_messages_2591_ = lean_ctor_get(v___x_2584_, 7);
v_infoState_2592_ = lean_ctor_get(v___x_2584_, 8);
v_snapshotTasks_2593_ = lean_ctor_get(v___x_2584_, 9);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v___x_2584_, 5);
lean_dec(v_unused_2622_);
v___x_2595_ = v___x_2584_;
v_isShared_2596_ = v_isSharedCheck_2621_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_snapshotTasks_2593_);
lean_inc(v_infoState_2592_);
lean_inc(v_messages_2591_);
lean_inc(v_recordedDeps_2590_);
lean_inc(v_traceState_2589_);
lean_inc(v_auxDeclNGen_2588_);
lean_inc(v_ngen_2587_);
lean_inc(v_nextMacroScope_2586_);
lean_inc(v_env_2585_);
lean_dec(v___x_2584_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2621_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_inc(v___x_2483_);
v___x_2597_ = l_Lean_addProtected(v_env_2585_, v___x_2483_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 5, v___x_2512_);
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_nextMacroScope_2586_);
lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_ngen_2587_);
lean_ctor_set(v_reuseFailAlloc_2620_, 3, v_auxDeclNGen_2588_);
lean_ctor_set(v_reuseFailAlloc_2620_, 4, v_traceState_2589_);
lean_ctor_set(v_reuseFailAlloc_2620_, 5, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2620_, 6, v_recordedDeps_2590_);
lean_ctor_set(v_reuseFailAlloc_2620_, 7, v_messages_2591_);
lean_ctor_set(v_reuseFailAlloc_2620_, 8, v_infoState_2592_);
lean_ctor_set(v_reuseFailAlloc_2620_, 9, v_snapshotTasks_2593_);
v___x_2599_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_mctx_2602_; lean_object* v_zetaDeltaFVarIds_2603_; lean_object* v_postponed_2604_; lean_object* v_diag_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2618_; 
v___x_2600_ = lean_st_ref_put(v___y_2464_, v___x_2599_);
v___x_2601_ = lean_st_ref_take(v___y_2462_);
v_mctx_2602_ = lean_ctor_get(v___x_2601_, 0);
v_zetaDeltaFVarIds_2603_ = lean_ctor_get(v___x_2601_, 2);
v_postponed_2604_ = lean_ctor_get(v___x_2601_, 3);
v_diag_2605_ = lean_ctor_get(v___x_2601_, 4);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v___x_2601_, 1);
lean_dec(v_unused_2619_);
v___x_2607_ = v___x_2601_;
v_isShared_2608_ = v_isSharedCheck_2618_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_diag_2605_);
lean_inc(v_postponed_2604_);
lean_inc(v_zetaDeltaFVarIds_2603_);
lean_inc(v_mctx_2602_);
lean_dec(v___x_2601_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2618_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 1, v___x_2524_);
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_mctx_2602_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_zetaDeltaFVarIds_2603_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v_postponed_2604_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v_diag_2605_);
v___x_2610_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_st_ref_put(v___y_2462_, v___x_2610_);
v___x_2612_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v___x_2483_);
v___x_2613_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v___x_2612_, v___x_2483_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec_ref_known(v___x_2613_, 1);
v___x_2614_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2483_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec_ref(v___x_2614_);
v___x_2615_ = lean_nat_add(v_i_2460_, v_step_2467_);
lean_dec(v_i_2460_);
v_b_2459_ = v___x_2479_;
v_i_2460_ = v___x_2615_;
goto _start;
}
else
{
lean_dec(v___x_2483_);
lean_dec(v_i_2460_);
lean_dec_ref(v_a_2457_);
lean_dec(v___x_2456_);
lean_dec(v___x_2455_);
lean_dec(v___x_2454_);
lean_dec(v_tail_2453_);
lean_dec(v_indName_2452_);
lean_dec_ref(v_val_2451_);
return v___x_2613_;
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
lean_dec(v___x_2483_);
lean_dec(v_i_2460_);
lean_dec_ref(v_a_2457_);
lean_dec(v___x_2456_);
lean_dec(v___x_2455_);
lean_dec(v___x_2454_);
lean_dec(v_tail_2453_);
lean_dec(v_indName_2452_);
lean_dec_ref(v_val_2451_);
return v___x_2497_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_a_2486_);
lean_dec(v___x_2483_);
lean_dec(v_i_2460_);
lean_dec_ref(v_a_2457_);
lean_dec(v___x_2456_);
lean_dec(v___x_2455_);
lean_dec(v___x_2454_);
lean_dec(v_tail_2453_);
lean_dec(v_indName_2452_);
lean_dec_ref(v_val_2451_);
v_a_2643_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2487_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2487_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v___x_2483_);
lean_dec(v_i_2460_);
lean_dec_ref(v_a_2457_);
lean_dec(v___x_2456_);
lean_dec(v___x_2455_);
lean_dec(v___x_2454_);
lean_dec(v_tail_2453_);
lean_dec(v_indName_2452_);
lean_dec_ref(v_val_2451_);
v_a_2651_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2485_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2485_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___boxed(lean_object* v_val_2659_, lean_object* v_indName_2660_, lean_object* v_tail_2661_, lean_object* v___x_2662_, lean_object* v___x_2663_, lean_object* v___x_2664_, lean_object* v_a_2665_, lean_object* v_range_2666_, lean_object* v_b_2667_, lean_object* v_i_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2659_, v_indName_2660_, v_tail_2661_, v___x_2662_, v___x_2663_, v___x_2664_, v_a_2665_, v_range_2666_, v_b_2667_, v_i_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec_ref(v_range_2666_);
return v_res_2674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2676_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_2677_ = lean_unsigned_to_nat(58u);
v___x_2678_ = lean_unsigned_to_nat(169u);
v___x_2679_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2680_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2681_ = l_mkPanicMessageWithDecl(v___x_2680_, v___x_2679_, v___x_2678_, v___x_2677_, v___x_2676_);
return v___x_2681_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2682_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_2683_ = lean_unsigned_to_nat(60u);
v___x_2684_ = lean_unsigned_to_nat(166u);
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2686_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2687_ = l_mkPanicMessageWithDecl(v___x_2686_, v___x_2685_, v___x_2684_, v___x_2683_, v___x_2682_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(lean_object* v_indName_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v___x_2694_; 
lean_inc(v_indName_2688_);
v___x_2694_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
if (lean_obj_tag(v_a_2695_) == 5)
{
lean_object* v_val_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_val_2696_ = lean_ctor_get(v_a_2695_, 0);
lean_inc_ref(v_val_2696_);
lean_dec_ref_known(v_a_2695_, 1);
lean_inc(v_indName_2688_);
v___x_2697_ = l_Lean_mkCasesOnName(v_indName_2688_);
lean_inc(v___x_2697_);
v___x_2698_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2697_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v_levelParams_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2737_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v_levelParams_2700_ = lean_ctor_get(v_a_2699_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_a_2699_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; lean_object* v_unused_2739_; 
v_unused_2738_ = lean_ctor_get(v_a_2699_, 2);
lean_dec(v_unused_2738_);
v_unused_2739_ = lean_ctor_get(v_a_2699_, 0);
lean_dec(v_unused_2739_);
v___x_2702_ = v_a_2699_;
v_isShared_2703_ = v_isSharedCheck_2737_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_levelParams_2700_);
lean_dec(v_a_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2737_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_box(0);
v___x_2705_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_2700_, v___x_2704_);
if (lean_obj_tag(v___x_2705_) == 1)
{
lean_object* v_tail_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_tail_2706_ = lean_ctor_get(v___x_2705_, 1);
lean_inc(v_tail_2706_);
lean_inc_n(v_indName_2688_, 2);
v___x_2707_ = l_Lean_mkCtorElimName(v_indName_2688_);
v___x_2708_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_2688_);
v___x_2709_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2697_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = l_Lean_InductiveVal_numCtors(v_val_2696_);
v___x_2713_ = lean_unsigned_to_nat(1u);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 2, v___x_2713_);
lean_ctor_set(v___x_2702_, 1, v___x_2712_);
lean_ctor_set(v___x_2702_, 0, v___x_2711_);
v___x_2715_ = v___x_2702_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_box(0);
v___x_2717_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2696_, v_indName_2688_, v_tail_2706_, v___x_2707_, v___x_2705_, v___x_2708_, v_a_2710_, v___x_2715_, v___x_2716_, v___x_2711_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec_ref(v___x_2715_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; 
v_unused_2725_ = lean_ctor_get(v___x_2717_, 0);
lean_dec(v_unused_2725_);
v___x_2719_ = v___x_2717_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_dec(v___x_2717_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2716_);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2716_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
return v___x_2717_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v___x_2708_);
lean_dec(v___x_2707_);
lean_dec(v_tail_2706_);
lean_dec_ref_known(v___x_2705_, 2);
lean_del_object(v___x_2702_);
lean_dec_ref(v_val_2696_);
lean_dec(v_indName_2688_);
v_a_2727_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2709_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2709_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec(v___x_2705_);
lean_del_object(v___x_2702_);
lean_dec(v___x_2697_);
lean_dec_ref(v_val_2696_);
lean_dec(v_indName_2688_);
v___x_2735_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1);
v___x_2736_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_2735_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
return v___x_2736_;
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v___x_2697_);
lean_dec_ref(v_val_2696_);
lean_dec(v_indName_2688_);
v_a_2740_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2698_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2698_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
else
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec(v_a_2695_);
lean_dec(v_indName_2688_);
v___x_2748_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2);
v___x_2749_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__8(v___x_2748_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
return v___x_2749_;
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_indName_2688_);
v_a_2750_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2694_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2694_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___boxed(lean_object* v_indName_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(lean_object* v_val_2765_, lean_object* v_indName_2766_, lean_object* v_tail_2767_, lean_object* v___x_2768_, lean_object* v___x_2769_, lean_object* v___x_2770_, lean_object* v_a_2771_, lean_object* v_range_2772_, lean_object* v_b_2773_, lean_object* v_i_2774_, lean_object* v_hs_2775_, lean_object* v_hl_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2765_, v_indName_2766_, v_tail_2767_, v___x_2768_, v___x_2769_, v___x_2770_, v_a_2771_, v_range_2772_, v_b_2773_, v_i_2774_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___boxed(lean_object** _args){
lean_object* v_val_2783_ = _args[0];
lean_object* v_indName_2784_ = _args[1];
lean_object* v_tail_2785_ = _args[2];
lean_object* v___x_2786_ = _args[3];
lean_object* v___x_2787_ = _args[4];
lean_object* v___x_2788_ = _args[5];
lean_object* v_a_2789_ = _args[6];
lean_object* v_range_2790_ = _args[7];
lean_object* v_b_2791_ = _args[8];
lean_object* v_i_2792_ = _args[9];
lean_object* v_hs_2793_ = _args[10];
lean_object* v_hl_2794_ = _args[11];
lean_object* v___y_2795_ = _args[12];
lean_object* v___y_2796_ = _args[13];
lean_object* v___y_2797_ = _args[14];
lean_object* v___y_2798_ = _args[15];
lean_object* v___y_2799_ = _args[16];
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(v_val_2783_, v_indName_2784_, v_tail_2785_, v___x_2786_, v___x_2787_, v___x_2788_, v_a_2789_, v_range_2790_, v_b_2791_, v_i_2792_, v_hs_2793_, v_hl_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v_range_2790_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(lean_object* v_00_u03b1_2801_, lean_object* v_attrName_2802_, lean_object* v_declName_2803_, lean_object* v_asyncPrefix_x3f_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2802_, v_declName_2803_, v_asyncPrefix_x3f_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2811_, lean_object* v_attrName_2812_, lean_object* v_declName_2813_, lean_object* v_asyncPrefix_x3f_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(v_00_u03b1_2811_, v_attrName_2812_, v_declName_2813_, v_asyncPrefix_x3f_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(lean_object* v_00_u03b1_2821_, lean_object* v_attrName_2822_, lean_object* v_declName_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2822_, v_declName_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_attrName_2831_, lean_object* v_declName_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(v_00_u03b1_2830_, v_attrName_2831_, v_declName_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0(lean_object* v_indName_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___x_2845_; 
lean_inc(v_indName_2839_);
v___x_2845_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v___x_2846_; 
lean_dec_ref_known(v___x_2845_, 1);
lean_inc(v_indName_2839_);
v___x_2846_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v___x_2847_; 
lean_dec_ref_known(v___x_2846_, 1);
v___x_2847_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
return v___x_2847_;
}
else
{
lean_dec(v_indName_2839_);
return v___x_2846_;
}
}
else
{
lean_dec(v_indName_2839_);
return v___x_2845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object* v_indName_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Lean_mkCtorElim___lam__0(v_indName_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(lean_object* v_declName_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
lean_inc(v_declName_2855_);
v___x_2861_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_declName_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2897_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2897_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2897_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
if (lean_obj_tag(v_a_2862_) == 5)
{
lean_object* v_val_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_del_object(v___x_2864_);
v_val_2866_ = lean_ctor_get(v_a_2862_, 0);
lean_inc_ref(v_val_2866_);
lean_dec_ref_known(v_a_2862_, 1);
v___x_2867_ = l_Lean_mkRecName(v_declName_2855_);
v___x_2868_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v___x_2867_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_toConstantVal_2869_; lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2883_; 
v_toConstantVal_2869_ = lean_ctor_get(v_val_2866_, 0);
lean_inc_ref(v_toConstantVal_2869_);
lean_dec_ref(v_val_2866_);
v_a_2870_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2872_ = v___x_2868_;
v_isShared_2873_ = v_isSharedCheck_2883_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2868_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2883_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_levelParams_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v_levelParams_2874_ = lean_ctor_get(v_toConstantVal_2869_, 1);
lean_inc(v_levelParams_2874_);
lean_dec_ref(v_toConstantVal_2869_);
v___x_2875_ = l_List_lengthTR___redArg(v_levelParams_2874_);
lean_dec(v_levelParams_2874_);
v___x_2876_ = l_Lean_ConstantInfo_levelParams(v_a_2870_);
lean_dec(v_a_2870_);
v___x_2877_ = l_List_lengthTR___redArg(v___x_2876_);
lean_dec(v___x_2876_);
v___x_2878_ = lean_nat_dec_lt(v___x_2875_, v___x_2877_);
lean_dec(v___x_2877_);
lean_dec(v___x_2875_);
v___x_2879_ = lean_box(v___x_2878_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2879_);
v___x_2881_ = v___x_2872_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec_ref(v_val_2866_);
v_a_2884_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2868_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2868_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_dec(v_a_2862_);
lean_dec(v_declName_2855_);
v___x_2892_ = 0;
v___x_2893_ = lean_box(v___x_2892_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2893_);
v___x_2895_ = v___x_2864_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_declName_2855_);
v_a_2898_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2861_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2861_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0___boxed(lean_object* v_declName_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_declName_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(lean_object* v___y_2913_, uint8_t v_isExporting_2914_, lean_object* v___x_2915_, lean_object* v___y_2916_, lean_object* v___x_2917_, lean_object* v_a_x3f_2918_){
_start:
{
lean_object* v___x_2920_; lean_object* v_env_2921_; lean_object* v_nextMacroScope_2922_; lean_object* v_ngen_2923_; lean_object* v_auxDeclNGen_2924_; lean_object* v_traceState_2925_; lean_object* v_recordedDeps_2926_; lean_object* v_messages_2927_; lean_object* v_infoState_2928_; lean_object* v_snapshotTasks_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2954_; 
v___x_2920_ = lean_st_ref_take(v___y_2913_);
v_env_2921_ = lean_ctor_get(v___x_2920_, 0);
v_nextMacroScope_2922_ = lean_ctor_get(v___x_2920_, 1);
v_ngen_2923_ = lean_ctor_get(v___x_2920_, 2);
v_auxDeclNGen_2924_ = lean_ctor_get(v___x_2920_, 3);
v_traceState_2925_ = lean_ctor_get(v___x_2920_, 4);
v_recordedDeps_2926_ = lean_ctor_get(v___x_2920_, 6);
v_messages_2927_ = lean_ctor_get(v___x_2920_, 7);
v_infoState_2928_ = lean_ctor_get(v___x_2920_, 8);
v_snapshotTasks_2929_ = lean_ctor_get(v___x_2920_, 9);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v___x_2920_, 5);
lean_dec(v_unused_2955_);
v___x_2931_ = v___x_2920_;
v_isShared_2932_ = v_isSharedCheck_2954_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_snapshotTasks_2929_);
lean_inc(v_infoState_2928_);
lean_inc(v_messages_2927_);
lean_inc(v_recordedDeps_2926_);
lean_inc(v_traceState_2925_);
lean_inc(v_auxDeclNGen_2924_);
lean_inc(v_ngen_2923_);
lean_inc(v_nextMacroScope_2922_);
lean_inc(v_env_2921_);
lean_dec(v___x_2920_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2954_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = l_Lean_Environment_setExporting(v_env_2921_, v_isExporting_2914_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 5, v___x_2915_);
lean_ctor_set(v___x_2931_, 0, v___x_2933_);
v___x_2935_ = v___x_2931_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_nextMacroScope_2922_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_ngen_2923_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_auxDeclNGen_2924_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_traceState_2925_);
lean_ctor_set(v_reuseFailAlloc_2953_, 5, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2953_, 6, v_recordedDeps_2926_);
lean_ctor_set(v_reuseFailAlloc_2953_, 7, v_messages_2927_);
lean_ctor_set(v_reuseFailAlloc_2953_, 8, v_infoState_2928_);
lean_ctor_set(v_reuseFailAlloc_2953_, 9, v_snapshotTasks_2929_);
v___x_2935_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v_mctx_2938_; lean_object* v_zetaDeltaFVarIds_2939_; lean_object* v_postponed_2940_; lean_object* v_diag_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2951_; 
v___x_2936_ = lean_st_ref_put(v___y_2913_, v___x_2935_);
v___x_2937_ = lean_st_ref_take(v___y_2916_);
v_mctx_2938_ = lean_ctor_get(v___x_2937_, 0);
v_zetaDeltaFVarIds_2939_ = lean_ctor_get(v___x_2937_, 2);
v_postponed_2940_ = lean_ctor_get(v___x_2937_, 3);
v_diag_2941_ = lean_ctor_get(v___x_2937_, 4);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; 
v_unused_2952_ = lean_ctor_get(v___x_2937_, 1);
lean_dec(v_unused_2952_);
v___x_2943_ = v___x_2937_;
v_isShared_2944_ = v_isSharedCheck_2951_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_diag_2941_);
lean_inc(v_postponed_2940_);
lean_inc(v_zetaDeltaFVarIds_2939_);
lean_inc(v_mctx_2938_);
lean_dec(v___x_2937_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2951_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = lean_box(0);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v___x_2917_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_mctx_2938_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2950_, 2, v_zetaDeltaFVarIds_2939_);
lean_ctor_set(v_reuseFailAlloc_2950_, 3, v_postponed_2940_);
lean_ctor_set(v_reuseFailAlloc_2950_, 4, v_diag_2941_);
v___x_2947_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = lean_st_ref_put(v___y_2916_, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2945_);
return v___x_2949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2956_, lean_object* v_isExporting_2957_, lean_object* v___x_2958_, lean_object* v___y_2959_, lean_object* v___x_2960_, lean_object* v_a_x3f_2961_, lean_object* v___y_2962_){
_start:
{
uint8_t v_isExporting_boxed_2963_; lean_object* v_res_2964_; 
v_isExporting_boxed_2963_ = lean_unbox(v_isExporting_2957_);
v_res_2964_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2956_, v_isExporting_boxed_2963_, v___x_2958_, v___y_2959_, v___x_2960_, v_a_x3f_2961_);
lean_dec(v_a_x3f_2961_);
lean_dec(v___y_2959_);
lean_dec(v___y_2956_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(lean_object* v_x_2965_, uint8_t v_isExporting_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; lean_object* v_env_2973_; lean_object* v___x_2974_; uint8_t v_isModule_2975_; 
v___x_2972_ = lean_st_ref_get(v___y_2970_);
v_env_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc_ref(v_env_2973_);
lean_dec(v___x_2972_);
v___x_2974_ = l_Lean_Environment_header(v_env_2973_);
v_isModule_2975_ = lean_ctor_get_uint8(v___x_2974_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2974_);
if (v_isModule_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec_ref(v_env_2973_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
v___x_2976_ = lean_apply_5(v_x_2965_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, lean_box(0));
return v___x_2976_;
}
else
{
uint8_t v_isExporting_2977_; 
v_isExporting_2977_ = lean_ctor_get_uint8(v_env_2973_, sizeof(void*)*13);
lean_dec_ref(v_env_2973_);
if (v_isExporting_2966_ == 0)
{
if (v_isExporting_2977_ == 0)
{
lean_object* v___x_3044_; 
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
v___x_3044_ = lean_apply_5(v_x_2965_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, lean_box(0));
return v___x_3044_;
}
else
{
goto v___jp_2978_;
}
}
else
{
if (v_isExporting_2977_ == 0)
{
goto v___jp_2978_;
}
else
{
lean_object* v___x_3045_; 
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
v___x_3045_ = lean_apply_5(v_x_2965_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, lean_box(0));
return v___x_3045_;
}
}
v___jp_2978_:
{
lean_object* v___x_2979_; lean_object* v_env_2980_; lean_object* v_nextMacroScope_2981_; lean_object* v_ngen_2982_; lean_object* v_auxDeclNGen_2983_; lean_object* v_traceState_2984_; lean_object* v_recordedDeps_2985_; lean_object* v_messages_2986_; lean_object* v_infoState_2987_; lean_object* v_snapshotTasks_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3042_; 
v___x_2979_ = lean_st_ref_take(v___y_2970_);
v_env_2980_ = lean_ctor_get(v___x_2979_, 0);
v_nextMacroScope_2981_ = lean_ctor_get(v___x_2979_, 1);
v_ngen_2982_ = lean_ctor_get(v___x_2979_, 2);
v_auxDeclNGen_2983_ = lean_ctor_get(v___x_2979_, 3);
v_traceState_2984_ = lean_ctor_get(v___x_2979_, 4);
v_recordedDeps_2985_ = lean_ctor_get(v___x_2979_, 6);
v_messages_2986_ = lean_ctor_get(v___x_2979_, 7);
v_infoState_2987_ = lean_ctor_get(v___x_2979_, 8);
v_snapshotTasks_2988_ = lean_ctor_get(v___x_2979_, 9);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3042_ == 0)
{
lean_object* v_unused_3043_; 
v_unused_3043_ = lean_ctor_get(v___x_2979_, 5);
lean_dec(v_unused_3043_);
v___x_2990_ = v___x_2979_;
v_isShared_2991_ = v_isSharedCheck_3042_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_snapshotTasks_2988_);
lean_inc(v_infoState_2987_);
lean_inc(v_messages_2986_);
lean_inc(v_recordedDeps_2985_);
lean_inc(v_traceState_2984_);
lean_inc(v_auxDeclNGen_2983_);
lean_inc(v_ngen_2982_);
lean_inc(v_nextMacroScope_2981_);
lean_inc(v_env_2980_);
lean_dec(v___x_2979_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3042_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2992_ = l_Lean_Environment_setExporting(v_env_2980_, v_isExporting_2966_);
v___x_2993_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__1);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 5, v___x_2993_);
lean_ctor_set(v___x_2990_, 0, v___x_2992_);
v___x_2995_ = v___x_2990_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_nextMacroScope_2981_);
lean_ctor_set(v_reuseFailAlloc_3041_, 2, v_ngen_2982_);
lean_ctor_set(v_reuseFailAlloc_3041_, 3, v_auxDeclNGen_2983_);
lean_ctor_set(v_reuseFailAlloc_3041_, 4, v_traceState_2984_);
lean_ctor_set(v_reuseFailAlloc_3041_, 5, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3041_, 6, v_recordedDeps_2985_);
lean_ctor_set(v_reuseFailAlloc_3041_, 7, v_messages_2986_);
lean_ctor_set(v_reuseFailAlloc_3041_, 8, v_infoState_2987_);
lean_ctor_set(v_reuseFailAlloc_3041_, 9, v_snapshotTasks_2988_);
v___x_2995_ = v_reuseFailAlloc_3041_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_mctx_2998_; lean_object* v_zetaDeltaFVarIds_2999_; lean_object* v_postponed_3000_; lean_object* v_diag_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3039_; 
v___x_2996_ = lean_st_ref_put(v___y_2970_, v___x_2995_);
v___x_2997_ = lean_st_ref_take(v___y_2968_);
v_mctx_2998_ = lean_ctor_get(v___x_2997_, 0);
v_zetaDeltaFVarIds_2999_ = lean_ctor_get(v___x_2997_, 2);
v_postponed_3000_ = lean_ctor_get(v___x_2997_, 3);
v_diag_3001_ = lean_ctor_get(v___x_2997_, 4);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v___x_2997_, 1);
lean_dec(v_unused_3040_);
v___x_3003_ = v___x_2997_;
v_isShared_3004_ = v_isSharedCheck_3039_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_diag_3001_);
lean_inc(v_postponed_3000_);
lean_inc(v_zetaDeltaFVarIds_2999_);
lean_inc(v_mctx_2998_);
lean_dec(v___x_2997_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3039_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3005_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__5);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 1, v___x_3005_);
v___x_3007_ = v___x_3003_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_mctx_2998_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3038_, 2, v_zetaDeltaFVarIds_2999_);
lean_ctor_set(v_reuseFailAlloc_3038_, 3, v_postponed_3000_);
lean_ctor_set(v_reuseFailAlloc_3038_, 4, v_diag_3001_);
v___x_3007_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; lean_object* v_r_3009_; 
v___x_3008_ = lean_st_ref_put(v___y_2968_, v___x_3007_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
v_r_3009_ = lean_apply_5(v_x_2965_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, lean_box(0));
if (lean_obj_tag(v_r_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3026_; 
v_a_3010_ = lean_ctor_get(v_r_3009_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_r_3009_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3012_ = v_r_3009_;
v_isShared_3013_ = v_isSharedCheck_3026_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v_r_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3026_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
lean_inc(v_a_3010_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set_tag(v___x_3012_, 1);
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
v___x_3016_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2970_, v_isExporting_2977_, v___x_2993_, v___y_2968_, v___x_3005_, v___x_3015_);
lean_dec_ref(v___x_3015_);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; 
v_unused_3024_ = lean_ctor_get(v___x_3016_, 0);
lean_dec(v_unused_3024_);
v___x_3018_ = v___x_3016_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_dec(v___x_3016_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v_a_3010_);
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3010_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_a_3027_ = lean_ctor_get(v_r_3009_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v_r_3009_, 1);
v___x_3028_ = lean_box(0);
v___x_3029_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2970_, v_isExporting_2977_, v___x_2993_, v___y_2968_, v___x_3005_, v___x_3028_);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3036_ == 0)
{
lean_object* v_unused_3037_; 
v_unused_3037_ = lean_ctor_get(v___x_3029_, 0);
lean_dec(v_unused_3037_);
v___x_3031_ = v___x_3029_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_dec(v___x_3029_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set_tag(v___x_3031_, 1);
lean_ctor_set(v___x_3031_, 0, v_a_3027_);
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3027_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___boxed(lean_object* v_x_3046_, lean_object* v_isExporting_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
uint8_t v_isExporting_boxed_3053_; lean_object* v_res_3054_; 
v_isExporting_boxed_3053_ = lean_unbox(v_isExporting_3047_);
v_res_3054_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_3046_, v_isExporting_boxed_3053_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim(lean_object* v_indName_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v___f_3061_; lean_object* v___x_3062_; lean_object* v_env_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; uint8_t v___x_3066_; 
lean_inc_n(v_indName_3055_, 2);
v___f_3061_ = lean_alloc_closure((void*)(l_Lean_mkCtorElim___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3061_, 0, v_indName_3055_);
v___x_3062_ = lean_st_ref_get(v_a_3059_);
v_env_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc_ref(v_env_3063_);
lean_dec(v___x_3062_);
v___x_3064_ = l_Lean_mkCtorIdxName(v_indName_3055_);
v___x_3065_ = 1;
v___x_3066_ = l_Lean_Environment_contains(v_env_3063_, v___x_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec_ref(v___f_3061_);
lean_dec(v_indName_3055_);
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; 
lean_inc(v_indName_3055_);
v___x_3069_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3131_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3131_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3131_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
if (lean_obj_tag(v_a_3070_) == 5)
{
lean_object* v_val_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v_val_3074_ = lean_ctor_get(v_a_3070_, 0);
lean_inc_ref(v_val_3074_);
lean_dec_ref_known(v_a_3070_, 1);
v___x_3075_ = lean_unsigned_to_nat(1u);
v___x_3076_ = l_Lean_InductiveVal_numCtors(v_val_3074_);
v___x_3077_ = lean_nat_dec_lt(v___x_3075_, v___x_3076_);
lean_dec(v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3080_; 
lean_dec_ref(v_val_3074_);
lean_dec_ref(v___f_3061_);
lean_dec(v_indName_3055_);
v___x_3078_ = lean_box(0);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3078_);
v___x_3080_ = v___x_3072_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
else
{
lean_object* v_toConstantVal_3082_; lean_object* v_type_3083_; lean_object* v___x_3084_; 
lean_del_object(v___x_3072_);
v_toConstantVal_3082_ = lean_ctor_get(v_val_3074_, 0);
lean_inc_ref(v_toConstantVal_3082_);
lean_dec_ref(v_val_3074_);
v_type_3083_ = lean_ctor_get(v_toConstantVal_3082_, 2);
lean_inc_ref(v_type_3083_);
lean_dec_ref(v_toConstantVal_3082_);
v___x_3084_ = l_Lean_Meta_isPropFormerType(v_type_3083_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3118_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3118_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3118_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_unbox(v_a_3085_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
lean_del_object(v___x_3087_);
lean_inc(v_indName_3055_);
v___x_3090_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_indName_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3105_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3105_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3105_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
uint8_t v___x_3095_; 
v___x_3095_ = lean_unbox(v_a_3091_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
lean_dec(v_a_3091_);
lean_dec(v_a_3085_);
lean_dec_ref(v___f_3061_);
lean_dec(v_indName_3055_);
v___x_3096_ = lean_box(0);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3096_);
v___x_3098_ = v___x_3093_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
else
{
uint8_t v___x_3100_; 
lean_del_object(v___x_3093_);
v___x_3100_ = l_Lean_isPrivateName(v_indName_3055_);
lean_dec(v_indName_3055_);
if (v___x_3100_ == 0)
{
uint8_t v___x_3101_; lean_object* v___x_3102_; 
lean_dec(v_a_3085_);
v___x_3101_ = lean_unbox(v_a_3091_);
lean_dec(v_a_3091_);
v___x_3102_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3061_, v___x_3101_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3102_;
}
else
{
uint8_t v___x_3103_; lean_object* v___x_3104_; 
lean_dec(v_a_3091_);
v___x_3103_ = lean_unbox(v_a_3085_);
lean_dec(v_a_3085_);
v___x_3104_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3061_, v___x_3103_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3104_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_a_3085_);
lean_dec_ref(v___f_3061_);
lean_dec(v_indName_3055_);
v_a_3106_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3090_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3090_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
lean_dec(v_a_3085_);
lean_dec_ref(v___f_3061_);
lean_dec(v_indName_3055_);
v___x_3114_ = lean_box(0);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3114_);
v___x_3116_ = v___x_3087_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v___f_3061_);
lean_dec(v_indName_3055_);
v_a_3119_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3084_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3084_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
lean_dec(v_a_3070_);
lean_dec_ref(v___f_3061_);
lean_dec(v_indName_3055_);
v___x_3127_ = lean_box(0);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3127_);
v___x_3129_ = v___x_3072_;
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
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___f_3061_);
lean_dec(v_indName_3055_);
v_a_3132_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3069_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3069_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___boxed(lean_object* v_indName_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_mkCtorElim(v_indName_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(lean_object* v_00_u03b1_3147_, lean_object* v_x_3148_, uint8_t v_isExporting_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_3148_, v_isExporting_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___boxed(lean_object* v_00_u03b1_3156_, lean_object* v_x_3157_, lean_object* v_isExporting_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_isExporting_boxed_3164_; lean_object* v_res_3165_; 
v_isExporting_boxed_3164_ = lean_unbox(v_isExporting_3158_);
v_res_3165_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(v_00_u03b1_3156_, v_x_3157_, v_isExporting_boxed_3164_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v_decl_3166_, lean_object* v_____r_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; 
lean_inc(v_decl_3166_);
v___x_3173_ = l_Lean_mkCtorIdx(v_decl_3166_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v___x_3174_; 
lean_dec_ref_known(v___x_3173_, 1);
v___x_3174_ = l_Lean_mkCtorElim(v_decl_3166_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3174_;
}
else
{
lean_dec(v_decl_3166_);
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_decl_3175_, lean_object* v_____r_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3175_, v_____r_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
return v_res_3182_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_3192_, uint8_t v_kind_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___y_3205_; 
v___x_3199_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_3200_ = l_Lean_MessageData_ofName(v_name_3192_);
v___x_3201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3199_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_3203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3201_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
switch(v_kind_3193_)
{
case 0:
{
lean_object* v___x_3212_; 
v___x_3212_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_3205_ = v___x_3212_;
goto v___jp_3204_;
}
case 1:
{
lean_object* v___x_3213_; 
v___x_3213_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_3205_ = v___x_3213_;
goto v___jp_3204_;
}
default: 
{
lean_object* v___x_3214_; 
v___x_3214_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_3205_ = v___x_3214_;
goto v___jp_3204_;
}
}
v___jp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_inc_ref(v___y_3205_);
v___x_3206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___y_3205_);
v___x_3207_ = l_Lean_MessageData_ofFormat(v___x_3206_);
v___x_3208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3203_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3208_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_3210_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_3215_, lean_object* v_kind_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v_kind_boxed_3222_; lean_object* v_res_3223_; 
v_kind_boxed_3222_ = lean_unbox(v_kind_3216_);
v_res_3223_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3215_, v_kind_boxed_3222_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
return v_res_3223_;
}
}
static uint64_t _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3230_; uint64_t v___x_3231_; 
v___x_3230_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3231_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3230_);
return v___x_3231_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_uint64_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3233_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3234_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set_uint64(v___x_3234_, sizeof(void*)*1, v___x_3232_);
return v___x_3234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
return v___x_3236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
return v___x_3238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
lean_ctor_set(v___x_3240_, 2, v___x_3239_);
lean_ctor_set(v___x_3240_, 3, v___x_3239_);
lean_ctor_set(v___x_3240_, 4, v___x_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3241_, lean_object* v___x_3242_, lean_object* v___x_3243_, lean_object* v_decl_3244_, lean_object* v___stx_3245_, uint8_t v_kind_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v___x_3250_; uint8_t v___x_3251_; uint8_t v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; size_t v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___y_3275_; 
v___x_3250_ = 0;
v___x_3251_ = l_Lean_instBEqAttributeKind_beq(v_kind_3246_, v___x_3250_);
v___x_3252_ = 1;
v___x_3253_ = 0;
v___x_3254_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3255_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3256_ = lean_unsigned_to_nat(32u);
v___x_3257_ = lean_mk_empty_array_with_capacity(v___x_3256_);
v___x_3258_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__3);
v___x_3259_ = ((size_t)5ULL);
lean_inc_n(v___x_3241_, 7);
v___x_3260_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3257_);
lean_ctor_set(v___x_3260_, 2, v___x_3241_);
lean_ctor_set(v___x_3260_, 3, v___x_3241_);
lean_ctor_set_usize(v___x_3260_, 4, v___x_3259_);
v___x_3261_ = lean_box(1);
lean_inc_ref(v___x_3260_);
v___x_3262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3255_);
lean_ctor_set(v___x_3262_, 1, v___x_3260_);
lean_ctor_set(v___x_3262_, 2, v___x_3261_);
v___x_3263_ = lean_mk_empty_array_with_capacity(v___x_3241_);
v___x_3264_ = lean_box(0);
lean_inc(v___x_3242_);
v___x_3265_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3265_, 0, v___x_3254_);
lean_ctor_set(v___x_3265_, 1, v___x_3242_);
lean_ctor_set(v___x_3265_, 2, v___x_3262_);
lean_ctor_set(v___x_3265_, 3, v___x_3263_);
lean_ctor_set(v___x_3265_, 4, v___x_3264_);
lean_ctor_set(v___x_3265_, 5, v___x_3241_);
lean_ctor_set(v___x_3265_, 6, v___x_3264_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*7, v___x_3253_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*7 + 1, v___x_3253_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*7 + 2, v___x_3253_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*7 + 3, v___x_3252_);
v___x_3266_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3241_);
lean_ctor_set(v___x_3266_, 1, v___x_3241_);
lean_ctor_set(v___x_3266_, 2, v___x_3241_);
lean_ctor_set(v___x_3266_, 3, v___x_3241_);
lean_ctor_set(v___x_3266_, 4, v___x_3255_);
lean_ctor_set(v___x_3266_, 5, v___x_3255_);
lean_ctor_set(v___x_3266_, 6, v___x_3255_);
lean_ctor_set(v___x_3266_, 7, v___x_3255_);
lean_ctor_set(v___x_3266_, 8, v___x_3255_);
lean_ctor_set(v___x_3266_, 9, v___x_3255_);
lean_ctor_set(v___x_3266_, 10, v___x_3255_);
v___x_3267_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7_spec__10___redArg___closed__2);
v___x_3268_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3255_);
lean_ctor_set(v___x_3269_, 1, v___x_3255_);
lean_ctor_set(v___x_3269_, 2, v___x_3241_);
v___x_3270_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3267_);
lean_ctor_set(v___x_3270_, 1, v___x_3255_);
lean_ctor_set(v___x_3270_, 2, v___x_3268_);
lean_ctor_set(v___x_3270_, 3, v___x_3255_);
lean_ctor_set(v___x_3270_, 4, v___x_3255_);
lean_ctor_set(v___x_3270_, 5, v___x_3255_);
lean_ctor_set(v___x_3270_, 6, v___x_3255_);
lean_ctor_set(v___x_3270_, 7, v___x_3269_);
v___x_3271_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3266_);
lean_ctor_set(v___x_3272_, 1, v___x_3270_);
lean_ctor_set(v___x_3272_, 2, v___x_3242_);
lean_ctor_set(v___x_3272_, 3, v___x_3260_);
lean_ctor_set(v___x_3272_, 4, v___x_3271_);
v___x_3273_ = lean_st_mk_ref(v___x_3272_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3285_; 
lean_dec(v_decl_3244_);
v___x_3285_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v___x_3243_, v_kind_3246_, v___x_3265_, v___x_3273_, v___y_3247_, v___y_3248_);
lean_dec(v___x_3273_);
lean_dec_ref_known(v___x_3265_, 7);
return v___x_3285_;
}
else
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_dec(v___x_3243_);
v___x_3286_ = lean_box(0);
v___x_3287_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3244_, v___x_3286_, v___x_3265_, v___x_3273_, v___y_3247_, v___y_3248_);
lean_dec_ref_known(v___x_3265_, 7);
v___y_3275_ = v___x_3287_;
goto v___jp_3274_;
}
v___jp_3274_:
{
if (lean_obj_tag(v___y_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3284_; 
v_a_3276_ = lean_ctor_get(v___y_3275_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___y_3275_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3278_ = v___y_3275_;
v_isShared_3279_ = v_isSharedCheck_3284_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___y_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3284_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3280_ = lean_st_ref_get(v___x_3273_);
lean_dec(v___x_3273_);
lean_dec(v___x_3280_);
if (v_isShared_3279_ == 0)
{
v___x_3282_ = v___x_3278_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3276_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
else
{
lean_dec(v___x_3273_);
return v___y_3275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3288_, lean_object* v___x_3289_, lean_object* v___x_3290_, lean_object* v_decl_3291_, lean_object* v___stx_3292_, lean_object* v_kind_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v_kind_boxed_3297_; lean_object* v_res_3298_; 
v_kind_boxed_3297_ = lean_unbox(v_kind_3293_);
v_res_3298_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3288_, v___x_3289_, v___x_3290_, v_decl_3291_, v___stx_3292_, v_kind_boxed_3297_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___stx_3292_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; lean_object* v_toCold_3304_; lean_object* v_env_3305_; lean_object* v_options_3306_; uint8_t v___x_3307_; lean_object* v_env_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3303_ = lean_st_ref_get(v___y_3301_);
v_toCold_3304_ = lean_ctor_get(v___y_3300_, 0);
v_env_3305_ = lean_ctor_get(v___x_3303_, 0);
lean_inc_ref(v_env_3305_);
lean_dec(v___x_3303_);
v_options_3306_ = lean_ctor_get(v_toCold_3304_, 2);
v___x_3307_ = 0;
v_env_3308_ = l_Lean_Environment_setRecordingDeps(v_env_3305_, v___x_3307_);
v___x_3309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__2);
v___x_3310_ = lean_unsigned_to_nat(32u);
v___x_3311_ = lean_mk_empty_array_with_capacity(v___x_3310_);
lean_dec_ref(v___x_3311_);
v___x_3312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__12_spec__14_spec__15___redArg___closed__5);
lean_inc_ref(v_options_3306_);
v___x_3313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3313_, 0, v_env_3308_);
lean_ctor_set(v___x_3313_, 1, v___x_3309_);
lean_ctor_set(v___x_3313_, 2, v___x_3312_);
lean_ctor_set(v___x_3313_, 3, v_options_3306_);
v___x_3314_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v_msgData_3299_);
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_ref_3325_; lean_object* v___x_3326_; lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3335_; 
v_ref_3325_ = lean_ctor_get(v___y_3322_, 2);
v___x_3326_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msg_3321_, v___y_3322_, v___y_3323_);
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
lean_inc(v_ref_3325_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_ref_3325_);
lean_ctor_set(v___x_3331_, 1, v_a_3327_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set_tag(v___x_3329_, 1);
lean_ctor_set(v___x_3329_, 0, v___x_3331_);
v___x_3333_ = v___x_3329_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
return v_res_3340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3343_ = l_Lean_stringToMessageData(v___x_3342_);
return v___x_3343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3346_ = l_Lean_stringToMessageData(v___x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3347_, lean_object* v_decl_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3352_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3353_ = l_Lean_MessageData_ofName(v___x_3347_);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3354_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v___x_3356_, v___y_3349_, v___y_3350_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3358_, lean_object* v_decl_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3358_, v_decl_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v_decl_3359_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3445_ = l_Lean_registerBuiltinAttribute(v___x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3448_, lean_object* v_msg_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3449_, v___y_3450_, v___y_3451_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3454_, lean_object* v_msg_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(v_00_u03b1_3454_, v_msg_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_3460_, lean_object* v_name_3461_, uint8_t v_kind_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3461_, v_kind_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_3469_, lean_object* v_name_3470_, lean_object* v_kind_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
uint8_t v_kind_boxed_3477_; lean_object* v_res_3478_; 
v_kind_boxed_3477_ = lean_unbox(v_kind_3471_);
v_res_3478_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(v_00_u03b1_3469_, v_name_3470_, v_kind_boxed_3477_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3482_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3483_ = l_Lean_addBuiltinDocString(v___x_3481_, v___x_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3485_;
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
