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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabAsElim;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19;
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Meta.Constructions.CtorElim.0.Lean.mkCtorElimType"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
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
static const lean_string_object l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 262, .m_capacity = 262, .m_length = 261, .m_data = "Generate the `.toCtorIdx` and `.ctor.elim` definitions for the given inductive.\n\nThis attribute is only meant to be used in `Init.Prelude` to build these constructions for\ntypes where we did not generate them immediately (due to `set_option genCtorIdx false`).\n"};
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
lean_object* v___f_49_; lean_object* v___x_1578__overap_50_; lean_object* v___x_51_; 
v___f_49_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_1578__overap_50_ = lean_panic_fn_borrowed(v___f_49_, v_msg_43_);
lean_inc(v___y_47_);
lean_inc_ref(v___y_46_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
v___x_51_ = lean_apply_5(v___x_1578__overap_50_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, lean_box(0));
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
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_array_fget_borrowed(v_array_66_, v_start_67_);
lean_inc(v___x_74_);
v___x_75_ = l_Lean_Meta_getLevel(v___x_74_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
lean_dec_ref_known(v___x_75_, 1);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_start_67_, v___x_77_);
lean_dec(v_start_67_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_78_);
v___x_80_ = v___x_70_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_array_66_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_stop_68_);
v___x_80_ = v_reuseFailAlloc_83_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_mkLevelMax_x27(v_b_60_, v_a_76_);
v_a_59_ = v___x_80_;
v_b_60_ = v___x_81_;
goto _start;
}
}
else
{
lean_del_object(v___x_70_);
lean_dec(v_stop_68_);
lean_dec(v_start_67_);
lean_dec_ref(v_array_66_);
lean_dec(v_b_60_);
return v___x_75_;
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
lean_object* v___x_206_; lean_object* v_env_207_; lean_object* v___x_208_; lean_object* v_mctx_209_; lean_object* v_lctx_210_; lean_object* v_options_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_206_ = lean_st_ref_get(v___y_204_);
v_env_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc_ref(v_env_207_);
lean_dec(v___x_206_);
v___x_208_ = lean_st_ref_get(v___y_202_);
v_mctx_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc_ref(v_mctx_209_);
lean_dec(v___x_208_);
v_lctx_210_ = lean_ctor_get(v___y_201_, 2);
v_options_211_ = lean_ctor_get(v___y_203_, 2);
lean_inc_ref(v_options_211_);
lean_inc_ref(v_lctx_210_);
v___x_212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_212_, 0, v_env_207_);
lean_ctor_set(v___x_212_, 1, v_mctx_209_);
lean_ctor_set(v___x_212_, 2, v_lctx_210_);
lean_ctor_set(v___x_212_, 3, v_options_211_);
v___x_213_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_msgData_200_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0___boxed(lean_object* v_msgData_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msgData_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_ref_228_; lean_object* v___x_229_; lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_238_; 
v_ref_228_ = lean_ctor_get(v___y_225_, 5);
v___x_229_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msg_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_238_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
lean_inc(v_ref_228_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_ref_228_);
lean_ctor_set(v___x_234_, 1, v_a_230_);
if (v_isShared_233_ == 0)
{
lean_ctor_set_tag(v___x_232_, 1);
lean_ctor_set(v___x_232_, 0, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg___boxed(lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(lean_object* v_t_253_, lean_object* v_k_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; 
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
lean_inc_ref(v_a_255_);
v___x_260_ = lean_whnf(v_t_253_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = l_Lean_Expr_isAppOfArity(v_a_261_, v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v_k_254_);
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1);
v___x_266_ = l_Lean_MessageData_ofExpr(v_a_261_);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_267_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = l_Lean_Expr_appArg_x21(v_a_261_);
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
lean_inc_ref(v_a_255_);
lean_inc_ref(v___x_269_);
v___x_270_ = lean_apply_6(v_k_254_, v___x_269_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, lean_box(0));
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_283_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_283_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_283_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_283_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3));
v___x_276_ = l_Lean_Expr_appFn_x21(v_a_261_);
lean_dec(v_a_261_);
v___x_277_ = l_Lean_Expr_constLevels_x21(v___x_276_);
lean_dec_ref(v___x_276_);
v___x_278_ = l_Lean_mkConst(v___x_275_, v___x_277_);
v___x_279_ = l_Lean_mkAppB(v___x_278_, v___x_269_, v_a_271_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_279_);
v___x_281_ = v___x_273_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_dec_ref(v___x_269_);
lean_dec(v_a_261_);
return v___x_270_;
}
}
}
else
{
lean_dec_ref(v_k_254_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___boxed(lean_object* v_t_284_, lean_object* v_k_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v_t_284_, v_k_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(lean_object* v_00_u03b1_292_, lean_object* v_msg_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___boxed(lean_object* v_00_u03b1_300_, lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(v_00_u03b1_300_, v_msg_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_307_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(lean_object* v_e_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; 
lean_inc(v_a_319_);
lean_inc_ref(v_a_318_);
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
lean_inc_ref(v_e_315_);
v___x_321_ = lean_infer_type(v_e_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
lean_inc(v_a_319_);
lean_inc_ref(v_a_318_);
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
v___x_323_ = lean_whnf(v_a_322_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_344_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_344_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_344_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_344_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = l_Lean_Expr_isAppOfArity(v_a_324_, v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_del_object(v___x_326_);
lean_dec_ref(v_e_315_);
v___x_331_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1);
v___x_332_ = l_Lean_MessageData_ofExpr(v_a_324_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_333_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_335_ = l_Lean_Expr_appArg_x21(v_a_324_);
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3));
v___x_337_ = l_Lean_Expr_appFn_x21(v_a_324_);
lean_dec(v_a_324_);
v___x_338_ = l_Lean_Expr_constLevels_x21(v___x_337_);
lean_dec_ref(v___x_337_);
v___x_339_ = l_Lean_mkConst(v___x_336_, v___x_338_);
v___x_340_ = l_Lean_mkAppB(v___x_339_, v___x_335_, v_e_315_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_340_);
v___x_342_ = v___x_326_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_dec_ref(v_e_315_);
return v___x_323_;
}
}
else
{
lean_dec_ref(v_e_315_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___boxed(lean_object* v_e_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_e_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(lean_object* v_a_352_, size_t v_sz_353_, size_t v_i_354_, lean_object* v_bs_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_lt(v_i_354_, v_sz_353_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec(v_a_352_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v_bs_355_);
return v___x_362_;
}
else
{
lean_object* v_v_363_; lean_object* v___x_364_; 
v_v_363_ = lean_array_uget_borrowed(v_bs_355_, v_i_354_);
lean_inc(v_v_363_);
lean_inc(v_a_352_);
v___x_364_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(v_a_352_, v_v_363_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v_bs_x27_367_; size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_364_, 1);
v___x_366_ = lean_unsigned_to_nat(0u);
v_bs_x27_367_ = lean_array_uset(v_bs_355_, v_i_354_, v___x_366_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_354_, v___x_368_);
v___x_370_ = lean_array_uset(v_bs_x27_367_, v_i_354_, v_a_365_);
v_i_354_ = v___x_369_;
v_bs_355_ = v___x_370_;
goto _start;
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v_bs_355_);
lean_dec(v_a_352_);
v_a_372_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_364_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_364_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0___boxed(lean_object* v_a_380_, lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_bs_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
size_t v_sz_boxed_389_; size_t v_i_boxed_390_; lean_object* v_res_391_; 
v_sz_boxed_389_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_390_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_380_, v_sz_boxed_389_, v_i_boxed_390_, v_bs_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_391_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = l_Lean_Level_ofNat(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(lean_object* v_n_394_, lean_object* v_es_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
lean_inc_ref(v_es_395_);
v___x_401_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(v_es_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v___x_404_; size_t v_sz_405_; size_t v___x_406_; lean_object* v___x_407_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_n(v_a_402_, 2);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0);
v___x_404_ = l_Lean_mkLevelMax_x27(v_a_402_, v___x_403_);
v_sz_405_ = lean_array_size(v_es_395_);
v___x_406_ = ((size_t)0ULL);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_402_, v_sz_405_, v___x_406_, v_es_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l_Lean_Level_normalize(v___x_404_);
lean_dec(v___x_404_);
v___x_410_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(v___x_409_);
v___x_411_ = l_Lean_Expr_sort___override(v___x_410_);
v___x_412_ = l_Lean_mkNatLookupTable(v_n_394_, v___x_411_, v_a_408_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_408_);
return v___x_412_;
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v___x_404_);
lean_dec_ref(v_n_394_);
v_a_413_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_407_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_407_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref(v_es_395_);
lean_dec_ref(v_n_394_);
v_a_421_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_401_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_401_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___boxed(lean_object* v_n_429_, lean_object* v_es_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_n_429_, v_es_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(lean_object* v_indName_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0));
v___x_440_ = l_Lean_Name_str___override(v_indName_438_, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElimName(lean_object* v_indName_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l_Lean_mkCtorElimName___closed__0));
v___x_444_ = l_Lean_Name_str___override(v_indName_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(lean_object* v_n1_445_, lean_object* v_n2_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_privatePrefix_x3f(v_n2_446_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_privateToUserName(v_n1_445_);
return v___x_448_;
}
else
{
lean_object* v_val_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_val_449_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v___x_447_, 1);
v___x_450_ = l_Lean_privateToUserName(v_n1_445_);
v___x_451_ = l_Lean_Name_appendCore(v_val_449_, v___x_450_);
lean_dec(v_val_449_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs___boxed(lean_object* v_n1_452_, lean_object* v_n2_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(v_n1_452_, v_n2_453_);
lean_dec(v_n2_453_);
return v_res_454_;
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
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName___boxed(lean_object* v_indName_461_, lean_object* v_conName_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_mkConstructorElimName(v_indName_461_, v_conName_462_);
lean_dec(v_indName_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(lean_object* v_k_464_, lean_object* v_b_465_, lean_object* v_c_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
v___x_472_ = lean_apply_7(v_k_464_, v_b_465_, v_c_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, lean_box(0));
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed(lean_object* v_k_473_, lean_object* v_b_474_, lean_object* v_c_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(v_k_473_, v_b_474_, v_c_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(lean_object* v_type_482_, lean_object* v_k_483_, uint8_t v_cleanupAnnotations_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___f_490_; uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___f_490_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_490_, 0, v_k_483_);
v___x_491_ = 0;
v___x_492_ = lean_box(0);
v___x_493_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_491_, v___x_492_, v_type_482_, v___f_490_, v_cleanupAnnotations_484_, v___x_491_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_502_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_493_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_493_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___boxed(lean_object* v_type_510_, lean_object* v_k_511_, lean_object* v_cleanupAnnotations_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_518_; lean_object* v_res_519_; 
v_cleanupAnnotations_boxed_518_ = lean_unbox(v_cleanupAnnotations_512_);
v_res_519_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_510_, v_k_511_, v_cleanupAnnotations_boxed_518_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(lean_object* v_00_u03b1_520_, lean_object* v_type_521_, lean_object* v_k_522_, uint8_t v_cleanupAnnotations_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_521_, v_k_522_, v_cleanupAnnotations_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___boxed(lean_object* v_00_u03b1_530_, lean_object* v_type_531_, lean_object* v_k_532_, lean_object* v_cleanupAnnotations_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_539_; lean_object* v_res_540_; 
v_cleanupAnnotations_boxed_539_ = lean_unbox(v_cleanupAnnotations_533_);
v_res_540_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(v_00_u03b1_530_, v_type_531_, v_k_532_, v_cleanupAnnotations_boxed_539_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(lean_object* v_name_541_, lean_object* v_levelParams_542_, lean_object* v_type_543_, lean_object* v_value_544_, lean_object* v_hints_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_548_; uint8_t v___y_550_; uint8_t v___y_557_; lean_object* v_env_560_; uint8_t v___x_561_; 
v___x_548_ = lean_st_ref_get(v___y_546_);
v_env_560_ = lean_ctor_get(v___x_548_, 0);
lean_inc_ref_n(v_env_560_, 2);
lean_dec(v___x_548_);
v___x_561_ = l_Lean_Environment_hasUnsafe(v_env_560_, v_type_543_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; 
v___x_562_ = l_Lean_Environment_hasUnsafe(v_env_560_, v_value_544_);
v___y_557_ = v___x_562_;
goto v___jp_556_;
}
else
{
lean_dec_ref(v_env_560_);
v___y_557_ = v___x_561_;
goto v___jp_556_;
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc(v_name_541_);
v___x_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_551_, 0, v_name_541_);
lean_ctor_set(v___x_551_, 1, v_levelParams_542_);
lean_ctor_set(v___x_551_, 2, v_type_543_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v_name_541_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_554_, 0, v___x_551_);
lean_ctor_set(v___x_554_, 1, v_value_544_);
lean_ctor_set(v___x_554_, 2, v_hints_545_);
lean_ctor_set(v___x_554_, 3, v___x_553_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*4, v___y_550_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
v___jp_556_:
{
if (v___y_557_ == 0)
{
uint8_t v___x_558_; 
v___x_558_ = 1;
v___y_550_ = v___x_558_;
goto v___jp_549_;
}
else
{
uint8_t v___x_559_; 
v___x_559_ = 0;
v___y_550_ = v___x_559_;
goto v___jp_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg___boxed(lean_object* v_name_563_, lean_object* v_levelParams_564_, lean_object* v_type_565_, lean_object* v_value_566_, lean_object* v_hints_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_563_, v_levelParams_564_, v_type_565_, v_value_566_, v_hints_567_, v___y_568_);
lean_dec(v___y_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(lean_object* v_name_571_, lean_object* v_levelParams_572_, lean_object* v_type_573_, lean_object* v_value_574_, lean_object* v_hints_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_571_, v_levelParams_572_, v_type_573_, v_value_574_, v_hints_575_, v___y_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___boxed(lean_object* v_name_582_, lean_object* v_levelParams_583_, lean_object* v_type_584_, lean_object* v_value_585_, lean_object* v_hints_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(v_name_582_, v_levelParams_583_, v_type_584_, v_value_585_, v_hints_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(lean_object* v_msg_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___f_599_; lean_object* v___x_4200__overap_600_; lean_object* v___x_601_; 
v___f_599_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_4200__overap_600_ = lean_panic_fn_borrowed(v___f_599_, v_msg_593_);
lean_inc(v___y_597_);
lean_inc_ref(v___y_596_);
lean_inc(v___y_595_);
lean_inc_ref(v___y_594_);
v___x_601_ = lean_apply_5(v___x_4200__overap_600_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, lean_box(0));
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v_msg_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(size_t v_sz_609_, size_t v_i_610_, lean_object* v_bs_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_610_, v_sz_609_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_bs_611_);
return v___x_618_;
}
else
{
lean_object* v_v_619_; lean_object* v___x_620_; 
v_v_619_ = lean_array_uget_borrowed(v_bs_611_, v_i_610_);
lean_inc(v___y_615_);
lean_inc_ref(v___y_614_);
lean_inc(v___y_613_);
lean_inc_ref(v___y_612_);
lean_inc(v_v_619_);
v___x_620_ = lean_infer_type(v_v_619_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v_bs_x27_623_; size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = lean_unsigned_to_nat(0u);
v_bs_x27_623_ = lean_array_uset(v_bs_611_, v_i_610_, v___x_622_);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_add(v_i_610_, v___x_624_);
v___x_626_ = lean_array_uset(v_bs_x27_623_, v_i_610_, v_a_621_);
v_i_610_ = v___x_625_;
v_bs_611_ = v___x_626_;
goto _start;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_bs_611_);
v_a_628_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_620_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_620_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___boxed(lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_bs_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
size_t v_sz_boxed_644_; size_t v_i_boxed_645_; lean_object* v_res_646_; 
v_sz_boxed_644_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_645_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(v_sz_boxed_644_, v_i_boxed_645_, v_bs_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v___x_649_, uint8_t v___x_650_, lean_object* v_ctorIdx_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
size_t v_sz_657_; size_t v___x_658_; lean_object* v___x_659_; 
v_sz_657_ = lean_array_size(v___x_647_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(v_sz_657_, v___x_658_, v___x_647_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
lean_inc_ref(v_ctorIdx_651_);
v___x_661_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_ctorIdx_651_, v_a_660_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = lean_unsigned_to_nat(2u);
v___x_664_ = lean_mk_empty_array_with_capacity(v___x_663_);
v___x_665_ = lean_array_push(v___x_664_, v___x_648_);
v___x_666_ = lean_array_push(v___x_665_, v_ctorIdx_651_);
v___x_667_ = l_Array_append___redArg(v___x_649_, v___x_666_);
lean_dec_ref(v___x_666_);
v___x_668_ = 1;
v___x_669_ = 1;
v___x_670_ = l_Lean_Meta_mkLambdaFVars(v___x_667_, v_a_662_, v___x_650_, v___x_668_, v___x_650_, v___x_668_, v___x_669_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec_ref(v___x_667_);
return v___x_670_;
}
else
{
lean_dec_ref(v_ctorIdx_651_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_648_);
return v___x_661_;
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_ctorIdx_651_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_648_);
v_a_671_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_659_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_659_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed(lean_object* v___x_679_, lean_object* v___x_680_, lean_object* v___x_681_, lean_object* v___x_682_, lean_object* v_ctorIdx_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v___x_6832__boxed_689_; lean_object* v_res_690_; 
v___x_6832__boxed_689_ = lean_unbox(v___x_682_);
v_res_690_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(v___x_679_, v___x_680_, v___x_681_, v___x_6832__boxed_689_, v_ctorIdx_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0(lean_object* v_k_691_, lean_object* v_b_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
v___x_698_ = lean_apply_6(v_k_691_, v_b_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, lean_box(0));
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_k_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0(v_k_699_, v_b_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(lean_object* v_name_707_, uint8_t v_bi_708_, lean_object* v_type_709_, lean_object* v_k_710_, uint8_t v_kind_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___f_717_; lean_object* v___x_718_; 
v___f_717_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_717_, 0, v_k_710_);
v___x_718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_707_, v_bi_708_, v_type_709_, v___f_717_, v_kind_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___boxed(lean_object* v_name_735_, lean_object* v_bi_736_, lean_object* v_type_737_, lean_object* v_k_738_, lean_object* v_kind_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
uint8_t v_bi_boxed_745_; uint8_t v_kind_boxed_746_; lean_object* v_res_747_; 
v_bi_boxed_745_ = lean_unbox(v_bi_736_);
v_kind_boxed_746_ = lean_unbox(v_kind_739_);
v_res_747_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(v_name_735_, v_bi_boxed_745_, v_type_737_, v_k_738_, v_kind_boxed_746_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(lean_object* v_name_748_, lean_object* v_type_749_, lean_object* v_k_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; 
v___x_756_ = 0;
v___x_757_ = 0;
v___x_758_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(v_name_748_, v___x_756_, v_type_749_, v_k_750_, v___x_757_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg___boxed(lean_object* v_name_759_, lean_object* v_type_760_, lean_object* v_k_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v_name_759_, v_type_760_, v_k_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_box(0);
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_776_ = l_Lean_mkConst(v___x_775_, v___x_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(lean_object* v_val_777_, lean_object* v___x_778_, uint8_t v___x_779_, lean_object* v_xs_780_, lean_object* v_x_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_numParams_787_; lean_object* v_numIndices_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_numParams_787_ = lean_ctor_get(v_val_777_, 1);
lean_inc_n(v_numParams_787_, 2);
v_numIndices_788_ = lean_ctor_get(v_val_777_, 2);
lean_inc(v_numIndices_788_);
lean_dec_ref(v_val_777_);
lean_inc_ref(v_xs_780_);
v___x_789_ = l_Array_toSubarray___redArg(v_xs_780_, v___x_778_, v_numParams_787_);
v___x_790_ = l_Subarray_copy___redArg(v___x_789_);
v___x_791_ = l_Lean_instInhabitedExpr;
v___x_792_ = lean_array_get(v___x_791_, v_xs_780_, v_numParams_787_);
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_numParams_787_, v___x_793_);
lean_dec(v_numParams_787_);
v___x_795_ = lean_nat_add(v___x_794_, v_numIndices_788_);
lean_dec(v_numIndices_788_);
lean_dec(v___x_794_);
v___x_796_ = lean_nat_add(v___x_795_, v___x_793_);
lean_dec(v___x_795_);
v___x_797_ = lean_array_get_size(v_xs_780_);
v___x_798_ = l_Array_toSubarray___redArg(v_xs_780_, v___x_796_, v___x_797_);
v___x_799_ = l_Subarray_copy___redArg(v___x_798_);
v___x_800_ = lean_box(v___x_779_);
v___f_801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_801_, 0, v___x_799_);
lean_closure_set(v___f_801_, 1, v___x_792_);
lean_closure_set(v___f_801_, 2, v___x_790_);
lean_closure_set(v___f_801_, 3, v___x_800_);
v___x_802_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_803_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_804_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_802_, v___x_803_, v___f_801_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed(lean_object* v_val_805_, lean_object* v___x_806_, lean_object* v___x_807_, lean_object* v_xs_808_, lean_object* v_x_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v___x_7008__boxed_815_; lean_object* v_res_816_; 
v___x_7008__boxed_815_ = lean_unbox(v___x_807_);
v_res_816_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(v_val_805_, v___x_806_, v___x_7008__boxed_815_, v_xs_808_, v_x_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v_x_809_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_817_, lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_fileName_824_; lean_object* v_fileMap_825_; lean_object* v_options_826_; lean_object* v_currRecDepth_827_; lean_object* v_maxRecDepth_828_; lean_object* v_ref_829_; lean_object* v_currNamespace_830_; lean_object* v_openDecls_831_; lean_object* v_initHeartbeats_832_; lean_object* v_maxHeartbeats_833_; lean_object* v_quotContext_834_; lean_object* v_currMacroScope_835_; uint8_t v_diag_836_; lean_object* v_cancelTk_x3f_837_; uint8_t v_suppressElabErrors_838_; lean_object* v_inheritedTraceOptions_839_; lean_object* v_ref_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_fileName_824_ = lean_ctor_get(v___y_821_, 0);
v_fileMap_825_ = lean_ctor_get(v___y_821_, 1);
v_options_826_ = lean_ctor_get(v___y_821_, 2);
v_currRecDepth_827_ = lean_ctor_get(v___y_821_, 3);
v_maxRecDepth_828_ = lean_ctor_get(v___y_821_, 4);
v_ref_829_ = lean_ctor_get(v___y_821_, 5);
v_currNamespace_830_ = lean_ctor_get(v___y_821_, 6);
v_openDecls_831_ = lean_ctor_get(v___y_821_, 7);
v_initHeartbeats_832_ = lean_ctor_get(v___y_821_, 8);
v_maxHeartbeats_833_ = lean_ctor_get(v___y_821_, 9);
v_quotContext_834_ = lean_ctor_get(v___y_821_, 10);
v_currMacroScope_835_ = lean_ctor_get(v___y_821_, 11);
v_diag_836_ = lean_ctor_get_uint8(v___y_821_, sizeof(void*)*14);
v_cancelTk_x3f_837_ = lean_ctor_get(v___y_821_, 12);
v_suppressElabErrors_838_ = lean_ctor_get_uint8(v___y_821_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_839_ = lean_ctor_get(v___y_821_, 13);
v_ref_840_ = l_Lean_replaceRef(v_ref_817_, v_ref_829_);
lean_inc_ref(v_inheritedTraceOptions_839_);
lean_inc(v_cancelTk_x3f_837_);
lean_inc(v_currMacroScope_835_);
lean_inc(v_quotContext_834_);
lean_inc(v_maxHeartbeats_833_);
lean_inc(v_initHeartbeats_832_);
lean_inc(v_openDecls_831_);
lean_inc(v_currNamespace_830_);
lean_inc(v_maxRecDepth_828_);
lean_inc(v_currRecDepth_827_);
lean_inc_ref(v_options_826_);
lean_inc_ref(v_fileMap_825_);
lean_inc_ref(v_fileName_824_);
v___x_841_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_841_, 0, v_fileName_824_);
lean_ctor_set(v___x_841_, 1, v_fileMap_825_);
lean_ctor_set(v___x_841_, 2, v_options_826_);
lean_ctor_set(v___x_841_, 3, v_currRecDepth_827_);
lean_ctor_set(v___x_841_, 4, v_maxRecDepth_828_);
lean_ctor_set(v___x_841_, 5, v_ref_840_);
lean_ctor_set(v___x_841_, 6, v_currNamespace_830_);
lean_ctor_set(v___x_841_, 7, v_openDecls_831_);
lean_ctor_set(v___x_841_, 8, v_initHeartbeats_832_);
lean_ctor_set(v___x_841_, 9, v_maxHeartbeats_833_);
lean_ctor_set(v___x_841_, 10, v_quotContext_834_);
lean_ctor_set(v___x_841_, 11, v_currMacroScope_835_);
lean_ctor_set(v___x_841_, 12, v_cancelTk_x3f_837_);
lean_ctor_set(v___x_841_, 13, v_inheritedTraceOptions_839_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*14, v_diag_836_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*14 + 1, v_suppressElabErrors_838_);
v___x_842_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_818_, v___y_819_, v___y_820_, v___x_841_, v___y_822_);
lean_dec_ref_known(v___x_841_, 14);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_843_, lean_object* v_msg_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_843_, v_msg_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v_ref_843_);
return v_res_850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_851_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
lean_ctor_set(v___x_856_, 2, v___x_855_);
lean_ctor_set(v___x_856_, 3, v___x_855_);
lean_ctor_set(v___x_856_, 4, v___x_854_);
lean_ctor_set(v___x_856_, 5, v___x_854_);
lean_ctor_set(v___x_856_, 6, v___x_854_);
lean_ctor_set(v___x_856_, 7, v___x_854_);
lean_ctor_set(v___x_856_, 8, v___x_854_);
lean_ctor_set(v___x_856_, 9, v___x_854_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_unsigned_to_nat(32u);
v___x_858_ = lean_mk_empty_array_with_capacity(v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_860_ = ((size_t)5ULL);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_unsigned_to_nat(32u);
v___x_863_ = lean_mk_empty_array_with_capacity(v___x_862_);
v___x_864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_865_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
lean_ctor_set(v___x_865_, 2, v___x_861_);
lean_ctor_set(v___x_865_, 3, v___x_861_);
lean_ctor_set_usize(v___x_865_, 4, v___x_860_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_866_ = lean_box(1);
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___x_866_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_872_ = l_Lean_stringToMessageData(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_891_, lean_object* v_declHint_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_env_896_; uint8_t v___y_898_; uint8_t v___x_954_; uint8_t v___x_955_; 
v___x_895_ = lean_st_ref_get(v___y_893_);
v_env_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_ref(v_env_896_);
lean_dec(v___x_895_);
v___x_954_ = l_Lean_Name_isAnonymous(v_declHint_892_);
v___x_955_ = lean_bool_not(v___x_954_);
if (v___x_955_ == 0)
{
v___y_898_ = v___x_955_;
goto v___jp_897_;
}
else
{
uint8_t v_isExporting_956_; 
v_isExporting_956_ = lean_ctor_get_uint8(v_env_896_, sizeof(void*)*8);
v___y_898_ = v_isExporting_956_;
goto v___jp_897_;
}
v___jp_897_:
{
if (v___y_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec_ref(v_env_896_);
lean_dec(v_declHint_892_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v_msg_891_);
return v___x_899_;
}
else
{
uint8_t v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = 0;
lean_inc_ref(v_env_896_);
v___x_901_ = l_Lean_Environment_setExporting(v_env_896_, v___x_900_);
lean_inc(v_declHint_892_);
lean_inc_ref(v___x_901_);
v___x_902_ = l_Lean_Environment_contains(v___x_901_, v_declHint_892_, v___y_898_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec_ref(v___x_901_);
lean_dec_ref(v_env_896_);
lean_dec(v_declHint_892_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v_msg_891_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_c_909_; lean_object* v___x_910_; 
v___x_904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_905_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_906_ = l_Lean_Options_empty;
v___x_907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_907_, 0, v___x_901_);
lean_ctor_set(v___x_907_, 1, v___x_904_);
lean_ctor_set(v___x_907_, 2, v___x_905_);
lean_ctor_set(v___x_907_, 3, v___x_906_);
lean_inc(v_declHint_892_);
v___x_908_ = l_Lean_MessageData_ofConstName(v_declHint_892_, v___x_900_);
v_c_909_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_909_, 0, v___x_907_);
lean_ctor_set(v_c_909_, 1, v___x_908_);
v___x_910_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_896_, v_declHint_892_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref(v_env_896_);
lean_dec(v_declHint_892_);
v___x_911_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_c_909_);
v___x_913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_MessageData_note(v___x_914_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v_msg_891_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
else
{
lean_object* v_val_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_953_; 
v_val_918_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_953_ == 0)
{
v___x_920_ = v___x_910_;
v_isShared_921_ = v_isSharedCheck_953_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_val_918_);
lean_dec(v___x_910_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_953_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_mod_925_; uint8_t v___x_926_; 
v___x_922_ = lean_box(0);
v___x_923_ = l_Lean_Environment_header(v_env_896_);
lean_dec_ref(v_env_896_);
v___x_924_ = l_Lean_EnvironmentHeader_moduleNames(v___x_923_);
v_mod_925_ = lean_array_get(v___x_922_, v___x_924_, v_val_918_);
lean_dec(v_val_918_);
lean_dec_ref(v___x_924_);
v___x_926_ = l_Lean_isPrivateName(v_declHint_892_);
lean_dec(v_declHint_892_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_927_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_c_909_);
v___x_929_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Lean_MessageData_ofName(v_mod_925_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_MessageData_note(v___x_934_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v_msg_891_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 0);
lean_ctor_set(v___x_920_, 0, v___x_936_);
v___x_938_ = v___x_920_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v_c_909_);
v___x_942_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_MessageData_ofName(v_mod_925_);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = l_Lean_MessageData_note(v___x_947_);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v_msg_891_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 0);
lean_ctor_set(v___x_920_, 0, v___x_949_);
v___x_951_ = v___x_920_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_957_, lean_object* v_declHint_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_957_, v_declHint_958_, v___y_959_);
lean_dec(v___y_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_962_, lean_object* v_declHint_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_979_; 
v___x_969_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_962_, v_declHint_963_, v___y_967_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_979_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_979_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_979_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_974_ = l_Lean_unknownIdentifierMessageTag;
v___x_975_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v_a_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_980_, lean_object* v_declHint_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_980_, v_declHint_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_988_, lean_object* v_msg_989_, lean_object* v_declHint_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; lean_object* v_a_997_; lean_object* v___x_998_; 
v___x_996_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_989_, v_declHint_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref(v___x_996_);
v___x_998_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_988_, v_a_997_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_999_, lean_object* v_msg_1000_, lean_object* v_declHint_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_999_, v_msg_1000_, v_declHint_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v_ref_999_);
return v_res_1007_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1014_, lean_object* v_constName_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1021_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_1022_ = 0;
lean_inc(v_constName_1015_);
v___x_1023_ = l_Lean_MessageData_ofConstName(v_constName_1015_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1021_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1014_, v___x_1026_, v_constName_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1028_, lean_object* v_constName_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1028_, v_constName_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v_ref_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(lean_object* v_constName_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_ref_1042_; lean_object* v___x_1043_; 
v_ref_1042_ = lean_ctor_get(v___y_1039_, 5);
v___x_1043_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1042_, v_constName_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(lean_object* v_constName_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v_env_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = lean_st_ref_get(v___y_1055_);
v_env_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_ref(v_env_1058_);
lean_dec(v___x_1057_);
v___x_1059_ = 0;
lean_inc(v_constName_1051_);
v___x_1060_ = l_Lean_Environment_findConstVal_x3f(v_env_1058_, v_constName_1051_, v___x_1059_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
return v___x_1061_;
}
else
{
lean_object* v_val_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_constName_1051_);
v_val_1062_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1060_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_val_1062_);
lean_dec(v___x_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 0);
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_val_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1___boxed(lean_object* v_constName_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_constName_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(lean_object* v_constName_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v_env_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1083_ = lean_st_ref_get(v___y_1081_);
v_env_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_env_1084_);
lean_dec(v___x_1083_);
v___x_1085_ = 0;
lean_inc(v_constName_1077_);
v___x_1086_ = l_Lean_Environment_find_x3f(v_env_1084_, v_constName_1077_, v___x_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1087_;
}
else
{
lean_object* v_val_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_constName_1077_);
v_val_1088_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1086_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_val_1088_);
lean_dec(v___x_1086_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 0);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_val_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(lean_object* v_constName_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_constName_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1102_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
v___x_1109_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
lean_ctor_set(v___x_1109_, 2, v___x_1108_);
lean_ctor_set(v___x_1109_, 3, v___x_1108_);
lean_ctor_set(v___x_1109_, 4, v___x_1108_);
lean_ctor_set(v___x_1109_, 5, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(lean_object* v_declName_1110_, uint8_t v_s_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_env_1116_; lean_object* v_nextMacroScope_1117_; lean_object* v_ngen_1118_; lean_object* v_auxDeclNGen_1119_; lean_object* v_traceState_1120_; lean_object* v_messages_1121_; lean_object* v_infoState_1122_; lean_object* v_snapshotTasks_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1152_; 
v___x_1115_ = lean_st_ref_take(v___y_1113_);
v_env_1116_ = lean_ctor_get(v___x_1115_, 0);
v_nextMacroScope_1117_ = lean_ctor_get(v___x_1115_, 1);
v_ngen_1118_ = lean_ctor_get(v___x_1115_, 2);
v_auxDeclNGen_1119_ = lean_ctor_get(v___x_1115_, 3);
v_traceState_1120_ = lean_ctor_get(v___x_1115_, 4);
v_messages_1121_ = lean_ctor_get(v___x_1115_, 6);
v_infoState_1122_ = lean_ctor_get(v___x_1115_, 7);
v_snapshotTasks_1123_ = lean_ctor_get(v___x_1115_, 8);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v___x_1115_, 5);
lean_dec(v_unused_1153_);
v___x_1125_ = v___x_1115_;
v_isShared_1126_ = v_isSharedCheck_1152_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_snapshotTasks_1123_);
lean_inc(v_infoState_1122_);
lean_inc(v_messages_1121_);
lean_inc(v_traceState_1120_);
lean_inc(v_auxDeclNGen_1119_);
lean_inc(v_ngen_1118_);
lean_inc(v_nextMacroScope_1117_);
lean_inc(v_env_1116_);
lean_dec(v___x_1115_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1152_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1127_ = 0;
v___x_1128_ = lean_box(0);
v___x_1129_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1116_, v_declName_1110_, v_s_1111_, v___x_1127_, v___x_1128_);
v___x_1130_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 5, v___x_1130_);
lean_ctor_set(v___x_1125_, 0, v___x_1129_);
v___x_1132_ = v___x_1125_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_nextMacroScope_1117_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_ngen_1118_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_auxDeclNGen_1119_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_traceState_1120_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1151_, 6, v_messages_1121_);
lean_ctor_set(v_reuseFailAlloc_1151_, 7, v_infoState_1122_);
lean_ctor_set(v_reuseFailAlloc_1151_, 8, v_snapshotTasks_1123_);
v___x_1132_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_mctx_1135_; lean_object* v_zetaDeltaFVarIds_1136_; lean_object* v_postponed_1137_; lean_object* v_diag_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1149_; 
v___x_1133_ = lean_st_ref_set(v___y_1113_, v___x_1132_);
v___x_1134_ = lean_st_ref_take(v___y_1112_);
v_mctx_1135_ = lean_ctor_get(v___x_1134_, 0);
v_zetaDeltaFVarIds_1136_ = lean_ctor_get(v___x_1134_, 2);
v_postponed_1137_ = lean_ctor_get(v___x_1134_, 3);
v_diag_1138_ = lean_ctor_get(v___x_1134_, 4);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v___x_1134_, 1);
lean_dec(v_unused_1150_);
v___x_1140_ = v___x_1134_;
v_isShared_1141_ = v_isSharedCheck_1149_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_diag_1138_);
lean_inc(v_postponed_1137_);
lean_inc(v_zetaDeltaFVarIds_1136_);
lean_inc(v_mctx_1135_);
lean_dec(v___x_1134_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1149_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1142_);
v___x_1144_ = v___x_1140_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_mctx_1135_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_zetaDeltaFVarIds_1136_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_postponed_1137_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_diag_1138_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_st_ref_set(v___y_1112_, v___x_1144_);
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object* v_declName_1154_, lean_object* v_s_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v_s_boxed_1159_; lean_object* v_res_1160_; 
v_s_boxed_1159_ = lean_unbox(v_s_1155_);
v_res_1160_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1154_, v_s_boxed_1159_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec(v___y_1156_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object* v_declName_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = 0;
v___x_1168_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1161_, v___x_1167_, v___y_1163_, v___y_1165_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___boxed(lean_object* v_declName_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v_declName_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
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
lean_object* v___x_1190_; 
lean_inc(v_indName_1184_);
v___x_1190_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1322_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1322_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1322_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
if (lean_obj_tag(v_a_1191_) == 5)
{
lean_object* v_val_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_val_1195_ = lean_ctor_get(v_a_1191_, 0);
lean_inc_ref(v_val_1195_);
lean_dec_ref_known(v_a_1191_, 1);
v___x_1196_ = l_Lean_InductiveVal_numCtors(v_val_1195_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_nat_dec_eq(v___x_1196_, v___x_1197_);
lean_dec(v___x_1196_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_del_object(v___x_1193_);
lean_inc(v_indName_1184_);
v___x_1199_ = l_Lean_mkCasesOnName(v_indName_1184_);
v___x_1200_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v___x_1199_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_levelParams_1202_; lean_object* v_type_1203_; lean_object* v___x_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v_levelParams_1202_ = lean_ctor_get(v_a_1201_, 1);
lean_inc(v_levelParams_1202_);
v_type_1203_ = lean_ctor_get(v_a_1201_, 2);
lean_inc_ref(v_type_1203_);
lean_dec(v_a_1201_);
v___x_1204_ = lean_box(v___x_1198_);
v___f_1205_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1205_, 0, v_val_1195_);
lean_closure_set(v___f_1205_, 1, v___x_1197_);
lean_closure_set(v___f_1205_, 2, v___x_1204_);
v___x_1206_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1203_, v___f_1205_, v___x_1198_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_n(v_a_1207_, 2);
lean_dec_ref_known(v___x_1206_, 1);
lean_inc(v_a_1188_);
lean_inc_ref(v_a_1187_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
v___x_1208_ = lean_infer_type(v_a_1207_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1291_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1210_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1184_);
v___x_1211_ = lean_box(1);
lean_inc(v___x_1210_);
v___x_1212_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1210_, v_levelParams_1202_, v_a_1209_, v_a_1207_, v___x_1211_, v_a_1188_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1291_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1291_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 1);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
uint8_t v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = 1;
v___x_1220_ = l_Lean_addAndCompile(v___x_1218_, v___x_1219_, v___x_1198_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1221_; lean_object* v_env_1222_; lean_object* v_nextMacroScope_1223_; lean_object* v_ngen_1224_; lean_object* v_auxDeclNGen_1225_; lean_object* v_traceState_1226_; lean_object* v_messages_1227_; lean_object* v_infoState_1228_; lean_object* v_snapshotTasks_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref_known(v___x_1220_, 1);
v___x_1221_ = lean_st_ref_take(v_a_1188_);
v_env_1222_ = lean_ctor_get(v___x_1221_, 0);
v_nextMacroScope_1223_ = lean_ctor_get(v___x_1221_, 1);
v_ngen_1224_ = lean_ctor_get(v___x_1221_, 2);
v_auxDeclNGen_1225_ = lean_ctor_get(v___x_1221_, 3);
v_traceState_1226_ = lean_ctor_get(v___x_1221_, 4);
v_messages_1227_ = lean_ctor_get(v___x_1221_, 6);
v_infoState_1228_ = lean_ctor_get(v___x_1221_, 7);
v_snapshotTasks_1229_ = lean_ctor_get(v___x_1221_, 8);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v___x_1221_, 5);
lean_dec(v_unused_1289_);
v___x_1231_ = v___x_1221_;
v_isShared_1232_ = v_isSharedCheck_1288_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_snapshotTasks_1229_);
lean_inc(v_infoState_1228_);
lean_inc(v_messages_1227_);
lean_inc(v_traceState_1226_);
lean_inc(v_auxDeclNGen_1225_);
lean_inc(v_ngen_1224_);
lean_inc(v_nextMacroScope_1223_);
lean_inc(v_env_1222_);
lean_dec(v___x_1221_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1288_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_inc(v___x_1210_);
v___x_1233_ = l_Lean_Meta_addToCompletionBlackList(v_env_1222_, v___x_1210_);
v___x_1234_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 5, v___x_1234_);
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_nextMacroScope_1223_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_ngen_1224_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_auxDeclNGen_1225_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_traceState_1226_);
lean_ctor_set(v_reuseFailAlloc_1287_, 5, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1287_, 6, v_messages_1227_);
lean_ctor_set(v_reuseFailAlloc_1287_, 7, v_infoState_1228_);
lean_ctor_set(v_reuseFailAlloc_1287_, 8, v_snapshotTasks_1229_);
v___x_1236_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_mctx_1239_; lean_object* v_zetaDeltaFVarIds_1240_; lean_object* v_postponed_1241_; lean_object* v_diag_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1285_; 
v___x_1237_ = lean_st_ref_set(v_a_1188_, v___x_1236_);
v___x_1238_ = lean_st_ref_take(v_a_1186_);
v_mctx_1239_ = lean_ctor_get(v___x_1238_, 0);
v_zetaDeltaFVarIds_1240_ = lean_ctor_get(v___x_1238_, 2);
v_postponed_1241_ = lean_ctor_get(v___x_1238_, 3);
v_diag_1242_ = lean_ctor_get(v___x_1238_, 4);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1238_, 1);
lean_dec(v_unused_1286_);
v___x_1244_ = v___x_1238_;
v_isShared_1245_ = v_isSharedCheck_1285_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_diag_1242_);
lean_inc(v_postponed_1241_);
lean_inc(v_zetaDeltaFVarIds_1240_);
lean_inc(v_mctx_1239_);
lean_dec(v___x_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1285_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_mctx_1239_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_zetaDeltaFVarIds_1240_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_postponed_1241_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_diag_1242_);
v___x_1248_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_env_1251_; lean_object* v_nextMacroScope_1252_; lean_object* v_ngen_1253_; lean_object* v_auxDeclNGen_1254_; lean_object* v_traceState_1255_; lean_object* v_messages_1256_; lean_object* v_infoState_1257_; lean_object* v_snapshotTasks_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1282_; 
v___x_1249_ = lean_st_ref_set(v_a_1186_, v___x_1248_);
v___x_1250_ = lean_st_ref_take(v_a_1188_);
v_env_1251_ = lean_ctor_get(v___x_1250_, 0);
v_nextMacroScope_1252_ = lean_ctor_get(v___x_1250_, 1);
v_ngen_1253_ = lean_ctor_get(v___x_1250_, 2);
v_auxDeclNGen_1254_ = lean_ctor_get(v___x_1250_, 3);
v_traceState_1255_ = lean_ctor_get(v___x_1250_, 4);
v_messages_1256_ = lean_ctor_get(v___x_1250_, 6);
v_infoState_1257_ = lean_ctor_get(v___x_1250_, 7);
v_snapshotTasks_1258_ = lean_ctor_get(v___x_1250_, 8);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v___x_1250_, 5);
lean_dec(v_unused_1283_);
v___x_1260_ = v___x_1250_;
v_isShared_1261_ = v_isSharedCheck_1282_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_snapshotTasks_1258_);
lean_inc(v_infoState_1257_);
lean_inc(v_messages_1256_);
lean_inc(v_traceState_1255_);
lean_inc(v_auxDeclNGen_1254_);
lean_inc(v_ngen_1253_);
lean_inc(v_nextMacroScope_1252_);
lean_inc(v_env_1251_);
lean_dec(v___x_1250_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1282_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
lean_inc(v___x_1210_);
v___x_1262_ = l_Lean_addProtected(v_env_1251_, v___x_1210_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 5, v___x_1234_);
lean_ctor_set(v___x_1260_, 0, v___x_1262_);
v___x_1264_ = v___x_1260_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_nextMacroScope_1252_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_ngen_1253_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_auxDeclNGen_1254_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v_traceState_1255_);
lean_ctor_set(v_reuseFailAlloc_1281_, 5, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1281_, 6, v_messages_1256_);
lean_ctor_set(v_reuseFailAlloc_1281_, 7, v_infoState_1257_);
lean_ctor_set(v_reuseFailAlloc_1281_, 8, v_snapshotTasks_1258_);
v___x_1264_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_mctx_1267_; lean_object* v_zetaDeltaFVarIds_1268_; lean_object* v_postponed_1269_; lean_object* v_diag_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1279_; 
v___x_1265_ = lean_st_ref_set(v_a_1188_, v___x_1264_);
v___x_1266_ = lean_st_ref_take(v_a_1186_);
v_mctx_1267_ = lean_ctor_get(v___x_1266_, 0);
v_zetaDeltaFVarIds_1268_ = lean_ctor_get(v___x_1266_, 2);
v_postponed_1269_ = lean_ctor_get(v___x_1266_, 3);
v_diag_1270_ = lean_ctor_get(v___x_1266_, 4);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1266_, 1);
lean_dec(v_unused_1280_);
v___x_1272_ = v___x_1266_;
v_isShared_1273_ = v_isSharedCheck_1279_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_diag_1270_);
lean_inc(v_postponed_1269_);
lean_inc(v_zetaDeltaFVarIds_1268_);
lean_inc(v_mctx_1267_);
lean_dec(v___x_1266_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1279_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1246_);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_mctx_1267_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_zetaDeltaFVarIds_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_postponed_1269_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_diag_1270_);
v___x_1275_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_st_ref_set(v_a_1186_, v___x_1275_);
v___x_1277_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_1210_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1277_;
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
lean_dec(v___x_1210_);
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_a_1207_);
lean_dec(v_levelParams_1202_);
lean_dec(v_indName_1184_);
v_a_1292_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1208_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1208_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_levelParams_1202_);
lean_dec(v_indName_1184_);
v_a_1300_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1206_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1206_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v_val_1195_);
lean_dec(v_indName_1184_);
v_a_1308_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1200_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1200_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec_ref(v_val_1195_);
lean_dec(v_indName_1184_);
v___x_1316_ = lean_box(0);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1316_);
v___x_1318_ = v___x_1193_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_del_object(v___x_1193_);
lean_dec(v_a_1191_);
lean_dec(v_indName_1184_);
v___x_1320_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2);
v___x_1321_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_1320_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_indName_1184_);
v_a_1323_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1190_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1190_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___boxed(lean_object* v_indName_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4(lean_object* v_00_u03b1_1338_, lean_object* v_name_1339_, uint8_t v_bi_1340_, lean_object* v_type_1341_, lean_object* v_k_1342_, uint8_t v_kind_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(v_name_1339_, v_bi_1340_, v_type_1341_, v_k_1342_, v_kind_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_name_1351_, lean_object* v_bi_1352_, lean_object* v_type_1353_, lean_object* v_k_1354_, lean_object* v_kind_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
uint8_t v_bi_boxed_1361_; uint8_t v_kind_boxed_1362_; lean_object* v_res_1363_; 
v_bi_boxed_1361_ = lean_unbox(v_bi_1352_);
v_kind_boxed_1362_ = lean_unbox(v_kind_1355_);
v_res_1363_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4(v_00_u03b1_1350_, v_name_1351_, v_bi_boxed_1361_, v_type_1353_, v_k_1354_, v_kind_boxed_1362_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(lean_object* v_00_u03b1_1364_, lean_object* v_name_1365_, lean_object* v_type_1366_, lean_object* v_k_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v_name_1365_, v_type_1366_, v_k_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_name_1375_, lean_object* v_type_1376_, lean_object* v_k_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v_00_u03b1_1374_, v_name_1375_, v_type_1376_, v_k_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(lean_object* v_declName_1384_, uint8_t v_s_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1384_, v_s_1385_, v___y_1387_, v___y_1389_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___boxed(lean_object* v_declName_1392_, lean_object* v_s_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v_s_boxed_1399_; lean_object* v_res_1400_; 
v_s_boxed_1399_ = lean_unbox(v_s_1393_);
v_res_1400_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(v_declName_1392_, v_s_boxed_1399_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(lean_object* v_00_u03b1_1401_, lean_object* v_constName_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_constName_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(v_00_u03b1_1409_, v_constName_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_1417_, lean_object* v_ref_1418_, lean_object* v_constName_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1418_, v_constName_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1426_, lean_object* v_ref_1427_, lean_object* v_constName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(v_00_u03b1_1426_, v_ref_1427_, v_constName_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_ref_1427_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_1435_, lean_object* v_ref_1436_, lean_object* v_msg_1437_, lean_object* v_declHint_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1436_, v_msg_1437_, v_declHint_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_1445_, lean_object* v_ref_1446_, lean_object* v_msg_1447_, lean_object* v_declHint_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_1445_, v_ref_1446_, v_msg_1447_, v_declHint_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v_ref_1446_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_1455_, lean_object* v_declHint_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_1455_, v_declHint_1456_, v___y_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1463_, lean_object* v_declHint_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_1463_, v_declHint_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_1471_, lean_object* v_ref_1472_, lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_1472_, v_msg_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_ref_1481_, lean_object* v_msg_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_1480_, v_ref_1481_, v_msg_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v_ref_1481_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(lean_object* v___x_1489_, lean_object* v_k_1490_, lean_object* v_zs_1491_, uint8_t v___x_1492_, uint8_t v___x_1493_, uint8_t v___x_1494_, lean_object* v_h_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
lean_inc_ref(v_h_1495_);
v___x_1501_ = l_Lean_Meta_mkEqNDRec(v___x_1489_, v_k_1490_, v_h_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_a_1502_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = l_Lean_mkAppN(v_a_1504_, v_zs_1491_);
v___x_1506_ = lean_array_push(v_zs_1491_, v_h_1495_);
v___x_1507_ = l_Lean_Meta_mkLambdaFVars(v___x_1506_, v___x_1505_, v___x_1492_, v___x_1493_, v___x_1492_, v___x_1493_, v___x_1494_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec_ref(v___x_1506_);
return v___x_1507_;
}
else
{
lean_dec_ref(v_h_1495_);
lean_dec_ref(v_zs_1491_);
return v___x_1503_;
}
}
else
{
lean_dec_ref(v_h_1495_);
lean_dec_ref(v_zs_1491_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___x_1508_, lean_object* v_k_1509_, lean_object* v_zs_1510_, lean_object* v___x_1511_, lean_object* v___x_1512_, lean_object* v___x_1513_, lean_object* v_h_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v___x_6019__boxed_1520_; uint8_t v___x_6020__boxed_1521_; uint8_t v___x_6021__boxed_1522_; lean_object* v_res_1523_; 
v___x_6019__boxed_1520_ = lean_unbox(v___x_1511_);
v___x_6020__boxed_1521_ = lean_unbox(v___x_1512_);
v___x_6021__boxed_1522_ = lean_unbox(v___x_1513_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(v___x_1508_, v_k_1509_, v_zs_1510_, v___x_6019__boxed_1520_, v___x_6020__boxed_1521_, v___x_6021__boxed_1522_, v_h_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(lean_object* v___x_1527_, lean_object* v_k_1528_, uint8_t v___x_1529_, uint8_t v___x_1530_, uint8_t v___x_1531_, lean_object* v___x_1532_, lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v___x_1535_, lean_object* v_ctorIdx_1536_, lean_object* v___x_1537_, lean_object* v_zs_1538_, lean_object* v___ctorRet_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1545_ = lean_box(v___x_1529_);
v___x_1546_ = lean_box(v___x_1530_);
v___x_1547_ = lean_box(v___x_1531_);
v___f_1548_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1548_, 0, v___x_1527_);
lean_closure_set(v___f_1548_, 1, v_k_1528_);
lean_closure_set(v___f_1548_, 2, v_zs_1538_);
lean_closure_set(v___f_1548_, 3, v___x_1545_);
lean_closure_set(v___f_1548_, 4, v___x_1546_);
lean_closure_set(v___f_1548_, 5, v___x_1547_);
v___x_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1));
v___x_1550_ = l_Lean_Level_ofNat(v___x_1532_);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___x_1533_);
v___x_1552_ = l_Lean_mkConst(v___x_1549_, v___x_1551_);
v___x_1553_ = l_Lean_mkRawNatLit(v___x_1534_);
v___x_1554_ = l_Lean_mkApp3(v___x_1552_, v___x_1535_, v_ctorIdx_1536_, v___x_1553_);
v___x_1555_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_1537_, v___x_1554_, v___f_1548_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1556_ = _args[0];
lean_object* v_k_1557_ = _args[1];
lean_object* v___x_1558_ = _args[2];
lean_object* v___x_1559_ = _args[3];
lean_object* v___x_1560_ = _args[4];
lean_object* v___x_1561_ = _args[5];
lean_object* v___x_1562_ = _args[6];
lean_object* v___x_1563_ = _args[7];
lean_object* v___x_1564_ = _args[8];
lean_object* v_ctorIdx_1565_ = _args[9];
lean_object* v___x_1566_ = _args[10];
lean_object* v_zs_1567_ = _args[11];
lean_object* v___ctorRet_1568_ = _args[12];
lean_object* v___y_1569_ = _args[13];
lean_object* v___y_1570_ = _args[14];
lean_object* v___y_1571_ = _args[15];
lean_object* v___y_1572_ = _args[16];
lean_object* v___y_1573_ = _args[17];
_start:
{
uint8_t v___x_6068__boxed_1574_; uint8_t v___x_6069__boxed_1575_; uint8_t v___x_6070__boxed_1576_; lean_object* v_res_1577_; 
v___x_6068__boxed_1574_ = lean_unbox(v___x_1558_);
v___x_6069__boxed_1575_ = lean_unbox(v___x_1559_);
v___x_6070__boxed_1576_ = lean_unbox(v___x_1560_);
v_res_1577_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(v___x_1556_, v_k_1557_, v___x_6068__boxed_1574_, v___x_6069__boxed_1575_, v___x_6070__boxed_1576_, v___x_1561_, v___x_1562_, v___x_1563_, v___x_1564_, v_ctorIdx_1565_, v___x_1566_, v_zs_1567_, v___ctorRet_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec_ref(v___ctorRet_1568_);
lean_dec(v___x_1561_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(lean_object* v___x_1581_, lean_object* v_k_1582_, lean_object* v_ctorIdx_1583_, lean_object* v_tail_1584_, lean_object* v___x_1585_, size_t v_sz_1586_, size_t v_i_1587_, lean_object* v_bs_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_usize_dec_lt(v_i_1587_, v_sz_1586_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; 
lean_dec(v_tail_1584_);
lean_dec_ref(v_ctorIdx_1583_);
lean_dec_ref(v_k_1582_);
lean_dec_ref(v___x_1581_);
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_bs_1588_);
return v___x_1595_;
}
else
{
lean_object* v_v_1596_; lean_object* v___x_1597_; lean_object* v_bs_x27_1598_; lean_object* v___y_1600_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_v_1596_ = lean_array_uget(v_bs_1588_, v_i_1587_);
v___x_1597_ = lean_unsigned_to_nat(0u);
v_bs_x27_1598_ = lean_array_uset(v_bs_1588_, v_i_1587_, v___x_1597_);
lean_inc(v_tail_1584_);
v___x_1614_ = l_Lean_mkConst(v_v_1596_, v_tail_1584_);
v___x_1615_ = l_Lean_mkAppN(v___x_1614_, v___x_1585_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
v___x_1616_ = lean_infer_type(v___x_1615_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; uint8_t v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = 0;
v___x_1619_ = 1;
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_1623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_1624_ = lean_usize_to_nat(v_i_1587_);
v___x_1625_ = lean_box(v___x_1618_);
v___x_1626_ = lean_box(v___x_1594_);
v___x_1627_ = lean_box(v___x_1619_);
lean_inc_ref(v_ctorIdx_1583_);
lean_inc_ref(v_k_1582_);
lean_inc_ref(v___x_1581_);
v___f_1628_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed), 18, 11);
lean_closure_set(v___f_1628_, 0, v___x_1581_);
lean_closure_set(v___f_1628_, 1, v_k_1582_);
lean_closure_set(v___f_1628_, 2, v___x_1625_);
lean_closure_set(v___f_1628_, 3, v___x_1626_);
lean_closure_set(v___f_1628_, 4, v___x_1627_);
lean_closure_set(v___f_1628_, 5, v___x_1620_);
lean_closure_set(v___f_1628_, 6, v___x_1621_);
lean_closure_set(v___f_1628_, 7, v___x_1624_);
lean_closure_set(v___f_1628_, 8, v___x_1622_);
lean_closure_set(v___f_1628_, 9, v_ctorIdx_1583_);
lean_closure_set(v___f_1628_, 10, v___x_1623_);
v___x_1629_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_a_1617_, v___f_1628_, v___x_1618_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
v___y_1600_ = v___x_1629_;
goto v___jp_1599_;
}
else
{
v___y_1600_ = v___x_1616_;
goto v___jp_1599_;
}
v___jp_1599_:
{
if (lean_obj_tag(v___y_1600_) == 0)
{
lean_object* v_a_1601_; size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v_a_1601_ = lean_ctor_get(v___y_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___y_1600_, 1);
v___x_1602_ = ((size_t)1ULL);
v___x_1603_ = lean_usize_add(v_i_1587_, v___x_1602_);
v___x_1604_ = lean_array_uset(v_bs_x27_1598_, v_i_1587_, v_a_1601_);
v_i_1587_ = v___x_1603_;
v_bs_1588_ = v___x_1604_;
goto _start;
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v_bs_x27_1598_);
lean_dec(v_tail_1584_);
lean_dec_ref(v_ctorIdx_1583_);
lean_dec_ref(v_k_1582_);
lean_dec_ref(v___x_1581_);
v_a_1606_ = lean_ctor_get(v___y_1600_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___y_1600_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___y_1600_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___y_1600_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___boxed(lean_object* v___x_1630_, lean_object* v_k_1631_, lean_object* v_ctorIdx_1632_, lean_object* v_tail_1633_, lean_object* v___x_1634_, lean_object* v_sz_1635_, lean_object* v_i_1636_, lean_object* v_bs_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
size_t v_sz_boxed_1643_; size_t v_i_boxed_1644_; lean_object* v_res_1645_; 
v_sz_boxed_1643_ = lean_unbox_usize(v_sz_1635_);
lean_dec(v_sz_1635_);
v_i_boxed_1644_ = lean_unbox_usize(v_i_1636_);
lean_dec(v_i_1636_);
v_res_1645_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1630_, v_k_1631_, v_ctorIdx_1632_, v_tail_1633_, v___x_1634_, v_sz_boxed_1643_, v_i_boxed_1644_, v_bs_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v___x_1634_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(lean_object* v___x_1646_, lean_object* v___x_1647_, lean_object* v_a_1648_, lean_object* v_ctors_1649_, lean_object* v___x_1650_, lean_object* v_ctorIdx_1651_, lean_object* v_tail_1652_, lean_object* v___x_1653_, lean_object* v_name_1654_, lean_object* v___x_1655_, lean_object* v_h_1656_, lean_object* v_k_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_inc_ref(v___x_1646_);
v___x_1663_ = l_Lean_mkAppN(v___x_1646_, v___x_1647_);
v___x_1664_ = l_Lean_mkArrow(v_a_1648_, v___x_1663_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; uint8_t v___x_1666_; uint8_t v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = 0;
v___x_1667_ = 1;
v___x_1668_ = 1;
v___x_1669_ = l_Lean_Meta_mkLambdaFVars(v___x_1647_, v_a_1665_, v___x_1666_, v___x_1667_, v___x_1666_, v___x_1667_, v___x_1668_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; size_t v_sz_1672_; size_t v___x_1673_; lean_object* v___x_1674_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = lean_array_mk(v_ctors_1649_);
v_sz_1672_ = lean_array_size(v___x_1671_);
v___x_1673_ = ((size_t)0ULL);
lean_inc_ref(v_ctorIdx_1651_);
lean_inc_ref(v_k_1657_);
v___x_1674_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1650_, v_k_1657_, v_ctorIdx_1651_, v_tail_1652_, v___x_1653_, v_sz_1672_, v___x_1673_, v___x_1671_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
v___x_1676_ = l_Lean_mkConst(v_name_1654_, v___x_1655_);
v___x_1677_ = l_Lean_mkAppN(v___x_1676_, v___x_1653_);
v___x_1678_ = l_Lean_Expr_app___override(v___x_1677_, v_a_1670_);
v___x_1679_ = l_Lean_mkAppN(v___x_1678_, v___x_1647_);
v___x_1680_ = l_Lean_mkAppN(v___x_1679_, v_a_1675_);
lean_dec(v_a_1675_);
lean_inc_ref(v_h_1656_);
v___x_1681_ = l_Lean_Expr_app___override(v___x_1680_, v_h_1656_);
v___x_1682_ = lean_unsigned_to_nat(2u);
v___x_1683_ = lean_mk_empty_array_with_capacity(v___x_1682_);
lean_inc_ref(v___x_1683_);
v___x_1684_ = lean_array_push(v___x_1683_, v___x_1646_);
v___x_1685_ = lean_array_push(v___x_1684_, v_ctorIdx_1651_);
v___x_1686_ = l_Array_append___redArg(v___x_1653_, v___x_1685_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = l_Array_append___redArg(v___x_1686_, v___x_1647_);
v___x_1688_ = lean_array_push(v___x_1683_, v_h_1656_);
v___x_1689_ = lean_array_push(v___x_1688_, v_k_1657_);
v___x_1690_ = l_Array_append___redArg(v___x_1687_, v___x_1689_);
lean_dec_ref(v___x_1689_);
v___x_1691_ = l_Lean_Meta_mkLambdaFVars(v___x_1690_, v___x_1681_, v___x_1666_, v___x_1667_, v___x_1666_, v___x_1667_, v___x_1668_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec_ref(v___x_1690_);
return v___x_1691_;
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_a_1670_);
lean_dec_ref(v_k_1657_);
lean_dec_ref(v_h_1656_);
lean_dec(v___x_1655_);
lean_dec(v_name_1654_);
lean_dec_ref(v___x_1653_);
lean_dec_ref(v_ctorIdx_1651_);
lean_dec_ref(v___x_1646_);
v_a_1692_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1674_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1674_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
else
{
lean_dec_ref(v_k_1657_);
lean_dec_ref(v_h_1656_);
lean_dec(v___x_1655_);
lean_dec(v_name_1654_);
lean_dec_ref(v___x_1653_);
lean_dec(v_tail_1652_);
lean_dec_ref(v_ctorIdx_1651_);
lean_dec_ref(v___x_1650_);
lean_dec(v_ctors_1649_);
lean_dec_ref(v___x_1646_);
return v___x_1669_;
}
}
else
{
lean_dec_ref(v_k_1657_);
lean_dec_ref(v_h_1656_);
lean_dec(v___x_1655_);
lean_dec(v_name_1654_);
lean_dec_ref(v___x_1653_);
lean_dec(v_tail_1652_);
lean_dec_ref(v_ctorIdx_1651_);
lean_dec_ref(v___x_1650_);
lean_dec(v_ctors_1649_);
lean_dec_ref(v___x_1646_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed(lean_object** _args){
lean_object* v___x_1700_ = _args[0];
lean_object* v___x_1701_ = _args[1];
lean_object* v_a_1702_ = _args[2];
lean_object* v_ctors_1703_ = _args[3];
lean_object* v___x_1704_ = _args[4];
lean_object* v_ctorIdx_1705_ = _args[5];
lean_object* v_tail_1706_ = _args[6];
lean_object* v___x_1707_ = _args[7];
lean_object* v_name_1708_ = _args[8];
lean_object* v___x_1709_ = _args[9];
lean_object* v_h_1710_ = _args[10];
lean_object* v_k_1711_ = _args[11];
lean_object* v___y_1712_ = _args[12];
lean_object* v___y_1713_ = _args[13];
lean_object* v___y_1714_ = _args[14];
lean_object* v___y_1715_ = _args[15];
lean_object* v___y_1716_ = _args[16];
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(v___x_1700_, v___x_1701_, v_a_1702_, v_ctors_1703_, v___x_1704_, v_ctorIdx_1705_, v_tail_1706_, v___x_1707_, v_name_1708_, v___x_1709_, v_h_1710_, v_k_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec_ref(v___x_1701_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v_a_1723_, lean_object* v_ctors_1724_, lean_object* v___x_1725_, lean_object* v_ctorIdx_1726_, lean_object* v_tail_1727_, lean_object* v___x_1728_, lean_object* v_name_1729_, lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v_h_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___f_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___f_1738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1738_, 0, v___x_1721_);
lean_closure_set(v___f_1738_, 1, v___x_1722_);
lean_closure_set(v___f_1738_, 2, v_a_1723_);
lean_closure_set(v___f_1738_, 3, v_ctors_1724_);
lean_closure_set(v___f_1738_, 4, v___x_1725_);
lean_closure_set(v___f_1738_, 5, v_ctorIdx_1726_);
lean_closure_set(v___f_1738_, 6, v_tail_1727_);
lean_closure_set(v___f_1738_, 7, v___x_1728_);
lean_closure_set(v___f_1738_, 8, v_name_1729_);
lean_closure_set(v___f_1738_, 9, v___x_1730_);
lean_closure_set(v___f_1738_, 10, v_h_1732_);
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1));
v___x_1740_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_1739_, v___x_1731_, v___f_1738_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed(lean_object** _args){
lean_object* v___x_1741_ = _args[0];
lean_object* v___x_1742_ = _args[1];
lean_object* v_a_1743_ = _args[2];
lean_object* v_ctors_1744_ = _args[3];
lean_object* v___x_1745_ = _args[4];
lean_object* v_ctorIdx_1746_ = _args[5];
lean_object* v_tail_1747_ = _args[6];
lean_object* v___x_1748_ = _args[7];
lean_object* v_name_1749_ = _args[8];
lean_object* v___x_1750_ = _args[9];
lean_object* v___x_1751_ = _args[10];
lean_object* v_h_1752_ = _args[11];
lean_object* v___y_1753_ = _args[12];
lean_object* v___y_1754_ = _args[13];
lean_object* v___y_1755_ = _args[14];
lean_object* v___y_1756_ = _args[15];
lean_object* v___y_1757_ = _args[16];
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(v___x_1741_, v___x_1742_, v_a_1743_, v_ctors_1744_, v___x_1745_, v_ctorIdx_1746_, v_tail_1747_, v___x_1748_, v_name_1749_, v___x_1750_, v___x_1751_, v_h_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(lean_object* v___x_1759_, lean_object* v___x_1760_, lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v_indName_1763_, lean_object* v_tail_1764_, lean_object* v___x_1765_, lean_object* v_ctors_1766_, lean_object* v_name_1767_, lean_object* v_ctorIdx_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_inc(v___x_1760_);
v___x_1774_ = l_Lean_mkConst(v___x_1759_, v___x_1760_);
lean_inc_ref(v___x_1762_);
lean_inc_ref_n(v___x_1761_, 2);
v___x_1775_ = lean_array_push(v___x_1761_, v___x_1762_);
v___x_1776_ = l_Lean_mkAppN(v___x_1774_, v___x_1775_);
lean_dec_ref(v___x_1775_);
lean_inc_ref_n(v_ctorIdx_1768_, 2);
lean_inc_ref(v___x_1776_);
v___x_1777_ = l_Lean_Expr_app___override(v___x_1776_, v_ctorIdx_1768_);
v___x_1778_ = l_Lean_mkCtorIdxName(v_indName_1763_);
lean_inc(v_tail_1764_);
v___x_1779_ = l_Lean_mkConst(v___x_1778_, v_tail_1764_);
v___x_1780_ = l_Array_append___redArg(v___x_1761_, v___x_1765_);
v___x_1781_ = l_Lean_mkAppN(v___x_1779_, v___x_1780_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = l_Lean_Meta_mkEq(v_ctorIdx_1768_, v___x_1781_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc_n(v_a_1783_, 2);
lean_dec_ref_known(v___x_1782_, 1);
v___f_1784_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed), 17, 11);
lean_closure_set(v___f_1784_, 0, v___x_1762_);
lean_closure_set(v___f_1784_, 1, v___x_1765_);
lean_closure_set(v___f_1784_, 2, v_a_1783_);
lean_closure_set(v___f_1784_, 3, v_ctors_1766_);
lean_closure_set(v___f_1784_, 4, v___x_1776_);
lean_closure_set(v___f_1784_, 5, v_ctorIdx_1768_);
lean_closure_set(v___f_1784_, 6, v_tail_1764_);
lean_closure_set(v___f_1784_, 7, v___x_1761_);
lean_closure_set(v___f_1784_, 8, v_name_1767_);
lean_closure_set(v___f_1784_, 9, v___x_1760_);
lean_closure_set(v___f_1784_, 10, v___x_1777_);
v___x_1785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_1786_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_1785_, v_a_1783_, v___f_1784_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1786_;
}
else
{
lean_dec_ref(v___x_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v_ctorIdx_1768_);
lean_dec(v_name_1767_);
lean_dec(v_ctors_1766_);
lean_dec_ref(v___x_1765_);
lean_dec(v_tail_1764_);
lean_dec_ref(v___x_1762_);
lean_dec_ref(v___x_1761_);
lean_dec(v___x_1760_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed(lean_object* v___x_1787_, lean_object* v___x_1788_, lean_object* v___x_1789_, lean_object* v___x_1790_, lean_object* v_indName_1791_, lean_object* v_tail_1792_, lean_object* v___x_1793_, lean_object* v_ctors_1794_, lean_object* v_name_1795_, lean_object* v_ctorIdx_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(v___x_1787_, v___x_1788_, v___x_1789_, v___x_1790_, v_indName_1791_, v_tail_1792_, v___x_1793_, v_ctors_1794_, v_name_1795_, v_ctorIdx_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(lean_object* v_val_1803_, lean_object* v___x_1804_, lean_object* v___x_1805_, lean_object* v___x_1806_, lean_object* v_indName_1807_, lean_object* v_tail_1808_, lean_object* v_name_1809_, lean_object* v___x_1810_, lean_object* v_xs_1811_, lean_object* v_x_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_numParams_1818_; lean_object* v_numIndices_1819_; lean_object* v_ctors_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_numParams_1818_ = lean_ctor_get(v_val_1803_, 1);
lean_inc_n(v_numParams_1818_, 2);
v_numIndices_1819_ = lean_ctor_get(v_val_1803_, 2);
lean_inc(v_numIndices_1819_);
v_ctors_1820_ = lean_ctor_get(v_val_1803_, 4);
lean_inc(v_ctors_1820_);
lean_dec_ref(v_val_1803_);
v___x_1821_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_1811_, 2);
v___x_1822_ = l_Array_toSubarray___redArg(v_xs_1811_, v___x_1821_, v_numParams_1818_);
v___x_1823_ = l_Subarray_copy___redArg(v___x_1822_);
v___x_1824_ = lean_array_get(v___x_1804_, v_xs_1811_, v_numParams_1818_);
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_nat_add(v_numParams_1818_, v___x_1825_);
lean_dec(v_numParams_1818_);
v___x_1827_ = lean_nat_add(v___x_1826_, v_numIndices_1819_);
lean_dec(v_numIndices_1819_);
lean_inc(v___x_1827_);
v___x_1828_ = l_Array_toSubarray___redArg(v_xs_1811_, v___x_1826_, v___x_1827_);
v___x_1829_ = l_Subarray_copy___redArg(v___x_1828_);
v___x_1830_ = lean_array_get(v___x_1804_, v_xs_1811_, v___x_1827_);
lean_dec(v___x_1827_);
lean_dec_ref(v_xs_1811_);
v___x_1831_ = lean_array_push(v___x_1829_, v___x_1830_);
v___f_1832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed), 15, 9);
lean_closure_set(v___f_1832_, 0, v___x_1805_);
lean_closure_set(v___f_1832_, 1, v___x_1806_);
lean_closure_set(v___f_1832_, 2, v___x_1823_);
lean_closure_set(v___f_1832_, 3, v___x_1824_);
lean_closure_set(v___f_1832_, 4, v_indName_1807_);
lean_closure_set(v___f_1832_, 5, v_tail_1808_);
lean_closure_set(v___f_1832_, 6, v___x_1831_);
lean_closure_set(v___f_1832_, 7, v_ctors_1820_);
lean_closure_set(v___f_1832_, 8, v_name_1809_);
v___x_1833_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_1834_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_1835_ = l_Lean_mkConst(v___x_1834_, v___x_1810_);
v___x_1836_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_1833_, v___x_1835_, v___f_1832_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed(lean_object* v_val_1837_, lean_object* v___x_1838_, lean_object* v___x_1839_, lean_object* v___x_1840_, lean_object* v_indName_1841_, lean_object* v_tail_1842_, lean_object* v_name_1843_, lean_object* v___x_1844_, lean_object* v_xs_1845_, lean_object* v_x_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(v_val_1837_, v___x_1838_, v___x_1839_, v___x_1840_, v_indName_1841_, v_tail_1842_, v_name_1843_, v___x_1844_, v_xs_1845_, v_x_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v_x_1846_);
lean_dec_ref(v___x_1838_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
if (lean_obj_tag(v_a_1853_) == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = l_List_reverse___redArg(v_a_1854_);
return v___x_1855_;
}
else
{
lean_object* v_head_1856_; lean_object* v_tail_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
v_head_1856_ = lean_ctor_get(v_a_1853_, 0);
v_tail_1857_ = lean_ctor_get(v_a_1853_, 1);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_a_1853_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1859_ = v_a_1853_;
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_tail_1857_);
lean_inc(v_head_1856_);
lean_dec(v_a_1853_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = l_Lean_mkLevelParam(v_head_1856_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v_a_1854_);
lean_ctor_set(v___x_1859_, 0, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_a_1854_);
v___x_1863_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
v_a_1853_ = v_tail_1857_;
v_a_1854_ = v___x_1863_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1869_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_1870_ = lean_unsigned_to_nat(58u);
v___x_1871_ = lean_unsigned_to_nat(113u);
v___x_1872_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1873_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1874_ = l_mkPanicMessageWithDecl(v___x_1873_, v___x_1872_, v___x_1871_, v___x_1870_, v___x_1869_);
return v___x_1874_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1876_ = lean_unsigned_to_nat(60u);
v___x_1877_ = lean_unsigned_to_nat(109u);
v___x_1878_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1879_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1880_ = l_mkPanicMessageWithDecl(v___x_1879_, v___x_1878_, v___x_1877_, v___x_1876_, v___x_1875_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(lean_object* v_indName_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v___x_1887_; 
lean_inc(v_indName_1881_);
v___x_1887_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
if (lean_obj_tag(v_a_1888_) == 5)
{
lean_object* v_val_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_val_1889_ = lean_ctor_get(v_a_1888_, 0);
lean_inc_ref(v_val_1889_);
lean_dec_ref_known(v_a_1888_, 1);
lean_inc_n(v_indName_1881_, 2);
v___x_1890_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1881_);
v___x_1891_ = l_Lean_mkCasesOnName(v_indName_1881_);
v___x_1892_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v___x_1891_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v_name_1894_; lean_object* v_levelParams_1895_; lean_object* v_type_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v_name_1894_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_name_1894_);
v_levelParams_1895_ = lean_ctor_get(v_a_1893_, 1);
lean_inc_n(v_levelParams_1895_, 2);
v_type_1896_ = lean_ctor_get(v_a_1893_, 2);
lean_inc_ref(v_type_1896_);
lean_dec(v_a_1893_);
v___x_1897_ = lean_box(0);
v___x_1898_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_1895_, v___x_1897_);
if (lean_obj_tag(v___x_1898_) == 1)
{
lean_object* v_tail_1899_; lean_object* v___x_1900_; lean_object* v___f_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; 
v_tail_1899_ = lean_ctor_get(v___x_1898_, 1);
lean_inc(v_tail_1899_);
v___x_1900_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1881_);
v___f_1901_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed), 15, 8);
lean_closure_set(v___f_1901_, 0, v_val_1889_);
lean_closure_set(v___f_1901_, 1, v___x_1900_);
lean_closure_set(v___f_1901_, 2, v___x_1890_);
lean_closure_set(v___f_1901_, 3, v___x_1898_);
lean_closure_set(v___f_1901_, 4, v_indName_1881_);
lean_closure_set(v___f_1901_, 5, v_tail_1899_);
lean_closure_set(v___f_1901_, 6, v_name_1894_);
lean_closure_set(v___f_1901_, 7, v___x_1897_);
v___x_1902_ = 0;
v___x_1903_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1896_, v___f_1901_, v___x_1902_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc_n(v_a_1904_, 2);
lean_dec_ref_known(v___x_1903_, 1);
lean_inc(v_a_1885_);
lean_inc_ref(v_a_1884_);
lean_inc(v_a_1883_);
lean_inc_ref(v_a_1882_);
v___x_1905_ = lean_infer_type(v_a_1904_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_2021_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = l_Lean_mkCtorElimName(v_indName_1881_);
v___x_1908_ = lean_box(1);
lean_inc(v___x_1907_);
v___x_1909_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1907_, v_levelParams_1895_, v_a_1906_, v_a_1904_, v___x_1908_, v_a_1885_);
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_2021_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_2021_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 1);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_2020_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
uint8_t v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = 1;
v___x_1917_ = l_Lean_addAndCompile(v___x_1915_, v___x_1916_, v___x_1902_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v___x_1918_; lean_object* v_env_1919_; lean_object* v_nextMacroScope_1920_; lean_object* v_ngen_1921_; lean_object* v_auxDeclNGen_1922_; lean_object* v_traceState_1923_; lean_object* v_messages_1924_; lean_object* v_infoState_1925_; lean_object* v_snapshotTasks_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref_known(v___x_1917_, 1);
v___x_1918_ = lean_st_ref_take(v_a_1885_);
v_env_1919_ = lean_ctor_get(v___x_1918_, 0);
v_nextMacroScope_1920_ = lean_ctor_get(v___x_1918_, 1);
v_ngen_1921_ = lean_ctor_get(v___x_1918_, 2);
v_auxDeclNGen_1922_ = lean_ctor_get(v___x_1918_, 3);
v_traceState_1923_ = lean_ctor_get(v___x_1918_, 4);
v_messages_1924_ = lean_ctor_get(v___x_1918_, 6);
v_infoState_1925_ = lean_ctor_get(v___x_1918_, 7);
v_snapshotTasks_1926_ = lean_ctor_get(v___x_1918_, 8);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_1918_, 5);
lean_dec(v_unused_2019_);
v___x_1928_ = v___x_1918_;
v_isShared_1929_ = v_isSharedCheck_2018_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_snapshotTasks_1926_);
lean_inc(v_infoState_1925_);
lean_inc(v_messages_1924_);
lean_inc(v_traceState_1923_);
lean_inc(v_auxDeclNGen_1922_);
lean_inc(v_ngen_1921_);
lean_inc(v_nextMacroScope_1920_);
lean_inc(v_env_1919_);
lean_dec(v___x_1918_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_2018_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
lean_inc(v___x_1907_);
v___x_1930_ = l_Lean_markAuxRecursor(v_env_1919_, v___x_1907_);
v___x_1931_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 5, v___x_1931_);
lean_ctor_set(v___x_1928_, 0, v___x_1930_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_nextMacroScope_1920_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_ngen_1921_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_auxDeclNGen_1922_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_traceState_1923_);
lean_ctor_set(v_reuseFailAlloc_2017_, 5, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_2017_, 6, v_messages_1924_);
lean_ctor_set(v_reuseFailAlloc_2017_, 7, v_infoState_1925_);
lean_ctor_set(v_reuseFailAlloc_2017_, 8, v_snapshotTasks_1926_);
v___x_1933_ = v_reuseFailAlloc_2017_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_mctx_1936_; lean_object* v_zetaDeltaFVarIds_1937_; lean_object* v_postponed_1938_; lean_object* v_diag_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_2015_; 
v___x_1934_ = lean_st_ref_set(v_a_1885_, v___x_1933_);
v___x_1935_ = lean_st_ref_take(v_a_1883_);
v_mctx_1936_ = lean_ctor_get(v___x_1935_, 0);
v_zetaDeltaFVarIds_1937_ = lean_ctor_get(v___x_1935_, 2);
v_postponed_1938_ = lean_ctor_get(v___x_1935_, 3);
v_diag_1939_ = lean_ctor_get(v___x_1935_, 4);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v___x_1935_, 1);
lean_dec(v_unused_2016_);
v___x_1941_ = v___x_1935_;
v_isShared_1942_ = v_isSharedCheck_2015_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_diag_1939_);
lean_inc(v_postponed_1938_);
lean_inc(v_zetaDeltaFVarIds_1937_);
lean_inc(v_mctx_1936_);
lean_dec(v___x_1935_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_2015_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 1, v___x_1943_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_mctx_1936_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_zetaDeltaFVarIds_1937_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_postponed_1938_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_diag_1939_);
v___x_1945_ = v_reuseFailAlloc_2014_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_env_1948_; lean_object* v_nextMacroScope_1949_; lean_object* v_ngen_1950_; lean_object* v_auxDeclNGen_1951_; lean_object* v_traceState_1952_; lean_object* v_messages_1953_; lean_object* v_infoState_1954_; lean_object* v_snapshotTasks_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2012_; 
v___x_1946_ = lean_st_ref_set(v_a_1883_, v___x_1945_);
v___x_1947_ = lean_st_ref_take(v_a_1885_);
v_env_1948_ = lean_ctor_get(v___x_1947_, 0);
v_nextMacroScope_1949_ = lean_ctor_get(v___x_1947_, 1);
v_ngen_1950_ = lean_ctor_get(v___x_1947_, 2);
v_auxDeclNGen_1951_ = lean_ctor_get(v___x_1947_, 3);
v_traceState_1952_ = lean_ctor_get(v___x_1947_, 4);
v_messages_1953_ = lean_ctor_get(v___x_1947_, 6);
v_infoState_1954_ = lean_ctor_get(v___x_1947_, 7);
v_snapshotTasks_1955_ = lean_ctor_get(v___x_1947_, 8);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___x_1947_, 5);
lean_dec(v_unused_2013_);
v___x_1957_ = v___x_1947_;
v_isShared_1958_ = v_isSharedCheck_2012_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_snapshotTasks_1955_);
lean_inc(v_infoState_1954_);
lean_inc(v_messages_1953_);
lean_inc(v_traceState_1952_);
lean_inc(v_auxDeclNGen_1951_);
lean_inc(v_ngen_1950_);
lean_inc(v_nextMacroScope_1949_);
lean_inc(v_env_1948_);
lean_dec(v___x_1947_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2012_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
lean_inc(v___x_1907_);
v___x_1959_ = l_Lean_Meta_addToCompletionBlackList(v_env_1948_, v___x_1907_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 5, v___x_1931_);
lean_ctor_set(v___x_1957_, 0, v___x_1959_);
v___x_1961_ = v___x_1957_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_nextMacroScope_1949_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_ngen_1950_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_auxDeclNGen_1951_);
lean_ctor_set(v_reuseFailAlloc_2011_, 4, v_traceState_1952_);
lean_ctor_set(v_reuseFailAlloc_2011_, 5, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_2011_, 6, v_messages_1953_);
lean_ctor_set(v_reuseFailAlloc_2011_, 7, v_infoState_1954_);
lean_ctor_set(v_reuseFailAlloc_2011_, 8, v_snapshotTasks_1955_);
v___x_1961_ = v_reuseFailAlloc_2011_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_mctx_1964_; lean_object* v_zetaDeltaFVarIds_1965_; lean_object* v_postponed_1966_; lean_object* v_diag_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2009_; 
v___x_1962_ = lean_st_ref_set(v_a_1885_, v___x_1961_);
v___x_1963_ = lean_st_ref_take(v_a_1883_);
v_mctx_1964_ = lean_ctor_get(v___x_1963_, 0);
v_zetaDeltaFVarIds_1965_ = lean_ctor_get(v___x_1963_, 2);
v_postponed_1966_ = lean_ctor_get(v___x_1963_, 3);
v_diag_1967_ = lean_ctor_get(v___x_1963_, 4);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v___x_1963_, 1);
lean_dec(v_unused_2010_);
v___x_1969_ = v___x_1963_;
v_isShared_1970_ = v_isSharedCheck_2009_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_diag_1967_);
lean_inc(v_postponed_1966_);
lean_inc(v_zetaDeltaFVarIds_1965_);
lean_inc(v_mctx_1964_);
lean_dec(v___x_1963_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2009_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v___x_1943_);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_mctx_1964_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_zetaDeltaFVarIds_1965_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_postponed_1966_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_diag_1967_);
v___x_1972_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_env_1975_; lean_object* v_nextMacroScope_1976_; lean_object* v_ngen_1977_; lean_object* v_auxDeclNGen_1978_; lean_object* v_traceState_1979_; lean_object* v_messages_1980_; lean_object* v_infoState_1981_; lean_object* v_snapshotTasks_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2006_; 
v___x_1973_ = lean_st_ref_set(v_a_1883_, v___x_1972_);
v___x_1974_ = lean_st_ref_take(v_a_1885_);
v_env_1975_ = lean_ctor_get(v___x_1974_, 0);
v_nextMacroScope_1976_ = lean_ctor_get(v___x_1974_, 1);
v_ngen_1977_ = lean_ctor_get(v___x_1974_, 2);
v_auxDeclNGen_1978_ = lean_ctor_get(v___x_1974_, 3);
v_traceState_1979_ = lean_ctor_get(v___x_1974_, 4);
v_messages_1980_ = lean_ctor_get(v___x_1974_, 6);
v_infoState_1981_ = lean_ctor_get(v___x_1974_, 7);
v_snapshotTasks_1982_ = lean_ctor_get(v___x_1974_, 8);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v___x_1974_, 5);
lean_dec(v_unused_2007_);
v___x_1984_ = v___x_1974_;
v_isShared_1985_ = v_isSharedCheck_2006_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_snapshotTasks_1982_);
lean_inc(v_infoState_1981_);
lean_inc(v_messages_1980_);
lean_inc(v_traceState_1979_);
lean_inc(v_auxDeclNGen_1978_);
lean_inc(v_ngen_1977_);
lean_inc(v_nextMacroScope_1976_);
lean_inc(v_env_1975_);
lean_dec(v___x_1974_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2006_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_inc(v___x_1907_);
v___x_1986_ = l_Lean_addProtected(v_env_1975_, v___x_1907_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 5, v___x_1931_);
lean_ctor_set(v___x_1984_, 0, v___x_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_nextMacroScope_1976_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_ngen_1977_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_auxDeclNGen_1978_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_traceState_1979_);
lean_ctor_set(v_reuseFailAlloc_2005_, 5, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_2005_, 6, v_messages_1980_);
lean_ctor_set(v_reuseFailAlloc_2005_, 7, v_infoState_1981_);
lean_ctor_set(v_reuseFailAlloc_2005_, 8, v_snapshotTasks_1982_);
v___x_1988_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v_mctx_1991_; lean_object* v_zetaDeltaFVarIds_1992_; lean_object* v_postponed_1993_; lean_object* v_diag_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2003_; 
v___x_1989_ = lean_st_ref_set(v_a_1885_, v___x_1988_);
v___x_1990_ = lean_st_ref_take(v_a_1883_);
v_mctx_1991_ = lean_ctor_get(v___x_1990_, 0);
v_zetaDeltaFVarIds_1992_ = lean_ctor_get(v___x_1990_, 2);
v_postponed_1993_ = lean_ctor_get(v___x_1990_, 3);
v_diag_1994_ = lean_ctor_get(v___x_1990_, 4);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v___x_1990_, 1);
lean_dec(v_unused_2004_);
v___x_1996_ = v___x_1990_;
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_diag_1994_);
lean_inc(v_postponed_1993_);
lean_inc(v_zetaDeltaFVarIds_1992_);
lean_inc(v_mctx_1991_);
lean_dec(v___x_1990_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v___x_1943_);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_mctx_1991_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_zetaDeltaFVarIds_1992_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_postponed_1993_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v_diag_1994_);
v___x_1999_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_st_ref_set(v_a_1883_, v___x_1999_);
v___x_2001_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_1907_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
return v___x_2001_;
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
lean_dec(v___x_1907_);
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_a_1904_);
lean_dec(v_levelParams_1895_);
lean_dec(v_indName_1881_);
v_a_2022_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1905_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1905_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_levelParams_1895_);
lean_dec(v_indName_1881_);
v_a_2030_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1903_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1903_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v___x_1898_);
lean_dec_ref(v_type_1896_);
lean_dec(v_levelParams_1895_);
lean_dec(v_name_1894_);
lean_dec(v___x_1890_);
lean_dec_ref(v_val_1889_);
lean_dec(v_indName_1881_);
v___x_2038_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2);
v___x_2039_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2038_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
return v___x_2039_;
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v___x_1890_);
lean_dec_ref(v_val_1889_);
lean_dec(v_indName_1881_);
v_a_2040_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1892_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_1892_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v_a_1888_);
lean_dec(v_indName_1881_);
v___x_2048_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3);
v___x_2049_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2048_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
return v___x_2049_;
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_indName_1881_);
v_a_2050_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1887_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1887_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___boxed(lean_object* v_indName_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(lean_object* v___x_2065_, lean_object* v_k_2066_, lean_object* v_ctorIdx_2067_, lean_object* v_tail_2068_, lean_object* v___x_2069_, lean_object* v_as_2070_, size_t v_sz_2071_, size_t v_i_2072_, lean_object* v_bs_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_2065_, v_k_2066_, v_ctorIdx_2067_, v_tail_2068_, v___x_2069_, v_sz_2071_, v_i_2072_, v_bs_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___boxed(lean_object* v___x_2080_, lean_object* v_k_2081_, lean_object* v_ctorIdx_2082_, lean_object* v_tail_2083_, lean_object* v___x_2084_, lean_object* v_as_2085_, lean_object* v_sz_2086_, lean_object* v_i_2087_, lean_object* v_bs_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
size_t v_sz_boxed_2094_; size_t v_i_boxed_2095_; lean_object* v_res_2096_; 
v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2086_);
lean_dec(v_sz_2086_);
v_i_boxed_2095_ = lean_unbox_usize(v_i_2087_);
lean_dec(v_i_2087_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(v___x_2080_, v_k_2081_, v_ctorIdx_2082_, v_tail_2083_, v___x_2084_, v_as_2085_, v_sz_boxed_2094_, v_i_boxed_2095_, v_bs_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec_ref(v_as_2085_);
lean_dec_ref(v___x_2084_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v___x_2099_, lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v___x_2102_, lean_object* v___f_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v___y_2106_, uint8_t v___x_2107_, lean_object* v_h_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
lean_inc_ref(v_h_2108_);
v___x_2114_ = l_Lean_Meta_mkEqSymm(v_h_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
lean_inc(v___x_2098_);
v___x_2116_ = l_Lean_mkConst(v___x_2097_, v___x_2098_);
v___x_2117_ = l_Lean_mkAppN(v___x_2116_, v___x_2099_);
lean_inc_ref_n(v___x_2100_, 2);
v___x_2118_ = l_Lean_Expr_app___override(v___x_2117_, v___x_2100_);
lean_inc_ref(v___x_2101_);
v___x_2119_ = l_Lean_Expr_app___override(v___x_2118_, v___x_2101_);
v___x_2120_ = l_Lean_mkConst(v___x_2102_, v___x_2098_);
lean_inc_ref(v___x_2099_);
v___x_2121_ = lean_array_push(v___x_2099_, v___x_2100_);
v___x_2122_ = lean_array_push(v___x_2121_, v___x_2101_);
v___x_2123_ = l_Lean_mkAppN(v___x_2120_, v___x_2122_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v___x_2123_, v___f_2103_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = l_Lean_mkAppN(v___x_2119_, v___x_2104_);
v___x_2127_ = l_Lean_Expr_app___override(v___x_2126_, v_a_2115_);
v___x_2128_ = l_Lean_Expr_app___override(v___x_2127_, v_a_2125_);
v___x_2129_ = lean_mk_empty_array_with_capacity(v___x_2105_);
v___x_2130_ = lean_array_push(v___x_2129_, v___x_2100_);
v___x_2131_ = l_Array_append___redArg(v___x_2099_, v___x_2130_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = l_Array_append___redArg(v___x_2131_, v___x_2104_);
v___x_2133_ = lean_unsigned_to_nat(2u);
v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
v___x_2135_ = lean_array_push(v___x_2134_, v_h_2108_);
v___x_2136_ = lean_array_push(v___x_2135_, v___y_2106_);
v___x_2137_ = l_Array_append___redArg(v___x_2132_, v___x_2136_);
lean_dec_ref(v___x_2136_);
v___x_2138_ = 0;
v___x_2139_ = 1;
v___x_2140_ = l_Lean_Meta_mkLambdaFVars(v___x_2137_, v___x_2128_, v___x_2138_, v___x_2107_, v___x_2138_, v___x_2107_, v___x_2139_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec_ref(v___x_2137_);
return v___x_2140_;
}
else
{
lean_dec_ref(v___x_2119_);
lean_dec(v_a_2115_);
lean_dec_ref(v_h_2108_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___x_2100_);
lean_dec_ref(v___x_2099_);
return v___x_2124_;
}
}
else
{
lean_dec_ref(v_h_2108_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___f_2103_);
lean_dec(v___x_2102_);
lean_dec_ref(v___x_2101_);
lean_dec_ref(v___x_2100_);
lean_dec_ref(v___x_2099_);
lean_dec(v___x_2098_);
lean_dec(v___x_2097_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_2141_ = _args[0];
lean_object* v___x_2142_ = _args[1];
lean_object* v___x_2143_ = _args[2];
lean_object* v___x_2144_ = _args[3];
lean_object* v___x_2145_ = _args[4];
lean_object* v___x_2146_ = _args[5];
lean_object* v___f_2147_ = _args[6];
lean_object* v___x_2148_ = _args[7];
lean_object* v___x_2149_ = _args[8];
lean_object* v___y_2150_ = _args[9];
lean_object* v___x_2151_ = _args[10];
lean_object* v_h_2152_ = _args[11];
lean_object* v___y_2153_ = _args[12];
lean_object* v___y_2154_ = _args[13];
lean_object* v___y_2155_ = _args[14];
lean_object* v___y_2156_ = _args[15];
lean_object* v___y_2157_ = _args[16];
_start:
{
uint8_t v___x_9833__boxed_2158_; lean_object* v_res_2159_; 
v___x_9833__boxed_2158_ = lean_unbox(v___x_2151_);
v_res_2159_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(v___x_2141_, v___x_2142_, v___x_2143_, v___x_2144_, v___x_2145_, v___x_2146_, v___f_2147_, v___x_2148_, v___x_2149_, v___y_2150_, v___x_9833__boxed_2158_, v_h_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___x_2149_);
lean_dec_ref(v___x_2148_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(lean_object* v___y_2160_, lean_object* v_x_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___y_2160_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2168_, lean_object* v_x_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(v___y_2168_, v_x_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec_ref(v_x_2169_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(lean_object* v_val_2176_, lean_object* v___x_2177_, lean_object* v___x_2178_, lean_object* v___x_2179_, lean_object* v_indName_2180_, lean_object* v_tail_2181_, lean_object* v_i_2182_, lean_object* v___x_2183_, lean_object* v___x_2184_, lean_object* v___x_2185_, uint8_t v___x_2186_, lean_object* v_xs_2187_, lean_object* v_x_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_numParams_2194_; lean_object* v_numIndices_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v_start_2205_; lean_object* v_stop_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___y_2211_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v_numParams_2194_ = lean_ctor_get(v_val_2176_, 1);
lean_inc_n(v_numParams_2194_, 2);
v_numIndices_2195_ = lean_ctor_get(v_val_2176_, 2);
lean_inc(v_numIndices_2195_);
lean_dec_ref(v_val_2176_);
lean_inc_ref_n(v_xs_2187_, 2);
v___x_2196_ = l_Array_toSubarray___redArg(v_xs_2187_, v___x_2177_, v_numParams_2194_);
v___x_2197_ = lean_array_get(v___x_2178_, v_xs_2187_, v_numParams_2194_);
v___x_2198_ = lean_nat_add(v_numParams_2194_, v___x_2179_);
lean_dec(v_numParams_2194_);
v___x_2199_ = lean_nat_add(v___x_2198_, v_numIndices_2195_);
lean_dec(v_numIndices_2195_);
lean_inc(v___x_2199_);
v___x_2200_ = l_Array_toSubarray___redArg(v_xs_2187_, v___x_2198_, v___x_2199_);
v___x_2201_ = lean_array_get(v___x_2178_, v_xs_2187_, v___x_2199_);
v___x_2202_ = lean_nat_add(v___x_2199_, v___x_2179_);
lean_dec(v___x_2199_);
v___x_2203_ = lean_array_get_size(v_xs_2187_);
v___x_2204_ = l_Array_toSubarray___redArg(v_xs_2187_, v___x_2202_, v___x_2203_);
v_start_2205_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_start_2205_);
v_stop_2206_ = lean_ctor_get(v___x_2204_, 2);
lean_inc(v_stop_2206_);
v___x_2207_ = l_Subarray_copy___redArg(v___x_2196_);
v___x_2208_ = l_Subarray_copy___redArg(v___x_2200_);
v___x_2209_ = lean_array_push(v___x_2208_, v___x_2201_);
v___x_2224_ = lean_nat_sub(v_stop_2206_, v_start_2205_);
lean_dec(v_start_2205_);
lean_dec(v_stop_2206_);
v___x_2225_ = lean_nat_dec_lt(v_i_2182_, v___x_2224_);
lean_dec(v___x_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref(v___x_2204_);
v___x_2226_ = l_outOfBounds___redArg(v___x_2178_);
v___y_2211_ = v___x_2226_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Subarray_get___redArg(v___x_2204_, v_i_2182_);
lean_dec_ref(v___x_2204_);
v___y_2211_ = v___x_2227_;
goto v___jp_2210_;
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2212_ = l_Lean_mkCtorIdxName(v_indName_2180_);
v___x_2213_ = l_Lean_mkConst(v___x_2212_, v_tail_2181_);
lean_inc_ref(v___x_2207_);
v___x_2214_ = l_Array_append___redArg(v___x_2207_, v___x_2209_);
v___x_2215_ = l_Lean_mkAppN(v___x_2213_, v___x_2214_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = l_Lean_mkRawNatLit(v_i_2182_);
lean_inc_ref(v___x_2216_);
v___x_2217_ = l_Lean_Meta_mkEq(v___x_2215_, v___x_2216_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___f_2219_; lean_object* v___x_2220_; lean_object* v___f_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
lean_inc_ref(v___y_2211_);
v___f_2219_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2219_, 0, v___y_2211_);
v___x_2220_ = lean_box(v___x_2186_);
v___f_2221_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed), 17, 11);
lean_closure_set(v___f_2221_, 0, v___x_2183_);
lean_closure_set(v___f_2221_, 1, v___x_2184_);
lean_closure_set(v___f_2221_, 2, v___x_2207_);
lean_closure_set(v___f_2221_, 3, v___x_2197_);
lean_closure_set(v___f_2221_, 4, v___x_2216_);
lean_closure_set(v___f_2221_, 5, v___x_2185_);
lean_closure_set(v___f_2221_, 6, v___f_2219_);
lean_closure_set(v___f_2221_, 7, v___x_2209_);
lean_closure_set(v___f_2221_, 8, v___x_2179_);
lean_closure_set(v___f_2221_, 9, v___y_2211_);
lean_closure_set(v___f_2221_, 10, v___x_2220_);
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_2223_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_2222_, v_a_2218_, v___f_2221_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2223_;
}
else
{
lean_dec_ref(v___x_2216_);
lean_dec_ref(v___y_2211_);
lean_dec_ref(v___x_2209_);
lean_dec_ref(v___x_2207_);
lean_dec(v___x_2197_);
lean_dec(v___x_2185_);
lean_dec(v___x_2184_);
lean_dec(v___x_2183_);
lean_dec(v___x_2179_);
return v___x_2217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_val_2228_ = _args[0];
lean_object* v___x_2229_ = _args[1];
lean_object* v___x_2230_ = _args[2];
lean_object* v___x_2231_ = _args[3];
lean_object* v_indName_2232_ = _args[4];
lean_object* v_tail_2233_ = _args[5];
lean_object* v_i_2234_ = _args[6];
lean_object* v___x_2235_ = _args[7];
lean_object* v___x_2236_ = _args[8];
lean_object* v___x_2237_ = _args[9];
lean_object* v___x_2238_ = _args[10];
lean_object* v_xs_2239_ = _args[11];
lean_object* v_x_2240_ = _args[12];
lean_object* v___y_2241_ = _args[13];
lean_object* v___y_2242_ = _args[14];
lean_object* v___y_2243_ = _args[15];
lean_object* v___y_2244_ = _args[16];
lean_object* v___y_2245_ = _args[17];
_start:
{
uint8_t v___x_9961__boxed_2246_; lean_object* v_res_2247_; 
v___x_9961__boxed_2246_ = lean_unbox(v___x_2238_);
v_res_2247_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(v_val_2228_, v___x_2229_, v___x_2230_, v___x_2231_, v_indName_2232_, v_tail_2233_, v_i_2234_, v___x_2235_, v___x_2236_, v___x_2237_, v___x_9961__boxed_2246_, v_xs_2239_, v_x_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec_ref(v_x_2240_);
lean_dec_ref(v___x_2230_);
return v_res_2247_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(lean_object* v_attrName_2257_, lean_object* v_declName_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2264_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2265_ = l_Lean_MessageData_ofName(v_attrName_2257_);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = 0;
v___x_2270_ = l_Lean_MessageData_ofConstName(v_declName_2258_, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2268_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2273_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_2275_, lean_object* v_declName_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2275_, v_declName_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2282_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0));
v___x_2285_ = l_Lean_stringToMessageData(v___x_2284_);
return v___x_2285_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2));
v___x_2288_ = l_Lean_stringToMessageData(v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(lean_object* v_attrName_2289_, lean_object* v_declName_2290_, lean_object* v_asyncPrefix_x3f_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___y_2298_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2291_) == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_MessageData_nil;
v___y_2298_ = v___x_2311_;
goto v___jp_2297_;
}
else
{
lean_object* v_val_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_val_2312_ = lean_ctor_get(v_asyncPrefix_x3f_2291_, 0);
lean_inc(v_val_2312_);
lean_dec_ref_known(v_asyncPrefix_x3f_2291_, 1);
v___x_2313_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3);
v___x_2314_ = l_Lean_MessageData_ofName(v_val_2312_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___y_2298_ = v___x_2317_;
goto v___jp_2297_;
}
v___jp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2299_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2300_ = l_Lean_MessageData_ofName(v_attrName_2289_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = 0;
v___x_2305_ = l_Lean_MessageData_ofConstName(v_declName_2290_, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2303_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1);
v___x_2308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v___y_2298_);
v___x_2310_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2309_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_2318_, lean_object* v_declName_2319_, lean_object* v_asyncPrefix_x3f_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2318_, v_declName_2319_, v_asyncPrefix_x3f_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(lean_object* v_attr_2327_, lean_object* v_decl_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___x_2377_; lean_object* v_env_2378_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___x_2393_; 
v___x_2377_ = lean_st_ref_get(v___y_2332_);
v_env_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc_ref(v_env_2378_);
lean_dec(v___x_2377_);
v___x_2393_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2378_, v_decl_2328_);
if (lean_obj_tag(v___x_2393_) == 0)
{
v___y_2380_ = v___y_2329_;
v___y_2381_ = v___y_2330_;
v___y_2382_ = v___y_2331_;
v___y_2383_ = v___y_2332_;
goto v___jp_2379_;
}
else
{
lean_object* v_attr_2394_; lean_object* v_toAttributeImplCore_2395_; lean_object* v_name_2396_; lean_object* v___x_2397_; 
lean_dec_ref_known(v___x_2393_, 1);
lean_dec_ref(v_env_2378_);
v_attr_2394_ = lean_ctor_get(v_attr_2327_, 0);
lean_inc_ref(v_attr_2394_);
lean_dec_ref(v_attr_2327_);
v_toAttributeImplCore_2395_ = lean_ctor_get(v_attr_2394_, 0);
lean_inc_ref(v_toAttributeImplCore_2395_);
lean_dec_ref(v_attr_2394_);
v_name_2396_ = lean_ctor_get(v_toAttributeImplCore_2395_, 1);
lean_inc(v_name_2396_);
lean_dec_ref(v_toAttributeImplCore_2395_);
v___x_2397_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_name_2396_, v_decl_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v___x_2397_;
}
v___jp_2334_:
{
lean_object* v___x_2337_; lean_object* v_ext_2338_; lean_object* v_toEnvExtension_2339_; lean_object* v_env_2340_; lean_object* v_nextMacroScope_2341_; lean_object* v_ngen_2342_; lean_object* v_auxDeclNGen_2343_; lean_object* v_traceState_2344_; lean_object* v_messages_2345_; lean_object* v_infoState_2346_; lean_object* v_snapshotTasks_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2375_; 
v___x_2337_ = lean_st_ref_take(v___y_2336_);
v_ext_2338_ = lean_ctor_get(v_attr_2327_, 1);
lean_inc_ref(v_ext_2338_);
lean_dec_ref(v_attr_2327_);
v_toEnvExtension_2339_ = lean_ctor_get(v_ext_2338_, 0);
v_env_2340_ = lean_ctor_get(v___x_2337_, 0);
v_nextMacroScope_2341_ = lean_ctor_get(v___x_2337_, 1);
v_ngen_2342_ = lean_ctor_get(v___x_2337_, 2);
v_auxDeclNGen_2343_ = lean_ctor_get(v___x_2337_, 3);
v_traceState_2344_ = lean_ctor_get(v___x_2337_, 4);
v_messages_2345_ = lean_ctor_get(v___x_2337_, 6);
v_infoState_2346_ = lean_ctor_get(v___x_2337_, 7);
v_snapshotTasks_2347_ = lean_ctor_get(v___x_2337_, 8);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v___x_2337_, 5);
lean_dec(v_unused_2376_);
v___x_2349_ = v___x_2337_;
v_isShared_2350_ = v_isSharedCheck_2375_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_snapshotTasks_2347_);
lean_inc(v_infoState_2346_);
lean_inc(v_messages_2345_);
lean_inc(v_traceState_2344_);
lean_inc(v_auxDeclNGen_2343_);
lean_inc(v_ngen_2342_);
lean_inc(v_nextMacroScope_2341_);
lean_inc(v_env_2340_);
lean_dec(v___x_2337_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2375_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_asyncMode_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v_asyncMode_2351_ = lean_ctor_get(v_toEnvExtension_2339_, 2);
lean_inc(v_asyncMode_2351_);
lean_inc(v_decl_2328_);
v___x_2352_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2338_, v_env_2340_, v_decl_2328_, v_asyncMode_2351_, v_decl_2328_);
lean_dec(v_asyncMode_2351_);
v___x_2353_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 5, v___x_2353_);
lean_ctor_set(v___x_2349_, 0, v___x_2352_);
v___x_2355_ = v___x_2349_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_nextMacroScope_2341_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_ngen_2342_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_auxDeclNGen_2343_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v_traceState_2344_);
lean_ctor_set(v_reuseFailAlloc_2374_, 5, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2374_, 6, v_messages_2345_);
lean_ctor_set(v_reuseFailAlloc_2374_, 7, v_infoState_2346_);
lean_ctor_set(v_reuseFailAlloc_2374_, 8, v_snapshotTasks_2347_);
v___x_2355_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v_mctx_2358_; lean_object* v_zetaDeltaFVarIds_2359_; lean_object* v_postponed_2360_; lean_object* v_diag_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2372_; 
v___x_2356_ = lean_st_ref_set(v___y_2336_, v___x_2355_);
v___x_2357_ = lean_st_ref_take(v___y_2335_);
v_mctx_2358_ = lean_ctor_get(v___x_2357_, 0);
v_zetaDeltaFVarIds_2359_ = lean_ctor_get(v___x_2357_, 2);
v_postponed_2360_ = lean_ctor_get(v___x_2357_, 3);
v_diag_2361_ = lean_ctor_get(v___x_2357_, 4);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v___x_2357_, 1);
lean_dec(v_unused_2373_);
v___x_2363_ = v___x_2357_;
v_isShared_2364_ = v_isSharedCheck_2372_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_diag_2361_);
lean_inc(v_postponed_2360_);
lean_inc(v_zetaDeltaFVarIds_2359_);
lean_inc(v_mctx_2358_);
lean_dec(v___x_2357_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2372_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v___x_2365_);
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_mctx_2358_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_zetaDeltaFVarIds_2359_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_postponed_2360_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v_diag_2361_);
v___x_2367_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = lean_st_ref_set(v___y_2335_, v___x_2367_);
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
}
}
}
v___jp_2379_:
{
lean_object* v_ext_2384_; lean_object* v_toEnvExtension_2385_; lean_object* v_attr_2386_; lean_object* v_asyncMode_2387_; uint8_t v___x_2388_; 
v_ext_2384_ = lean_ctor_get(v_attr_2327_, 1);
v_toEnvExtension_2385_ = lean_ctor_get(v_ext_2384_, 0);
v_attr_2386_ = lean_ctor_get(v_attr_2327_, 0);
v_asyncMode_2387_ = lean_ctor_get(v_toEnvExtension_2385_, 2);
lean_inc(v_decl_2328_);
lean_inc_ref(v_env_2378_);
v___x_2388_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2378_, v_decl_2328_, v_asyncMode_2387_);
if (v___x_2388_ == 0)
{
lean_object* v_toAttributeImplCore_2389_; lean_object* v_name_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_inc_ref(v_attr_2386_);
lean_dec_ref(v_attr_2327_);
v_toAttributeImplCore_2389_ = lean_ctor_get(v_attr_2386_, 0);
lean_inc_ref(v_toAttributeImplCore_2389_);
lean_dec_ref(v_attr_2386_);
v_name_2390_ = lean_ctor_get(v_toAttributeImplCore_2389_, 1);
lean_inc(v_name_2390_);
lean_dec_ref(v_toAttributeImplCore_2389_);
v___x_2391_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2378_);
v___x_2392_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_name_2390_, v_decl_2328_, v___x_2391_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v___x_2392_;
}
else
{
lean_dec_ref(v_env_2378_);
v___y_2335_ = v___y_2381_;
v___y_2336_ = v___y_2383_;
goto v___jp_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___boxed(lean_object* v_attr_2398_, lean_object* v_decl_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v_attr_2398_, v_decl_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(lean_object* v_val_2406_, lean_object* v_indName_2407_, lean_object* v_tail_2408_, lean_object* v___x_2409_, lean_object* v___x_2410_, lean_object* v___x_2411_, lean_object* v_a_2412_, lean_object* v_range_2413_, lean_object* v_b_2414_, lean_object* v_i_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_stop_2421_; lean_object* v_step_2422_; uint8_t v___x_2423_; 
v_stop_2421_ = lean_ctor_get(v_range_2413_, 1);
v_step_2422_ = lean_ctor_get(v_range_2413_, 2);
v___x_2423_ = lean_nat_dec_lt(v_i_2415_, v_stop_2421_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; 
lean_dec(v_i_2415_);
lean_dec_ref(v_a_2412_);
lean_dec(v___x_2411_);
lean_dec(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec(v_tail_2408_);
lean_dec(v_indName_2407_);
lean_dec_ref(v_val_2406_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v_b_2414_);
return v___x_2424_;
}
else
{
lean_object* v_levelParams_2425_; lean_object* v_type_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___f_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; 
v_levelParams_2425_ = lean_ctor_get(v_a_2412_, 1);
v_type_2426_ = lean_ctor_get(v_a_2412_, 2);
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = l_Lean_instInhabitedExpr;
v___x_2429_ = lean_unsigned_to_nat(1u);
v___x_2430_ = lean_box(v___x_2423_);
lean_inc(v___x_2411_);
lean_inc(v___x_2410_);
lean_inc(v___x_2409_);
lean_inc(v_i_2415_);
lean_inc(v_tail_2408_);
lean_inc(v_indName_2407_);
lean_inc_ref(v_val_2406_);
v___f_2431_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed), 18, 11);
lean_closure_set(v___f_2431_, 0, v_val_2406_);
lean_closure_set(v___f_2431_, 1, v___x_2427_);
lean_closure_set(v___f_2431_, 2, v___x_2428_);
lean_closure_set(v___f_2431_, 3, v___x_2429_);
lean_closure_set(v___f_2431_, 4, v_indName_2407_);
lean_closure_set(v___f_2431_, 5, v_tail_2408_);
lean_closure_set(v___f_2431_, 6, v_i_2415_);
lean_closure_set(v___f_2431_, 7, v___x_2409_);
lean_closure_set(v___f_2431_, 8, v___x_2410_);
lean_closure_set(v___f_2431_, 9, v___x_2411_);
lean_closure_set(v___f_2431_, 10, v___x_2430_);
v___x_2432_ = 0;
lean_inc_ref(v_type_2426_);
v___x_2433_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_2426_, v___f_2431_, v___x_2432_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2435_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc_n(v_a_2434_, 2);
lean_dec_ref_known(v___x_2433_, 1);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
v___x_2435_ = lean_infer_type(v_a_2434_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v_ctors_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2591_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_ctors_2437_ = lean_ctor_get(v_val_2406_, 4);
v___x_2438_ = lean_box(0);
lean_inc(v_i_2415_);
v___x_2439_ = l_List_get_x21Internal___redArg(v___x_2438_, v_ctors_2437_, v_i_2415_);
v___x_2440_ = l_Lean_mkConstructorElimName(v_indName_2407_, v___x_2439_);
v___x_2441_ = lean_box(1);
lean_inc(v_levelParams_2425_);
lean_inc(v___x_2440_);
v___x_2442_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_2440_, v_levelParams_2425_, v_a_2436_, v_a_2434_, v___x_2441_, v___y_2419_);
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2591_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2591_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 1);
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_addAndCompile(v___x_2448_, v___x_2423_, v___x_2432_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; lean_object* v_env_2451_; lean_object* v_nextMacroScope_2452_; lean_object* v_ngen_2453_; lean_object* v_auxDeclNGen_2454_; lean_object* v_traceState_2455_; lean_object* v_messages_2456_; lean_object* v_infoState_2457_; lean_object* v_snapshotTasks_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2588_; 
lean_dec_ref_known(v___x_2449_, 1);
v___x_2450_ = lean_st_ref_take(v___y_2419_);
v_env_2451_ = lean_ctor_get(v___x_2450_, 0);
v_nextMacroScope_2452_ = lean_ctor_get(v___x_2450_, 1);
v_ngen_2453_ = lean_ctor_get(v___x_2450_, 2);
v_auxDeclNGen_2454_ = lean_ctor_get(v___x_2450_, 3);
v_traceState_2455_ = lean_ctor_get(v___x_2450_, 4);
v_messages_2456_ = lean_ctor_get(v___x_2450_, 6);
v_infoState_2457_ = lean_ctor_get(v___x_2450_, 7);
v_snapshotTasks_2458_ = lean_ctor_get(v___x_2450_, 8);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2450_, 5);
lean_dec(v_unused_2589_);
v___x_2460_ = v___x_2450_;
v_isShared_2461_ = v_isSharedCheck_2588_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snapshotTasks_2458_);
lean_inc(v_infoState_2457_);
lean_inc(v_messages_2456_);
lean_inc(v_traceState_2455_);
lean_inc(v_auxDeclNGen_2454_);
lean_inc(v_ngen_2453_);
lean_inc(v_nextMacroScope_2452_);
lean_inc(v_env_2451_);
lean_dec(v___x_2450_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2588_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_inc(v___x_2440_);
v___x_2462_ = l_Lean_markAuxRecursor(v_env_2451_, v___x_2440_);
v___x_2463_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 5, v___x_2463_);
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2465_ = v___x_2460_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_nextMacroScope_2452_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_ngen_2453_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_auxDeclNGen_2454_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v_traceState_2455_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v_messages_2456_);
lean_ctor_set(v_reuseFailAlloc_2587_, 7, v_infoState_2457_);
lean_ctor_set(v_reuseFailAlloc_2587_, 8, v_snapshotTasks_2458_);
v___x_2465_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v_mctx_2468_; lean_object* v_zetaDeltaFVarIds_2469_; lean_object* v_postponed_2470_; lean_object* v_diag_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2585_; 
v___x_2466_ = lean_st_ref_set(v___y_2419_, v___x_2465_);
v___x_2467_ = lean_st_ref_take(v___y_2417_);
v_mctx_2468_ = lean_ctor_get(v___x_2467_, 0);
v_zetaDeltaFVarIds_2469_ = lean_ctor_get(v___x_2467_, 2);
v_postponed_2470_ = lean_ctor_get(v___x_2467_, 3);
v_diag_2471_ = lean_ctor_get(v___x_2467_, 4);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v___x_2467_, 1);
lean_dec(v_unused_2586_);
v___x_2473_ = v___x_2467_;
v_isShared_2474_ = v_isSharedCheck_2585_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_diag_2471_);
lean_inc(v_postponed_2470_);
lean_inc(v_zetaDeltaFVarIds_2469_);
lean_inc(v_mctx_2468_);
lean_dec(v___x_2467_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2585_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 1, v___x_2475_);
v___x_2477_ = v___x_2473_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_mctx_2468_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_zetaDeltaFVarIds_2469_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_postponed_2470_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_diag_2471_);
v___x_2477_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_env_2480_; lean_object* v_nextMacroScope_2481_; lean_object* v_ngen_2482_; lean_object* v_auxDeclNGen_2483_; lean_object* v_traceState_2484_; lean_object* v_messages_2485_; lean_object* v_infoState_2486_; lean_object* v_snapshotTasks_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2582_; 
v___x_2478_ = lean_st_ref_set(v___y_2417_, v___x_2477_);
v___x_2479_ = lean_st_ref_take(v___y_2419_);
v_env_2480_ = lean_ctor_get(v___x_2479_, 0);
v_nextMacroScope_2481_ = lean_ctor_get(v___x_2479_, 1);
v_ngen_2482_ = lean_ctor_get(v___x_2479_, 2);
v_auxDeclNGen_2483_ = lean_ctor_get(v___x_2479_, 3);
v_traceState_2484_ = lean_ctor_get(v___x_2479_, 4);
v_messages_2485_ = lean_ctor_get(v___x_2479_, 6);
v_infoState_2486_ = lean_ctor_get(v___x_2479_, 7);
v_snapshotTasks_2487_ = lean_ctor_get(v___x_2479_, 8);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v___x_2479_, 5);
lean_dec(v_unused_2583_);
v___x_2489_ = v___x_2479_;
v_isShared_2490_ = v_isSharedCheck_2582_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_snapshotTasks_2487_);
lean_inc(v_infoState_2486_);
lean_inc(v_messages_2485_);
lean_inc(v_traceState_2484_);
lean_inc(v_auxDeclNGen_2483_);
lean_inc(v_ngen_2482_);
lean_inc(v_nextMacroScope_2481_);
lean_inc(v_env_2480_);
lean_dec(v___x_2479_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2582_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_inc(v___x_2440_);
v___x_2491_ = l_Lean_markSparseCasesOn(v_env_2480_, v___x_2440_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 5, v___x_2463_);
lean_ctor_set(v___x_2489_, 0, v___x_2491_);
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_nextMacroScope_2481_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_ngen_2482_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_auxDeclNGen_2483_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_traceState_2484_);
lean_ctor_set(v_reuseFailAlloc_2581_, 5, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2581_, 6, v_messages_2485_);
lean_ctor_set(v_reuseFailAlloc_2581_, 7, v_infoState_2486_);
lean_ctor_set(v_reuseFailAlloc_2581_, 8, v_snapshotTasks_2487_);
v___x_2493_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_mctx_2496_; lean_object* v_zetaDeltaFVarIds_2497_; lean_object* v_postponed_2498_; lean_object* v_diag_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2579_; 
v___x_2494_ = lean_st_ref_set(v___y_2419_, v___x_2493_);
v___x_2495_ = lean_st_ref_take(v___y_2417_);
v_mctx_2496_ = lean_ctor_get(v___x_2495_, 0);
v_zetaDeltaFVarIds_2497_ = lean_ctor_get(v___x_2495_, 2);
v_postponed_2498_ = lean_ctor_get(v___x_2495_, 3);
v_diag_2499_ = lean_ctor_get(v___x_2495_, 4);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2495_, 1);
lean_dec(v_unused_2580_);
v___x_2501_ = v___x_2495_;
v_isShared_2502_ = v_isSharedCheck_2579_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_diag_2499_);
lean_inc(v_postponed_2498_);
lean_inc(v_zetaDeltaFVarIds_2497_);
lean_inc(v_mctx_2496_);
lean_dec(v___x_2495_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2579_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2475_);
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_mctx_2496_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_zetaDeltaFVarIds_2497_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_postponed_2498_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_diag_2499_);
v___x_2504_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v_env_2507_; lean_object* v_nextMacroScope_2508_; lean_object* v_ngen_2509_; lean_object* v_auxDeclNGen_2510_; lean_object* v_traceState_2511_; lean_object* v_messages_2512_; lean_object* v_infoState_2513_; lean_object* v_snapshotTasks_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2576_; 
v___x_2505_ = lean_st_ref_set(v___y_2417_, v___x_2504_);
v___x_2506_ = lean_st_ref_take(v___y_2419_);
v_env_2507_ = lean_ctor_get(v___x_2506_, 0);
v_nextMacroScope_2508_ = lean_ctor_get(v___x_2506_, 1);
v_ngen_2509_ = lean_ctor_get(v___x_2506_, 2);
v_auxDeclNGen_2510_ = lean_ctor_get(v___x_2506_, 3);
v_traceState_2511_ = lean_ctor_get(v___x_2506_, 4);
v_messages_2512_ = lean_ctor_get(v___x_2506_, 6);
v_infoState_2513_ = lean_ctor_get(v___x_2506_, 7);
v_snapshotTasks_2514_ = lean_ctor_get(v___x_2506_, 8);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2576_ == 0)
{
lean_object* v_unused_2577_; 
v_unused_2577_ = lean_ctor_get(v___x_2506_, 5);
lean_dec(v_unused_2577_);
v___x_2516_ = v___x_2506_;
v_isShared_2517_ = v_isSharedCheck_2576_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_snapshotTasks_2514_);
lean_inc(v_infoState_2513_);
lean_inc(v_messages_2512_);
lean_inc(v_traceState_2511_);
lean_inc(v_auxDeclNGen_2510_);
lean_inc(v_ngen_2509_);
lean_inc(v_nextMacroScope_2508_);
lean_inc(v_env_2507_);
lean_dec(v___x_2506_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2576_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
lean_inc(v___x_2440_);
v___x_2518_ = l_Lean_Meta_addToCompletionBlackList(v_env_2507_, v___x_2440_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 5, v___x_2463_);
lean_ctor_set(v___x_2516_, 0, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_nextMacroScope_2508_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_ngen_2509_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_auxDeclNGen_2510_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_traceState_2511_);
lean_ctor_set(v_reuseFailAlloc_2575_, 5, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2575_, 6, v_messages_2512_);
lean_ctor_set(v_reuseFailAlloc_2575_, 7, v_infoState_2513_);
lean_ctor_set(v_reuseFailAlloc_2575_, 8, v_snapshotTasks_2514_);
v___x_2520_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_mctx_2523_; lean_object* v_zetaDeltaFVarIds_2524_; lean_object* v_postponed_2525_; lean_object* v_diag_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2573_; 
v___x_2521_ = lean_st_ref_set(v___y_2419_, v___x_2520_);
v___x_2522_ = lean_st_ref_take(v___y_2417_);
v_mctx_2523_ = lean_ctor_get(v___x_2522_, 0);
v_zetaDeltaFVarIds_2524_ = lean_ctor_get(v___x_2522_, 2);
v_postponed_2525_ = lean_ctor_get(v___x_2522_, 3);
v_diag_2526_ = lean_ctor_get(v___x_2522_, 4);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v___x_2522_, 1);
lean_dec(v_unused_2574_);
v___x_2528_ = v___x_2522_;
v_isShared_2529_ = v_isSharedCheck_2573_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_diag_2526_);
lean_inc(v_postponed_2525_);
lean_inc(v_zetaDeltaFVarIds_2524_);
lean_inc(v_mctx_2523_);
lean_dec(v___x_2522_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2573_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2475_);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_mctx_2523_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_zetaDeltaFVarIds_2524_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_postponed_2525_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_diag_2526_);
v___x_2531_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v_env_2534_; lean_object* v_nextMacroScope_2535_; lean_object* v_ngen_2536_; lean_object* v_auxDeclNGen_2537_; lean_object* v_traceState_2538_; lean_object* v_messages_2539_; lean_object* v_infoState_2540_; lean_object* v_snapshotTasks_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2570_; 
v___x_2532_ = lean_st_ref_set(v___y_2417_, v___x_2531_);
v___x_2533_ = lean_st_ref_take(v___y_2419_);
v_env_2534_ = lean_ctor_get(v___x_2533_, 0);
v_nextMacroScope_2535_ = lean_ctor_get(v___x_2533_, 1);
v_ngen_2536_ = lean_ctor_get(v___x_2533_, 2);
v_auxDeclNGen_2537_ = lean_ctor_get(v___x_2533_, 3);
v_traceState_2538_ = lean_ctor_get(v___x_2533_, 4);
v_messages_2539_ = lean_ctor_get(v___x_2533_, 6);
v_infoState_2540_ = lean_ctor_get(v___x_2533_, 7);
v_snapshotTasks_2541_ = lean_ctor_get(v___x_2533_, 8);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2570_ == 0)
{
lean_object* v_unused_2571_; 
v_unused_2571_ = lean_ctor_get(v___x_2533_, 5);
lean_dec(v_unused_2571_);
v___x_2543_ = v___x_2533_;
v_isShared_2544_ = v_isSharedCheck_2570_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_snapshotTasks_2541_);
lean_inc(v_infoState_2540_);
lean_inc(v_messages_2539_);
lean_inc(v_traceState_2538_);
lean_inc(v_auxDeclNGen_2537_);
lean_inc(v_ngen_2536_);
lean_inc(v_nextMacroScope_2535_);
lean_inc(v_env_2534_);
lean_dec(v___x_2533_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2570_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_inc(v___x_2440_);
v___x_2545_ = l_Lean_addProtected(v_env_2534_, v___x_2440_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 5, v___x_2463_);
lean_ctor_set(v___x_2543_, 0, v___x_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_nextMacroScope_2535_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_ngen_2536_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_auxDeclNGen_2537_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v_traceState_2538_);
lean_ctor_set(v_reuseFailAlloc_2569_, 5, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2569_, 6, v_messages_2539_);
lean_ctor_set(v_reuseFailAlloc_2569_, 7, v_infoState_2540_);
lean_ctor_set(v_reuseFailAlloc_2569_, 8, v_snapshotTasks_2541_);
v___x_2547_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v_mctx_2550_; lean_object* v_zetaDeltaFVarIds_2551_; lean_object* v_postponed_2552_; lean_object* v_diag_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2567_; 
v___x_2548_ = lean_st_ref_set(v___y_2419_, v___x_2547_);
v___x_2549_ = lean_st_ref_take(v___y_2417_);
v_mctx_2550_ = lean_ctor_get(v___x_2549_, 0);
v_zetaDeltaFVarIds_2551_ = lean_ctor_get(v___x_2549_, 2);
v_postponed_2552_ = lean_ctor_get(v___x_2549_, 3);
v_diag_2553_ = lean_ctor_get(v___x_2549_, 4);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; 
v_unused_2568_ = lean_ctor_get(v___x_2549_, 1);
lean_dec(v_unused_2568_);
v___x_2555_ = v___x_2549_;
v_isShared_2556_ = v_isSharedCheck_2567_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_diag_2553_);
lean_inc(v_postponed_2552_);
lean_inc(v_zetaDeltaFVarIds_2551_);
lean_inc(v_mctx_2550_);
lean_dec(v___x_2549_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2567_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v___x_2475_);
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_mctx_2550_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_zetaDeltaFVarIds_2551_);
lean_ctor_set(v_reuseFailAlloc_2566_, 3, v_postponed_2552_);
lean_ctor_set(v_reuseFailAlloc_2566_, 4, v_diag_2553_);
v___x_2558_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = lean_st_ref_set(v___y_2417_, v___x_2558_);
v___x_2560_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v___x_2440_);
v___x_2561_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v___x_2560_, v___x_2440_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_dec_ref_known(v___x_2561_, 1);
v___x_2562_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_2440_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec_ref(v___x_2562_);
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_nat_add(v_i_2415_, v_step_2422_);
lean_dec(v_i_2415_);
v_b_2414_ = v___x_2563_;
v_i_2415_ = v___x_2564_;
goto _start;
}
else
{
lean_dec(v___x_2440_);
lean_dec(v_i_2415_);
lean_dec_ref(v_a_2412_);
lean_dec(v___x_2411_);
lean_dec(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec(v_tail_2408_);
lean_dec(v_indName_2407_);
lean_dec_ref(v_val_2406_);
return v___x_2561_;
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
lean_dec(v___x_2440_);
lean_dec(v_i_2415_);
lean_dec_ref(v_a_2412_);
lean_dec(v___x_2411_);
lean_dec(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec(v_tail_2408_);
lean_dec(v_indName_2407_);
lean_dec_ref(v_val_2406_);
return v___x_2449_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2434_);
lean_dec(v_i_2415_);
lean_dec_ref(v_a_2412_);
lean_dec(v___x_2411_);
lean_dec(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec(v_tail_2408_);
lean_dec(v_indName_2407_);
lean_dec_ref(v_val_2406_);
v_a_2592_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2435_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2435_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_i_2415_);
lean_dec_ref(v_a_2412_);
lean_dec(v___x_2411_);
lean_dec(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec(v_tail_2408_);
lean_dec(v_indName_2407_);
lean_dec_ref(v_val_2406_);
v_a_2600_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2433_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2433_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___boxed(lean_object* v_val_2608_, lean_object* v_indName_2609_, lean_object* v_tail_2610_, lean_object* v___x_2611_, lean_object* v___x_2612_, lean_object* v___x_2613_, lean_object* v_a_2614_, lean_object* v_range_2615_, lean_object* v_b_2616_, lean_object* v_i_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2608_, v_indName_2609_, v_tail_2610_, v___x_2611_, v___x_2612_, v___x_2613_, v_a_2614_, v_range_2615_, v_b_2616_, v_i_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v_range_2615_);
return v_res_2623_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2625_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_2626_ = lean_unsigned_to_nat(58u);
v___x_2627_ = lean_unsigned_to_nat(169u);
v___x_2628_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2630_ = l_mkPanicMessageWithDecl(v___x_2629_, v___x_2628_, v___x_2627_, v___x_2626_, v___x_2625_);
return v___x_2630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2631_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_2632_ = lean_unsigned_to_nat(60u);
v___x_2633_ = lean_unsigned_to_nat(166u);
v___x_2634_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2635_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2636_ = l_mkPanicMessageWithDecl(v___x_2635_, v___x_2634_, v___x_2633_, v___x_2632_, v___x_2631_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(lean_object* v_indName_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2643_; 
lean_inc(v_indName_2637_);
v___x_2643_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
if (lean_obj_tag(v_a_2644_) == 5)
{
lean_object* v_val_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_val_2645_ = lean_ctor_get(v_a_2644_, 0);
lean_inc_ref(v_val_2645_);
lean_dec_ref_known(v_a_2644_, 1);
lean_inc(v_indName_2637_);
v___x_2646_ = l_Lean_mkCasesOnName(v_indName_2637_);
lean_inc(v___x_2646_);
v___x_2647_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v___x_2646_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v_levelParams_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2686_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v_levelParams_2649_ = lean_ctor_get(v_a_2648_, 1);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_a_2648_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; lean_object* v_unused_2688_; 
v_unused_2687_ = lean_ctor_get(v_a_2648_, 2);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_a_2648_, 0);
lean_dec(v_unused_2688_);
v___x_2651_ = v_a_2648_;
v_isShared_2652_ = v_isSharedCheck_2686_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_levelParams_2649_);
lean_dec(v_a_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2686_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_box(0);
v___x_2654_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_2649_, v___x_2653_);
if (lean_obj_tag(v___x_2654_) == 1)
{
lean_object* v_tail_2655_; lean_object* v___x_2656_; 
v_tail_2655_ = lean_ctor_get(v___x_2654_, 1);
lean_inc(v_tail_2655_);
v___x_2656_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v___x_2646_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
lean_inc_n(v_indName_2637_, 2);
v___x_2658_ = l_Lean_mkCtorElimName(v_indName_2637_);
v___x_2659_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_2637_);
v___x_2660_ = lean_unsigned_to_nat(0u);
v___x_2661_ = l_Lean_InductiveVal_numCtors(v_val_2645_);
v___x_2662_ = lean_unsigned_to_nat(1u);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 2, v___x_2662_);
lean_ctor_set(v___x_2651_, 1, v___x_2661_);
lean_ctor_set(v___x_2651_, 0, v___x_2660_);
v___x_2664_ = v___x_2651_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_box(0);
v___x_2666_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2645_, v_indName_2637_, v_tail_2655_, v___x_2658_, v___x_2654_, v___x_2659_, v_a_2657_, v___x_2664_, v___x_2665_, v___x_2660_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec_ref(v___x_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2674_);
v___x_2668_ = v___x_2666_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_dec(v___x_2666_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2665_);
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2665_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
else
{
return v___x_2666_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref_known(v___x_2654_, 2);
lean_dec(v_tail_2655_);
lean_del_object(v___x_2651_);
lean_dec_ref(v_val_2645_);
lean_dec(v_indName_2637_);
v_a_2676_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2656_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2656_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_dec(v___x_2654_);
lean_del_object(v___x_2651_);
lean_dec(v___x_2646_);
lean_dec_ref(v_val_2645_);
lean_dec(v_indName_2637_);
v___x_2684_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1);
v___x_2685_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2684_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
return v___x_2685_;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v___x_2646_);
lean_dec_ref(v_val_2645_);
lean_dec(v_indName_2637_);
v_a_2689_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2647_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2647_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec(v_a_2644_);
lean_dec(v_indName_2637_);
v___x_2697_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2);
v___x_2698_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2697_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
return v___x_2698_;
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_indName_2637_);
v_a_2699_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2643_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2643_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___boxed(lean_object* v_indName_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(lean_object* v_val_2714_, lean_object* v_indName_2715_, lean_object* v_tail_2716_, lean_object* v___x_2717_, lean_object* v___x_2718_, lean_object* v___x_2719_, lean_object* v_a_2720_, lean_object* v_range_2721_, lean_object* v_b_2722_, lean_object* v_i_2723_, lean_object* v_hs_2724_, lean_object* v_hl_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2714_, v_indName_2715_, v_tail_2716_, v___x_2717_, v___x_2718_, v___x_2719_, v_a_2720_, v_range_2721_, v_b_2722_, v_i_2723_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___boxed(lean_object** _args){
lean_object* v_val_2732_ = _args[0];
lean_object* v_indName_2733_ = _args[1];
lean_object* v_tail_2734_ = _args[2];
lean_object* v___x_2735_ = _args[3];
lean_object* v___x_2736_ = _args[4];
lean_object* v___x_2737_ = _args[5];
lean_object* v_a_2738_ = _args[6];
lean_object* v_range_2739_ = _args[7];
lean_object* v_b_2740_ = _args[8];
lean_object* v_i_2741_ = _args[9];
lean_object* v_hs_2742_ = _args[10];
lean_object* v_hl_2743_ = _args[11];
lean_object* v___y_2744_ = _args[12];
lean_object* v___y_2745_ = _args[13];
lean_object* v___y_2746_ = _args[14];
lean_object* v___y_2747_ = _args[15];
lean_object* v___y_2748_ = _args[16];
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(v_val_2732_, v_indName_2733_, v_tail_2734_, v___x_2735_, v___x_2736_, v___x_2737_, v_a_2738_, v_range_2739_, v_b_2740_, v_i_2741_, v_hs_2742_, v_hl_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v_range_2739_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(lean_object* v_00_u03b1_2750_, lean_object* v_attrName_2751_, lean_object* v_declName_2752_, lean_object* v_asyncPrefix_x3f_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2751_, v_declName_2752_, v_asyncPrefix_x3f_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2760_, lean_object* v_attrName_2761_, lean_object* v_declName_2762_, lean_object* v_asyncPrefix_x3f_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(v_00_u03b1_2760_, v_attrName_2761_, v_declName_2762_, v_asyncPrefix_x3f_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(lean_object* v_00_u03b1_2770_, lean_object* v_attrName_2771_, lean_object* v_declName_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2771_, v_declName_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2779_, lean_object* v_attrName_2780_, lean_object* v_declName_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(v_00_u03b1_2779_, v_attrName_2780_, v_declName_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(lean_object* v___y_2788_, uint8_t v_isExporting_2789_, lean_object* v___x_2790_, lean_object* v___y_2791_, lean_object* v___x_2792_, lean_object* v_a_x3f_2793_){
_start:
{
lean_object* v___x_2795_; lean_object* v_env_2796_; lean_object* v_nextMacroScope_2797_; lean_object* v_ngen_2798_; lean_object* v_auxDeclNGen_2799_; lean_object* v_traceState_2800_; lean_object* v_messages_2801_; lean_object* v_infoState_2802_; lean_object* v_snapshotTasks_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2828_; 
v___x_2795_ = lean_st_ref_take(v___y_2788_);
v_env_2796_ = lean_ctor_get(v___x_2795_, 0);
v_nextMacroScope_2797_ = lean_ctor_get(v___x_2795_, 1);
v_ngen_2798_ = lean_ctor_get(v___x_2795_, 2);
v_auxDeclNGen_2799_ = lean_ctor_get(v___x_2795_, 3);
v_traceState_2800_ = lean_ctor_get(v___x_2795_, 4);
v_messages_2801_ = lean_ctor_get(v___x_2795_, 6);
v_infoState_2802_ = lean_ctor_get(v___x_2795_, 7);
v_snapshotTasks_2803_ = lean_ctor_get(v___x_2795_, 8);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2828_ == 0)
{
lean_object* v_unused_2829_; 
v_unused_2829_ = lean_ctor_get(v___x_2795_, 5);
lean_dec(v_unused_2829_);
v___x_2805_ = v___x_2795_;
v_isShared_2806_ = v_isSharedCheck_2828_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_snapshotTasks_2803_);
lean_inc(v_infoState_2802_);
lean_inc(v_messages_2801_);
lean_inc(v_traceState_2800_);
lean_inc(v_auxDeclNGen_2799_);
lean_inc(v_ngen_2798_);
lean_inc(v_nextMacroScope_2797_);
lean_inc(v_env_2796_);
lean_dec(v___x_2795_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2828_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2807_ = l_Lean_Environment_setExporting(v_env_2796_, v_isExporting_2789_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 5, v___x_2790_);
lean_ctor_set(v___x_2805_, 0, v___x_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_nextMacroScope_2797_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_ngen_2798_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_auxDeclNGen_2799_);
lean_ctor_set(v_reuseFailAlloc_2827_, 4, v_traceState_2800_);
lean_ctor_set(v_reuseFailAlloc_2827_, 5, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2827_, 6, v_messages_2801_);
lean_ctor_set(v_reuseFailAlloc_2827_, 7, v_infoState_2802_);
lean_ctor_set(v_reuseFailAlloc_2827_, 8, v_snapshotTasks_2803_);
v___x_2809_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v_mctx_2812_; lean_object* v_zetaDeltaFVarIds_2813_; lean_object* v_postponed_2814_; lean_object* v_diag_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2825_; 
v___x_2810_ = lean_st_ref_set(v___y_2788_, v___x_2809_);
v___x_2811_ = lean_st_ref_take(v___y_2791_);
v_mctx_2812_ = lean_ctor_get(v___x_2811_, 0);
v_zetaDeltaFVarIds_2813_ = lean_ctor_get(v___x_2811_, 2);
v_postponed_2814_ = lean_ctor_get(v___x_2811_, 3);
v_diag_2815_ = lean_ctor_get(v___x_2811_, 4);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2811_, 1);
lean_dec(v_unused_2826_);
v___x_2817_ = v___x_2811_;
v_isShared_2818_ = v_isSharedCheck_2825_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_diag_2815_);
lean_inc(v_postponed_2814_);
lean_inc(v_zetaDeltaFVarIds_2813_);
lean_inc(v_mctx_2812_);
lean_dec(v___x_2811_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2825_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v___x_2792_);
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_mctx_2812_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_zetaDeltaFVarIds_2813_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_postponed_2814_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v_diag_2815_);
v___x_2820_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2821_ = lean_st_ref_set(v___y_2791_, v___x_2820_);
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0___boxed(lean_object* v___y_2830_, lean_object* v_isExporting_2831_, lean_object* v___x_2832_, lean_object* v___y_2833_, lean_object* v___x_2834_, lean_object* v_a_x3f_2835_, lean_object* v___y_2836_){
_start:
{
uint8_t v_isExporting_boxed_2837_; lean_object* v_res_2838_; 
v_isExporting_boxed_2837_ = lean_unbox(v_isExporting_2831_);
v_res_2838_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(v___y_2830_, v_isExporting_boxed_2837_, v___x_2832_, v___y_2833_, v___x_2834_, v_a_x3f_2835_);
lean_dec(v_a_x3f_2835_);
lean_dec(v___y_2833_);
lean_dec(v___y_2830_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(lean_object* v_x_2839_, uint8_t v_isExporting_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; lean_object* v_env_2847_; uint8_t v_isExporting_2848_; uint8_t v___y_2915_; lean_object* v___x_2917_; uint8_t v_isModule_2918_; uint8_t v___x_2919_; 
v___x_2846_ = lean_st_ref_get(v___y_2844_);
v_env_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_ref(v_env_2847_);
lean_dec(v___x_2846_);
v_isExporting_2848_ = lean_ctor_get_uint8(v_env_2847_, sizeof(void*)*8);
v___x_2917_ = l_Lean_Environment_header(v_env_2847_);
lean_dec_ref(v_env_2847_);
v_isModule_2918_ = lean_ctor_get_uint8(v___x_2917_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2917_);
v___x_2919_ = lean_bool_not(v_isModule_2918_);
if (v___x_2919_ == 0)
{
if (v_isExporting_2848_ == 0)
{
if (v_isExporting_2840_ == 0)
{
lean_object* v___x_2920_; 
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc_ref(v___y_2841_);
v___x_2920_ = lean_apply_5(v_x_2839_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, lean_box(0));
return v___x_2920_;
}
else
{
goto v___jp_2849_;
}
}
else
{
v___y_2915_ = v_isExporting_2840_;
goto v___jp_2914_;
}
}
else
{
v___y_2915_ = v___x_2919_;
goto v___jp_2914_;
}
v___jp_2849_:
{
lean_object* v___x_2850_; lean_object* v_env_2851_; lean_object* v_nextMacroScope_2852_; lean_object* v_ngen_2853_; lean_object* v_auxDeclNGen_2854_; lean_object* v_traceState_2855_; lean_object* v_messages_2856_; lean_object* v_infoState_2857_; lean_object* v_snapshotTasks_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2912_; 
v___x_2850_ = lean_st_ref_take(v___y_2844_);
v_env_2851_ = lean_ctor_get(v___x_2850_, 0);
v_nextMacroScope_2852_ = lean_ctor_get(v___x_2850_, 1);
v_ngen_2853_ = lean_ctor_get(v___x_2850_, 2);
v_auxDeclNGen_2854_ = lean_ctor_get(v___x_2850_, 3);
v_traceState_2855_ = lean_ctor_get(v___x_2850_, 4);
v_messages_2856_ = lean_ctor_get(v___x_2850_, 6);
v_infoState_2857_ = lean_ctor_get(v___x_2850_, 7);
v_snapshotTasks_2858_ = lean_ctor_get(v___x_2850_, 8);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; 
v_unused_2913_ = lean_ctor_get(v___x_2850_, 5);
lean_dec(v_unused_2913_);
v___x_2860_ = v___x_2850_;
v_isShared_2861_ = v_isSharedCheck_2912_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_snapshotTasks_2858_);
lean_inc(v_infoState_2857_);
lean_inc(v_messages_2856_);
lean_inc(v_traceState_2855_);
lean_inc(v_auxDeclNGen_2854_);
lean_inc(v_ngen_2853_);
lean_inc(v_nextMacroScope_2852_);
lean_inc(v_env_2851_);
lean_dec(v___x_2850_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2912_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2862_ = l_Lean_Environment_setExporting(v_env_2851_, v_isExporting_2840_);
v___x_2863_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 5, v___x_2863_);
lean_ctor_set(v___x_2860_, 0, v___x_2862_);
v___x_2865_ = v___x_2860_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_nextMacroScope_2852_);
lean_ctor_set(v_reuseFailAlloc_2911_, 2, v_ngen_2853_);
lean_ctor_set(v_reuseFailAlloc_2911_, 3, v_auxDeclNGen_2854_);
lean_ctor_set(v_reuseFailAlloc_2911_, 4, v_traceState_2855_);
lean_ctor_set(v_reuseFailAlloc_2911_, 5, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2911_, 6, v_messages_2856_);
lean_ctor_set(v_reuseFailAlloc_2911_, 7, v_infoState_2857_);
lean_ctor_set(v_reuseFailAlloc_2911_, 8, v_snapshotTasks_2858_);
v___x_2865_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v_mctx_2868_; lean_object* v_zetaDeltaFVarIds_2869_; lean_object* v_postponed_2870_; lean_object* v_diag_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2909_; 
v___x_2866_ = lean_st_ref_set(v___y_2844_, v___x_2865_);
v___x_2867_ = lean_st_ref_take(v___y_2842_);
v_mctx_2868_ = lean_ctor_get(v___x_2867_, 0);
v_zetaDeltaFVarIds_2869_ = lean_ctor_get(v___x_2867_, 2);
v_postponed_2870_ = lean_ctor_get(v___x_2867_, 3);
v_diag_2871_ = lean_ctor_get(v___x_2867_, 4);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2909_ == 0)
{
lean_object* v_unused_2910_; 
v_unused_2910_ = lean_ctor_get(v___x_2867_, 1);
lean_dec(v_unused_2910_);
v___x_2873_ = v___x_2867_;
v_isShared_2874_ = v_isSharedCheck_2909_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_diag_2871_);
lean_inc(v_postponed_2870_);
lean_inc(v_zetaDeltaFVarIds_2869_);
lean_inc(v_mctx_2868_);
lean_dec(v___x_2867_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2909_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2875_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2875_);
v___x_2877_ = v___x_2873_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_mctx_2868_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_zetaDeltaFVarIds_2869_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v_postponed_2870_);
lean_ctor_set(v_reuseFailAlloc_2908_, 4, v_diag_2871_);
v___x_2877_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v_r_2879_; 
v___x_2878_ = lean_st_ref_set(v___y_2842_, v___x_2877_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc_ref(v___y_2841_);
v_r_2879_ = lean_apply_5(v_x_2839_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, lean_box(0));
if (lean_obj_tag(v_r_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2896_; 
v_a_2880_ = lean_ctor_get(v_r_2879_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_r_2879_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2882_ = v_r_2879_;
v_isShared_2883_ = v_isSharedCheck_2896_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v_r_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2896_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
lean_inc(v_a_2880_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set_tag(v___x_2882_, 1);
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v___x_2886_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(v___y_2844_, v_isExporting_2848_, v___x_2863_, v___y_2842_, v___x_2875_, v___x_2885_);
lean_dec_ref(v___x_2885_);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2893_ == 0)
{
lean_object* v_unused_2894_; 
v_unused_2894_ = lean_ctor_get(v___x_2886_, 0);
lean_dec(v_unused_2894_);
v___x_2888_ = v___x_2886_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v___x_2886_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v_a_2880_);
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2880_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_a_2897_ = lean_ctor_get(v_r_2879_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v_r_2879_, 1);
v___x_2898_ = lean_box(0);
v___x_2899_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(v___y_2844_, v_isExporting_2848_, v___x_2863_, v___y_2842_, v___x_2875_, v___x_2898_);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v___x_2899_, 0);
lean_dec(v_unused_2907_);
v___x_2901_ = v___x_2899_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_dec(v___x_2899_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set_tag(v___x_2901_, 1);
lean_ctor_set(v___x_2901_, 0, v_a_2897_);
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2897_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
}
}
}
v___jp_2914_:
{
if (v___y_2915_ == 0)
{
goto v___jp_2849_;
}
else
{
lean_object* v___x_2916_; 
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc_ref(v___y_2841_);
v___x_2916_ = lean_apply_5(v_x_2839_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, lean_box(0));
return v___x_2916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___boxed(lean_object* v_x_2921_, lean_object* v_isExporting_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v_isExporting_boxed_2928_; lean_object* v_res_2929_; 
v_isExporting_boxed_2928_ = lean_unbox(v_isExporting_2922_);
v_res_2929_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(v_x_2921_, v_isExporting_boxed_2928_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0(lean_object* v_00_u03b1_2930_, lean_object* v_x_2931_, uint8_t v_isExporting_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(v_x_2931_, v_isExporting_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___boxed(lean_object* v_00_u03b1_2939_, lean_object* v_x_2940_, lean_object* v_isExporting_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v_isExporting_boxed_2947_; lean_object* v_res_2948_; 
v_isExporting_boxed_2947_ = lean_unbox(v_isExporting_2941_);
v_res_2948_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0(v_00_u03b1_2939_, v_x_2940_, v_isExporting_boxed_2947_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0(lean_object* v_indName_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; 
lean_inc(v_indName_2949_);
v___x_2955_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v___x_2956_; 
lean_dec_ref_known(v___x_2955_, 1);
lean_inc(v_indName_2949_);
v___x_2956_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v___x_2957_; 
lean_dec_ref_known(v___x_2956_, 1);
v___x_2957_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
return v___x_2957_;
}
else
{
lean_dec(v_indName_2949_);
return v___x_2956_;
}
}
else
{
lean_dec(v_indName_2949_);
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object* v_indName_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_mkCtorElim___lam__0(v_indName_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim(lean_object* v_indName_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v___x_2971_; lean_object* v_env_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; uint8_t v___x_2975_; 
v___x_2971_ = lean_st_ref_get(v_a_2969_);
v_env_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc_ref(v_env_2972_);
lean_dec(v___x_2971_);
lean_inc(v_indName_2965_);
v___x_2973_ = l_Lean_mkCtorIdxName(v_indName_2965_);
v___x_2974_ = 1;
v___x_2975_ = l_Lean_Environment_contains(v_env_2972_, v___x_2973_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_dec(v_indName_2965_);
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
else
{
lean_object* v___x_2978_; 
lean_inc(v_indName_2965_);
v___x_2978_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3044_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_3044_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3044_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
if (lean_obj_tag(v_a_2979_) == 5)
{
lean_object* v_val_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; 
v_val_2983_ = lean_ctor_get(v_a_2979_, 0);
lean_inc_ref(v_val_2983_);
lean_dec_ref_known(v_a_2979_, 1);
v___x_2984_ = lean_unsigned_to_nat(1u);
v___x_2985_ = l_Lean_InductiveVal_numCtors(v_val_2983_);
v___x_2986_ = lean_nat_dec_lt(v___x_2984_, v___x_2985_);
lean_dec(v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
lean_dec_ref(v_val_2983_);
lean_dec(v_indName_2965_);
v___x_2987_ = lean_box(0);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2987_);
v___x_2989_ = v___x_2981_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
else
{
lean_object* v_toConstantVal_2991_; lean_object* v_levelParams_2992_; lean_object* v_type_2993_; lean_object* v___x_2994_; 
lean_del_object(v___x_2981_);
v_toConstantVal_2991_ = lean_ctor_get(v_val_2983_, 0);
lean_inc_ref(v_toConstantVal_2991_);
lean_dec_ref(v_val_2983_);
v_levelParams_2992_ = lean_ctor_get(v_toConstantVal_2991_, 1);
lean_inc(v_levelParams_2992_);
v_type_2993_ = lean_ctor_get(v_toConstantVal_2991_, 2);
lean_inc_ref(v_type_2993_);
lean_dec_ref(v_toConstantVal_2991_);
v___x_2994_ = l_Lean_Meta_isPropFormerType(v_type_2993_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3031_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3031_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3031_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_unbox(v_a_2995_);
lean_dec(v_a_2995_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_del_object(v___x_2997_);
lean_inc(v_indName_2965_);
v___x_3000_ = l_Lean_mkRecName(v_indName_2965_);
v___x_3001_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v___x_3000_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3018_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3018_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3018_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3006_ = l_List_lengthTR___redArg(v_levelParams_2992_);
lean_dec(v_levelParams_2992_);
v___x_3007_ = l_Lean_ConstantInfo_levelParams(v_a_3002_);
lean_dec(v_a_3002_);
v___x_3008_ = l_List_lengthTR___redArg(v___x_3007_);
lean_dec(v___x_3007_);
v___x_3009_ = lean_nat_dec_lt(v___x_3006_, v___x_3008_);
lean_dec(v___x_3008_);
lean_dec(v___x_3006_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
lean_dec(v_indName_2965_);
v___x_3010_ = lean_box(0);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3010_);
v___x_3012_ = v___x_3004_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
else
{
lean_object* v___f_3014_; uint8_t v___x_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; 
lean_del_object(v___x_3004_);
lean_inc(v_indName_2965_);
v___f_3014_ = lean_alloc_closure((void*)(l_Lean_mkCtorElim___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3014_, 0, v_indName_2965_);
v___x_3015_ = l_Lean_isPrivateName(v_indName_2965_);
lean_dec(v_indName_2965_);
v___x_3016_ = lean_bool_not(v___x_3015_);
v___x_3017_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(v___f_3014_, v___x_3016_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
return v___x_3017_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_levelParams_2992_);
lean_dec(v_indName_2965_);
v_a_3019_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3001_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3001_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
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
else
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
lean_dec(v_levelParams_2992_);
lean_dec(v_indName_2965_);
v___x_3027_ = lean_box(0);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3027_);
v___x_3029_ = v___x_2997_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec(v_levelParams_2992_);
lean_dec(v_indName_2965_);
v_a_3032_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2994_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2994_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
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
else
{
lean_object* v___x_3040_; lean_object* v___x_3042_; 
lean_dec(v_a_2979_);
lean_dec(v_indName_2965_);
v___x_3040_ = lean_box(0);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_3040_);
v___x_3042_ = v___x_2981_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v_indName_2965_);
v_a_3045_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2978_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2978_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___boxed(lean_object* v_indName_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_mkCtorElim(v_indName_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v_decl_3060_, lean_object* v_____r_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; 
lean_inc(v_decl_3060_);
v___x_3067_ = l_Lean_mkCtorIdx(v_decl_3060_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3068_; 
lean_dec_ref_known(v___x_3067_, 1);
v___x_3068_ = l_Lean_mkCtorElim(v_decl_3060_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v___x_3068_;
}
else
{
lean_dec(v_decl_3060_);
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_decl_3069_, lean_object* v_____r_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3069_, v_____r_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
return v_res_3076_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_3082_ = l_Lean_stringToMessageData(v___x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_3086_, uint8_t v_kind_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___y_3099_; 
v___x_3093_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_3094_ = l_Lean_MessageData_ofName(v_name_3086_);
v___x_3095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3093_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v___x_3096_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_3097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
switch(v_kind_3087_)
{
case 0:
{
lean_object* v___x_3106_; 
v___x_3106_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_3099_ = v___x_3106_;
goto v___jp_3098_;
}
case 1:
{
lean_object* v___x_3107_; 
v___x_3107_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_3099_ = v___x_3107_;
goto v___jp_3098_;
}
default: 
{
lean_object* v___x_3108_; 
v___x_3108_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_3099_ = v___x_3108_;
goto v___jp_3098_;
}
}
v___jp_3098_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_inc_ref(v___y_3099_);
v___x_3100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___y_3099_);
v___x_3101_ = l_Lean_MessageData_ofFormat(v___x_3100_);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3097_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_3104_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_3109_, lean_object* v_kind_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
uint8_t v_kind_boxed_3116_; lean_object* v_res_3117_; 
v_kind_boxed_3116_ = lean_unbox(v_kind_3110_);
v_res_3117_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3109_, v_kind_boxed_3116_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3117_;
}
}
static uint64_t _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3124_; uint64_t v___x_3125_; 
v___x_3124_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3125_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3124_);
return v___x_3125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = lean_uint64_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3127_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3128_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set_uint64(v___x_3128_, sizeof(void*)*1, v___x_3126_);
return v___x_3128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3133_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
lean_ctor_set(v___x_3133_, 2, v___x_3132_);
lean_ctor_set(v___x_3133_, 3, v___x_3132_);
lean_ctor_set(v___x_3133_, 4, v___x_3132_);
lean_ctor_set(v___x_3133_, 5, v___x_3132_);
return v___x_3133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
lean_ctor_set(v___x_3135_, 2, v___x_3134_);
lean_ctor_set(v___x_3135_, 3, v___x_3134_);
lean_ctor_set(v___x_3135_, 4, v___x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3136_, lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v_decl_3139_, lean_object* v___stx_3140_, uint8_t v_kind_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
uint8_t v___x_3145_; uint8_t v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; size_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___y_3165_; uint8_t v___x_3175_; uint8_t v___x_3176_; 
v___x_3145_ = 1;
v___x_3146_ = 0;
v___x_3147_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3148_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3149_ = lean_unsigned_to_nat(32u);
v___x_3150_ = lean_mk_empty_array_with_capacity(v___x_3149_);
v___x_3151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3152_ = ((size_t)5ULL);
lean_inc_n(v___x_3136_, 6);
v___x_3153_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set(v___x_3153_, 1, v___x_3150_);
lean_ctor_set(v___x_3153_, 2, v___x_3136_);
lean_ctor_set(v___x_3153_, 3, v___x_3136_);
lean_ctor_set_usize(v___x_3153_, 4, v___x_3152_);
v___x_3154_ = lean_box(1);
lean_inc_ref(v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3148_);
lean_ctor_set(v___x_3155_, 1, v___x_3153_);
lean_ctor_set(v___x_3155_, 2, v___x_3154_);
v___x_3156_ = lean_mk_empty_array_with_capacity(v___x_3136_);
v___x_3157_ = lean_box(0);
lean_inc(v___x_3137_);
v___x_3158_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3158_, 0, v___x_3147_);
lean_ctor_set(v___x_3158_, 1, v___x_3137_);
lean_ctor_set(v___x_3158_, 2, v___x_3155_);
lean_ctor_set(v___x_3158_, 3, v___x_3156_);
lean_ctor_set(v___x_3158_, 4, v___x_3157_);
lean_ctor_set(v___x_3158_, 5, v___x_3136_);
lean_ctor_set(v___x_3158_, 6, v___x_3157_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*7, v___x_3146_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*7 + 1, v___x_3146_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*7 + 2, v___x_3146_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*7 + 3, v___x_3145_);
v___x_3159_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3136_);
lean_ctor_set(v___x_3159_, 1, v___x_3136_);
lean_ctor_set(v___x_3159_, 2, v___x_3136_);
lean_ctor_set(v___x_3159_, 3, v___x_3136_);
lean_ctor_set(v___x_3159_, 4, v___x_3148_);
lean_ctor_set(v___x_3159_, 5, v___x_3148_);
lean_ctor_set(v___x_3159_, 6, v___x_3148_);
lean_ctor_set(v___x_3159_, 7, v___x_3148_);
lean_ctor_set(v___x_3159_, 8, v___x_3148_);
lean_ctor_set(v___x_3159_, 9, v___x_3148_);
v___x_3160_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3161_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3159_);
lean_ctor_set(v___x_3162_, 1, v___x_3160_);
lean_ctor_set(v___x_3162_, 2, v___x_3137_);
lean_ctor_set(v___x_3162_, 3, v___x_3153_);
lean_ctor_set(v___x_3162_, 4, v___x_3161_);
v___x_3163_ = lean_st_mk_ref(v___x_3162_);
v___x_3175_ = 0;
v___x_3176_ = l_Lean_instBEqAttributeKind_beq(v_kind_3141_, v___x_3175_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; 
lean_dec(v_decl_3139_);
v___x_3177_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v___x_3138_, v_kind_3141_, v___x_3158_, v___x_3163_, v___y_3142_, v___y_3143_);
lean_dec_ref_known(v___x_3158_, 7);
v___y_3165_ = v___x_3177_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v___x_3138_);
v___x_3178_ = lean_box(0);
v___x_3179_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3139_, v___x_3178_, v___x_3158_, v___x_3163_, v___y_3142_, v___y_3143_);
lean_dec_ref_known(v___x_3158_, 7);
v___y_3165_ = v___x_3179_;
goto v___jp_3164_;
}
v___jp_3164_:
{
if (lean_obj_tag(v___y_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3174_; 
v_a_3166_ = lean_ctor_get(v___y_3165_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___y_3165_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3168_ = v___y_3165_;
v_isShared_3169_ = v_isSharedCheck_3174_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___y_3165_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3174_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_st_ref_get(v___x_3163_);
lean_dec(v___x_3163_);
lean_dec(v___x_3170_);
if (v_isShared_3169_ == 0)
{
v___x_3172_ = v___x_3168_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3166_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
else
{
lean_dec(v___x_3163_);
return v___y_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3180_, lean_object* v___x_3181_, lean_object* v___x_3182_, lean_object* v_decl_3183_, lean_object* v___stx_3184_, lean_object* v_kind_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
uint8_t v_kind_boxed_3189_; lean_object* v_res_3190_; 
v_kind_boxed_3189_ = lean_unbox(v_kind_3185_);
v_res_3190_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3180_, v___x_3181_, v___x_3182_, v_decl_3183_, v___stx_3184_, v_kind_boxed_3189_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___stx_3184_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; lean_object* v_env_3196_; lean_object* v_options_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3195_ = lean_st_ref_get(v___y_3193_);
v_env_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc_ref(v_env_3196_);
lean_dec(v___x_3195_);
v_options_3197_ = lean_ctor_get(v___y_3192_, 2);
v___x_3198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3199_ = lean_unsigned_to_nat(32u);
v___x_3200_ = lean_mk_empty_array_with_capacity(v___x_3199_);
lean_dec_ref(v___x_3200_);
v___x_3201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
lean_inc_ref(v_options_3197_);
v___x_3202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3202_, 0, v_env_3196_);
lean_ctor_set(v___x_3202_, 1, v___x_3198_);
lean_ctor_set(v___x_3202_, 2, v___x_3201_);
lean_ctor_set(v___x_3202_, 3, v_options_3197_);
v___x_3203_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v_msgData_3191_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_ref_3214_; lean_object* v___x_3215_; lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3224_; 
v_ref_3214_ = lean_ctor_get(v___y_3211_, 5);
v___x_3215_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msg_3210_, v___y_3211_, v___y_3212_);
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3218_ = v___x_3215_;
v_isShared_3219_ = v_isSharedCheck_3224_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3215_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3224_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
lean_inc(v_ref_3214_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_ref_3214_);
lean_ctor_set(v___x_3220_, 1, v_a_3216_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set_tag(v___x_3218_, 1);
lean_ctor_set(v___x_3218_, 0, v___x_3220_);
v___x_3222_ = v___x_3218_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
return v_res_3229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3232_ = l_Lean_stringToMessageData(v___x_3231_);
return v___x_3232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3235_ = l_Lean_stringToMessageData(v___x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3236_, lean_object* v_decl_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3241_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3242_ = l_Lean_MessageData_ofName(v___x_3236_);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v___x_3245_, v___y_3238_, v___y_3239_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3247_, lean_object* v_decl_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3247_, v_decl_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v_decl_3248_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3334_ = l_Lean_registerBuiltinAttribute(v___x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3337_, lean_object* v_msg_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3338_, v___y_3339_, v___y_3340_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3343_, lean_object* v_msg_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(v_00_u03b1_3343_, v_msg_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_3349_, lean_object* v_name_3350_, uint8_t v_kind_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3350_, v_kind_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_3358_, lean_object* v_name_3359_, lean_object* v_kind_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
uint8_t v_kind_boxed_3366_; lean_object* v_res_3367_; 
v_kind_boxed_3366_ = lean_unbox(v_kind_3360_);
v_res_3367_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(v_00_u03b1_3358_, v_name_3359_, v_kind_boxed_3366_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3370_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3372_ = l_Lean_addBuiltinDocString(v___x_3370_, v___x_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3374_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatTable(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
