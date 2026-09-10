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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabAsElim;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_206_; lean_object* v_env_207_; lean_object* v___x_208_; lean_object* v_toCold_209_; lean_object* v_mctx_210_; lean_object* v_lctx_211_; lean_object* v_options_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_206_ = lean_st_ref_get(v___y_204_);
v_env_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc_ref(v_env_207_);
lean_dec(v___x_206_);
v___x_208_ = lean_st_ref_get(v___y_202_);
v_toCold_209_ = lean_ctor_get(v___y_203_, 0);
v_mctx_210_ = lean_ctor_get(v___x_208_, 0);
lean_inc_ref(v_mctx_210_);
lean_dec(v___x_208_);
v_lctx_211_ = lean_ctor_get(v___y_201_, 2);
v_options_212_ = lean_ctor_get(v_toCold_209_, 2);
lean_inc_ref(v_options_212_);
lean_inc_ref(v_lctx_211_);
v___x_213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_213_, 0, v_env_207_);
lean_ctor_set(v___x_213_, 1, v_mctx_210_);
lean_ctor_set(v___x_213_, 2, v_lctx_211_);
lean_ctor_set(v___x_213_, 3, v_options_212_);
v___x_214_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v_msgData_200_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0___boxed(lean_object* v_msgData_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msgData_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(lean_object* v_msg_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_ref_229_; lean_object* v___x_230_; lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_ref_229_ = lean_ctor_get(v___y_226_, 2);
v___x_230_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msg_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
lean_inc(v_ref_229_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_ref_229_);
lean_ctor_set(v___x_235_, 1, v_a_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 1);
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg___boxed(lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(lean_object* v_t_254_, lean_object* v_k_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; 
lean_inc(v_a_259_);
lean_inc_ref(v_a_258_);
lean_inc(v_a_257_);
lean_inc_ref(v_a_256_);
v___x_261_ = lean_whnf(v_t_254_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = l_Lean_Expr_isAppOfArity(v_a_262_, v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v_k_255_);
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1);
v___x_267_ = l_Lean_MessageData_ofExpr(v_a_262_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_268_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = l_Lean_Expr_appArg_x21(v_a_262_);
lean_inc(v_a_259_);
lean_inc_ref(v_a_258_);
lean_inc(v_a_257_);
lean_inc_ref(v_a_256_);
lean_inc_ref(v___x_270_);
v___x_271_ = lean_apply_6(v_k_255_, v___x_270_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, lean_box(0));
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_284_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_284_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_284_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_284_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3));
v___x_277_ = l_Lean_Expr_appFn_x21(v_a_262_);
lean_dec(v_a_262_);
v___x_278_ = l_Lean_Expr_constLevels_x21(v___x_277_);
lean_dec_ref(v___x_277_);
v___x_279_ = l_Lean_mkConst(v___x_276_, v___x_278_);
v___x_280_ = l_Lean_mkAppB(v___x_279_, v___x_270_, v_a_272_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_280_);
v___x_282_ = v___x_274_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_dec_ref(v___x_270_);
lean_dec(v_a_262_);
return v___x_271_;
}
}
}
else
{
lean_dec_ref(v_k_255_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___boxed(lean_object* v_t_285_, lean_object* v_k_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v_t_285_, v_k_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(lean_object* v_00_u03b1_293_, lean_object* v_msg_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___boxed(lean_object* v_00_u03b1_301_, lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(v_00_u03b1_301_, v_msg_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(lean_object* v_e_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; 
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc_ref(v_e_316_);
v___x_322_ = lean_infer_type(v_e_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
v___x_324_ = lean_whnf(v_a_323_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_345_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_345_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1));
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = l_Lean_Expr_isAppOfArity(v_a_325_, v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
lean_del_object(v___x_327_);
lean_dec_ref(v_e_316_);
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1);
v___x_333_ = l_Lean_MessageData_ofExpr(v_a_325_);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_334_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_336_ = l_Lean_Expr_appArg_x21(v_a_325_);
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3));
v___x_338_ = l_Lean_Expr_appFn_x21(v_a_325_);
lean_dec(v_a_325_);
v___x_339_ = l_Lean_Expr_constLevels_x21(v___x_338_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_Lean_mkConst(v___x_337_, v___x_339_);
v___x_341_ = l_Lean_mkAppB(v___x_340_, v___x_336_, v_e_316_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_341_);
v___x_343_ = v___x_327_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_dec_ref(v_e_316_);
return v___x_324_;
}
}
else
{
lean_dec_ref(v_e_316_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___boxed(lean_object* v_e_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_e_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(lean_object* v_a_353_, size_t v_sz_354_, size_t v_i_355_, lean_object* v_bs_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_usize_dec_lt(v_i_355_, v_sz_354_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_a_353_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_bs_356_);
return v___x_363_;
}
else
{
lean_object* v_v_364_; lean_object* v___x_365_; 
v_v_364_ = lean_array_uget_borrowed(v_bs_356_, v_i_355_);
lean_inc(v_v_364_);
lean_inc(v_a_353_);
v___x_365_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(v_a_353_, v_v_364_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_367_; lean_object* v_bs_x27_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
v___x_367_ = lean_unsigned_to_nat(0u);
v_bs_x27_368_ = lean_array_uset(v_bs_356_, v_i_355_, v___x_367_);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_355_, v___x_369_);
v___x_371_ = lean_array_uset(v_bs_x27_368_, v_i_355_, v_a_366_);
v_i_355_ = v___x_370_;
v_bs_356_ = v___x_371_;
goto _start;
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v_bs_356_);
lean_dec(v_a_353_);
v_a_373_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_365_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_365_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0___boxed(lean_object* v_a_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_bs_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_391_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_381_, v_sz_boxed_390_, v_i_boxed_391_, v_bs_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = l_Lean_Level_ofNat(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(lean_object* v_n_395_, lean_object* v_es_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; 
lean_inc_ref(v_es_396_);
v___x_402_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(v_es_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v___x_405_; size_t v_sz_406_; size_t v___x_407_; lean_object* v___x_408_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc_n(v_a_403_, 2);
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0);
v___x_405_ = l_Lean_mkLevelMax_x27(v_a_403_, v___x_404_);
v_sz_406_ = lean_array_size(v_es_396_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_403_, v_sz_406_, v___x_407_, v_es_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = l_Lean_Level_normalize(v___x_405_);
lean_dec(v___x_405_);
v___x_411_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(v___x_410_);
v___x_412_ = l_Lean_Expr_sort___override(v___x_411_);
v___x_413_ = l_Lean_mkNatLookupTable(v_n_395_, v___x_412_, v_a_409_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_409_);
return v___x_413_;
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v___x_405_);
lean_dec_ref(v_n_395_);
v_a_414_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_408_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_408_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_es_396_);
lean_dec_ref(v_n_395_);
v_a_422_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_402_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_402_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___boxed(lean_object* v_n_430_, lean_object* v_es_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_n_430_, v_es_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(lean_object* v_indName_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0));
v___x_441_ = l_Lean_Name_str___override(v_indName_439_, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElimName(lean_object* v_indName_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_mkCtorElimName___closed__0));
v___x_445_ = l_Lean_Name_str___override(v_indName_443_, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(lean_object* v_n1_446_, lean_object* v_n2_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_privatePrefix_x3f(v_n2_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_privateToUserName(v_n1_446_);
return v___x_449_;
}
else
{
lean_object* v_val_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_val_450_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_448_, 1);
v___x_451_ = l_Lean_privateToUserName(v_n1_446_);
v___x_452_ = l_Lean_Name_appendCore(v_val_450_, v___x_451_);
lean_dec(v_val_450_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs___boxed(lean_object* v_n1_453_, lean_object* v_n2_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(v_n1_453_, v_n2_454_);
lean_dec(v_n2_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName(lean_object* v_indName_457_, lean_object* v_conName_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = ((lean_object*)(l_Lean_mkConstructorElimName___closed__0));
v___x_460_ = l_Lean_Name_str___override(v_conName_458_, v___x_459_);
v___x_461_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(v___x_460_, v_indName_457_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorElimName___boxed(lean_object* v_indName_462_, lean_object* v_conName_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_mkConstructorElimName(v_indName_462_, v_conName_463_);
lean_dec(v_indName_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(lean_object* v_k_465_, lean_object* v_b_466_, lean_object* v_c_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
v___x_473_ = lean_apply_7(v_k_465_, v_b_466_, v_c_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, lean_box(0));
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed(lean_object* v_k_474_, lean_object* v_b_475_, lean_object* v_c_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(v_k_474_, v_b_475_, v_c_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(lean_object* v_type_483_, lean_object* v_k_484_, uint8_t v_cleanupAnnotations_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___f_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___f_491_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_491_, 0, v_k_484_);
v___x_492_ = 0;
v___x_493_ = lean_box(0);
v___x_494_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_492_, v___x_493_, v_type_483_, v___f_491_, v_cleanupAnnotations_485_, v___x_492_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_a_503_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_494_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_494_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___boxed(lean_object* v_type_511_, lean_object* v_k_512_, lean_object* v_cleanupAnnotations_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_519_; lean_object* v_res_520_; 
v_cleanupAnnotations_boxed_519_ = lean_unbox(v_cleanupAnnotations_513_);
v_res_520_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_511_, v_k_512_, v_cleanupAnnotations_boxed_519_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(lean_object* v_00_u03b1_521_, lean_object* v_type_522_, lean_object* v_k_523_, uint8_t v_cleanupAnnotations_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_522_, v_k_523_, v_cleanupAnnotations_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___boxed(lean_object* v_00_u03b1_531_, lean_object* v_type_532_, lean_object* v_k_533_, lean_object* v_cleanupAnnotations_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_540_; lean_object* v_res_541_; 
v_cleanupAnnotations_boxed_540_ = lean_unbox(v_cleanupAnnotations_534_);
v_res_541_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(v_00_u03b1_531_, v_type_532_, v_k_533_, v_cleanupAnnotations_boxed_540_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(lean_object* v_name_542_, lean_object* v_levelParams_543_, lean_object* v_type_544_, lean_object* v_value_545_, lean_object* v_hints_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; uint8_t v___y_551_; uint8_t v___y_558_; lean_object* v_env_561_; uint8_t v___x_562_; 
v___x_549_ = lean_st_ref_get(v___y_547_);
v_env_561_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref_n(v_env_561_, 2);
lean_dec(v___x_549_);
v___x_562_ = l_Lean_Environment_hasUnsafe(v_env_561_, v_type_544_);
if (v___x_562_ == 0)
{
uint8_t v___x_563_; 
v___x_563_ = l_Lean_Environment_hasUnsafe(v_env_561_, v_value_545_);
v___y_558_ = v___x_563_;
goto v___jp_557_;
}
else
{
lean_dec_ref(v_env_561_);
v___y_558_ = v___x_562_;
goto v___jp_557_;
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc(v_name_542_);
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v_name_542_);
lean_ctor_set(v___x_552_, 1, v_levelParams_543_);
lean_ctor_set(v___x_552_, 2, v_type_544_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_554_, 0, v_name_542_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_555_, 0, v___x_552_);
lean_ctor_set(v___x_555_, 1, v_value_545_);
lean_ctor_set(v___x_555_, 2, v_hints_546_);
lean_ctor_set(v___x_555_, 3, v___x_554_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*4, v___y_551_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
uint8_t v___x_559_; 
v___x_559_ = 1;
v___y_551_ = v___x_559_;
goto v___jp_550_;
}
else
{
uint8_t v___x_560_; 
v___x_560_ = 0;
v___y_551_ = v___x_560_;
goto v___jp_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg___boxed(lean_object* v_name_564_, lean_object* v_levelParams_565_, lean_object* v_type_566_, lean_object* v_value_567_, lean_object* v_hints_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_564_, v_levelParams_565_, v_type_566_, v_value_567_, v_hints_568_, v___y_569_);
lean_dec(v___y_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(lean_object* v_name_572_, lean_object* v_levelParams_573_, lean_object* v_type_574_, lean_object* v_value_575_, lean_object* v_hints_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_572_, v_levelParams_573_, v_type_574_, v_value_575_, v_hints_576_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___boxed(lean_object* v_name_583_, lean_object* v_levelParams_584_, lean_object* v_type_585_, lean_object* v_value_586_, lean_object* v_hints_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(v_name_583_, v_levelParams_584_, v_type_585_, v_value_586_, v_hints_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(lean_object* v_msg_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___f_600_; lean_object* v___x_4160__overap_601_; lean_object* v___x_602_; 
v___f_600_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_4160__overap_601_ = lean_panic_fn_borrowed(v___f_600_, v_msg_594_);
lean_inc(v___y_598_);
lean_inc_ref(v___y_597_);
lean_inc(v___y_596_);
lean_inc_ref(v___y_595_);
v___x_602_ = lean_apply_5(v___x_4160__overap_601_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, lean_box(0));
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(lean_object* v_msg_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v_msg_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(size_t v_sz_610_, size_t v_i_611_, lean_object* v_bs_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_lt(v_i_611_, v_sz_610_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_bs_612_);
return v___x_619_;
}
else
{
lean_object* v_v_620_; lean_object* v___x_621_; 
v_v_620_ = lean_array_uget_borrowed(v_bs_612_, v_i_611_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc(v___y_614_);
lean_inc_ref(v___y_613_);
lean_inc(v_v_620_);
v___x_621_ = lean_infer_type(v_v_620_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_623_; lean_object* v_bs_x27_624_; size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = lean_unsigned_to_nat(0u);
v_bs_x27_624_ = lean_array_uset(v_bs_612_, v_i_611_, v___x_623_);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_611_, v___x_625_);
v___x_627_ = lean_array_uset(v_bs_x27_624_, v_i_611_, v_a_622_);
v_i_611_ = v___x_626_;
v_bs_612_ = v___x_627_;
goto _start;
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_bs_612_);
v_a_629_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_621_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_621_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1___boxed(lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_bs_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
size_t v_sz_boxed_645_; size_t v_i_boxed_646_; lean_object* v_res_647_; 
v_sz_boxed_645_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_646_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_sz_boxed_645_, v_i_boxed_646_, v_bs_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(lean_object* v___x_648_, lean_object* v___x_649_, lean_object* v___x_650_, uint8_t v___x_651_, lean_object* v_ctorIdx_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
size_t v_sz_658_; size_t v___x_659_; lean_object* v___x_660_; 
v_sz_658_ = lean_array_size(v___x_648_);
v___x_659_ = ((size_t)0ULL);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_sz_658_, v___x_659_, v___x_648_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
lean_inc_ref(v_ctorIdx_652_);
v___x_662_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_ctorIdx_652_, v_a_661_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v___x_664_ = lean_unsigned_to_nat(2u);
v___x_665_ = lean_mk_empty_array_with_capacity(v___x_664_);
v___x_666_ = lean_array_push(v___x_665_, v___x_649_);
v___x_667_ = lean_array_push(v___x_666_, v_ctorIdx_652_);
v___x_668_ = l_Array_append___redArg(v___x_650_, v___x_667_);
lean_dec_ref(v___x_667_);
v___x_669_ = 1;
v___x_670_ = 1;
v___x_671_ = l_Lean_Meta_mkLambdaFVars(v___x_668_, v_a_663_, v___x_651_, v___x_669_, v___x_651_, v___x_669_, v___x_670_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec_ref(v___x_668_);
return v___x_671_;
}
else
{
lean_dec_ref(v_ctorIdx_652_);
lean_dec_ref(v___x_650_);
lean_dec_ref(v___x_649_);
return v___x_662_;
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_ctorIdx_652_);
lean_dec_ref(v___x_650_);
lean_dec_ref(v___x_649_);
v_a_672_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_660_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_660_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed(lean_object* v___x_680_, lean_object* v___x_681_, lean_object* v___x_682_, lean_object* v___x_683_, lean_object* v_ctorIdx_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
uint8_t v___x_6628__boxed_690_; lean_object* v_res_691_; 
v___x_6628__boxed_690_ = lean_unbox(v___x_683_);
v_res_691_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(v___x_680_, v___x_681_, v___x_682_, v___x_6628__boxed_690_, v_ctorIdx_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0(lean_object* v_k_692_, lean_object* v_b_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; 
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
v___x_699_ = lean_apply_6(v_k_692_, v_b_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, lean_box(0));
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_700_, lean_object* v_b_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0(v_k_700_, v_b_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(lean_object* v_name_708_, uint8_t v_bi_709_, lean_object* v_type_710_, lean_object* v_k_711_, uint8_t v_kind_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___f_718_; lean_object* v___x_719_; 
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_718_, 0, v_k_711_);
v___x_719_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_708_, v_bi_709_, v_type_710_, v___f_718_, v_kind_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_719_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_719_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg___boxed(lean_object* v_name_736_, lean_object* v_bi_737_, lean_object* v_type_738_, lean_object* v_k_739_, lean_object* v_kind_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
uint8_t v_bi_boxed_746_; uint8_t v_kind_boxed_747_; lean_object* v_res_748_; 
v_bi_boxed_746_ = lean_unbox(v_bi_737_);
v_kind_boxed_747_ = lean_unbox(v_kind_740_);
v_res_748_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_736_, v_bi_boxed_746_, v_type_738_, v_k_739_, v_kind_boxed_747_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(lean_object* v_name_749_, lean_object* v_type_750_, lean_object* v_k_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
uint8_t v___x_757_; uint8_t v___x_758_; lean_object* v___x_759_; 
v___x_757_ = 0;
v___x_758_ = 0;
v___x_759_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_749_, v___x_757_, v_type_750_, v_k_751_, v___x_758_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg___boxed(lean_object* v_name_760_, lean_object* v_type_761_, lean_object* v_k_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v_name_760_, v_type_761_, v_k_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
return v_res_768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_box(0);
v___x_776_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_777_ = l_Lean_mkConst(v___x_776_, v___x_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(lean_object* v_val_778_, lean_object* v___x_779_, lean_object* v___x_780_, uint8_t v___x_781_, lean_object* v_xs_782_, lean_object* v_x_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_numParams_789_; lean_object* v_numIndices_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_numParams_789_ = lean_ctor_get(v_val_778_, 1);
lean_inc_n(v_numParams_789_, 2);
v_numIndices_790_ = lean_ctor_get(v_val_778_, 2);
lean_inc(v_numIndices_790_);
lean_dec_ref(v_val_778_);
lean_inc_ref(v_xs_782_);
v___x_791_ = l_Array_toSubarray___redArg(v_xs_782_, v___x_779_, v_numParams_789_);
v___x_792_ = l_Subarray_copy___redArg(v___x_791_);
v___x_793_ = lean_array_get(v___x_780_, v_xs_782_, v_numParams_789_);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_add(v_numParams_789_, v___x_794_);
lean_dec(v_numParams_789_);
v___x_796_ = lean_nat_add(v___x_795_, v_numIndices_790_);
lean_dec(v_numIndices_790_);
lean_dec(v___x_795_);
v___x_797_ = lean_nat_add(v___x_796_, v___x_794_);
lean_dec(v___x_796_);
v___x_798_ = lean_array_get_size(v_xs_782_);
v___x_799_ = l_Array_toSubarray___redArg(v_xs_782_, v___x_797_, v___x_798_);
v___x_800_ = l_Subarray_copy___redArg(v___x_799_);
v___x_801_ = lean_box(v___x_781_);
v___f_802_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_802_, 0, v___x_800_);
lean_closure_set(v___f_802_, 1, v___x_793_);
lean_closure_set(v___f_802_, 2, v___x_792_);
lean_closure_set(v___f_802_, 3, v___x_801_);
v___x_803_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_804_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_805_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_803_, v___x_804_, v___f_802_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed(lean_object* v_val_806_, lean_object* v___x_807_, lean_object* v___x_808_, lean_object* v___x_809_, lean_object* v_xs_810_, lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v___x_6805__boxed_817_; lean_object* v_res_818_; 
v___x_6805__boxed_817_ = lean_unbox(v___x_809_);
v_res_818_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(v_val_806_, v___x_807_, v___x_808_, v___x_6805__boxed_817_, v_xs_810_, v_x_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v_x_811_);
lean_dec_ref(v___x_808_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_819_, lean_object* v_msg_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_toCold_826_; lean_object* v_currRecDepth_827_; lean_object* v_ref_828_; uint8_t v_diag_829_; uint8_t v_suppressElabErrors_830_; lean_object* v_ref_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_toCold_826_ = lean_ctor_get(v___y_823_, 0);
v_currRecDepth_827_ = lean_ctor_get(v___y_823_, 1);
v_ref_828_ = lean_ctor_get(v___y_823_, 2);
v_diag_829_ = lean_ctor_get_uint8(v___y_823_, sizeof(void*)*3);
v_suppressElabErrors_830_ = lean_ctor_get_uint8(v___y_823_, sizeof(void*)*3 + 1);
v_ref_831_ = l_Lean_replaceRef(v_ref_819_, v_ref_828_);
lean_inc(v_currRecDepth_827_);
lean_inc_ref(v_toCold_826_);
v___x_832_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_832_, 0, v_toCold_826_);
lean_ctor_set(v___x_832_, 1, v_currRecDepth_827_);
lean_ctor_set(v___x_832_, 2, v_ref_831_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*3, v_diag_829_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*3 + 1, v_suppressElabErrors_830_);
v___x_833_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_820_, v___y_821_, v___y_822_, v___x_832_, v___y_824_);
lean_dec_ref_known(v___x_832_, 3);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_834_, lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_834_, v_msg_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v_ref_834_);
return v_res_841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
lean_ctor_set(v___x_847_, 2, v___x_846_);
lean_ctor_set(v___x_847_, 3, v___x_846_);
lean_ctor_set(v___x_847_, 4, v___x_845_);
lean_ctor_set(v___x_847_, 5, v___x_845_);
lean_ctor_set(v___x_847_, 6, v___x_845_);
lean_ctor_set(v___x_847_, 7, v___x_845_);
lean_ctor_set(v___x_847_, 8, v___x_845_);
lean_ctor_set(v___x_847_, 9, v___x_845_);
lean_ctor_set(v___x_847_, 10, v___x_845_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_unsigned_to_nat(32u);
v___x_849_ = lean_mk_empty_array_with_capacity(v___x_848_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_851_ = ((size_t)5ULL);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_unsigned_to_nat(32u);
v___x_854_ = lean_mk_empty_array_with_capacity(v___x_853_);
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_856_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_854_);
lean_ctor_set(v___x_856_, 2, v___x_852_);
lean_ctor_set(v___x_856_, 3, v___x_852_);
lean_ctor_set_usize(v___x_856_, 4, v___x_851_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_857_ = lean_box(1);
v___x_858_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_859_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_858_);
lean_ctor_set(v___x_860_, 2, v___x_857_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_869_ = l_Lean_stringToMessageData(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_872_ = l_Lean_stringToMessageData(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_882_, lean_object* v_declHint_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v_env_887_; uint8_t v___x_888_; 
v___x_886_ = lean_st_ref_get(v___y_884_);
v_env_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_env_887_);
lean_dec(v___x_886_);
v___x_888_ = l_Lean_Name_isAnonymous(v_declHint_883_);
if (v___x_888_ == 0)
{
uint8_t v_isExporting_889_; 
v_isExporting_889_ = lean_ctor_get_uint8(v_env_887_, sizeof(void*)*8);
if (v_isExporting_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec_ref(v_env_887_);
lean_dec(v_declHint_883_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v_msg_882_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; uint8_t v___x_892_; 
lean_inc_ref(v_env_887_);
v___x_891_ = l_Lean_Environment_setExporting(v_env_887_, v___x_888_);
lean_inc(v_declHint_883_);
lean_inc_ref(v___x_891_);
v___x_892_ = l_Lean_Environment_contains(v___x_891_, v_declHint_883_, v_isExporting_889_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
lean_dec_ref(v___x_891_);
lean_dec_ref(v_env_887_);
lean_dec(v_declHint_883_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v_msg_882_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_c_899_; lean_object* v___x_900_; 
v___x_894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_896_ = l_Lean_Options_empty;
v___x_897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_897_, 0, v___x_891_);
lean_ctor_set(v___x_897_, 1, v___x_894_);
lean_ctor_set(v___x_897_, 2, v___x_895_);
lean_ctor_set(v___x_897_, 3, v___x_896_);
lean_inc(v_declHint_883_);
v___x_898_ = l_Lean_MessageData_ofConstName(v_declHint_883_, v___x_888_);
v_c_899_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_899_, 0, v___x_897_);
lean_ctor_set(v_c_899_, 1, v___x_898_);
v___x_900_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_887_, v_declHint_883_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec_ref(v_env_887_);
lean_dec(v_declHint_883_);
v___x_901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v_c_899_);
v___x_903_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_MessageData_note(v___x_904_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v_msg_882_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
else
{
lean_object* v_val_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_943_; 
v_val_908_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_943_ == 0)
{
v___x_910_ = v___x_900_;
v_isShared_911_ = v_isSharedCheck_943_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_val_908_);
lean_dec(v___x_900_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_943_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_mod_915_; uint8_t v___x_916_; 
v___x_912_ = lean_box(0);
v___x_913_ = l_Lean_Environment_header(v_env_887_);
lean_dec_ref(v_env_887_);
v___x_914_ = l_Lean_EnvironmentHeader_moduleNames(v___x_913_);
v_mod_915_ = lean_array_get(v___x_912_, v___x_914_, v_val_908_);
lean_dec(v_val_908_);
lean_dec_ref(v___x_914_);
v___x_916_ = l_Lean_isPrivateName(v_declHint_883_);
lean_dec(v_declHint_883_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v_c_899_);
v___x_919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_MessageData_ofName(v_mod_915_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_MessageData_note(v___x_924_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v_msg_882_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 0);
lean_ctor_set(v___x_910_, 0, v___x_926_);
v___x_928_ = v___x_910_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v_c_899_);
v___x_932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_MessageData_ofName(v_mod_915_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_MessageData_note(v___x_937_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v_msg_882_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 0);
lean_ctor_set(v___x_910_, 0, v___x_939_);
v___x_941_ = v___x_910_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_944_; 
lean_dec_ref(v_env_887_);
lean_dec(v_declHint_883_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_msg_882_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_945_, lean_object* v_declHint_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_945_, v_declHint_946_, v___y_947_);
lean_dec(v___y_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_950_, lean_object* v_declHint_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_967_; 
v___x_957_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_950_, v_declHint_951_, v___y_955_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_967_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_962_ = l_Lean_unknownIdentifierMessageTag;
v___x_963_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v_a_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_963_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_968_, lean_object* v_declHint_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_968_, v_declHint_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_976_, lean_object* v_msg_977_, lean_object* v_declHint_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v_a_985_; lean_object* v___x_986_; 
v___x_984_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_977_, v_declHint_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v___x_986_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_976_, v_a_985_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_987_, lean_object* v_msg_988_, lean_object* v_declHint_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_987_, v_msg_988_, v_declHint_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v_ref_987_);
return v_res_995_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1002_, lean_object* v_constName_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1009_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_1010_ = 0;
lean_inc(v_constName_1003_);
v___x_1011_ = l_Lean_MessageData_ofConstName(v_constName_1003_, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1009_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1002_, v___x_1014_, v_constName_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1016_, lean_object* v_constName_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1016_, v_constName_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v_ref_1016_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(lean_object* v_constName_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_ref_1030_; lean_object* v___x_1031_; 
v_ref_1030_ = lean_ctor_get(v___y_1027_, 2);
v___x_1031_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1030_, v_constName_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(lean_object* v_constName_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; lean_object* v_env_1046_; uint8_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = lean_st_ref_get(v___y_1043_);
v_env_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc_ref(v_env_1046_);
lean_dec(v___x_1045_);
v___x_1047_ = 0;
lean_inc(v_constName_1039_);
v___x_1048_ = l_Lean_Environment_find_x3f(v_env_1046_, v_constName_1039_, v___x_1047_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1049_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_constName_1039_);
v_val_1050_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1048_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_val_1050_);
lean_dec(v___x_1048_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 0);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_val_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(lean_object* v_constName_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_constName_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1064_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
v___x_1071_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
lean_ctor_set(v___x_1071_, 3, v___x_1070_);
lean_ctor_set(v___x_1071_, 4, v___x_1070_);
lean_ctor_set(v___x_1071_, 5, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(lean_object* v_declName_1072_, uint8_t v_s_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_env_1078_; lean_object* v_nextMacroScope_1079_; lean_object* v_ngen_1080_; lean_object* v_auxDeclNGen_1081_; lean_object* v_traceState_1082_; lean_object* v_messages_1083_; lean_object* v_infoState_1084_; lean_object* v_snapshotTasks_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1114_; 
v___x_1077_ = lean_st_ref_take(v___y_1075_);
v_env_1078_ = lean_ctor_get(v___x_1077_, 0);
v_nextMacroScope_1079_ = lean_ctor_get(v___x_1077_, 1);
v_ngen_1080_ = lean_ctor_get(v___x_1077_, 2);
v_auxDeclNGen_1081_ = lean_ctor_get(v___x_1077_, 3);
v_traceState_1082_ = lean_ctor_get(v___x_1077_, 4);
v_messages_1083_ = lean_ctor_get(v___x_1077_, 6);
v_infoState_1084_ = lean_ctor_get(v___x_1077_, 7);
v_snapshotTasks_1085_ = lean_ctor_get(v___x_1077_, 8);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; 
v_unused_1115_ = lean_ctor_get(v___x_1077_, 5);
lean_dec(v_unused_1115_);
v___x_1087_ = v___x_1077_;
v_isShared_1088_ = v_isSharedCheck_1114_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_snapshotTasks_1085_);
lean_inc(v_infoState_1084_);
lean_inc(v_messages_1083_);
lean_inc(v_traceState_1082_);
lean_inc(v_auxDeclNGen_1081_);
lean_inc(v_ngen_1080_);
lean_inc(v_nextMacroScope_1079_);
lean_inc(v_env_1078_);
lean_dec(v___x_1077_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1114_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1089_ = 0;
v___x_1090_ = lean_box(0);
v___x_1091_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1078_, v_declName_1072_, v_s_1073_, v___x_1089_, v___x_1090_);
v___x_1092_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 5, v___x_1092_);
lean_ctor_set(v___x_1087_, 0, v___x_1091_);
v___x_1094_ = v___x_1087_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_nextMacroScope_1079_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_ngen_1080_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_auxDeclNGen_1081_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_traceState_1082_);
lean_ctor_set(v_reuseFailAlloc_1113_, 5, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1113_, 6, v_messages_1083_);
lean_ctor_set(v_reuseFailAlloc_1113_, 7, v_infoState_1084_);
lean_ctor_set(v_reuseFailAlloc_1113_, 8, v_snapshotTasks_1085_);
v___x_1094_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_mctx_1097_; lean_object* v_zetaDeltaFVarIds_1098_; lean_object* v_postponed_1099_; lean_object* v_diag_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1111_; 
v___x_1095_ = lean_st_ref_put(v___y_1075_, v___x_1094_);
v___x_1096_ = lean_st_ref_take(v___y_1074_);
v_mctx_1097_ = lean_ctor_get(v___x_1096_, 0);
v_zetaDeltaFVarIds_1098_ = lean_ctor_get(v___x_1096_, 2);
v_postponed_1099_ = lean_ctor_get(v___x_1096_, 3);
v_diag_1100_ = lean_ctor_get(v___x_1096_, 4);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; 
v_unused_1112_ = lean_ctor_get(v___x_1096_, 1);
lean_dec(v_unused_1112_);
v___x_1102_ = v___x_1096_;
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_diag_1100_);
lean_inc(v_postponed_1099_);
lean_inc(v_zetaDeltaFVarIds_1098_);
lean_inc(v_mctx_1097_);
lean_dec(v___x_1096_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_mctx_1097_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_zetaDeltaFVarIds_1098_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_postponed_1099_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_diag_1100_);
v___x_1106_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_st_ref_put(v___y_1074_, v___x_1106_);
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object* v_declName_1116_, lean_object* v_s_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v_s_boxed_1121_; lean_object* v_res_1122_; 
v_s_boxed_1121_ = lean_unbox(v_s_1117_);
v_res_1122_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1116_, v_s_boxed_1121_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object* v_declName_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = 0;
v___x_1130_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1123_, v___x_1129_, v___y_1125_, v___y_1127_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___boxed(lean_object* v_declName_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v_declName_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(lean_object* v_constName_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v_env_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_st_ref_get(v___y_1142_);
v_env_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc_ref(v_env_1145_);
lean_dec(v___x_1144_);
v___x_1146_ = 0;
lean_inc(v_constName_1138_);
v___x_1147_ = l_Lean_Environment_findConstVal_x3f(v_env_1145_, v_constName_1138_, v___x_1146_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1148_;
}
else
{
lean_object* v_val_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_constName_1138_);
v_val_1149_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1147_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_val_1149_);
lean_dec(v___x_1147_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 0);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_val_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(lean_object* v_constName_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v_constName_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1166_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1167_ = lean_unsigned_to_nat(60u);
v___x_1168_ = lean_unsigned_to_nat(81u);
v___x_1169_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0));
v___x_1170_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1171_ = l_mkPanicMessageWithDecl(v___x_1170_, v___x_1169_, v___x_1168_, v___x_1167_, v___x_1166_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(lean_object* v_indName_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; 
lean_inc(v_indName_1172_);
v___x_1178_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1311_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1311_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1311_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
if (lean_obj_tag(v_a_1179_) == 5)
{
lean_object* v_val_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_val_1183_ = lean_ctor_get(v_a_1179_, 0);
lean_inc_ref(v_val_1183_);
lean_dec_ref_known(v_a_1179_, 1);
v___x_1184_ = l_Lean_InductiveVal_numCtors(v_val_1183_);
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = lean_nat_dec_eq(v___x_1184_, v___x_1185_);
lean_dec(v___x_1184_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1181_);
lean_inc(v_indName_1172_);
v___x_1187_ = l_Lean_mkCasesOnName(v_indName_1172_);
v___x_1188_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1187_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v_levelParams_1190_; lean_object* v_type_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v_levelParams_1190_ = lean_ctor_get(v_a_1189_, 1);
lean_inc(v_levelParams_1190_);
v_type_1191_ = lean_ctor_get(v_a_1189_, 2);
lean_inc_ref(v_type_1191_);
lean_dec(v_a_1189_);
v___x_1192_ = l_Lean_instInhabitedExpr;
v___x_1193_ = lean_box(v___x_1186_);
v___f_1194_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1194_, 0, v_val_1183_);
lean_closure_set(v___f_1194_, 1, v___x_1185_);
lean_closure_set(v___f_1194_, 2, v___x_1192_);
lean_closure_set(v___f_1194_, 3, v___x_1193_);
v___x_1195_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1191_, v___f_1194_, v___x_1186_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_n(v_a_1196_, 2);
lean_dec_ref_known(v___x_1195_, 1);
lean_inc(v_a_1176_);
lean_inc_ref(v_a_1175_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
v___x_1197_ = lean_infer_type(v_a_1196_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1280_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1172_);
v___x_1200_ = lean_box(1);
lean_inc(v___x_1199_);
v___x_1201_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1199_, v_levelParams_1190_, v_a_1198_, v_a_1196_, v___x_1200_, v_a_1176_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1280_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1280_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set_tag(v___x_1204_, 1);
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
uint8_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = 1;
v___x_1209_ = l_Lean_addAndCompile(v___x_1207_, v___x_1208_, v___x_1186_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; lean_object* v_env_1211_; lean_object* v_nextMacroScope_1212_; lean_object* v_ngen_1213_; lean_object* v_auxDeclNGen_1214_; lean_object* v_traceState_1215_; lean_object* v_messages_1216_; lean_object* v_infoState_1217_; lean_object* v_snapshotTasks_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref_known(v___x_1209_, 1);
v___x_1210_ = lean_st_ref_take(v_a_1176_);
v_env_1211_ = lean_ctor_get(v___x_1210_, 0);
v_nextMacroScope_1212_ = lean_ctor_get(v___x_1210_, 1);
v_ngen_1213_ = lean_ctor_get(v___x_1210_, 2);
v_auxDeclNGen_1214_ = lean_ctor_get(v___x_1210_, 3);
v_traceState_1215_ = lean_ctor_get(v___x_1210_, 4);
v_messages_1216_ = lean_ctor_get(v___x_1210_, 6);
v_infoState_1217_ = lean_ctor_get(v___x_1210_, 7);
v_snapshotTasks_1218_ = lean_ctor_get(v___x_1210_, 8);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1210_, 5);
lean_dec(v_unused_1278_);
v___x_1220_ = v___x_1210_;
v_isShared_1221_ = v_isSharedCheck_1277_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snapshotTasks_1218_);
lean_inc(v_infoState_1217_);
lean_inc(v_messages_1216_);
lean_inc(v_traceState_1215_);
lean_inc(v_auxDeclNGen_1214_);
lean_inc(v_ngen_1213_);
lean_inc(v_nextMacroScope_1212_);
lean_inc(v_env_1211_);
lean_dec(v___x_1210_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1277_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
lean_inc(v___x_1199_);
v___x_1222_ = l_Lean_Meta_addToCompletionBlackList(v_env_1211_, v___x_1199_);
v___x_1223_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 5, v___x_1223_);
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1225_ = v___x_1220_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_nextMacroScope_1212_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_ngen_1213_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_auxDeclNGen_1214_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_traceState_1215_);
lean_ctor_set(v_reuseFailAlloc_1276_, 5, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1276_, 6, v_messages_1216_);
lean_ctor_set(v_reuseFailAlloc_1276_, 7, v_infoState_1217_);
lean_ctor_set(v_reuseFailAlloc_1276_, 8, v_snapshotTasks_1218_);
v___x_1225_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_mctx_1228_; lean_object* v_zetaDeltaFVarIds_1229_; lean_object* v_postponed_1230_; lean_object* v_diag_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1274_; 
v___x_1226_ = lean_st_ref_put(v_a_1176_, v___x_1225_);
v___x_1227_ = lean_st_ref_take(v_a_1174_);
v_mctx_1228_ = lean_ctor_get(v___x_1227_, 0);
v_zetaDeltaFVarIds_1229_ = lean_ctor_get(v___x_1227_, 2);
v_postponed_1230_ = lean_ctor_get(v___x_1227_, 3);
v_diag_1231_ = lean_ctor_get(v___x_1227_, 4);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1227_, 1);
lean_dec(v_unused_1275_);
v___x_1233_ = v___x_1227_;
v_isShared_1234_ = v_isSharedCheck_1274_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_diag_1231_);
lean_inc(v_postponed_1230_);
lean_inc(v_zetaDeltaFVarIds_1229_);
lean_inc(v_mctx_1228_);
lean_dec(v___x_1227_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1274_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_mctx_1228_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_zetaDeltaFVarIds_1229_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_postponed_1230_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_diag_1231_);
v___x_1237_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_env_1240_; lean_object* v_nextMacroScope_1241_; lean_object* v_ngen_1242_; lean_object* v_auxDeclNGen_1243_; lean_object* v_traceState_1244_; lean_object* v_messages_1245_; lean_object* v_infoState_1246_; lean_object* v_snapshotTasks_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1271_; 
v___x_1238_ = lean_st_ref_put(v_a_1174_, v___x_1237_);
v___x_1239_ = lean_st_ref_take(v_a_1176_);
v_env_1240_ = lean_ctor_get(v___x_1239_, 0);
v_nextMacroScope_1241_ = lean_ctor_get(v___x_1239_, 1);
v_ngen_1242_ = lean_ctor_get(v___x_1239_, 2);
v_auxDeclNGen_1243_ = lean_ctor_get(v___x_1239_, 3);
v_traceState_1244_ = lean_ctor_get(v___x_1239_, 4);
v_messages_1245_ = lean_ctor_get(v___x_1239_, 6);
v_infoState_1246_ = lean_ctor_get(v___x_1239_, 7);
v_snapshotTasks_1247_ = lean_ctor_get(v___x_1239_, 8);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1239_, 5);
lean_dec(v_unused_1272_);
v___x_1249_ = v___x_1239_;
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snapshotTasks_1247_);
lean_inc(v_infoState_1246_);
lean_inc(v_messages_1245_);
lean_inc(v_traceState_1244_);
lean_inc(v_auxDeclNGen_1243_);
lean_inc(v_ngen_1242_);
lean_inc(v_nextMacroScope_1241_);
lean_inc(v_env_1240_);
lean_dec(v___x_1239_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
lean_inc(v___x_1199_);
v___x_1251_ = l_Lean_addProtected(v_env_1240_, v___x_1199_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 5, v___x_1223_);
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_nextMacroScope_1241_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_ngen_1242_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_auxDeclNGen_1243_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_traceState_1244_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1270_, 6, v_messages_1245_);
lean_ctor_set(v_reuseFailAlloc_1270_, 7, v_infoState_1246_);
lean_ctor_set(v_reuseFailAlloc_1270_, 8, v_snapshotTasks_1247_);
v___x_1253_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_mctx_1256_; lean_object* v_zetaDeltaFVarIds_1257_; lean_object* v_postponed_1258_; lean_object* v_diag_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
v___x_1254_ = lean_st_ref_put(v_a_1176_, v___x_1253_);
v___x_1255_ = lean_st_ref_take(v_a_1174_);
v_mctx_1256_ = lean_ctor_get(v___x_1255_, 0);
v_zetaDeltaFVarIds_1257_ = lean_ctor_get(v___x_1255_, 2);
v_postponed_1258_ = lean_ctor_get(v___x_1255_, 3);
v_diag_1259_ = lean_ctor_get(v___x_1255_, 4);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v___x_1255_, 1);
lean_dec(v_unused_1269_);
v___x_1261_ = v___x_1255_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_diag_1259_);
lean_inc(v_postponed_1258_);
lean_inc(v_zetaDeltaFVarIds_1257_);
lean_inc(v_mctx_1256_);
lean_dec(v___x_1255_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1235_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_mctx_1256_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_zetaDeltaFVarIds_1257_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_postponed_1258_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_diag_1259_);
v___x_1264_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_st_ref_put(v_a_1174_, v___x_1264_);
v___x_1266_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_1199_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1266_;
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
lean_dec(v___x_1199_);
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_a_1196_);
lean_dec(v_levelParams_1190_);
lean_dec(v_indName_1172_);
v_a_1281_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1197_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1197_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_levelParams_1190_);
lean_dec(v_indName_1172_);
v_a_1289_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1195_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1195_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_val_1183_);
lean_dec(v_indName_1172_);
v_a_1297_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1188_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1188_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_dec_ref(v_val_1183_);
lean_dec(v_indName_1172_);
v___x_1305_ = lean_box(0);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1305_);
v___x_1307_ = v___x_1181_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_del_object(v___x_1181_);
lean_dec(v_a_1179_);
lean_dec(v_indName_1172_);
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2);
v___x_1310_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_1309_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1310_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_indName_1172_);
v_a_1312_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1178_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1178_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___boxed(lean_object* v_indName_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(lean_object* v_00_u03b1_1327_, lean_object* v_name_1328_, uint8_t v_bi_1329_, lean_object* v_type_1330_, lean_object* v_k_1331_, uint8_t v_kind_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___redArg(v_name_1328_, v_bi_1329_, v_type_1330_, v_k_1331_, v_kind_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_name_1340_, lean_object* v_bi_1341_, lean_object* v_type_1342_, lean_object* v_k_1343_, lean_object* v_kind_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
uint8_t v_bi_boxed_1350_; uint8_t v_kind_boxed_1351_; lean_object* v_res_1352_; 
v_bi_boxed_1350_ = lean_unbox(v_bi_1341_);
v_kind_boxed_1351_ = lean_unbox(v_kind_1344_);
v_res_1352_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2_spec__3(v_00_u03b1_1339_, v_name_1340_, v_bi_boxed_1350_, v_type_1342_, v_k_1343_, v_kind_boxed_1351_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(lean_object* v_00_u03b1_1353_, lean_object* v_name_1354_, lean_object* v_type_1355_, lean_object* v_k_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v_name_1354_, v_type_1355_, v_k_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_name_1364_, lean_object* v_type_1365_, lean_object* v_k_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(v_00_u03b1_1363_, v_name_1364_, v_type_1365_, v_k_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(lean_object* v_declName_1373_, uint8_t v_s_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1373_, v_s_1374_, v___y_1376_, v___y_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___boxed(lean_object* v_declName_1381_, lean_object* v_s_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v_s_boxed_1388_; lean_object* v_res_1389_; 
v_s_boxed_1388_ = lean_unbox(v_s_1382_);
v_res_1389_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(v_declName_1381_, v_s_boxed_1388_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(lean_object* v_00_u03b1_1390_, lean_object* v_constName_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1398_, lean_object* v_constName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(v_00_u03b1_1398_, v_constName_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_1406_, lean_object* v_ref_1407_, lean_object* v_constName_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1407_, v_constName_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_ref_1416_, lean_object* v_constName_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(v_00_u03b1_1415_, v_ref_1416_, v_constName_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v_ref_1416_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_1424_, lean_object* v_ref_1425_, lean_object* v_msg_1426_, lean_object* v_declHint_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1425_, v_msg_1426_, v_declHint_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_ref_1435_, lean_object* v_msg_1436_, lean_object* v_declHint_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_1434_, v_ref_1435_, v_msg_1436_, v_declHint_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v_ref_1435_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_1444_, lean_object* v_declHint_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_1444_, v_declHint_1445_, v___y_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1452_, lean_object* v_declHint_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_1452_, v_declHint_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_1460_, lean_object* v_ref_1461_, lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_1461_, v_msg_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_ref_1470_, lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_1469_, v_ref_1470_, v_msg_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v_ref_1470_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(lean_object* v___x_1478_, lean_object* v_k_1479_, lean_object* v_zs_1480_, uint8_t v___x_1481_, uint8_t v___x_1482_, uint8_t v___x_1483_, lean_object* v_h_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
lean_inc_ref(v_h_1484_);
v___x_1490_ = l_Lean_Meta_mkEqNDRec(v___x_1478_, v_k_1479_, v_h_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1492_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(v_a_1491_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1494_ = l_Lean_mkAppN(v_a_1493_, v_zs_1480_);
v___x_1495_ = lean_array_push(v_zs_1480_, v_h_1484_);
v___x_1496_ = l_Lean_Meta_mkLambdaFVars(v___x_1495_, v___x_1494_, v___x_1481_, v___x_1482_, v___x_1481_, v___x_1482_, v___x_1483_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec_ref(v___x_1495_);
return v___x_1496_;
}
else
{
lean_dec_ref(v_h_1484_);
lean_dec_ref(v_zs_1480_);
return v___x_1492_;
}
}
else
{
lean_dec_ref(v_h_1484_);
lean_dec_ref(v_zs_1480_);
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___x_1497_, lean_object* v_k_1498_, lean_object* v_zs_1499_, lean_object* v___x_1500_, lean_object* v___x_1501_, lean_object* v___x_1502_, lean_object* v_h_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_5986__boxed_1509_; uint8_t v___x_5987__boxed_1510_; uint8_t v___x_5988__boxed_1511_; lean_object* v_res_1512_; 
v___x_5986__boxed_1509_ = lean_unbox(v___x_1500_);
v___x_5987__boxed_1510_ = lean_unbox(v___x_1501_);
v___x_5988__boxed_1511_ = lean_unbox(v___x_1502_);
v_res_1512_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(v___x_1497_, v_k_1498_, v_zs_1499_, v___x_5986__boxed_1509_, v___x_5987__boxed_1510_, v___x_5988__boxed_1511_, v_h_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(lean_object* v___x_1516_, lean_object* v_k_1517_, uint8_t v___x_1518_, uint8_t v___x_1519_, uint8_t v___x_1520_, lean_object* v___x_1521_, lean_object* v___x_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, lean_object* v_ctorIdx_1525_, lean_object* v___x_1526_, lean_object* v_zs_1527_, lean_object* v___ctorRet_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1534_ = lean_box(v___x_1518_);
v___x_1535_ = lean_box(v___x_1519_);
v___x_1536_ = lean_box(v___x_1520_);
v___f_1537_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1537_, 0, v___x_1516_);
lean_closure_set(v___f_1537_, 1, v_k_1517_);
lean_closure_set(v___f_1537_, 2, v_zs_1527_);
lean_closure_set(v___f_1537_, 3, v___x_1534_);
lean_closure_set(v___f_1537_, 4, v___x_1535_);
lean_closure_set(v___f_1537_, 5, v___x_1536_);
v___x_1538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1));
v___x_1539_ = l_Lean_Level_ofNat(v___x_1521_);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1522_);
v___x_1541_ = l_Lean_mkConst(v___x_1538_, v___x_1540_);
v___x_1542_ = l_Lean_mkRawNatLit(v___x_1523_);
v___x_1543_ = l_Lean_mkApp3(v___x_1541_, v___x_1524_, v_ctorIdx_1525_, v___x_1542_);
v___x_1544_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1526_, v___x_1543_, v___f_1537_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1545_ = _args[0];
lean_object* v_k_1546_ = _args[1];
lean_object* v___x_1547_ = _args[2];
lean_object* v___x_1548_ = _args[3];
lean_object* v___x_1549_ = _args[4];
lean_object* v___x_1550_ = _args[5];
lean_object* v___x_1551_ = _args[6];
lean_object* v___x_1552_ = _args[7];
lean_object* v___x_1553_ = _args[8];
lean_object* v_ctorIdx_1554_ = _args[9];
lean_object* v___x_1555_ = _args[10];
lean_object* v_zs_1556_ = _args[11];
lean_object* v___ctorRet_1557_ = _args[12];
lean_object* v___y_1558_ = _args[13];
lean_object* v___y_1559_ = _args[14];
lean_object* v___y_1560_ = _args[15];
lean_object* v___y_1561_ = _args[16];
lean_object* v___y_1562_ = _args[17];
_start:
{
uint8_t v___x_6035__boxed_1563_; uint8_t v___x_6036__boxed_1564_; uint8_t v___x_6037__boxed_1565_; lean_object* v_res_1566_; 
v___x_6035__boxed_1563_ = lean_unbox(v___x_1547_);
v___x_6036__boxed_1564_ = lean_unbox(v___x_1548_);
v___x_6037__boxed_1565_ = lean_unbox(v___x_1549_);
v_res_1566_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(v___x_1545_, v_k_1546_, v___x_6035__boxed_1563_, v___x_6036__boxed_1564_, v___x_6037__boxed_1565_, v___x_1550_, v___x_1551_, v___x_1552_, v___x_1553_, v_ctorIdx_1554_, v___x_1555_, v_zs_1556_, v___ctorRet_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec_ref(v___ctorRet_1557_);
lean_dec(v___x_1550_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(lean_object* v___x_1570_, lean_object* v_k_1571_, lean_object* v_ctorIdx_1572_, lean_object* v_tail_1573_, lean_object* v___x_1574_, size_t v_sz_1575_, size_t v_i_1576_, lean_object* v_bs_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_usize_dec_lt(v_i_1576_, v_sz_1575_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec(v_tail_1573_);
lean_dec_ref(v_ctorIdx_1572_);
lean_dec_ref(v_k_1571_);
lean_dec_ref(v___x_1570_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_bs_1577_);
return v___x_1584_;
}
else
{
lean_object* v_v_1585_; lean_object* v___x_1586_; lean_object* v_bs_x27_1587_; lean_object* v___y_1589_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_v_1585_ = lean_array_uget(v_bs_1577_, v_i_1576_);
v___x_1586_ = lean_unsigned_to_nat(0u);
v_bs_x27_1587_ = lean_array_uset(v_bs_1577_, v_i_1576_, v___x_1586_);
lean_inc(v_tail_1573_);
v___x_1603_ = l_Lean_mkConst(v_v_1585_, v_tail_1573_);
v___x_1604_ = l_Lean_mkAppN(v___x_1603_, v___x_1574_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
v___x_1605_ = lean_infer_type(v___x_1604_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; uint8_t v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___f_1617_; lean_object* v___x_1618_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v___x_1607_ = 0;
v___x_1608_ = 1;
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_1612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_1613_ = lean_usize_to_nat(v_i_1576_);
v___x_1614_ = lean_box(v___x_1607_);
v___x_1615_ = lean_box(v___x_1583_);
v___x_1616_ = lean_box(v___x_1608_);
lean_inc_ref(v_ctorIdx_1572_);
lean_inc_ref(v_k_1571_);
lean_inc_ref(v___x_1570_);
v___f_1617_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed), 18, 11);
lean_closure_set(v___f_1617_, 0, v___x_1570_);
lean_closure_set(v___f_1617_, 1, v_k_1571_);
lean_closure_set(v___f_1617_, 2, v___x_1614_);
lean_closure_set(v___f_1617_, 3, v___x_1615_);
lean_closure_set(v___f_1617_, 4, v___x_1616_);
lean_closure_set(v___f_1617_, 5, v___x_1609_);
lean_closure_set(v___f_1617_, 6, v___x_1610_);
lean_closure_set(v___f_1617_, 7, v___x_1613_);
lean_closure_set(v___f_1617_, 8, v___x_1611_);
lean_closure_set(v___f_1617_, 9, v_ctorIdx_1572_);
lean_closure_set(v___f_1617_, 10, v___x_1612_);
v___x_1618_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_a_1606_, v___f_1617_, v___x_1607_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
v___y_1589_ = v___x_1618_;
goto v___jp_1588_;
}
else
{
v___y_1589_ = v___x_1605_;
goto v___jp_1588_;
}
v___jp_1588_:
{
if (lean_obj_tag(v___y_1589_) == 0)
{
lean_object* v_a_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v_a_1590_ = lean_ctor_get(v___y_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___y_1589_, 1);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_add(v_i_1576_, v___x_1591_);
v___x_1593_ = lean_array_uset(v_bs_x27_1587_, v_i_1576_, v_a_1590_);
v_i_1576_ = v___x_1592_;
v_bs_1577_ = v___x_1593_;
goto _start;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v_bs_x27_1587_);
lean_dec(v_tail_1573_);
lean_dec_ref(v_ctorIdx_1572_);
lean_dec_ref(v_k_1571_);
lean_dec_ref(v___x_1570_);
v_a_1595_ = lean_ctor_get(v___y_1589_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___y_1589_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___y_1589_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___y_1589_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___boxed(lean_object* v___x_1619_, lean_object* v_k_1620_, lean_object* v_ctorIdx_1621_, lean_object* v_tail_1622_, lean_object* v___x_1623_, lean_object* v_sz_1624_, lean_object* v_i_1625_, lean_object* v_bs_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
size_t v_sz_boxed_1632_; size_t v_i_boxed_1633_; lean_object* v_res_1634_; 
v_sz_boxed_1632_ = lean_unbox_usize(v_sz_1624_);
lean_dec(v_sz_1624_);
v_i_boxed_1633_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1619_, v_k_1620_, v_ctorIdx_1621_, v_tail_1622_, v___x_1623_, v_sz_boxed_1632_, v_i_boxed_1633_, v_bs_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec_ref(v___x_1623_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(lean_object* v___x_1635_, lean_object* v___x_1636_, lean_object* v_a_1637_, lean_object* v_ctors_1638_, lean_object* v___x_1639_, lean_object* v_ctorIdx_1640_, lean_object* v_tail_1641_, lean_object* v___x_1642_, lean_object* v_name_1643_, lean_object* v___x_1644_, lean_object* v_h_1645_, lean_object* v_k_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_inc_ref(v___x_1635_);
v___x_1652_ = l_Lean_mkAppN(v___x_1635_, v___x_1636_);
v___x_1653_ = l_Lean_mkArrow(v_a_1637_, v___x_1652_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; uint8_t v___x_1655_; uint8_t v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1655_ = 0;
v___x_1656_ = 1;
v___x_1657_ = 1;
v___x_1658_ = l_Lean_Meta_mkLambdaFVars(v___x_1636_, v_a_1654_, v___x_1655_, v___x_1656_, v___x_1655_, v___x_1656_, v___x_1657_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; size_t v_sz_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = lean_array_mk(v_ctors_1638_);
v_sz_1661_ = lean_array_size(v___x_1660_);
v___x_1662_ = ((size_t)0ULL);
lean_inc_ref(v_ctorIdx_1640_);
lean_inc_ref(v_k_1646_);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1639_, v_k_1646_, v_ctorIdx_1640_, v_tail_1641_, v___x_1642_, v_sz_1661_, v___x_1662_, v___x_1660_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = l_Lean_mkConst(v_name_1643_, v___x_1644_);
v___x_1666_ = l_Lean_mkAppN(v___x_1665_, v___x_1642_);
v___x_1667_ = l_Lean_Expr_app___override(v___x_1666_, v_a_1659_);
v___x_1668_ = l_Lean_mkAppN(v___x_1667_, v___x_1636_);
v___x_1669_ = l_Lean_mkAppN(v___x_1668_, v_a_1664_);
lean_dec(v_a_1664_);
lean_inc_ref(v_h_1645_);
v___x_1670_ = l_Lean_Expr_app___override(v___x_1669_, v_h_1645_);
v___x_1671_ = lean_unsigned_to_nat(2u);
v___x_1672_ = lean_mk_empty_array_with_capacity(v___x_1671_);
lean_inc_ref(v___x_1672_);
v___x_1673_ = lean_array_push(v___x_1672_, v___x_1635_);
v___x_1674_ = lean_array_push(v___x_1673_, v_ctorIdx_1640_);
v___x_1675_ = l_Array_append___redArg(v___x_1642_, v___x_1674_);
lean_dec_ref(v___x_1674_);
v___x_1676_ = l_Array_append___redArg(v___x_1675_, v___x_1636_);
v___x_1677_ = lean_array_push(v___x_1672_, v_h_1645_);
v___x_1678_ = lean_array_push(v___x_1677_, v_k_1646_);
v___x_1679_ = l_Array_append___redArg(v___x_1676_, v___x_1678_);
lean_dec_ref(v___x_1678_);
v___x_1680_ = l_Lean_Meta_mkLambdaFVars(v___x_1679_, v___x_1670_, v___x_1655_, v___x_1656_, v___x_1655_, v___x_1656_, v___x_1657_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec_ref(v___x_1679_);
return v___x_1680_;
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1659_);
lean_dec_ref(v_k_1646_);
lean_dec_ref(v_h_1645_);
lean_dec(v___x_1644_);
lean_dec(v_name_1643_);
lean_dec_ref(v___x_1642_);
lean_dec_ref(v_ctorIdx_1640_);
lean_dec_ref(v___x_1635_);
v_a_1681_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1663_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1663_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_dec_ref(v_k_1646_);
lean_dec_ref(v_h_1645_);
lean_dec(v___x_1644_);
lean_dec(v_name_1643_);
lean_dec_ref(v___x_1642_);
lean_dec(v_tail_1641_);
lean_dec_ref(v_ctorIdx_1640_);
lean_dec_ref(v___x_1639_);
lean_dec(v_ctors_1638_);
lean_dec_ref(v___x_1635_);
return v___x_1658_;
}
}
else
{
lean_dec_ref(v_k_1646_);
lean_dec_ref(v_h_1645_);
lean_dec(v___x_1644_);
lean_dec(v_name_1643_);
lean_dec_ref(v___x_1642_);
lean_dec(v_tail_1641_);
lean_dec_ref(v_ctorIdx_1640_);
lean_dec_ref(v___x_1639_);
lean_dec(v_ctors_1638_);
lean_dec_ref(v___x_1635_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed(lean_object** _args){
lean_object* v___x_1689_ = _args[0];
lean_object* v___x_1690_ = _args[1];
lean_object* v_a_1691_ = _args[2];
lean_object* v_ctors_1692_ = _args[3];
lean_object* v___x_1693_ = _args[4];
lean_object* v_ctorIdx_1694_ = _args[5];
lean_object* v_tail_1695_ = _args[6];
lean_object* v___x_1696_ = _args[7];
lean_object* v_name_1697_ = _args[8];
lean_object* v___x_1698_ = _args[9];
lean_object* v_h_1699_ = _args[10];
lean_object* v_k_1700_ = _args[11];
lean_object* v___y_1701_ = _args[12];
lean_object* v___y_1702_ = _args[13];
lean_object* v___y_1703_ = _args[14];
lean_object* v___y_1704_ = _args[15];
lean_object* v___y_1705_ = _args[16];
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(v___x_1689_, v___x_1690_, v_a_1691_, v_ctors_1692_, v___x_1693_, v_ctorIdx_1694_, v_tail_1695_, v___x_1696_, v_name_1697_, v___x_1698_, v_h_1699_, v_k_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___x_1690_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(lean_object* v___x_1710_, lean_object* v___x_1711_, lean_object* v_a_1712_, lean_object* v_ctors_1713_, lean_object* v___x_1714_, lean_object* v_ctorIdx_1715_, lean_object* v_tail_1716_, lean_object* v___x_1717_, lean_object* v_name_1718_, lean_object* v___x_1719_, lean_object* v___x_1720_, lean_object* v_h_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___f_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___f_1727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1727_, 0, v___x_1710_);
lean_closure_set(v___f_1727_, 1, v___x_1711_);
lean_closure_set(v___f_1727_, 2, v_a_1712_);
lean_closure_set(v___f_1727_, 3, v_ctors_1713_);
lean_closure_set(v___f_1727_, 4, v___x_1714_);
lean_closure_set(v___f_1727_, 5, v_ctorIdx_1715_);
lean_closure_set(v___f_1727_, 6, v_tail_1716_);
lean_closure_set(v___f_1727_, 7, v___x_1717_);
lean_closure_set(v___f_1727_, 8, v_name_1718_);
lean_closure_set(v___f_1727_, 9, v___x_1719_);
lean_closure_set(v___f_1727_, 10, v_h_1721_);
v___x_1728_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1));
v___x_1729_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1728_, v___x_1720_, v___f_1727_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed(lean_object** _args){
lean_object* v___x_1730_ = _args[0];
lean_object* v___x_1731_ = _args[1];
lean_object* v_a_1732_ = _args[2];
lean_object* v_ctors_1733_ = _args[3];
lean_object* v___x_1734_ = _args[4];
lean_object* v_ctorIdx_1735_ = _args[5];
lean_object* v_tail_1736_ = _args[6];
lean_object* v___x_1737_ = _args[7];
lean_object* v_name_1738_ = _args[8];
lean_object* v___x_1739_ = _args[9];
lean_object* v___x_1740_ = _args[10];
lean_object* v_h_1741_ = _args[11];
lean_object* v___y_1742_ = _args[12];
lean_object* v___y_1743_ = _args[13];
lean_object* v___y_1744_ = _args[14];
lean_object* v___y_1745_ = _args[15];
lean_object* v___y_1746_ = _args[16];
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(v___x_1730_, v___x_1731_, v_a_1732_, v_ctors_1733_, v___x_1734_, v_ctorIdx_1735_, v_tail_1736_, v___x_1737_, v_name_1738_, v___x_1739_, v___x_1740_, v_h_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(lean_object* v___x_1748_, lean_object* v___x_1749_, lean_object* v___x_1750_, lean_object* v___x_1751_, lean_object* v_indName_1752_, lean_object* v_tail_1753_, lean_object* v___x_1754_, lean_object* v_ctors_1755_, lean_object* v_name_1756_, lean_object* v_ctorIdx_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_inc(v___x_1749_);
v___x_1763_ = l_Lean_mkConst(v___x_1748_, v___x_1749_);
lean_inc_ref(v___x_1751_);
lean_inc_ref_n(v___x_1750_, 2);
v___x_1764_ = lean_array_push(v___x_1750_, v___x_1751_);
v___x_1765_ = l_Lean_mkAppN(v___x_1763_, v___x_1764_);
lean_dec_ref(v___x_1764_);
lean_inc_ref_n(v_ctorIdx_1757_, 2);
lean_inc_ref(v___x_1765_);
v___x_1766_ = l_Lean_Expr_app___override(v___x_1765_, v_ctorIdx_1757_);
v___x_1767_ = l_Lean_mkCtorIdxName(v_indName_1752_);
lean_inc(v_tail_1753_);
v___x_1768_ = l_Lean_mkConst(v___x_1767_, v_tail_1753_);
v___x_1769_ = l_Array_append___redArg(v___x_1750_, v___x_1754_);
v___x_1770_ = l_Lean_mkAppN(v___x_1768_, v___x_1769_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = l_Lean_Meta_mkEq(v_ctorIdx_1757_, v___x_1770_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_n(v_a_1772_, 2);
lean_dec_ref_known(v___x_1771_, 1);
v___f_1773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed), 17, 11);
lean_closure_set(v___f_1773_, 0, v___x_1751_);
lean_closure_set(v___f_1773_, 1, v___x_1754_);
lean_closure_set(v___f_1773_, 2, v_a_1772_);
lean_closure_set(v___f_1773_, 3, v_ctors_1755_);
lean_closure_set(v___f_1773_, 4, v___x_1765_);
lean_closure_set(v___f_1773_, 5, v_ctorIdx_1757_);
lean_closure_set(v___f_1773_, 6, v_tail_1753_);
lean_closure_set(v___f_1773_, 7, v___x_1750_);
lean_closure_set(v___f_1773_, 8, v_name_1756_);
lean_closure_set(v___f_1773_, 9, v___x_1749_);
lean_closure_set(v___f_1773_, 10, v___x_1766_);
v___x_1774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_1775_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1774_, v_a_1772_, v___f_1773_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
return v___x_1775_;
}
else
{
lean_dec_ref(v___x_1766_);
lean_dec_ref(v___x_1765_);
lean_dec_ref(v_ctorIdx_1757_);
lean_dec(v_name_1756_);
lean_dec(v_ctors_1755_);
lean_dec_ref(v___x_1754_);
lean_dec(v_tail_1753_);
lean_dec_ref(v___x_1751_);
lean_dec_ref(v___x_1750_);
lean_dec(v___x_1749_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed(lean_object* v___x_1776_, lean_object* v___x_1777_, lean_object* v___x_1778_, lean_object* v___x_1779_, lean_object* v_indName_1780_, lean_object* v_tail_1781_, lean_object* v___x_1782_, lean_object* v_ctors_1783_, lean_object* v_name_1784_, lean_object* v_ctorIdx_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(v___x_1776_, v___x_1777_, v___x_1778_, v___x_1779_, v_indName_1780_, v_tail_1781_, v___x_1782_, v_ctors_1783_, v_name_1784_, v_ctorIdx_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(lean_object* v_val_1792_, lean_object* v___x_1793_, lean_object* v___x_1794_, lean_object* v___x_1795_, lean_object* v_indName_1796_, lean_object* v_tail_1797_, lean_object* v_name_1798_, lean_object* v___x_1799_, lean_object* v_xs_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_numParams_1807_; lean_object* v_numIndices_1808_; lean_object* v_ctors_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___f_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_numParams_1807_ = lean_ctor_get(v_val_1792_, 1);
lean_inc_n(v_numParams_1807_, 2);
v_numIndices_1808_ = lean_ctor_get(v_val_1792_, 2);
lean_inc(v_numIndices_1808_);
v_ctors_1809_ = lean_ctor_get(v_val_1792_, 4);
lean_inc(v_ctors_1809_);
lean_dec_ref(v_val_1792_);
v___x_1810_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_1800_, 2);
v___x_1811_ = l_Array_toSubarray___redArg(v_xs_1800_, v___x_1810_, v_numParams_1807_);
v___x_1812_ = l_Subarray_copy___redArg(v___x_1811_);
v___x_1813_ = lean_array_get(v___x_1793_, v_xs_1800_, v_numParams_1807_);
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = lean_nat_add(v_numParams_1807_, v___x_1814_);
lean_dec(v_numParams_1807_);
v___x_1816_ = lean_nat_add(v___x_1815_, v_numIndices_1808_);
lean_dec(v_numIndices_1808_);
lean_inc(v___x_1816_);
v___x_1817_ = l_Array_toSubarray___redArg(v_xs_1800_, v___x_1815_, v___x_1816_);
v___x_1818_ = l_Subarray_copy___redArg(v___x_1817_);
v___x_1819_ = lean_array_get(v___x_1793_, v_xs_1800_, v___x_1816_);
lean_dec(v___x_1816_);
lean_dec_ref(v_xs_1800_);
v___x_1820_ = lean_array_push(v___x_1818_, v___x_1819_);
v___f_1821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed), 15, 9);
lean_closure_set(v___f_1821_, 0, v___x_1794_);
lean_closure_set(v___f_1821_, 1, v___x_1795_);
lean_closure_set(v___f_1821_, 2, v___x_1812_);
lean_closure_set(v___f_1821_, 3, v___x_1813_);
lean_closure_set(v___f_1821_, 4, v_indName_1796_);
lean_closure_set(v___f_1821_, 5, v_tail_1797_);
lean_closure_set(v___f_1821_, 6, v___x_1820_);
lean_closure_set(v___f_1821_, 7, v_ctors_1809_);
lean_closure_set(v___f_1821_, 8, v_name_1798_);
v___x_1822_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_1823_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_1824_ = l_Lean_mkConst(v___x_1823_, v___x_1799_);
v___x_1825_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1822_, v___x_1824_, v___f_1821_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed(lean_object* v_val_1826_, lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v___x_1829_, lean_object* v_indName_1830_, lean_object* v_tail_1831_, lean_object* v_name_1832_, lean_object* v___x_1833_, lean_object* v_xs_1834_, lean_object* v_x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(v_val_1826_, v___x_1827_, v___x_1828_, v___x_1829_, v_indName_1830_, v_tail_1831_, v_name_1832_, v___x_1833_, v_xs_1834_, v_x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v_x_1835_);
lean_dec_ref(v___x_1827_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
if (lean_obj_tag(v_a_1842_) == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = l_List_reverse___redArg(v_a_1843_);
return v___x_1844_;
}
else
{
lean_object* v_head_1845_; lean_object* v_tail_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1855_; 
v_head_1845_ = lean_ctor_get(v_a_1842_, 0);
v_tail_1846_ = lean_ctor_get(v_a_1842_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1848_ = v_a_1842_;
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_tail_1846_);
lean_inc(v_head_1845_);
lean_dec(v_a_1842_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_mkLevelParam(v_head_1845_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v_a_1843_);
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_a_1843_);
v___x_1852_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v_a_1842_ = v_tail_1846_;
v_a_1843_ = v___x_1852_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1858_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_1859_ = lean_unsigned_to_nat(58u);
v___x_1860_ = lean_unsigned_to_nat(113u);
v___x_1861_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1862_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1863_ = l_mkPanicMessageWithDecl(v___x_1862_, v___x_1861_, v___x_1860_, v___x_1859_, v___x_1858_);
return v___x_1863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1865_ = lean_unsigned_to_nat(60u);
v___x_1866_ = lean_unsigned_to_nat(109u);
v___x_1867_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1869_ = l_mkPanicMessageWithDecl(v___x_1868_, v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(lean_object* v_indName_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; 
lean_inc(v_indName_1870_);
v___x_1876_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
if (lean_obj_tag(v_a_1877_) == 5)
{
lean_object* v_val_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_val_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc_ref(v_val_1878_);
lean_dec_ref_known(v_a_1877_, 1);
lean_inc_n(v_indName_1870_, 2);
v___x_1879_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1870_);
v___x_1880_ = l_Lean_mkCasesOnName(v_indName_1870_);
v___x_1881_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1880_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v_name_1883_; lean_object* v_levelParams_1884_; lean_object* v_type_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v_name_1883_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_name_1883_);
v_levelParams_1884_ = lean_ctor_get(v_a_1882_, 1);
lean_inc_n(v_levelParams_1884_, 2);
v_type_1885_ = lean_ctor_get(v_a_1882_, 2);
lean_inc_ref(v_type_1885_);
lean_dec(v_a_1882_);
v___x_1886_ = lean_box(0);
v___x_1887_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_1884_, v___x_1886_);
if (lean_obj_tag(v___x_1887_) == 1)
{
lean_object* v_tail_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v_tail_1888_ = lean_ctor_get(v___x_1887_, 1);
lean_inc(v_tail_1888_);
v___x_1889_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1870_);
v___f_1890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed), 15, 8);
lean_closure_set(v___f_1890_, 0, v_val_1878_);
lean_closure_set(v___f_1890_, 1, v___x_1889_);
lean_closure_set(v___f_1890_, 2, v___x_1879_);
lean_closure_set(v___f_1890_, 3, v___x_1887_);
lean_closure_set(v___f_1890_, 4, v_indName_1870_);
lean_closure_set(v___f_1890_, 5, v_tail_1888_);
lean_closure_set(v___f_1890_, 6, v_name_1883_);
lean_closure_set(v___f_1890_, 7, v___x_1886_);
v___x_1891_ = 0;
v___x_1892_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1885_, v___f_1890_, v___x_1891_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc_n(v_a_1893_, 2);
lean_dec_ref_known(v___x_1892_, 1);
lean_inc(v_a_1874_);
lean_inc_ref(v_a_1873_);
lean_inc(v_a_1872_);
lean_inc_ref(v_a_1871_);
v___x_1894_ = lean_infer_type(v_a_1893_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_2010_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = l_Lean_mkCtorElimName(v_indName_1870_);
v___x_1897_ = lean_box(1);
lean_inc(v___x_1896_);
v___x_1898_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1896_, v_levelParams_1884_, v_a_1895_, v_a_1893_, v___x_1897_, v_a_1874_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_2010_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_2010_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 1);
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
uint8_t v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = 1;
v___x_1906_ = l_Lean_addAndCompile(v___x_1904_, v___x_1905_, v___x_1891_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1907_; lean_object* v_env_1908_; lean_object* v_nextMacroScope_1909_; lean_object* v_ngen_1910_; lean_object* v_auxDeclNGen_1911_; lean_object* v_traceState_1912_; lean_object* v_messages_1913_; lean_object* v_infoState_1914_; lean_object* v_snapshotTasks_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref_known(v___x_1906_, 1);
v___x_1907_ = lean_st_ref_take(v_a_1874_);
v_env_1908_ = lean_ctor_get(v___x_1907_, 0);
v_nextMacroScope_1909_ = lean_ctor_get(v___x_1907_, 1);
v_ngen_1910_ = lean_ctor_get(v___x_1907_, 2);
v_auxDeclNGen_1911_ = lean_ctor_get(v___x_1907_, 3);
v_traceState_1912_ = lean_ctor_get(v___x_1907_, 4);
v_messages_1913_ = lean_ctor_get(v___x_1907_, 6);
v_infoState_1914_ = lean_ctor_get(v___x_1907_, 7);
v_snapshotTasks_1915_ = lean_ctor_get(v___x_1907_, 8);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v___x_1907_, 5);
lean_dec(v_unused_2008_);
v___x_1917_ = v___x_1907_;
v_isShared_1918_ = v_isSharedCheck_2007_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_snapshotTasks_1915_);
lean_inc(v_infoState_1914_);
lean_inc(v_messages_1913_);
lean_inc(v_traceState_1912_);
lean_inc(v_auxDeclNGen_1911_);
lean_inc(v_ngen_1910_);
lean_inc(v_nextMacroScope_1909_);
lean_inc(v_env_1908_);
lean_dec(v___x_1907_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_2007_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_inc(v___x_1896_);
v___x_1919_ = l_Lean_markAuxRecursor(v_env_1908_, v___x_1896_);
v___x_1920_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 5, v___x_1920_);
lean_ctor_set(v___x_1917_, 0, v___x_1919_);
v___x_1922_ = v___x_1917_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_nextMacroScope_1909_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_ngen_1910_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_auxDeclNGen_1911_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_traceState_1912_);
lean_ctor_set(v_reuseFailAlloc_2006_, 5, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_2006_, 6, v_messages_1913_);
lean_ctor_set(v_reuseFailAlloc_2006_, 7, v_infoState_1914_);
lean_ctor_set(v_reuseFailAlloc_2006_, 8, v_snapshotTasks_1915_);
v___x_1922_ = v_reuseFailAlloc_2006_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_mctx_1925_; lean_object* v_zetaDeltaFVarIds_1926_; lean_object* v_postponed_1927_; lean_object* v_diag_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_2004_; 
v___x_1923_ = lean_st_ref_put(v_a_1874_, v___x_1922_);
v___x_1924_ = lean_st_ref_take(v_a_1872_);
v_mctx_1925_ = lean_ctor_get(v___x_1924_, 0);
v_zetaDeltaFVarIds_1926_ = lean_ctor_get(v___x_1924_, 2);
v_postponed_1927_ = lean_ctor_get(v___x_1924_, 3);
v_diag_1928_ = lean_ctor_get(v___x_1924_, 4);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1924_, 1);
lean_dec(v_unused_2005_);
v___x_1930_ = v___x_1924_;
v_isShared_1931_ = v_isSharedCheck_2004_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_diag_1928_);
lean_inc(v_postponed_1927_);
lean_inc(v_zetaDeltaFVarIds_1926_);
lean_inc(v_mctx_1925_);
lean_dec(v___x_1924_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_2004_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_mctx_1925_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_zetaDeltaFVarIds_1926_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_postponed_1927_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_diag_1928_);
v___x_1934_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v_env_1937_; lean_object* v_nextMacroScope_1938_; lean_object* v_ngen_1939_; lean_object* v_auxDeclNGen_1940_; lean_object* v_traceState_1941_; lean_object* v_messages_1942_; lean_object* v_infoState_1943_; lean_object* v_snapshotTasks_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2001_; 
v___x_1935_ = lean_st_ref_put(v_a_1872_, v___x_1934_);
v___x_1936_ = lean_st_ref_take(v_a_1874_);
v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
v_nextMacroScope_1938_ = lean_ctor_get(v___x_1936_, 1);
v_ngen_1939_ = lean_ctor_get(v___x_1936_, 2);
v_auxDeclNGen_1940_ = lean_ctor_get(v___x_1936_, 3);
v_traceState_1941_ = lean_ctor_get(v___x_1936_, 4);
v_messages_1942_ = lean_ctor_get(v___x_1936_, 6);
v_infoState_1943_ = lean_ctor_get(v___x_1936_, 7);
v_snapshotTasks_1944_ = lean_ctor_get(v___x_1936_, 8);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v___x_1936_, 5);
lean_dec(v_unused_2002_);
v___x_1946_ = v___x_1936_;
v_isShared_1947_ = v_isSharedCheck_2001_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_snapshotTasks_1944_);
lean_inc(v_infoState_1943_);
lean_inc(v_messages_1942_);
lean_inc(v_traceState_1941_);
lean_inc(v_auxDeclNGen_1940_);
lean_inc(v_ngen_1939_);
lean_inc(v_nextMacroScope_1938_);
lean_inc(v_env_1937_);
lean_dec(v___x_1936_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2001_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
lean_inc(v___x_1896_);
v___x_1948_ = l_Lean_Meta_addToCompletionBlackList(v_env_1937_, v___x_1896_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 5, v___x_1920_);
lean_ctor_set(v___x_1946_, 0, v___x_1948_);
v___x_1950_ = v___x_1946_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_nextMacroScope_1938_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_ngen_1939_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_auxDeclNGen_1940_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_traceState_1941_);
lean_ctor_set(v_reuseFailAlloc_2000_, 5, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_2000_, 6, v_messages_1942_);
lean_ctor_set(v_reuseFailAlloc_2000_, 7, v_infoState_1943_);
lean_ctor_set(v_reuseFailAlloc_2000_, 8, v_snapshotTasks_1944_);
v___x_1950_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_mctx_1953_; lean_object* v_zetaDeltaFVarIds_1954_; lean_object* v_postponed_1955_; lean_object* v_diag_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1998_; 
v___x_1951_ = lean_st_ref_put(v_a_1874_, v___x_1950_);
v___x_1952_ = lean_st_ref_take(v_a_1872_);
v_mctx_1953_ = lean_ctor_get(v___x_1952_, 0);
v_zetaDeltaFVarIds_1954_ = lean_ctor_get(v___x_1952_, 2);
v_postponed_1955_ = lean_ctor_get(v___x_1952_, 3);
v_diag_1956_ = lean_ctor_get(v___x_1952_, 4);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v___x_1952_, 1);
lean_dec(v_unused_1999_);
v___x_1958_ = v___x_1952_;
v_isShared_1959_ = v_isSharedCheck_1998_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_diag_1956_);
lean_inc(v_postponed_1955_);
lean_inc(v_zetaDeltaFVarIds_1954_);
lean_inc(v_mctx_1953_);
lean_dec(v___x_1952_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1998_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v___x_1932_);
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_mctx_1953_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v_zetaDeltaFVarIds_1954_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v_postponed_1955_);
lean_ctor_set(v_reuseFailAlloc_1997_, 4, v_diag_1956_);
v___x_1961_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_env_1964_; lean_object* v_nextMacroScope_1965_; lean_object* v_ngen_1966_; lean_object* v_auxDeclNGen_1967_; lean_object* v_traceState_1968_; lean_object* v_messages_1969_; lean_object* v_infoState_1970_; lean_object* v_snapshotTasks_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1995_; 
v___x_1962_ = lean_st_ref_put(v_a_1872_, v___x_1961_);
v___x_1963_ = lean_st_ref_take(v_a_1874_);
v_env_1964_ = lean_ctor_get(v___x_1963_, 0);
v_nextMacroScope_1965_ = lean_ctor_get(v___x_1963_, 1);
v_ngen_1966_ = lean_ctor_get(v___x_1963_, 2);
v_auxDeclNGen_1967_ = lean_ctor_get(v___x_1963_, 3);
v_traceState_1968_ = lean_ctor_get(v___x_1963_, 4);
v_messages_1969_ = lean_ctor_get(v___x_1963_, 6);
v_infoState_1970_ = lean_ctor_get(v___x_1963_, 7);
v_snapshotTasks_1971_ = lean_ctor_get(v___x_1963_, 8);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1963_, 5);
lean_dec(v_unused_1996_);
v___x_1973_ = v___x_1963_;
v_isShared_1974_ = v_isSharedCheck_1995_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snapshotTasks_1971_);
lean_inc(v_infoState_1970_);
lean_inc(v_messages_1969_);
lean_inc(v_traceState_1968_);
lean_inc(v_auxDeclNGen_1967_);
lean_inc(v_ngen_1966_);
lean_inc(v_nextMacroScope_1965_);
lean_inc(v_env_1964_);
lean_dec(v___x_1963_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1995_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_inc(v___x_1896_);
v___x_1975_ = l_Lean_addProtected(v_env_1964_, v___x_1896_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 5, v___x_1920_);
lean_ctor_set(v___x_1973_, 0, v___x_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_nextMacroScope_1965_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_ngen_1966_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_auxDeclNGen_1967_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_traceState_1968_);
lean_ctor_set(v_reuseFailAlloc_1994_, 5, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1994_, 6, v_messages_1969_);
lean_ctor_set(v_reuseFailAlloc_1994_, 7, v_infoState_1970_);
lean_ctor_set(v_reuseFailAlloc_1994_, 8, v_snapshotTasks_1971_);
v___x_1977_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v_mctx_1980_; lean_object* v_zetaDeltaFVarIds_1981_; lean_object* v_postponed_1982_; lean_object* v_diag_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1992_; 
v___x_1978_ = lean_st_ref_put(v_a_1874_, v___x_1977_);
v___x_1979_ = lean_st_ref_take(v_a_1872_);
v_mctx_1980_ = lean_ctor_get(v___x_1979_, 0);
v_zetaDeltaFVarIds_1981_ = lean_ctor_get(v___x_1979_, 2);
v_postponed_1982_ = lean_ctor_get(v___x_1979_, 3);
v_diag_1983_ = lean_ctor_get(v___x_1979_, 4);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1979_, 1);
lean_dec(v_unused_1993_);
v___x_1985_ = v___x_1979_;
v_isShared_1986_ = v_isSharedCheck_1992_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_diag_1983_);
lean_inc(v_postponed_1982_);
lean_inc(v_zetaDeltaFVarIds_1981_);
lean_inc(v_mctx_1980_);
lean_dec(v___x_1979_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1992_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v___x_1932_);
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_mctx_1980_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_zetaDeltaFVarIds_1981_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_postponed_1982_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v_diag_1983_);
v___x_1988_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_st_ref_put(v_a_1872_, v___x_1988_);
v___x_1990_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_1896_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1990_;
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
lean_dec(v___x_1896_);
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_a_1893_);
lean_dec(v_levelParams_1884_);
lean_dec(v_indName_1870_);
v_a_2011_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1894_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1894_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_levelParams_1884_);
lean_dec(v_indName_1870_);
v_a_2019_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1892_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1892_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec(v___x_1887_);
lean_dec_ref(v_type_1885_);
lean_dec(v_levelParams_1884_);
lean_dec(v_name_1883_);
lean_dec(v___x_1879_);
lean_dec_ref(v_val_1878_);
lean_dec(v_indName_1870_);
v___x_2027_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2);
v___x_2028_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2027_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_2028_;
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v___x_1879_);
lean_dec_ref(v_val_1878_);
lean_dec(v_indName_1870_);
v_a_2029_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1881_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1881_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec(v_a_1877_);
lean_dec(v_indName_1870_);
v___x_2037_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3);
v___x_2038_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2037_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_2038_;
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_indName_1870_);
v_a_2039_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_1876_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_1876_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___boxed(lean_object* v_indName_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(lean_object* v___x_2054_, lean_object* v_k_2055_, lean_object* v_ctorIdx_2056_, lean_object* v_tail_2057_, lean_object* v___x_2058_, lean_object* v_as_2059_, size_t v_sz_2060_, size_t v_i_2061_, lean_object* v_bs_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_2054_, v_k_2055_, v_ctorIdx_2056_, v_tail_2057_, v___x_2058_, v_sz_2060_, v_i_2061_, v_bs_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___boxed(lean_object* v___x_2069_, lean_object* v_k_2070_, lean_object* v_ctorIdx_2071_, lean_object* v_tail_2072_, lean_object* v___x_2073_, lean_object* v_as_2074_, lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_bs_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(v___x_2069_, v_k_2070_, v_ctorIdx_2071_, v_tail_2072_, v___x_2073_, v_as_2074_, v_sz_boxed_2083_, v_i_boxed_2084_, v_bs_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec_ref(v_as_2074_);
lean_dec_ref(v___x_2073_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(lean_object* v___x_2086_, lean_object* v___x_2087_, lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v___x_2091_, lean_object* v___f_2092_, lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v___y_2095_, uint8_t v___x_2096_, lean_object* v_h_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; 
lean_inc_ref(v_h_2097_);
v___x_2103_ = l_Lean_Meta_mkEqSymm(v_h_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
lean_inc(v___x_2087_);
v___x_2105_ = l_Lean_mkConst(v___x_2086_, v___x_2087_);
v___x_2106_ = l_Lean_mkAppN(v___x_2105_, v___x_2088_);
lean_inc_ref_n(v___x_2089_, 2);
v___x_2107_ = l_Lean_Expr_app___override(v___x_2106_, v___x_2089_);
lean_inc_ref(v___x_2090_);
v___x_2108_ = l_Lean_Expr_app___override(v___x_2107_, v___x_2090_);
v___x_2109_ = l_Lean_mkConst(v___x_2091_, v___x_2087_);
lean_inc_ref(v___x_2088_);
v___x_2110_ = lean_array_push(v___x_2088_, v___x_2089_);
v___x_2111_ = lean_array_push(v___x_2110_, v___x_2090_);
v___x_2112_ = l_Lean_mkAppN(v___x_2109_, v___x_2111_);
lean_dec_ref(v___x_2111_);
v___x_2113_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v___x_2112_, v___f_2092_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l_Lean_mkAppN(v___x_2108_, v___x_2093_);
v___x_2116_ = l_Lean_Expr_app___override(v___x_2115_, v_a_2104_);
v___x_2117_ = l_Lean_Expr_app___override(v___x_2116_, v_a_2114_);
v___x_2118_ = lean_mk_empty_array_with_capacity(v___x_2094_);
v___x_2119_ = lean_array_push(v___x_2118_, v___x_2089_);
v___x_2120_ = l_Array_append___redArg(v___x_2088_, v___x_2119_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = l_Array_append___redArg(v___x_2120_, v___x_2093_);
v___x_2122_ = lean_unsigned_to_nat(2u);
v___x_2123_ = lean_mk_empty_array_with_capacity(v___x_2122_);
v___x_2124_ = lean_array_push(v___x_2123_, v_h_2097_);
v___x_2125_ = lean_array_push(v___x_2124_, v___y_2095_);
v___x_2126_ = l_Array_append___redArg(v___x_2121_, v___x_2125_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = 0;
v___x_2128_ = 1;
v___x_2129_ = l_Lean_Meta_mkLambdaFVars(v___x_2126_, v___x_2117_, v___x_2127_, v___x_2096_, v___x_2127_, v___x_2096_, v___x_2128_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec_ref(v___x_2126_);
return v___x_2129_;
}
else
{
lean_dec_ref(v___x_2108_);
lean_dec(v_a_2104_);
lean_dec_ref(v_h_2097_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
return v___x_2113_;
}
}
else
{
lean_dec_ref(v_h_2097_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v___f_2092_);
lean_dec(v___x_2091_);
lean_dec_ref(v___x_2090_);
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_2130_ = _args[0];
lean_object* v___x_2131_ = _args[1];
lean_object* v___x_2132_ = _args[2];
lean_object* v___x_2133_ = _args[3];
lean_object* v___x_2134_ = _args[4];
lean_object* v___x_2135_ = _args[5];
lean_object* v___f_2136_ = _args[6];
lean_object* v___x_2137_ = _args[7];
lean_object* v___x_2138_ = _args[8];
lean_object* v___y_2139_ = _args[9];
lean_object* v___x_2140_ = _args[10];
lean_object* v_h_2141_ = _args[11];
lean_object* v___y_2142_ = _args[12];
lean_object* v___y_2143_ = _args[13];
lean_object* v___y_2144_ = _args[14];
lean_object* v___y_2145_ = _args[15];
lean_object* v___y_2146_ = _args[16];
_start:
{
uint8_t v___x_9813__boxed_2147_; lean_object* v_res_2148_; 
v___x_9813__boxed_2147_ = lean_unbox(v___x_2140_);
v_res_2148_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2133_, v___x_2134_, v___x_2135_, v___f_2136_, v___x_2137_, v___x_2138_, v___y_2139_, v___x_9813__boxed_2147_, v_h_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___x_2138_);
lean_dec_ref(v___x_2137_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(lean_object* v___y_2149_, lean_object* v_x_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___y_2149_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2157_, lean_object* v_x_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(v___y_2157_, v_x_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_x_2158_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(lean_object* v_val_2165_, lean_object* v___x_2166_, lean_object* v___x_2167_, lean_object* v___x_2168_, lean_object* v_indName_2169_, lean_object* v_tail_2170_, lean_object* v_i_2171_, lean_object* v___x_2172_, lean_object* v___x_2173_, lean_object* v___x_2174_, uint8_t v___x_2175_, lean_object* v_xs_2176_, lean_object* v_x_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_numParams_2183_; lean_object* v_numIndices_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v_start_2194_; lean_object* v_stop_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___y_2200_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v_numParams_2183_ = lean_ctor_get(v_val_2165_, 1);
lean_inc_n(v_numParams_2183_, 2);
v_numIndices_2184_ = lean_ctor_get(v_val_2165_, 2);
lean_inc(v_numIndices_2184_);
lean_dec_ref(v_val_2165_);
lean_inc_ref_n(v_xs_2176_, 2);
v___x_2185_ = l_Array_toSubarray___redArg(v_xs_2176_, v___x_2166_, v_numParams_2183_);
v___x_2186_ = lean_array_get(v___x_2167_, v_xs_2176_, v_numParams_2183_);
v___x_2187_ = lean_nat_add(v_numParams_2183_, v___x_2168_);
lean_dec(v_numParams_2183_);
v___x_2188_ = lean_nat_add(v___x_2187_, v_numIndices_2184_);
lean_dec(v_numIndices_2184_);
lean_inc(v___x_2188_);
v___x_2189_ = l_Array_toSubarray___redArg(v_xs_2176_, v___x_2187_, v___x_2188_);
v___x_2190_ = lean_array_get(v___x_2167_, v_xs_2176_, v___x_2188_);
v___x_2191_ = lean_nat_add(v___x_2188_, v___x_2168_);
lean_dec(v___x_2188_);
v___x_2192_ = lean_array_get_size(v_xs_2176_);
v___x_2193_ = l_Array_toSubarray___redArg(v_xs_2176_, v___x_2191_, v___x_2192_);
v_start_2194_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_start_2194_);
v_stop_2195_ = lean_ctor_get(v___x_2193_, 2);
lean_inc(v_stop_2195_);
v___x_2196_ = l_Subarray_copy___redArg(v___x_2185_);
v___x_2197_ = l_Subarray_copy___redArg(v___x_2189_);
v___x_2198_ = lean_array_push(v___x_2197_, v___x_2190_);
v___x_2213_ = lean_nat_sub(v_stop_2195_, v_start_2194_);
lean_dec(v_start_2194_);
lean_dec(v_stop_2195_);
v___x_2214_ = lean_nat_dec_lt(v_i_2171_, v___x_2213_);
lean_dec(v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; 
lean_dec_ref(v___x_2193_);
v___x_2215_ = l_outOfBounds___redArg(v___x_2167_);
v___y_2200_ = v___x_2215_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Subarray_get___redArg(v___x_2193_, v_i_2171_);
lean_dec_ref(v___x_2193_);
v___y_2200_ = v___x_2216_;
goto v___jp_2199_;
}
v___jp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2201_ = l_Lean_mkCtorIdxName(v_indName_2169_);
v___x_2202_ = l_Lean_mkConst(v___x_2201_, v_tail_2170_);
lean_inc_ref(v___x_2196_);
v___x_2203_ = l_Array_append___redArg(v___x_2196_, v___x_2198_);
v___x_2204_ = l_Lean_mkAppN(v___x_2202_, v___x_2203_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = l_Lean_mkRawNatLit(v_i_2171_);
lean_inc_ref(v___x_2205_);
v___x_2206_ = l_Lean_Meta_mkEq(v___x_2204_, v___x_2205_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___f_2208_; lean_object* v___x_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___x_2206_, 1);
lean_inc_ref(v___y_2200_);
v___f_2208_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2208_, 0, v___y_2200_);
v___x_2209_ = lean_box(v___x_2175_);
v___f_2210_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed), 17, 11);
lean_closure_set(v___f_2210_, 0, v___x_2172_);
lean_closure_set(v___f_2210_, 1, v___x_2173_);
lean_closure_set(v___f_2210_, 2, v___x_2196_);
lean_closure_set(v___f_2210_, 3, v___x_2186_);
lean_closure_set(v___f_2210_, 4, v___x_2205_);
lean_closure_set(v___f_2210_, 5, v___x_2174_);
lean_closure_set(v___f_2210_, 6, v___f_2208_);
lean_closure_set(v___f_2210_, 7, v___x_2198_);
lean_closure_set(v___f_2210_, 8, v___x_2168_);
lean_closure_set(v___f_2210_, 9, v___y_2200_);
lean_closure_set(v___f_2210_, 10, v___x_2209_);
v___x_2211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_2212_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_2211_, v_a_2207_, v___f_2210_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
return v___x_2212_;
}
else
{
lean_dec_ref(v___x_2205_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v___x_2196_);
lean_dec(v___x_2186_);
lean_dec(v___x_2174_);
lean_dec(v___x_2173_);
lean_dec(v___x_2172_);
lean_dec(v___x_2168_);
return v___x_2206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_val_2217_ = _args[0];
lean_object* v___x_2218_ = _args[1];
lean_object* v___x_2219_ = _args[2];
lean_object* v___x_2220_ = _args[3];
lean_object* v_indName_2221_ = _args[4];
lean_object* v_tail_2222_ = _args[5];
lean_object* v_i_2223_ = _args[6];
lean_object* v___x_2224_ = _args[7];
lean_object* v___x_2225_ = _args[8];
lean_object* v___x_2226_ = _args[9];
lean_object* v___x_2227_ = _args[10];
lean_object* v_xs_2228_ = _args[11];
lean_object* v_x_2229_ = _args[12];
lean_object* v___y_2230_ = _args[13];
lean_object* v___y_2231_ = _args[14];
lean_object* v___y_2232_ = _args[15];
lean_object* v___y_2233_ = _args[16];
lean_object* v___y_2234_ = _args[17];
_start:
{
uint8_t v___x_9941__boxed_2235_; lean_object* v_res_2236_; 
v___x_9941__boxed_2235_ = lean_unbox(v___x_2227_);
v_res_2236_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(v_val_2217_, v___x_2218_, v___x_2219_, v___x_2220_, v_indName_2221_, v_tail_2222_, v_i_2223_, v___x_2224_, v___x_2225_, v___x_2226_, v___x_9941__boxed_2235_, v_xs_2228_, v_x_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v_x_2229_);
lean_dec_ref(v___x_2219_);
return v_res_2236_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0));
v___x_2239_ = l_Lean_stringToMessageData(v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(lean_object* v_attrName_2246_, lean_object* v_declName_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2253_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2254_ = l_Lean_MessageData_ofName(v_attrName_2246_);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = 0;
v___x_2259_ = l_Lean_MessageData_ofConstName(v_declName_2247_, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2257_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2262_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_2264_, lean_object* v_declName_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2264_, v_declName_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
return v_res_2271_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0));
v___x_2274_ = l_Lean_stringToMessageData(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(lean_object* v_attrName_2278_, lean_object* v_declName_2279_, lean_object* v_asyncPrefix_x3f_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___y_2287_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2280_) == 0)
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_MessageData_nil;
v___y_2287_ = v___x_2300_;
goto v___jp_2286_;
}
else
{
lean_object* v_val_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_val_2301_ = lean_ctor_get(v_asyncPrefix_x3f_2280_, 0);
lean_inc(v_val_2301_);
lean_dec_ref_known(v_asyncPrefix_x3f_2280_, 1);
v___x_2302_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3);
v___x_2303_ = l_Lean_MessageData_ofName(v_val_2301_);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___y_2287_ = v___x_2306_;
goto v___jp_2286_;
}
v___jp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2288_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2289_ = l_Lean_MessageData_ofName(v_attrName_2278_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = 0;
v___x_2294_ = l_Lean_MessageData_ofConstName(v_declName_2279_, v___x_2293_);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2292_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___y_2287_);
v___x_2299_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2298_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_2307_, lean_object* v_declName_2308_, lean_object* v_asyncPrefix_x3f_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2307_, v_declName_2308_, v_asyncPrefix_x3f_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(lean_object* v_attr_2316_, lean_object* v_decl_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___x_2366_; lean_object* v_env_2367_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___x_2382_; 
v___x_2366_ = lean_st_ref_get(v___y_2321_);
v_env_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc_ref(v_env_2367_);
lean_dec(v___x_2366_);
v___x_2382_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2367_, v_decl_2317_);
if (lean_obj_tag(v___x_2382_) == 0)
{
v___y_2369_ = v___y_2318_;
v___y_2370_ = v___y_2319_;
v___y_2371_ = v___y_2320_;
v___y_2372_ = v___y_2321_;
goto v___jp_2368_;
}
else
{
lean_object* v_attr_2383_; lean_object* v_toAttributeImplCore_2384_; lean_object* v_name_2385_; lean_object* v___x_2386_; 
lean_dec_ref_known(v___x_2382_, 1);
lean_dec_ref(v_env_2367_);
v_attr_2383_ = lean_ctor_get(v_attr_2316_, 0);
lean_inc_ref(v_attr_2383_);
lean_dec_ref(v_attr_2316_);
v_toAttributeImplCore_2384_ = lean_ctor_get(v_attr_2383_, 0);
lean_inc_ref(v_toAttributeImplCore_2384_);
lean_dec_ref(v_attr_2383_);
v_name_2385_ = lean_ctor_get(v_toAttributeImplCore_2384_, 1);
lean_inc(v_name_2385_);
lean_dec_ref(v_toAttributeImplCore_2384_);
v___x_2386_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_name_2385_, v_decl_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2386_;
}
v___jp_2323_:
{
lean_object* v___x_2326_; lean_object* v_ext_2327_; lean_object* v_toEnvExtension_2328_; lean_object* v_env_2329_; lean_object* v_nextMacroScope_2330_; lean_object* v_ngen_2331_; lean_object* v_auxDeclNGen_2332_; lean_object* v_traceState_2333_; lean_object* v_messages_2334_; lean_object* v_infoState_2335_; lean_object* v_snapshotTasks_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2364_; 
v___x_2326_ = lean_st_ref_take(v___y_2325_);
v_ext_2327_ = lean_ctor_get(v_attr_2316_, 1);
lean_inc_ref(v_ext_2327_);
lean_dec_ref(v_attr_2316_);
v_toEnvExtension_2328_ = lean_ctor_get(v_ext_2327_, 0);
v_env_2329_ = lean_ctor_get(v___x_2326_, 0);
v_nextMacroScope_2330_ = lean_ctor_get(v___x_2326_, 1);
v_ngen_2331_ = lean_ctor_get(v___x_2326_, 2);
v_auxDeclNGen_2332_ = lean_ctor_get(v___x_2326_, 3);
v_traceState_2333_ = lean_ctor_get(v___x_2326_, 4);
v_messages_2334_ = lean_ctor_get(v___x_2326_, 6);
v_infoState_2335_ = lean_ctor_get(v___x_2326_, 7);
v_snapshotTasks_2336_ = lean_ctor_get(v___x_2326_, 8);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v___x_2326_, 5);
lean_dec(v_unused_2365_);
v___x_2338_ = v___x_2326_;
v_isShared_2339_ = v_isSharedCheck_2364_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_snapshotTasks_2336_);
lean_inc(v_infoState_2335_);
lean_inc(v_messages_2334_);
lean_inc(v_traceState_2333_);
lean_inc(v_auxDeclNGen_2332_);
lean_inc(v_ngen_2331_);
lean_inc(v_nextMacroScope_2330_);
lean_inc(v_env_2329_);
lean_dec(v___x_2326_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2364_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_asyncMode_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v_asyncMode_2340_ = lean_ctor_get(v_toEnvExtension_2328_, 2);
lean_inc(v_asyncMode_2340_);
lean_inc(v_decl_2317_);
v___x_2341_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2327_, v_env_2329_, v_decl_2317_, v_asyncMode_2340_, v_decl_2317_);
lean_dec(v_asyncMode_2340_);
v___x_2342_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 5, v___x_2342_);
lean_ctor_set(v___x_2338_, 0, v___x_2341_);
v___x_2344_ = v___x_2338_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_nextMacroScope_2330_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_ngen_2331_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v_auxDeclNGen_2332_);
lean_ctor_set(v_reuseFailAlloc_2363_, 4, v_traceState_2333_);
lean_ctor_set(v_reuseFailAlloc_2363_, 5, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2363_, 6, v_messages_2334_);
lean_ctor_set(v_reuseFailAlloc_2363_, 7, v_infoState_2335_);
lean_ctor_set(v_reuseFailAlloc_2363_, 8, v_snapshotTasks_2336_);
v___x_2344_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v_mctx_2347_; lean_object* v_zetaDeltaFVarIds_2348_; lean_object* v_postponed_2349_; lean_object* v_diag_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2361_; 
v___x_2345_ = lean_st_ref_put(v___y_2325_, v___x_2344_);
v___x_2346_ = lean_st_ref_take(v___y_2324_);
v_mctx_2347_ = lean_ctor_get(v___x_2346_, 0);
v_zetaDeltaFVarIds_2348_ = lean_ctor_get(v___x_2346_, 2);
v_postponed_2349_ = lean_ctor_get(v___x_2346_, 3);
v_diag_2350_ = lean_ctor_get(v___x_2346_, 4);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v___x_2346_, 1);
lean_dec(v_unused_2362_);
v___x_2352_ = v___x_2346_;
v_isShared_2353_ = v_isSharedCheck_2361_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_diag_2350_);
lean_inc(v_postponed_2349_);
lean_inc(v_zetaDeltaFVarIds_2348_);
lean_inc(v_mctx_2347_);
lean_dec(v___x_2346_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2361_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 1, v___x_2354_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_mctx_2347_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_zetaDeltaFVarIds_2348_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_postponed_2349_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_diag_2350_);
v___x_2356_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_st_ref_put(v___y_2324_, v___x_2356_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
}
}
}
v___jp_2368_:
{
lean_object* v_ext_2373_; lean_object* v_toEnvExtension_2374_; lean_object* v_attr_2375_; lean_object* v_asyncMode_2376_; uint8_t v___x_2377_; 
v_ext_2373_ = lean_ctor_get(v_attr_2316_, 1);
v_toEnvExtension_2374_ = lean_ctor_get(v_ext_2373_, 0);
v_attr_2375_ = lean_ctor_get(v_attr_2316_, 0);
v_asyncMode_2376_ = lean_ctor_get(v_toEnvExtension_2374_, 2);
lean_inc(v_decl_2317_);
lean_inc_ref(v_env_2367_);
v___x_2377_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2367_, v_decl_2317_, v_asyncMode_2376_);
if (v___x_2377_ == 0)
{
lean_object* v_toAttributeImplCore_2378_; lean_object* v_name_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_inc_ref(v_attr_2375_);
lean_dec_ref(v_attr_2316_);
v_toAttributeImplCore_2378_ = lean_ctor_get(v_attr_2375_, 0);
lean_inc_ref(v_toAttributeImplCore_2378_);
lean_dec_ref(v_attr_2375_);
v_name_2379_ = lean_ctor_get(v_toAttributeImplCore_2378_, 1);
lean_inc(v_name_2379_);
lean_dec_ref(v_toAttributeImplCore_2378_);
v___x_2380_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2367_);
v___x_2381_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_name_2379_, v_decl_2317_, v___x_2380_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2381_;
}
else
{
lean_dec_ref(v_env_2367_);
v___y_2324_ = v___y_2370_;
v___y_2325_ = v___y_2372_;
goto v___jp_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___boxed(lean_object* v_attr_2387_, lean_object* v_decl_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v_attr_2387_, v_decl_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(lean_object* v_val_2395_, lean_object* v_indName_2396_, lean_object* v_tail_2397_, lean_object* v___x_2398_, lean_object* v___x_2399_, lean_object* v___x_2400_, lean_object* v_a_2401_, lean_object* v_range_2402_, lean_object* v_b_2403_, lean_object* v_i_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_stop_2410_; lean_object* v_step_2411_; uint8_t v___x_2412_; 
v_stop_2410_ = lean_ctor_get(v_range_2402_, 1);
v_step_2411_ = lean_ctor_get(v_range_2402_, 2);
v___x_2412_ = lean_nat_dec_lt(v_i_2404_, v_stop_2410_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec(v_i_2404_);
lean_dec_ref(v_a_2401_);
lean_dec(v___x_2400_);
lean_dec(v___x_2399_);
lean_dec(v___x_2398_);
lean_dec(v_tail_2397_);
lean_dec(v_indName_2396_);
lean_dec_ref(v_val_2395_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_b_2403_);
return v___x_2413_;
}
else
{
lean_object* v_levelParams_2414_; lean_object* v_type_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___f_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; 
v_levelParams_2414_ = lean_ctor_get(v_a_2401_, 1);
v_type_2415_ = lean_ctor_get(v_a_2401_, 2);
v___x_2416_ = lean_unsigned_to_nat(0u);
v___x_2417_ = l_Lean_instInhabitedExpr;
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_box(v___x_2412_);
lean_inc(v___x_2400_);
lean_inc(v___x_2399_);
lean_inc(v___x_2398_);
lean_inc(v_i_2404_);
lean_inc(v_tail_2397_);
lean_inc(v_indName_2396_);
lean_inc_ref(v_val_2395_);
v___f_2420_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed), 18, 11);
lean_closure_set(v___f_2420_, 0, v_val_2395_);
lean_closure_set(v___f_2420_, 1, v___x_2416_);
lean_closure_set(v___f_2420_, 2, v___x_2417_);
lean_closure_set(v___f_2420_, 3, v___x_2418_);
lean_closure_set(v___f_2420_, 4, v_indName_2396_);
lean_closure_set(v___f_2420_, 5, v_tail_2397_);
lean_closure_set(v___f_2420_, 6, v_i_2404_);
lean_closure_set(v___f_2420_, 7, v___x_2398_);
lean_closure_set(v___f_2420_, 8, v___x_2399_);
lean_closure_set(v___f_2420_, 9, v___x_2400_);
lean_closure_set(v___f_2420_, 10, v___x_2419_);
v___x_2421_ = 0;
lean_inc_ref(v_type_2415_);
v___x_2422_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_2415_, v___f_2420_, v___x_2421_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc_n(v_a_2423_, 2);
lean_dec_ref_known(v___x_2422_, 1);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
v___x_2424_ = lean_infer_type(v_a_2423_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v_ctors_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2580_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v_ctors_2426_ = lean_ctor_get(v_val_2395_, 4);
v___x_2427_ = lean_box(0);
lean_inc(v_i_2404_);
v___x_2428_ = l_List_get_x21Internal___redArg(v___x_2427_, v_ctors_2426_, v_i_2404_);
v___x_2429_ = l_Lean_mkConstructorElimName(v_indName_2396_, v___x_2428_);
v___x_2430_ = lean_box(1);
lean_inc(v_levelParams_2414_);
lean_inc(v___x_2429_);
v___x_2431_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_2429_, v_levelParams_2414_, v_a_2425_, v_a_2423_, v___x_2430_, v___y_2408_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2580_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2580_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 1);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_addAndCompile(v___x_2437_, v___x_2412_, v___x_2421_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v___x_2439_; lean_object* v_env_2440_; lean_object* v_nextMacroScope_2441_; lean_object* v_ngen_2442_; lean_object* v_auxDeclNGen_2443_; lean_object* v_traceState_2444_; lean_object* v_messages_2445_; lean_object* v_infoState_2446_; lean_object* v_snapshotTasks_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref_known(v___x_2438_, 1);
v___x_2439_ = lean_st_ref_take(v___y_2408_);
v_env_2440_ = lean_ctor_get(v___x_2439_, 0);
v_nextMacroScope_2441_ = lean_ctor_get(v___x_2439_, 1);
v_ngen_2442_ = lean_ctor_get(v___x_2439_, 2);
v_auxDeclNGen_2443_ = lean_ctor_get(v___x_2439_, 3);
v_traceState_2444_ = lean_ctor_get(v___x_2439_, 4);
v_messages_2445_ = lean_ctor_get(v___x_2439_, 6);
v_infoState_2446_ = lean_ctor_get(v___x_2439_, 7);
v_snapshotTasks_2447_ = lean_ctor_get(v___x_2439_, 8);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2439_, 5);
lean_dec(v_unused_2578_);
v___x_2449_ = v___x_2439_;
v_isShared_2450_ = v_isSharedCheck_2577_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_snapshotTasks_2447_);
lean_inc(v_infoState_2446_);
lean_inc(v_messages_2445_);
lean_inc(v_traceState_2444_);
lean_inc(v_auxDeclNGen_2443_);
lean_inc(v_ngen_2442_);
lean_inc(v_nextMacroScope_2441_);
lean_inc(v_env_2440_);
lean_dec(v___x_2439_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2577_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
lean_inc(v___x_2429_);
v___x_2451_ = l_Lean_markAuxRecursor(v_env_2440_, v___x_2429_);
v___x_2452_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 5, v___x_2452_);
lean_ctor_set(v___x_2449_, 0, v___x_2451_);
v___x_2454_ = v___x_2449_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_nextMacroScope_2441_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v_ngen_2442_);
lean_ctor_set(v_reuseFailAlloc_2576_, 3, v_auxDeclNGen_2443_);
lean_ctor_set(v_reuseFailAlloc_2576_, 4, v_traceState_2444_);
lean_ctor_set(v_reuseFailAlloc_2576_, 5, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2576_, 6, v_messages_2445_);
lean_ctor_set(v_reuseFailAlloc_2576_, 7, v_infoState_2446_);
lean_ctor_set(v_reuseFailAlloc_2576_, 8, v_snapshotTasks_2447_);
v___x_2454_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v_mctx_2457_; lean_object* v_zetaDeltaFVarIds_2458_; lean_object* v_postponed_2459_; lean_object* v_diag_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2574_; 
v___x_2455_ = lean_st_ref_put(v___y_2408_, v___x_2454_);
v___x_2456_ = lean_st_ref_take(v___y_2406_);
v_mctx_2457_ = lean_ctor_get(v___x_2456_, 0);
v_zetaDeltaFVarIds_2458_ = lean_ctor_get(v___x_2456_, 2);
v_postponed_2459_ = lean_ctor_get(v___x_2456_, 3);
v_diag_2460_ = lean_ctor_get(v___x_2456_, 4);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; 
v_unused_2575_ = lean_ctor_get(v___x_2456_, 1);
lean_dec(v_unused_2575_);
v___x_2462_ = v___x_2456_;
v_isShared_2463_ = v_isSharedCheck_2574_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_diag_2460_);
lean_inc(v_postponed_2459_);
lean_inc(v_zetaDeltaFVarIds_2458_);
lean_inc(v_mctx_2457_);
lean_dec(v___x_2456_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2574_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_mctx_2457_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_zetaDeltaFVarIds_2458_);
lean_ctor_set(v_reuseFailAlloc_2573_, 3, v_postponed_2459_);
lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_diag_2460_);
v___x_2466_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_env_2469_; lean_object* v_nextMacroScope_2470_; lean_object* v_ngen_2471_; lean_object* v_auxDeclNGen_2472_; lean_object* v_traceState_2473_; lean_object* v_messages_2474_; lean_object* v_infoState_2475_; lean_object* v_snapshotTasks_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2571_; 
v___x_2467_ = lean_st_ref_put(v___y_2406_, v___x_2466_);
v___x_2468_ = lean_st_ref_take(v___y_2408_);
v_env_2469_ = lean_ctor_get(v___x_2468_, 0);
v_nextMacroScope_2470_ = lean_ctor_get(v___x_2468_, 1);
v_ngen_2471_ = lean_ctor_get(v___x_2468_, 2);
v_auxDeclNGen_2472_ = lean_ctor_get(v___x_2468_, 3);
v_traceState_2473_ = lean_ctor_get(v___x_2468_, 4);
v_messages_2474_ = lean_ctor_get(v___x_2468_, 6);
v_infoState_2475_ = lean_ctor_get(v___x_2468_, 7);
v_snapshotTasks_2476_ = lean_ctor_get(v___x_2468_, 8);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; 
v_unused_2572_ = lean_ctor_get(v___x_2468_, 5);
lean_dec(v_unused_2572_);
v___x_2478_ = v___x_2468_;
v_isShared_2479_ = v_isSharedCheck_2571_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_snapshotTasks_2476_);
lean_inc(v_infoState_2475_);
lean_inc(v_messages_2474_);
lean_inc(v_traceState_2473_);
lean_inc(v_auxDeclNGen_2472_);
lean_inc(v_ngen_2471_);
lean_inc(v_nextMacroScope_2470_);
lean_inc(v_env_2469_);
lean_dec(v___x_2468_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2571_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_inc(v___x_2429_);
v___x_2480_ = l_Lean_markSparseCasesOn(v_env_2469_, v___x_2429_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 5, v___x_2452_);
lean_ctor_set(v___x_2478_, 0, v___x_2480_);
v___x_2482_ = v___x_2478_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_nextMacroScope_2470_);
lean_ctor_set(v_reuseFailAlloc_2570_, 2, v_ngen_2471_);
lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_auxDeclNGen_2472_);
lean_ctor_set(v_reuseFailAlloc_2570_, 4, v_traceState_2473_);
lean_ctor_set(v_reuseFailAlloc_2570_, 5, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2570_, 6, v_messages_2474_);
lean_ctor_set(v_reuseFailAlloc_2570_, 7, v_infoState_2475_);
lean_ctor_set(v_reuseFailAlloc_2570_, 8, v_snapshotTasks_2476_);
v___x_2482_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_mctx_2485_; lean_object* v_zetaDeltaFVarIds_2486_; lean_object* v_postponed_2487_; lean_object* v_diag_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2568_; 
v___x_2483_ = lean_st_ref_put(v___y_2408_, v___x_2482_);
v___x_2484_ = lean_st_ref_take(v___y_2406_);
v_mctx_2485_ = lean_ctor_get(v___x_2484_, 0);
v_zetaDeltaFVarIds_2486_ = lean_ctor_get(v___x_2484_, 2);
v_postponed_2487_ = lean_ctor_get(v___x_2484_, 3);
v_diag_2488_ = lean_ctor_get(v___x_2484_, 4);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v___x_2484_, 1);
lean_dec(v_unused_2569_);
v___x_2490_ = v___x_2484_;
v_isShared_2491_ = v_isSharedCheck_2568_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_diag_2488_);
lean_inc(v_postponed_2487_);
lean_inc(v_zetaDeltaFVarIds_2486_);
lean_inc(v_mctx_2485_);
lean_dec(v___x_2484_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2568_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 1, v___x_2464_);
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_mctx_2485_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_zetaDeltaFVarIds_2486_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v_postponed_2487_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_diag_2488_);
v___x_2493_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_env_2496_; lean_object* v_nextMacroScope_2497_; lean_object* v_ngen_2498_; lean_object* v_auxDeclNGen_2499_; lean_object* v_traceState_2500_; lean_object* v_messages_2501_; lean_object* v_infoState_2502_; lean_object* v_snapshotTasks_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2565_; 
v___x_2494_ = lean_st_ref_put(v___y_2406_, v___x_2493_);
v___x_2495_ = lean_st_ref_take(v___y_2408_);
v_env_2496_ = lean_ctor_get(v___x_2495_, 0);
v_nextMacroScope_2497_ = lean_ctor_get(v___x_2495_, 1);
v_ngen_2498_ = lean_ctor_get(v___x_2495_, 2);
v_auxDeclNGen_2499_ = lean_ctor_get(v___x_2495_, 3);
v_traceState_2500_ = lean_ctor_get(v___x_2495_, 4);
v_messages_2501_ = lean_ctor_get(v___x_2495_, 6);
v_infoState_2502_ = lean_ctor_get(v___x_2495_, 7);
v_snapshotTasks_2503_ = lean_ctor_get(v___x_2495_, 8);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2495_, 5);
lean_dec(v_unused_2566_);
v___x_2505_ = v___x_2495_;
v_isShared_2506_ = v_isSharedCheck_2565_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_snapshotTasks_2503_);
lean_inc(v_infoState_2502_);
lean_inc(v_messages_2501_);
lean_inc(v_traceState_2500_);
lean_inc(v_auxDeclNGen_2499_);
lean_inc(v_ngen_2498_);
lean_inc(v_nextMacroScope_2497_);
lean_inc(v_env_2496_);
lean_dec(v___x_2495_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2565_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
lean_inc(v___x_2429_);
v___x_2507_ = l_Lean_Meta_addToCompletionBlackList(v_env_2496_, v___x_2429_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 5, v___x_2452_);
lean_ctor_set(v___x_2505_, 0, v___x_2507_);
v___x_2509_ = v___x_2505_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_nextMacroScope_2497_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_ngen_2498_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_auxDeclNGen_2499_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v_traceState_2500_);
lean_ctor_set(v_reuseFailAlloc_2564_, 5, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2564_, 6, v_messages_2501_);
lean_ctor_set(v_reuseFailAlloc_2564_, 7, v_infoState_2502_);
lean_ctor_set(v_reuseFailAlloc_2564_, 8, v_snapshotTasks_2503_);
v___x_2509_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v_mctx_2512_; lean_object* v_zetaDeltaFVarIds_2513_; lean_object* v_postponed_2514_; lean_object* v_diag_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2562_; 
v___x_2510_ = lean_st_ref_put(v___y_2408_, v___x_2509_);
v___x_2511_ = lean_st_ref_take(v___y_2406_);
v_mctx_2512_ = lean_ctor_get(v___x_2511_, 0);
v_zetaDeltaFVarIds_2513_ = lean_ctor_get(v___x_2511_, 2);
v_postponed_2514_ = lean_ctor_get(v___x_2511_, 3);
v_diag_2515_ = lean_ctor_get(v___x_2511_, 4);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2511_, 1);
lean_dec(v_unused_2563_);
v___x_2517_ = v___x_2511_;
v_isShared_2518_ = v_isSharedCheck_2562_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_diag_2515_);
lean_inc(v_postponed_2514_);
lean_inc(v_zetaDeltaFVarIds_2513_);
lean_inc(v_mctx_2512_);
lean_dec(v___x_2511_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2562_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 1, v___x_2464_);
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_mctx_2512_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_zetaDeltaFVarIds_2513_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_postponed_2514_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_diag_2515_);
v___x_2520_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_env_2523_; lean_object* v_nextMacroScope_2524_; lean_object* v_ngen_2525_; lean_object* v_auxDeclNGen_2526_; lean_object* v_traceState_2527_; lean_object* v_messages_2528_; lean_object* v_infoState_2529_; lean_object* v_snapshotTasks_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2559_; 
v___x_2521_ = lean_st_ref_put(v___y_2406_, v___x_2520_);
v___x_2522_ = lean_st_ref_take(v___y_2408_);
v_env_2523_ = lean_ctor_get(v___x_2522_, 0);
v_nextMacroScope_2524_ = lean_ctor_get(v___x_2522_, 1);
v_ngen_2525_ = lean_ctor_get(v___x_2522_, 2);
v_auxDeclNGen_2526_ = lean_ctor_get(v___x_2522_, 3);
v_traceState_2527_ = lean_ctor_get(v___x_2522_, 4);
v_messages_2528_ = lean_ctor_get(v___x_2522_, 6);
v_infoState_2529_ = lean_ctor_get(v___x_2522_, 7);
v_snapshotTasks_2530_ = lean_ctor_get(v___x_2522_, 8);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2522_, 5);
lean_dec(v_unused_2560_);
v___x_2532_ = v___x_2522_;
v_isShared_2533_ = v_isSharedCheck_2559_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_snapshotTasks_2530_);
lean_inc(v_infoState_2529_);
lean_inc(v_messages_2528_);
lean_inc(v_traceState_2527_);
lean_inc(v_auxDeclNGen_2526_);
lean_inc(v_ngen_2525_);
lean_inc(v_nextMacroScope_2524_);
lean_inc(v_env_2523_);
lean_dec(v___x_2522_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2559_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_inc(v___x_2429_);
v___x_2534_ = l_Lean_addProtected(v_env_2523_, v___x_2429_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 5, v___x_2452_);
lean_ctor_set(v___x_2532_, 0, v___x_2534_);
v___x_2536_ = v___x_2532_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_nextMacroScope_2524_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_ngen_2525_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_auxDeclNGen_2526_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_traceState_2527_);
lean_ctor_set(v_reuseFailAlloc_2558_, 5, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2558_, 6, v_messages_2528_);
lean_ctor_set(v_reuseFailAlloc_2558_, 7, v_infoState_2529_);
lean_ctor_set(v_reuseFailAlloc_2558_, 8, v_snapshotTasks_2530_);
v___x_2536_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_mctx_2539_; lean_object* v_zetaDeltaFVarIds_2540_; lean_object* v_postponed_2541_; lean_object* v_diag_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2556_; 
v___x_2537_ = lean_st_ref_put(v___y_2408_, v___x_2536_);
v___x_2538_ = lean_st_ref_take(v___y_2406_);
v_mctx_2539_ = lean_ctor_get(v___x_2538_, 0);
v_zetaDeltaFVarIds_2540_ = lean_ctor_get(v___x_2538_, 2);
v_postponed_2541_ = lean_ctor_get(v___x_2538_, 3);
v_diag_2542_ = lean_ctor_get(v___x_2538_, 4);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; 
v_unused_2557_ = lean_ctor_get(v___x_2538_, 1);
lean_dec(v_unused_2557_);
v___x_2544_ = v___x_2538_;
v_isShared_2545_ = v_isSharedCheck_2556_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_diag_2542_);
lean_inc(v_postponed_2541_);
lean_inc(v_zetaDeltaFVarIds_2540_);
lean_inc(v_mctx_2539_);
lean_dec(v___x_2538_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2556_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 1, v___x_2464_);
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_mctx_2539_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_zetaDeltaFVarIds_2540_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_postponed_2541_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_diag_2542_);
v___x_2547_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_st_ref_put(v___y_2406_, v___x_2547_);
v___x_2549_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v___x_2429_);
v___x_2550_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v___x_2549_, v___x_2429_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec_ref_known(v___x_2550_, 1);
v___x_2551_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_2429_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref(v___x_2551_);
v___x_2552_ = lean_box(0);
v___x_2553_ = lean_nat_add(v_i_2404_, v_step_2411_);
lean_dec(v_i_2404_);
v_b_2403_ = v___x_2552_;
v_i_2404_ = v___x_2553_;
goto _start;
}
else
{
lean_dec(v___x_2429_);
lean_dec(v_i_2404_);
lean_dec_ref(v_a_2401_);
lean_dec(v___x_2400_);
lean_dec(v___x_2399_);
lean_dec(v___x_2398_);
lean_dec(v_tail_2397_);
lean_dec(v_indName_2396_);
lean_dec_ref(v_val_2395_);
return v___x_2550_;
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
lean_dec(v___x_2429_);
lean_dec(v_i_2404_);
lean_dec_ref(v_a_2401_);
lean_dec(v___x_2400_);
lean_dec(v___x_2399_);
lean_dec(v___x_2398_);
lean_dec(v_tail_2397_);
lean_dec(v_indName_2396_);
lean_dec_ref(v_val_2395_);
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2423_);
lean_dec(v_i_2404_);
lean_dec_ref(v_a_2401_);
lean_dec(v___x_2400_);
lean_dec(v___x_2399_);
lean_dec(v___x_2398_);
lean_dec(v_tail_2397_);
lean_dec(v_indName_2396_);
lean_dec_ref(v_val_2395_);
v_a_2581_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2424_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2424_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v_i_2404_);
lean_dec_ref(v_a_2401_);
lean_dec(v___x_2400_);
lean_dec(v___x_2399_);
lean_dec(v___x_2398_);
lean_dec(v_tail_2397_);
lean_dec(v_indName_2396_);
lean_dec_ref(v_val_2395_);
v_a_2589_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2422_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2422_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___boxed(lean_object* v_val_2597_, lean_object* v_indName_2598_, lean_object* v_tail_2599_, lean_object* v___x_2600_, lean_object* v___x_2601_, lean_object* v___x_2602_, lean_object* v_a_2603_, lean_object* v_range_2604_, lean_object* v_b_2605_, lean_object* v_i_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2597_, v_indName_2598_, v_tail_2599_, v___x_2600_, v___x_2601_, v___x_2602_, v_a_2603_, v_range_2604_, v_b_2605_, v_i_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v_range_2604_);
return v_res_2612_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_2615_ = lean_unsigned_to_nat(58u);
v___x_2616_ = lean_unsigned_to_nat(169u);
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2618_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2619_ = l_mkPanicMessageWithDecl(v___x_2618_, v___x_2617_, v___x_2616_, v___x_2615_, v___x_2614_);
return v___x_2619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2620_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_2621_ = lean_unsigned_to_nat(60u);
v___x_2622_ = lean_unsigned_to_nat(166u);
v___x_2623_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2624_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2625_ = l_mkPanicMessageWithDecl(v___x_2624_, v___x_2623_, v___x_2622_, v___x_2621_, v___x_2620_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(lean_object* v_indName_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v___x_2632_; 
lean_inc(v_indName_2626_);
v___x_2632_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
if (lean_obj_tag(v_a_2633_) == 5)
{
lean_object* v_val_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_val_2634_ = lean_ctor_get(v_a_2633_, 0);
lean_inc_ref(v_val_2634_);
lean_dec_ref_known(v_a_2633_, 1);
lean_inc(v_indName_2626_);
v___x_2635_ = l_Lean_mkCasesOnName(v_indName_2626_);
lean_inc(v___x_2635_);
v___x_2636_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2635_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v_levelParams_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2675_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v_levelParams_2638_ = lean_ctor_get(v_a_2637_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; lean_object* v_unused_2677_; 
v_unused_2676_ = lean_ctor_get(v_a_2637_, 2);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_a_2637_, 0);
lean_dec(v_unused_2677_);
v___x_2640_ = v_a_2637_;
v_isShared_2641_ = v_isSharedCheck_2675_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_levelParams_2638_);
lean_dec(v_a_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2675_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_box(0);
v___x_2643_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_2638_, v___x_2642_);
if (lean_obj_tag(v___x_2643_) == 1)
{
lean_object* v_tail_2644_; lean_object* v___x_2645_; 
v_tail_2644_ = lean_ctor_get(v___x_2643_, 1);
lean_inc(v_tail_2644_);
v___x_2645_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2635_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
lean_inc_n(v_indName_2626_, 2);
v___x_2647_ = l_Lean_mkCtorElimName(v_indName_2626_);
v___x_2648_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_2626_);
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = l_Lean_InductiveVal_numCtors(v_val_2634_);
v___x_2651_ = lean_unsigned_to_nat(1u);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 2, v___x_2651_);
lean_ctor_set(v___x_2640_, 1, v___x_2650_);
lean_ctor_set(v___x_2640_, 0, v___x_2649_);
v___x_2653_ = v___x_2640_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_box(0);
v___x_2655_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2634_, v_indName_2626_, v_tail_2644_, v___x_2647_, v___x_2643_, v___x_2648_, v_a_2646_, v___x_2653_, v___x_2654_, v___x_2649_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec_ref(v___x_2653_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v___x_2655_, 0);
lean_dec(v_unused_2663_);
v___x_2657_ = v___x_2655_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_dec(v___x_2655_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2654_);
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2654_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
else
{
return v___x_2655_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_tail_2644_);
lean_dec_ref_known(v___x_2643_, 2);
lean_del_object(v___x_2640_);
lean_dec_ref(v_val_2634_);
lean_dec(v_indName_2626_);
v_a_2665_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2645_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2645_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec(v___x_2643_);
lean_del_object(v___x_2640_);
lean_dec(v___x_2635_);
lean_dec_ref(v_val_2634_);
lean_dec(v_indName_2626_);
v___x_2673_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1);
v___x_2674_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2673_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
return v___x_2674_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v___x_2635_);
lean_dec_ref(v_val_2634_);
lean_dec(v_indName_2626_);
v_a_2678_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2636_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2636_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec(v_a_2633_);
lean_dec(v_indName_2626_);
v___x_2686_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2);
v___x_2687_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2686_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
return v___x_2687_;
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_indName_2626_);
v_a_2688_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2632_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2632_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___boxed(lean_object* v_indName_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(lean_object* v_val_2703_, lean_object* v_indName_2704_, lean_object* v_tail_2705_, lean_object* v___x_2706_, lean_object* v___x_2707_, lean_object* v___x_2708_, lean_object* v_a_2709_, lean_object* v_range_2710_, lean_object* v_b_2711_, lean_object* v_i_2712_, lean_object* v_hs_2713_, lean_object* v_hl_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2703_, v_indName_2704_, v_tail_2705_, v___x_2706_, v___x_2707_, v___x_2708_, v_a_2709_, v_range_2710_, v_b_2711_, v_i_2712_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___boxed(lean_object** _args){
lean_object* v_val_2721_ = _args[0];
lean_object* v_indName_2722_ = _args[1];
lean_object* v_tail_2723_ = _args[2];
lean_object* v___x_2724_ = _args[3];
lean_object* v___x_2725_ = _args[4];
lean_object* v___x_2726_ = _args[5];
lean_object* v_a_2727_ = _args[6];
lean_object* v_range_2728_ = _args[7];
lean_object* v_b_2729_ = _args[8];
lean_object* v_i_2730_ = _args[9];
lean_object* v_hs_2731_ = _args[10];
lean_object* v_hl_2732_ = _args[11];
lean_object* v___y_2733_ = _args[12];
lean_object* v___y_2734_ = _args[13];
lean_object* v___y_2735_ = _args[14];
lean_object* v___y_2736_ = _args[15];
lean_object* v___y_2737_ = _args[16];
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(v_val_2721_, v_indName_2722_, v_tail_2723_, v___x_2724_, v___x_2725_, v___x_2726_, v_a_2727_, v_range_2728_, v_b_2729_, v_i_2730_, v_hs_2731_, v_hl_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v_range_2728_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(lean_object* v_00_u03b1_2739_, lean_object* v_attrName_2740_, lean_object* v_declName_2741_, lean_object* v_asyncPrefix_x3f_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2740_, v_declName_2741_, v_asyncPrefix_x3f_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2749_, lean_object* v_attrName_2750_, lean_object* v_declName_2751_, lean_object* v_asyncPrefix_x3f_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(v_00_u03b1_2749_, v_attrName_2750_, v_declName_2751_, v_asyncPrefix_x3f_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(lean_object* v_00_u03b1_2759_, lean_object* v_attrName_2760_, lean_object* v_declName_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2760_, v_declName_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2768_, lean_object* v_attrName_2769_, lean_object* v_declName_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(v_00_u03b1_2768_, v_attrName_2769_, v_declName_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(lean_object* v___y_2777_, uint8_t v_isExporting_2778_, lean_object* v___x_2779_, lean_object* v___y_2780_, lean_object* v___x_2781_, lean_object* v_a_x3f_2782_){
_start:
{
lean_object* v___x_2784_; lean_object* v_env_2785_; lean_object* v_nextMacroScope_2786_; lean_object* v_ngen_2787_; lean_object* v_auxDeclNGen_2788_; lean_object* v_traceState_2789_; lean_object* v_messages_2790_; lean_object* v_infoState_2791_; lean_object* v_snapshotTasks_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2817_; 
v___x_2784_ = lean_st_ref_take(v___y_2777_);
v_env_2785_ = lean_ctor_get(v___x_2784_, 0);
v_nextMacroScope_2786_ = lean_ctor_get(v___x_2784_, 1);
v_ngen_2787_ = lean_ctor_get(v___x_2784_, 2);
v_auxDeclNGen_2788_ = lean_ctor_get(v___x_2784_, 3);
v_traceState_2789_ = lean_ctor_get(v___x_2784_, 4);
v_messages_2790_ = lean_ctor_get(v___x_2784_, 6);
v_infoState_2791_ = lean_ctor_get(v___x_2784_, 7);
v_snapshotTasks_2792_ = lean_ctor_get(v___x_2784_, 8);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v___x_2784_, 5);
lean_dec(v_unused_2818_);
v___x_2794_ = v___x_2784_;
v_isShared_2795_ = v_isSharedCheck_2817_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_snapshotTasks_2792_);
lean_inc(v_infoState_2791_);
lean_inc(v_messages_2790_);
lean_inc(v_traceState_2789_);
lean_inc(v_auxDeclNGen_2788_);
lean_inc(v_ngen_2787_);
lean_inc(v_nextMacroScope_2786_);
lean_inc(v_env_2785_);
lean_dec(v___x_2784_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2817_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2796_ = l_Lean_Environment_setExporting(v_env_2785_, v_isExporting_2778_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 5, v___x_2779_);
lean_ctor_set(v___x_2794_, 0, v___x_2796_);
v___x_2798_ = v___x_2794_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_nextMacroScope_2786_);
lean_ctor_set(v_reuseFailAlloc_2816_, 2, v_ngen_2787_);
lean_ctor_set(v_reuseFailAlloc_2816_, 3, v_auxDeclNGen_2788_);
lean_ctor_set(v_reuseFailAlloc_2816_, 4, v_traceState_2789_);
lean_ctor_set(v_reuseFailAlloc_2816_, 5, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2816_, 6, v_messages_2790_);
lean_ctor_set(v_reuseFailAlloc_2816_, 7, v_infoState_2791_);
lean_ctor_set(v_reuseFailAlloc_2816_, 8, v_snapshotTasks_2792_);
v___x_2798_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v_mctx_2801_; lean_object* v_zetaDeltaFVarIds_2802_; lean_object* v_postponed_2803_; lean_object* v_diag_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2814_; 
v___x_2799_ = lean_st_ref_put(v___y_2777_, v___x_2798_);
v___x_2800_ = lean_st_ref_take(v___y_2780_);
v_mctx_2801_ = lean_ctor_get(v___x_2800_, 0);
v_zetaDeltaFVarIds_2802_ = lean_ctor_get(v___x_2800_, 2);
v_postponed_2803_ = lean_ctor_get(v___x_2800_, 3);
v_diag_2804_ = lean_ctor_get(v___x_2800_, 4);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; 
v_unused_2815_ = lean_ctor_get(v___x_2800_, 1);
lean_dec(v_unused_2815_);
v___x_2806_ = v___x_2800_;
v_isShared_2807_ = v_isSharedCheck_2814_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_diag_2804_);
lean_inc(v_postponed_2803_);
lean_inc(v_zetaDeltaFVarIds_2802_);
lean_inc(v_mctx_2801_);
lean_dec(v___x_2800_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2814_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 1, v___x_2781_);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_mctx_2801_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_zetaDeltaFVarIds_2802_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_postponed_2803_);
lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_diag_2804_);
v___x_2809_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = lean_st_ref_put(v___y_2780_, v___x_2809_);
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
return v___x_2812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2819_, lean_object* v_isExporting_2820_, lean_object* v___x_2821_, lean_object* v___y_2822_, lean_object* v___x_2823_, lean_object* v_a_x3f_2824_, lean_object* v___y_2825_){
_start:
{
uint8_t v_isExporting_boxed_2826_; lean_object* v_res_2827_; 
v_isExporting_boxed_2826_ = lean_unbox(v_isExporting_2820_);
v_res_2827_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2819_, v_isExporting_boxed_2826_, v___x_2821_, v___y_2822_, v___x_2823_, v_a_x3f_2824_);
lean_dec(v_a_x3f_2824_);
lean_dec(v___y_2822_);
lean_dec(v___y_2819_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(lean_object* v_x_2828_, uint8_t v_isExporting_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; lean_object* v_env_2836_; lean_object* v___x_2837_; uint8_t v_isModule_2838_; 
v___x_2835_ = lean_st_ref_get(v___y_2833_);
v_env_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc_ref(v_env_2836_);
lean_dec(v___x_2835_);
v___x_2837_ = l_Lean_Environment_header(v_env_2836_);
v_isModule_2838_ = lean_ctor_get_uint8(v___x_2837_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2837_);
if (v_isModule_2838_ == 0)
{
lean_object* v___x_2839_; 
lean_dec_ref(v_env_2836_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
v___x_2839_ = lean_apply_5(v_x_2828_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, lean_box(0));
return v___x_2839_;
}
else
{
uint8_t v_isExporting_2840_; 
v_isExporting_2840_ = lean_ctor_get_uint8(v_env_2836_, sizeof(void*)*8);
lean_dec_ref(v_env_2836_);
if (v_isExporting_2829_ == 0)
{
if (v_isExporting_2840_ == 0)
{
lean_object* v___x_2906_; 
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
v___x_2906_ = lean_apply_5(v_x_2828_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, lean_box(0));
return v___x_2906_;
}
else
{
goto v___jp_2841_;
}
}
else
{
if (v_isExporting_2840_ == 0)
{
goto v___jp_2841_;
}
else
{
lean_object* v___x_2907_; 
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
v___x_2907_ = lean_apply_5(v_x_2828_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, lean_box(0));
return v___x_2907_;
}
}
v___jp_2841_:
{
lean_object* v___x_2842_; lean_object* v_env_2843_; lean_object* v_nextMacroScope_2844_; lean_object* v_ngen_2845_; lean_object* v_auxDeclNGen_2846_; lean_object* v_traceState_2847_; lean_object* v_messages_2848_; lean_object* v_infoState_2849_; lean_object* v_snapshotTasks_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2904_; 
v___x_2842_ = lean_st_ref_take(v___y_2833_);
v_env_2843_ = lean_ctor_get(v___x_2842_, 0);
v_nextMacroScope_2844_ = lean_ctor_get(v___x_2842_, 1);
v_ngen_2845_ = lean_ctor_get(v___x_2842_, 2);
v_auxDeclNGen_2846_ = lean_ctor_get(v___x_2842_, 3);
v_traceState_2847_ = lean_ctor_get(v___x_2842_, 4);
v_messages_2848_ = lean_ctor_get(v___x_2842_, 6);
v_infoState_2849_ = lean_ctor_get(v___x_2842_, 7);
v_snapshotTasks_2850_ = lean_ctor_get(v___x_2842_, 8);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v___x_2842_, 5);
lean_dec(v_unused_2905_);
v___x_2852_ = v___x_2842_;
v_isShared_2853_ = v_isSharedCheck_2904_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_snapshotTasks_2850_);
lean_inc(v_infoState_2849_);
lean_inc(v_messages_2848_);
lean_inc(v_traceState_2847_);
lean_inc(v_auxDeclNGen_2846_);
lean_inc(v_ngen_2845_);
lean_inc(v_nextMacroScope_2844_);
lean_inc(v_env_2843_);
lean_dec(v___x_2842_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2904_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2854_ = l_Lean_Environment_setExporting(v_env_2843_, v_isExporting_2829_);
v___x_2855_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 5, v___x_2855_);
lean_ctor_set(v___x_2852_, 0, v___x_2854_);
v___x_2857_ = v___x_2852_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_nextMacroScope_2844_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_ngen_2845_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_auxDeclNGen_2846_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_traceState_2847_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_messages_2848_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_infoState_2849_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_snapshotTasks_2850_);
v___x_2857_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v_mctx_2860_; lean_object* v_zetaDeltaFVarIds_2861_; lean_object* v_postponed_2862_; lean_object* v_diag_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2901_; 
v___x_2858_ = lean_st_ref_put(v___y_2833_, v___x_2857_);
v___x_2859_ = lean_st_ref_take(v___y_2831_);
v_mctx_2860_ = lean_ctor_get(v___x_2859_, 0);
v_zetaDeltaFVarIds_2861_ = lean_ctor_get(v___x_2859_, 2);
v_postponed_2862_ = lean_ctor_get(v___x_2859_, 3);
v_diag_2863_ = lean_ctor_get(v___x_2859_, 4);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v___x_2859_, 1);
lean_dec(v_unused_2902_);
v___x_2865_ = v___x_2859_;
v_isShared_2866_ = v_isSharedCheck_2901_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_diag_2863_);
lean_inc(v_postponed_2862_);
lean_inc(v_zetaDeltaFVarIds_2861_);
lean_inc(v_mctx_2860_);
lean_dec(v___x_2859_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2901_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v___x_2867_);
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_mctx_2860_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_zetaDeltaFVarIds_2861_);
lean_ctor_set(v_reuseFailAlloc_2900_, 3, v_postponed_2862_);
lean_ctor_set(v_reuseFailAlloc_2900_, 4, v_diag_2863_);
v___x_2869_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; lean_object* v_r_2871_; 
v___x_2870_ = lean_st_ref_put(v___y_2831_, v___x_2869_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
v_r_2871_ = lean_apply_5(v_x_2828_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, lean_box(0));
if (lean_obj_tag(v_r_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2888_; 
v_a_2872_ = lean_ctor_get(v_r_2871_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_r_2871_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2874_ = v_r_2871_;
v_isShared_2875_ = v_isSharedCheck_2888_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v_r_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2888_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
lean_inc(v_a_2872_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set_tag(v___x_2874_, 1);
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
v___x_2878_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2833_, v_isExporting_2840_, v___x_2855_, v___y_2831_, v___x_2867_, v___x_2877_);
lean_dec_ref(v___x_2877_);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; 
v_unused_2886_ = lean_ctor_get(v___x_2878_, 0);
lean_dec(v_unused_2886_);
v___x_2880_ = v___x_2878_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_dec(v___x_2878_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v_a_2872_);
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2872_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_a_2889_ = lean_ctor_get(v_r_2871_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v_r_2871_, 1);
v___x_2890_ = lean_box(0);
v___x_2891_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2833_, v_isExporting_2840_, v___x_2855_, v___y_2831_, v___x_2867_, v___x_2890_);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2891_, 0);
lean_dec(v_unused_2899_);
v___x_2893_ = v___x_2891_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_dec(v___x_2891_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set_tag(v___x_2893_, 1);
lean_ctor_set(v___x_2893_, 0, v_a_2889_);
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2889_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___boxed(lean_object* v_x_2908_, lean_object* v_isExporting_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v_isExporting_boxed_2915_; lean_object* v_res_2916_; 
v_isExporting_boxed_2915_ = lean_unbox(v_isExporting_2909_);
v_res_2916_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_2908_, v_isExporting_boxed_2915_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(lean_object* v_00_u03b1_2917_, lean_object* v_x_2918_, uint8_t v_isExporting_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_2918_, v_isExporting_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_x_2927_, lean_object* v_isExporting_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
uint8_t v_isExporting_boxed_2934_; lean_object* v_res_2935_; 
v_isExporting_boxed_2934_ = lean_unbox(v_isExporting_2928_);
v_res_2935_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(v_00_u03b1_2926_, v_x_2927_, v_isExporting_boxed_2934_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0(lean_object* v_indName_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; 
lean_inc(v_indName_2936_);
v___x_2942_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref_known(v___x_2942_, 1);
lean_inc(v_indName_2936_);
v___x_2943_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2944_; 
lean_dec_ref_known(v___x_2943_, 1);
v___x_2944_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
return v___x_2944_;
}
else
{
lean_dec(v_indName_2936_);
return v___x_2943_;
}
}
else
{
lean_dec(v_indName_2936_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object* v_indName_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_mkCtorElim___lam__0(v_indName_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(lean_object* v_declName_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
lean_inc(v_declName_2952_);
v___x_2958_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_declName_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2994_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2994_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2994_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
if (lean_obj_tag(v_a_2959_) == 5)
{
lean_object* v_val_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_del_object(v___x_2961_);
v_val_2963_ = lean_ctor_get(v_a_2959_, 0);
lean_inc_ref(v_val_2963_);
lean_dec_ref_known(v_a_2959_, 1);
v___x_2964_ = l_Lean_mkRecName(v_declName_2952_);
v___x_2965_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v___x_2964_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_toConstantVal_2966_; lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2980_; 
v_toConstantVal_2966_ = lean_ctor_get(v_val_2963_, 0);
lean_inc_ref(v_toConstantVal_2966_);
lean_dec_ref(v_val_2963_);
v_a_2967_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2969_ = v___x_2965_;
v_isShared_2970_ = v_isSharedCheck_2980_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2965_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2980_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v_levelParams_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v_levelParams_2971_ = lean_ctor_get(v_toConstantVal_2966_, 1);
lean_inc(v_levelParams_2971_);
lean_dec_ref(v_toConstantVal_2966_);
v___x_2972_ = l_List_lengthTR___redArg(v_levelParams_2971_);
lean_dec(v_levelParams_2971_);
v___x_2973_ = l_Lean_ConstantInfo_levelParams(v_a_2967_);
lean_dec(v_a_2967_);
v___x_2974_ = l_List_lengthTR___redArg(v___x_2973_);
lean_dec(v___x_2973_);
v___x_2975_ = lean_nat_dec_lt(v___x_2972_, v___x_2974_);
lean_dec(v___x_2974_);
lean_dec(v___x_2972_);
v___x_2976_ = lean_box(v___x_2975_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2976_);
v___x_2978_ = v___x_2969_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v_val_2963_);
v_a_2981_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2965_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2965_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
lean_dec(v_a_2959_);
lean_dec(v_declName_2952_);
v___x_2989_ = 0;
v___x_2990_ = lean_box(v___x_2989_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2990_);
v___x_2992_ = v___x_2961_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_declName_2952_);
v_a_2995_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2958_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2958_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0___boxed(lean_object* v_declName_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_declName_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim(lean_object* v_indName_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v___x_3016_; lean_object* v_env_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; uint8_t v___x_3020_; 
v___x_3016_ = lean_st_ref_get(v_a_3014_);
v_env_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc_ref(v_env_3017_);
lean_dec(v___x_3016_);
lean_inc(v_indName_3010_);
v___x_3018_ = l_Lean_mkCtorIdxName(v_indName_3010_);
v___x_3019_ = 1;
v___x_3020_ = l_Lean_Environment_contains(v_env_3017_, v___x_3018_, v___x_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_dec(v_indName_3010_);
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; 
lean_inc(v_indName_3010_);
v___x_3023_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3086_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3086_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3086_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
if (lean_obj_tag(v_a_3024_) == 5)
{
lean_object* v_val_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v_val_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc_ref(v_val_3028_);
lean_dec_ref_known(v_a_3024_, 1);
v___x_3029_ = lean_unsigned_to_nat(1u);
v___x_3030_ = l_Lean_InductiveVal_numCtors(v_val_3028_);
v___x_3031_ = lean_nat_dec_lt(v___x_3029_, v___x_3030_);
lean_dec(v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
lean_dec_ref(v_val_3028_);
lean_dec(v_indName_3010_);
v___x_3032_ = lean_box(0);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3032_);
v___x_3034_ = v___x_3026_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
else
{
lean_object* v_toConstantVal_3036_; lean_object* v_type_3037_; lean_object* v___x_3038_; 
lean_del_object(v___x_3026_);
v_toConstantVal_3036_ = lean_ctor_get(v_val_3028_, 0);
lean_inc_ref(v_toConstantVal_3036_);
lean_dec_ref(v_val_3028_);
v_type_3037_ = lean_ctor_get(v_toConstantVal_3036_, 2);
lean_inc_ref(v_type_3037_);
lean_dec_ref(v_toConstantVal_3036_);
v___x_3038_ = l_Lean_Meta_isPropFormerType(v_type_3037_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3073_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3073_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3073_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
uint8_t v___x_3043_; 
v___x_3043_ = lean_unbox(v_a_3039_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
lean_del_object(v___x_3041_);
lean_inc(v_indName_3010_);
v___x_3044_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_indName_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3060_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3060_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3060_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_unbox(v_a_3045_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3052_; 
lean_dec(v_a_3045_);
lean_dec(v_a_3039_);
lean_dec(v_indName_3010_);
v___x_3050_ = lean_box(0);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3050_);
v___x_3052_ = v___x_3047_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
else
{
lean_object* v___f_3054_; uint8_t v___x_3055_; 
lean_del_object(v___x_3047_);
lean_inc(v_indName_3010_);
v___f_3054_ = lean_alloc_closure((void*)(l_Lean_mkCtorElim___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3054_, 0, v_indName_3010_);
v___x_3055_ = l_Lean_isPrivateName(v_indName_3010_);
lean_dec(v_indName_3010_);
if (v___x_3055_ == 0)
{
uint8_t v___x_3056_; lean_object* v___x_3057_; 
lean_dec(v_a_3039_);
v___x_3056_ = lean_unbox(v_a_3045_);
lean_dec(v_a_3045_);
v___x_3057_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3054_, v___x_3056_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
return v___x_3057_;
}
else
{
uint8_t v___x_3058_; lean_object* v___x_3059_; 
lean_dec(v_a_3045_);
v___x_3058_ = lean_unbox(v_a_3039_);
lean_dec(v_a_3039_);
v___x_3059_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3054_, v___x_3058_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
return v___x_3059_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_a_3039_);
lean_dec(v_indName_3010_);
v_a_3061_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3044_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3044_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
lean_dec(v_a_3039_);
lean_dec(v_indName_3010_);
v___x_3069_ = lean_box(0);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3069_);
v___x_3071_ = v___x_3041_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_indName_3010_);
v_a_3074_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3038_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3038_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
lean_dec(v_a_3024_);
lean_dec(v_indName_3010_);
v___x_3082_ = lean_box(0);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3082_);
v___x_3084_ = v___x_3026_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_indName_3010_);
v_a_3087_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3023_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3023_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___boxed(lean_object* v_indName_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_mkCtorElim(v_indName_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v_decl_3102_, lean_object* v_____r_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
lean_inc(v_decl_3102_);
v___x_3109_ = l_Lean_mkCtorIdx(v_decl_3102_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3110_; 
lean_dec_ref_known(v___x_3109_, 1);
v___x_3110_ = l_Lean_mkCtorElim(v_decl_3102_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
return v___x_3110_;
}
else
{
lean_dec(v_decl_3102_);
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_decl_3111_, lean_object* v_____r_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3111_, v_____r_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
return v_res_3118_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_3121_ = l_Lean_stringToMessageData(v___x_3120_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_3124_ = l_Lean_stringToMessageData(v___x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_3128_, uint8_t v_kind_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___y_3141_; 
v___x_3135_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_3136_ = l_Lean_MessageData_ofName(v_name_3128_);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_3139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3137_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
switch(v_kind_3129_)
{
case 0:
{
lean_object* v___x_3148_; 
v___x_3148_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_3141_ = v___x_3148_;
goto v___jp_3140_;
}
case 1:
{
lean_object* v___x_3149_; 
v___x_3149_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_3141_ = v___x_3149_;
goto v___jp_3140_;
}
default: 
{
lean_object* v___x_3150_; 
v___x_3150_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_3141_ = v___x_3150_;
goto v___jp_3140_;
}
}
v___jp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_inc_ref(v___y_3141_);
v___x_3142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___y_3141_);
v___x_3143_ = l_Lean_MessageData_ofFormat(v___x_3142_);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3139_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_3146_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_3151_, lean_object* v_kind_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
uint8_t v_kind_boxed_3158_; lean_object* v_res_3159_; 
v_kind_boxed_3158_ = lean_unbox(v_kind_3152_);
v_res_3159_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3151_, v_kind_boxed_3158_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
return v_res_3159_;
}
}
static uint64_t _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3166_; uint64_t v___x_3167_; 
v___x_3166_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3167_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3166_);
return v___x_3167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_uint64_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3170_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set_uint64(v___x_3170_, sizeof(void*)*1, v___x_3168_);
return v___x_3170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3171_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3175_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
lean_ctor_set(v___x_3175_, 2, v___x_3174_);
lean_ctor_set(v___x_3175_, 3, v___x_3174_);
lean_ctor_set(v___x_3175_, 4, v___x_3174_);
lean_ctor_set(v___x_3175_, 5, v___x_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
lean_ctor_set(v___x_3177_, 2, v___x_3176_);
lean_ctor_set(v___x_3177_, 3, v___x_3176_);
lean_ctor_set(v___x_3177_, 4, v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3178_, lean_object* v___x_3179_, lean_object* v___x_3180_, lean_object* v_decl_3181_, lean_object* v___stx_3182_, uint8_t v_kind_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v___x_3187_; uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; size_t v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___y_3207_; uint8_t v___x_3217_; uint8_t v___x_3218_; 
v___x_3187_ = 1;
v___x_3188_ = 0;
v___x_3189_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3190_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3191_ = lean_unsigned_to_nat(32u);
v___x_3192_ = lean_mk_empty_array_with_capacity(v___x_3191_);
v___x_3193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3194_ = ((size_t)5ULL);
lean_inc_n(v___x_3178_, 6);
v___x_3195_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3192_);
lean_ctor_set(v___x_3195_, 2, v___x_3178_);
lean_ctor_set(v___x_3195_, 3, v___x_3178_);
lean_ctor_set_usize(v___x_3195_, 4, v___x_3194_);
v___x_3196_ = lean_box(1);
lean_inc_ref(v___x_3195_);
v___x_3197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3190_);
lean_ctor_set(v___x_3197_, 1, v___x_3195_);
lean_ctor_set(v___x_3197_, 2, v___x_3196_);
v___x_3198_ = lean_mk_empty_array_with_capacity(v___x_3178_);
v___x_3199_ = lean_box(0);
lean_inc(v___x_3179_);
v___x_3200_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3200_, 0, v___x_3189_);
lean_ctor_set(v___x_3200_, 1, v___x_3179_);
lean_ctor_set(v___x_3200_, 2, v___x_3197_);
lean_ctor_set(v___x_3200_, 3, v___x_3198_);
lean_ctor_set(v___x_3200_, 4, v___x_3199_);
lean_ctor_set(v___x_3200_, 5, v___x_3178_);
lean_ctor_set(v___x_3200_, 6, v___x_3199_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*7, v___x_3188_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*7 + 1, v___x_3188_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*7 + 2, v___x_3188_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*7 + 3, v___x_3187_);
v___x_3201_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3178_);
lean_ctor_set(v___x_3201_, 1, v___x_3178_);
lean_ctor_set(v___x_3201_, 2, v___x_3178_);
lean_ctor_set(v___x_3201_, 3, v___x_3178_);
lean_ctor_set(v___x_3201_, 4, v___x_3190_);
lean_ctor_set(v___x_3201_, 5, v___x_3190_);
lean_ctor_set(v___x_3201_, 6, v___x_3190_);
lean_ctor_set(v___x_3201_, 7, v___x_3190_);
lean_ctor_set(v___x_3201_, 8, v___x_3190_);
lean_ctor_set(v___x_3201_, 9, v___x_3190_);
lean_ctor_set(v___x_3201_, 10, v___x_3190_);
v___x_3202_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3203_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3201_);
lean_ctor_set(v___x_3204_, 1, v___x_3202_);
lean_ctor_set(v___x_3204_, 2, v___x_3179_);
lean_ctor_set(v___x_3204_, 3, v___x_3195_);
lean_ctor_set(v___x_3204_, 4, v___x_3203_);
v___x_3205_ = lean_st_mk_ref(v___x_3204_);
v___x_3217_ = 0;
v___x_3218_ = l_Lean_instBEqAttributeKind_beq(v_kind_3183_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; 
lean_dec(v_decl_3181_);
v___x_3219_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v___x_3180_, v_kind_3183_, v___x_3200_, v___x_3205_, v___y_3184_, v___y_3185_);
lean_dec_ref_known(v___x_3200_, 7);
v___y_3207_ = v___x_3219_;
goto v___jp_3206_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec(v___x_3180_);
v___x_3220_ = lean_box(0);
v___x_3221_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3181_, v___x_3220_, v___x_3200_, v___x_3205_, v___y_3184_, v___y_3185_);
lean_dec_ref_known(v___x_3200_, 7);
v___y_3207_ = v___x_3221_;
goto v___jp_3206_;
}
v___jp_3206_:
{
if (lean_obj_tag(v___y_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
v_a_3208_ = lean_ctor_get(v___y_3207_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___y_3207_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3210_ = v___y_3207_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___y_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_st_ref_get(v___x_3205_);
lean_dec(v___x_3205_);
lean_dec(v___x_3212_);
if (v_isShared_3211_ == 0)
{
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3208_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
else
{
lean_dec(v___x_3205_);
return v___y_3207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3222_, lean_object* v___x_3223_, lean_object* v___x_3224_, lean_object* v_decl_3225_, lean_object* v___stx_3226_, lean_object* v_kind_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
uint8_t v_kind_boxed_3231_; lean_object* v_res_3232_; 
v_kind_boxed_3231_ = lean_unbox(v_kind_3227_);
v_res_3232_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3222_, v___x_3223_, v___x_3224_, v_decl_3225_, v___stx_3226_, v_kind_boxed_3231_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___stx_3226_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; lean_object* v_toCold_3238_; lean_object* v_env_3239_; lean_object* v_options_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3237_ = lean_st_ref_get(v___y_3235_);
v_toCold_3238_ = lean_ctor_get(v___y_3234_, 0);
v_env_3239_ = lean_ctor_get(v___x_3237_, 0);
lean_inc_ref(v_env_3239_);
lean_dec(v___x_3237_);
v_options_3240_ = lean_ctor_get(v_toCold_3238_, 2);
v___x_3241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3242_ = lean_unsigned_to_nat(32u);
v___x_3243_ = lean_mk_empty_array_with_capacity(v___x_3242_);
lean_dec_ref(v___x_3243_);
v___x_3244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
lean_inc_ref(v_options_3240_);
v___x_3245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3245_, 0, v_env_3239_);
lean_ctor_set(v___x_3245_, 1, v___x_3241_);
lean_ctor_set(v___x_3245_, 2, v___x_3244_);
lean_ctor_set(v___x_3245_, 3, v_options_3240_);
v___x_3246_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
lean_ctor_set(v___x_3246_, 1, v_msgData_3233_);
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_ref_3257_; lean_object* v___x_3258_; lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3267_; 
v_ref_3257_ = lean_ctor_get(v___y_3254_, 2);
v___x_3258_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msg_3253_, v___y_3254_, v___y_3255_);
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
lean_inc(v_ref_3257_);
v___x_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3263_, 0, v_ref_3257_);
lean_ctor_set(v___x_3263_, 1, v_a_3259_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set_tag(v___x_3261_, 1);
lean_ctor_set(v___x_3261_, 0, v___x_3263_);
v___x_3265_ = v___x_3261_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3275_ = l_Lean_stringToMessageData(v___x_3274_);
return v___x_3275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3278_ = l_Lean_stringToMessageData(v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3279_, lean_object* v_decl_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3284_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3285_ = l_Lean_MessageData_ofName(v___x_3279_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v___x_3288_, v___y_3281_, v___y_3282_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3290_, lean_object* v_decl_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3290_, v_decl_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v_decl_3291_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3377_ = l_Lean_registerBuiltinAttribute(v___x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3380_, lean_object* v_msg_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3381_, v___y_3382_, v___y_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3386_, lean_object* v_msg_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(v_00_u03b1_3386_, v_msg_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_3392_, lean_object* v_name_3393_, uint8_t v_kind_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3393_, v_kind_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_3401_, lean_object* v_name_3402_, lean_object* v_kind_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
uint8_t v_kind_boxed_3409_; lean_object* v_res_3410_; 
v_kind_boxed_3409_ = lean_unbox(v_kind_3403_);
v_res_3410_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(v_00_u03b1_3401_, v_name_3402_, v_kind_boxed_3409_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3415_ = l_Lean_addBuiltinDocString(v___x_3413_, v___x_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3417_;
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
