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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___f_595_; lean_object* v___x_4300__overap_596_; lean_object* v___x_597_; 
v___f_595_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0));
v___x_4300__overap_596_ = lean_panic_fn_borrowed(v___f_595_, v_msg_589_);
lean_inc(v___y_593_);
lean_inc_ref(v___y_592_);
lean_inc(v___y_591_);
lean_inc_ref(v___y_590_);
v___x_597_ = lean_apply_5(v___x_4300__overap_596_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, lean_box(0));
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
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
uint8_t v___x_6840__boxed_685_; lean_object* v_res_686_; 
v___x_6840__boxed_685_ = lean_unbox(v___x_678_);
v_res_686_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(v___x_675_, v___x_676_, v___x_677_, v___x_6840__boxed_685_, v_ctorIdx_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
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
uint8_t v___x_7017__boxed_812_; lean_object* v_res_813_; 
v___x_7017__boxed_812_ = lean_unbox(v___x_804_);
v_res_813_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(v_val_801_, v___x_802_, v___x_803_, v___x_7017__boxed_812_, v_xs_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec_ref(v_x_806_);
lean_dec_ref(v___x_803_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_814_, lean_object* v_msg_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_toCold_821_; lean_object* v_currRecDepth_822_; lean_object* v_ref_823_; uint16_t v_optionFlags_824_; uint8_t v_suppressElabErrors_825_; uint8_t v_checkDeprecated_826_; uint8_t v_isRecordingDeps_827_; lean_object* v_ref_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_toCold_821_ = lean_ctor_get(v___y_818_, 0);
v_currRecDepth_822_ = lean_ctor_get(v___y_818_, 1);
v_ref_823_ = lean_ctor_get(v___y_818_, 2);
v_optionFlags_824_ = lean_ctor_get_uint16(v___y_818_, sizeof(void*)*3);
v_suppressElabErrors_825_ = lean_ctor_get_uint8(v___y_818_, sizeof(void*)*3 + 2);
v_checkDeprecated_826_ = lean_ctor_get_uint8(v___y_818_, sizeof(void*)*3 + 3);
v_isRecordingDeps_827_ = lean_ctor_get_uint8(v___y_818_, sizeof(void*)*3 + 4);
v_ref_828_ = l_Lean_replaceRef(v_ref_814_, v_ref_823_);
lean_inc(v_currRecDepth_822_);
lean_inc_ref(v_toCold_821_);
v___x_829_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_829_, 0, v_toCold_821_);
lean_ctor_set(v___x_829_, 1, v_currRecDepth_822_);
lean_ctor_set(v___x_829_, 2, v_ref_828_);
lean_ctor_set_uint16(v___x_829_, sizeof(void*)*3, v_optionFlags_824_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*3 + 2, v_suppressElabErrors_825_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*3 + 3, v_checkDeprecated_826_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*3 + 4, v_isRecordingDeps_827_);
v___x_830_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_815_, v___y_816_, v___y_817_, v___x_829_, v___y_819_);
lean_dec_ref_known(v___x_829_, 3);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_831_, lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_831_, v_msg_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v_ref_831_);
return v_res_838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_842_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
lean_ctor_set(v___x_845_, 2, v___x_844_);
lean_ctor_set(v___x_845_, 3, v___x_844_);
lean_ctor_set(v___x_845_, 4, v___x_843_);
lean_ctor_set(v___x_845_, 5, v___x_843_);
lean_ctor_set(v___x_845_, 6, v___x_843_);
lean_ctor_set(v___x_845_, 7, v___x_843_);
lean_ctor_set(v___x_845_, 8, v___x_843_);
lean_ctor_set(v___x_845_, 9, v___x_843_);
lean_ctor_set(v___x_845_, 10, v___x_843_);
lean_ctor_set(v___x_845_, 11, v___x_842_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_unsigned_to_nat(32u);
v___x_847_ = lean_mk_empty_array_with_capacity(v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_849_ = ((size_t)5ULL);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_unsigned_to_nat(32u);
v___x_852_ = lean_mk_empty_array_with_capacity(v___x_851_);
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_854_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
lean_ctor_set(v___x_854_, 2, v___x_850_);
lean_ctor_set(v___x_854_, 3, v___x_850_);
lean_ctor_set_usize(v___x_854_, 4, v___x_849_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_box(1);
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
lean_ctor_set(v___x_858_, 2, v___x_855_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_880_, lean_object* v_declHint_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_env_886_; uint8_t v___x_887_; 
v___x_884_ = lean_box(0);
v___x_885_ = lean_st_ref_get(v___y_882_);
v_env_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc_ref(v_env_886_);
lean_dec(v___x_885_);
v___x_887_ = l_Lean_Name_isAnonymous(v_declHint_881_);
if (v___x_887_ == 0)
{
uint8_t v_isExporting_888_; 
v_isExporting_888_ = lean_ctor_get_uint8(v_env_886_, sizeof(void*)*13);
if (v_isExporting_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec_ref(v_env_886_);
lean_dec(v_declHint_881_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v_msg_880_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; uint8_t v___x_891_; 
lean_inc_ref(v_env_886_);
v___x_890_ = l_Lean_Environment_setExporting(v_env_886_, v___x_887_);
lean_inc(v_declHint_881_);
lean_inc_ref(v___x_890_);
v___x_891_ = l_Lean_Environment_contains(v___x_890_, v_declHint_881_, v_isExporting_888_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec_ref(v___x_890_);
lean_dec_ref(v_env_886_);
lean_dec(v_declHint_881_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v_msg_880_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_c_898_; lean_object* v___x_899_; 
v___x_893_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_895_ = l_Lean_Options_empty;
lean_inc_ref(v___x_890_);
v___x_896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_896_, 0, v___x_890_);
lean_ctor_set(v___x_896_, 1, v___x_893_);
lean_ctor_set(v___x_896_, 2, v___x_894_);
lean_ctor_set(v___x_896_, 3, v___x_895_);
lean_inc(v_declHint_881_);
v___x_897_ = l_Lean_MessageData_ofConstName(v_declHint_881_, v___x_887_);
v_c_898_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_898_, 0, v___x_896_);
lean_ctor_set(v_c_898_, 1, v___x_897_);
v___x_899_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_890_, v_declHint_881_);
lean_dec_ref(v___x_890_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref(v_env_886_);
lean_dec(v_declHint_881_);
v___x_900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_c_898_);
v___x_902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_MessageData_note(v___x_903_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v_msg_880_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
else
{
lean_object* v_val_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_941_; 
v_val_907_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_941_ == 0)
{
v___x_909_ = v___x_899_;
v_isShared_910_ = v_isSharedCheck_941_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_val_907_);
lean_dec(v___x_899_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_941_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v_moduleNames_912_; lean_object* v_mod_913_; uint8_t v___x_914_; 
v___x_911_ = l_Lean_Environment_header(v_env_886_);
lean_dec_ref(v_env_886_);
v_moduleNames_912_ = lean_ctor_get(v___x_911_, 4);
lean_inc_ref(v_moduleNames_912_);
lean_dec_ref(v___x_911_);
v_mod_913_ = lean_array_get(v___x_884_, v_moduleNames_912_, v_val_907_);
lean_dec(v_val_907_);
lean_dec_ref(v_moduleNames_912_);
v___x_914_ = l_Lean_isPrivateName(v_declHint_881_);
lean_dec(v_declHint_881_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v_c_898_);
v___x_917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_MessageData_ofName(v_mod_913_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_MessageData_note(v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v_msg_880_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 0);
lean_ctor_set(v___x_909_, 0, v___x_924_);
v___x_926_ = v___x_909_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_c_898_);
v___x_930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_MessageData_ofName(v_mod_913_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_MessageData_note(v___x_935_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v_msg_880_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 0);
lean_ctor_set(v___x_909_, 0, v___x_937_);
v___x_939_ = v___x_909_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_942_; 
lean_dec_ref(v_env_886_);
lean_dec(v_declHint_881_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_msg_880_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_943_, lean_object* v_declHint_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_943_, v_declHint_944_, v___y_945_);
lean_dec(v___y_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_948_, lean_object* v_declHint_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v___x_955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_948_, v_declHint_949_, v___y_953_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = l_Lean_unknownIdentifierMessageTag;
v___x_961_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v_a_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_966_, lean_object* v_declHint_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_966_, v_declHint_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_974_, lean_object* v_msg_975_, lean_object* v_declHint_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_a_983_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_975_, v_declHint_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___x_982_);
v___x_984_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_974_, v_a_983_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_985_, lean_object* v_msg_986_, lean_object* v_declHint_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_985_, v_msg_986_, v_declHint_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v_ref_985_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_1000_, lean_object* v_constName_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1007_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_1008_ = 0;
lean_inc(v_constName_1001_);
v___x_1009_ = l_Lean_MessageData_ofConstName(v_constName_1001_, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_1000_, v___x_1012_, v_constName_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1014_, lean_object* v_constName_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1014_, v_constName_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v_ref_1014_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(lean_object* v_constName_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_ref_1028_; lean_object* v___x_1029_; 
v_ref_1028_ = lean_ctor_get(v___y_1025_, 2);
v___x_1029_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_1028_, v_constName_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(lean_object* v_constName_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_env_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; 
v___x_1043_ = lean_st_ref_get(v___y_1041_);
v_env_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc_ref(v_env_1044_);
lean_dec(v___x_1043_);
v___x_1045_ = 0;
lean_inc(v_constName_1037_);
v___x_1046_ = l_Lean_Environment_find_x3f(v_env_1044_, v_constName_1037_, v___x_1045_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v___x_1047_;
}
else
{
lean_object* v_val_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_constName_1037_);
v_val_1048_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1046_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_val_1048_);
lean_dec(v___x_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 0);
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_val_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(lean_object* v_constName_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_constName_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1062_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
v___x_1068_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
lean_ctor_set(v___x_1068_, 2, v___x_1067_);
lean_ctor_set(v___x_1068_, 3, v___x_1067_);
lean_ctor_set(v___x_1068_, 4, v___x_1067_);
lean_ctor_set(v___x_1068_, 5, v___x_1067_);
lean_ctor_set(v___x_1068_, 6, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(lean_object* v_declName_1069_, uint8_t v_s_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v_env_1075_; lean_object* v_nextMacroScope_1076_; lean_object* v_ngen_1077_; lean_object* v_auxDeclNGen_1078_; lean_object* v_traceState_1079_; lean_object* v_recordedDeps_1080_; lean_object* v_messages_1081_; lean_object* v_infoState_1082_; lean_object* v_snapshotTasks_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1112_; 
v___x_1074_ = lean_st_ref_take(v___y_1072_);
v_env_1075_ = lean_ctor_get(v___x_1074_, 0);
v_nextMacroScope_1076_ = lean_ctor_get(v___x_1074_, 1);
v_ngen_1077_ = lean_ctor_get(v___x_1074_, 2);
v_auxDeclNGen_1078_ = lean_ctor_get(v___x_1074_, 3);
v_traceState_1079_ = lean_ctor_get(v___x_1074_, 4);
v_recordedDeps_1080_ = lean_ctor_get(v___x_1074_, 6);
v_messages_1081_ = lean_ctor_get(v___x_1074_, 7);
v_infoState_1082_ = lean_ctor_get(v___x_1074_, 8);
v_snapshotTasks_1083_ = lean_ctor_get(v___x_1074_, 9);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; 
v_unused_1113_ = lean_ctor_get(v___x_1074_, 5);
lean_dec(v_unused_1113_);
v___x_1085_ = v___x_1074_;
v_isShared_1086_ = v_isSharedCheck_1112_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_snapshotTasks_1083_);
lean_inc(v_infoState_1082_);
lean_inc(v_messages_1081_);
lean_inc(v_recordedDeps_1080_);
lean_inc(v_traceState_1079_);
lean_inc(v_auxDeclNGen_1078_);
lean_inc(v_ngen_1077_);
lean_inc(v_nextMacroScope_1076_);
lean_inc(v_env_1075_);
lean_dec(v___x_1074_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1112_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1087_ = 0;
v___x_1088_ = lean_box(0);
v___x_1089_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1075_, v_declName_1069_, v_s_1070_, v___x_1087_, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 5, v___x_1090_);
lean_ctor_set(v___x_1085_, 0, v___x_1089_);
v___x_1092_ = v___x_1085_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_nextMacroScope_1076_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_ngen_1077_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_auxDeclNGen_1078_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v_traceState_1079_);
lean_ctor_set(v_reuseFailAlloc_1111_, 5, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1111_, 6, v_recordedDeps_1080_);
lean_ctor_set(v_reuseFailAlloc_1111_, 7, v_messages_1081_);
lean_ctor_set(v_reuseFailAlloc_1111_, 8, v_infoState_1082_);
lean_ctor_set(v_reuseFailAlloc_1111_, 9, v_snapshotTasks_1083_);
v___x_1092_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_mctx_1095_; lean_object* v_zetaDeltaFVarIds_1096_; lean_object* v_postponed_1097_; lean_object* v_diag_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1109_; 
v___x_1093_ = lean_st_ref_put(v___y_1072_, v___x_1092_);
v___x_1094_ = lean_st_ref_take(v___y_1071_);
v_mctx_1095_ = lean_ctor_get(v___x_1094_, 0);
v_zetaDeltaFVarIds_1096_ = lean_ctor_get(v___x_1094_, 2);
v_postponed_1097_ = lean_ctor_get(v___x_1094_, 3);
v_diag_1098_ = lean_ctor_get(v___x_1094_, 4);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v___x_1094_, 1);
lean_dec(v_unused_1110_);
v___x_1100_ = v___x_1094_;
v_isShared_1101_ = v_isSharedCheck_1109_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_diag_1098_);
lean_inc(v_postponed_1097_);
lean_inc(v_zetaDeltaFVarIds_1096_);
lean_inc(v_mctx_1095_);
lean_dec(v___x_1094_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1109_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v___x_1103_);
v___x_1105_ = v___x_1100_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_mctx_1095_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_zetaDeltaFVarIds_1096_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_postponed_1097_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_diag_1098_);
v___x_1105_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_st_ref_put(v___y_1071_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1102_);
return v___x_1107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(lean_object* v_declName_1114_, lean_object* v_s_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v_s_boxed_1119_; lean_object* v_res_1120_; 
v_s_boxed_1119_ = lean_unbox(v_s_1115_);
v_res_1120_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1114_, v_s_boxed_1119_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec(v___y_1116_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(lean_object* v_declName_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
uint8_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = 0;
v___x_1128_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_1121_, v___x_1127_, v___y_1123_, v___y_1125_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___boxed(lean_object* v_declName_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v_declName_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(lean_object* v_constName_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v_env_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v___x_1142_ = lean_st_ref_get(v___y_1140_);
v_env_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_ref(v_env_1143_);
lean_dec(v___x_1142_);
v___x_1144_ = 0;
lean_inc(v_constName_1136_);
v___x_1145_ = l_Lean_Environment_findConstVal_x3f(v_env_1143_, v_constName_1136_, v___x_1144_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1146_;
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_constName_1136_);
v_val_1147_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1145_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_val_1147_);
lean_dec(v___x_1145_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 0);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_val_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(lean_object* v_constName_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v_constName_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1165_ = lean_unsigned_to_nat(60u);
v___x_1166_ = lean_unsigned_to_nat(81u);
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0));
v___x_1168_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1169_ = l_mkPanicMessageWithDecl(v___x_1168_, v___x_1167_, v___x_1166_, v___x_1165_, v___x_1164_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(lean_object* v_indName_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1170_);
v___x_1177_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1311_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1311_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1311_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
if (lean_obj_tag(v_a_1178_) == 5)
{
lean_object* v_val_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_val_1182_ = lean_ctor_get(v_a_1178_, 0);
lean_inc_ref(v_val_1182_);
lean_dec_ref_known(v_a_1178_, 1);
v___x_1183_ = l_Lean_InductiveVal_numCtors(v_val_1182_);
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = lean_nat_dec_eq(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_del_object(v___x_1180_);
v___x_1186_ = lean_box(v___x_1185_);
v___f_1187_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1187_, 0, v_val_1182_);
lean_closure_set(v___f_1187_, 1, v___x_1184_);
lean_closure_set(v___f_1187_, 2, v___x_1176_);
lean_closure_set(v___f_1187_, 3, v___x_1186_);
lean_inc(v_indName_1170_);
v___x_1188_ = l_Lean_mkCasesOnName(v_indName_1170_);
v___x_1189_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1188_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v_levelParams_1191_; lean_object* v_type_1192_; lean_object* v___x_1193_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v_levelParams_1191_ = lean_ctor_get(v_a_1190_, 1);
lean_inc(v_levelParams_1191_);
v_type_1192_ = lean_ctor_get(v_a_1190_, 2);
lean_inc_ref(v_type_1192_);
lean_dec(v_a_1190_);
v___x_1193_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1192_, v___f_1187_, v___x_1185_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_n(v_a_1194_, 2);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1170_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc(v_a_1172_);
lean_inc_ref(v_a_1171_);
v___x_1196_ = lean_infer_type(v_a_1194_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1280_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = lean_box(1);
lean_inc(v___x_1195_);
v___x_1199_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1195_, v_levelParams_1191_, v_a_1197_, v_a_1194_, v___x_1198_, v_a_1174_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1280_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1280_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 1);
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
uint8_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = 1;
v___x_1207_ = l_Lean_addAndCompile(v___x_1205_, v___x_1206_, v___x_1185_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___x_1208_; lean_object* v_env_1209_; lean_object* v_nextMacroScope_1210_; lean_object* v_ngen_1211_; lean_object* v_auxDeclNGen_1212_; lean_object* v_traceState_1213_; lean_object* v_recordedDeps_1214_; lean_object* v_messages_1215_; lean_object* v_infoState_1216_; lean_object* v_snapshotTasks_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref_known(v___x_1207_, 1);
v___x_1208_ = lean_st_ref_take(v_a_1174_);
v_env_1209_ = lean_ctor_get(v___x_1208_, 0);
v_nextMacroScope_1210_ = lean_ctor_get(v___x_1208_, 1);
v_ngen_1211_ = lean_ctor_get(v___x_1208_, 2);
v_auxDeclNGen_1212_ = lean_ctor_get(v___x_1208_, 3);
v_traceState_1213_ = lean_ctor_get(v___x_1208_, 4);
v_recordedDeps_1214_ = lean_ctor_get(v___x_1208_, 6);
v_messages_1215_ = lean_ctor_get(v___x_1208_, 7);
v_infoState_1216_ = lean_ctor_get(v___x_1208_, 8);
v_snapshotTasks_1217_ = lean_ctor_get(v___x_1208_, 9);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1208_, 5);
lean_dec(v_unused_1278_);
v___x_1219_ = v___x_1208_;
v_isShared_1220_ = v_isSharedCheck_1277_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_snapshotTasks_1217_);
lean_inc(v_infoState_1216_);
lean_inc(v_messages_1215_);
lean_inc(v_recordedDeps_1214_);
lean_inc(v_traceState_1213_);
lean_inc(v_auxDeclNGen_1212_);
lean_inc(v_ngen_1211_);
lean_inc(v_nextMacroScope_1210_);
lean_inc(v_env_1209_);
lean_dec(v___x_1208_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1277_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_inc(v___x_1195_);
v___x_1221_ = l_Lean_Meta_addToCompletionBlackList(v_env_1209_, v___x_1195_);
v___x_1222_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 5, v___x_1222_);
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1224_ = v___x_1219_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_nextMacroScope_1210_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_ngen_1211_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_auxDeclNGen_1212_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_traceState_1213_);
lean_ctor_set(v_reuseFailAlloc_1276_, 5, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1276_, 6, v_recordedDeps_1214_);
lean_ctor_set(v_reuseFailAlloc_1276_, 7, v_messages_1215_);
lean_ctor_set(v_reuseFailAlloc_1276_, 8, v_infoState_1216_);
lean_ctor_set(v_reuseFailAlloc_1276_, 9, v_snapshotTasks_1217_);
v___x_1224_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_mctx_1227_; lean_object* v_zetaDeltaFVarIds_1228_; lean_object* v_postponed_1229_; lean_object* v_diag_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1274_; 
v___x_1225_ = lean_st_ref_put(v_a_1174_, v___x_1224_);
v___x_1226_ = lean_st_ref_take(v_a_1172_);
v_mctx_1227_ = lean_ctor_get(v___x_1226_, 0);
v_zetaDeltaFVarIds_1228_ = lean_ctor_get(v___x_1226_, 2);
v_postponed_1229_ = lean_ctor_get(v___x_1226_, 3);
v_diag_1230_ = lean_ctor_get(v___x_1226_, 4);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1226_, 1);
lean_dec(v_unused_1275_);
v___x_1232_ = v___x_1226_;
v_isShared_1233_ = v_isSharedCheck_1274_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_diag_1230_);
lean_inc(v_postponed_1229_);
lean_inc(v_zetaDeltaFVarIds_1228_);
lean_inc(v_mctx_1227_);
lean_dec(v___x_1226_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1274_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v___x_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_mctx_1227_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_zetaDeltaFVarIds_1228_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_postponed_1229_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_diag_1230_);
v___x_1236_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_env_1239_; lean_object* v_nextMacroScope_1240_; lean_object* v_ngen_1241_; lean_object* v_auxDeclNGen_1242_; lean_object* v_traceState_1243_; lean_object* v_recordedDeps_1244_; lean_object* v_messages_1245_; lean_object* v_infoState_1246_; lean_object* v_snapshotTasks_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1271_; 
v___x_1237_ = lean_st_ref_put(v_a_1172_, v___x_1236_);
v___x_1238_ = lean_st_ref_take(v_a_1174_);
v_env_1239_ = lean_ctor_get(v___x_1238_, 0);
v_nextMacroScope_1240_ = lean_ctor_get(v___x_1238_, 1);
v_ngen_1241_ = lean_ctor_get(v___x_1238_, 2);
v_auxDeclNGen_1242_ = lean_ctor_get(v___x_1238_, 3);
v_traceState_1243_ = lean_ctor_get(v___x_1238_, 4);
v_recordedDeps_1244_ = lean_ctor_get(v___x_1238_, 6);
v_messages_1245_ = lean_ctor_get(v___x_1238_, 7);
v_infoState_1246_ = lean_ctor_get(v___x_1238_, 8);
v_snapshotTasks_1247_ = lean_ctor_get(v___x_1238_, 9);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1238_, 5);
lean_dec(v_unused_1272_);
v___x_1249_ = v___x_1238_;
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snapshotTasks_1247_);
lean_inc(v_infoState_1246_);
lean_inc(v_messages_1245_);
lean_inc(v_recordedDeps_1244_);
lean_inc(v_traceState_1243_);
lean_inc(v_auxDeclNGen_1242_);
lean_inc(v_ngen_1241_);
lean_inc(v_nextMacroScope_1240_);
lean_inc(v_env_1239_);
lean_dec(v___x_1238_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
lean_inc(v___x_1195_);
v___x_1251_ = l_Lean_addProtected(v_env_1239_, v___x_1195_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 5, v___x_1222_);
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_nextMacroScope_1240_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_ngen_1241_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_auxDeclNGen_1242_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_traceState_1243_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1270_, 6, v_recordedDeps_1244_);
lean_ctor_set(v_reuseFailAlloc_1270_, 7, v_messages_1245_);
lean_ctor_set(v_reuseFailAlloc_1270_, 8, v_infoState_1246_);
lean_ctor_set(v_reuseFailAlloc_1270_, 9, v_snapshotTasks_1247_);
v___x_1253_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_mctx_1256_; lean_object* v_zetaDeltaFVarIds_1257_; lean_object* v_postponed_1258_; lean_object* v_diag_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
v___x_1254_ = lean_st_ref_put(v_a_1174_, v___x_1253_);
v___x_1255_ = lean_st_ref_take(v_a_1172_);
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
lean_ctor_set(v___x_1261_, 1, v___x_1234_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_mctx_1256_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_zetaDeltaFVarIds_1257_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_postponed_1258_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_diag_1259_);
v___x_1264_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_st_ref_put(v_a_1172_, v___x_1264_);
v___x_1266_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_1195_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
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
lean_dec(v___x_1195_);
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v___x_1195_);
lean_dec(v_a_1194_);
lean_dec(v_levelParams_1191_);
v_a_1281_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1196_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1196_);
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
lean_dec(v_levelParams_1191_);
lean_dec(v_indName_1170_);
v_a_1289_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1193_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1193_);
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
lean_dec_ref(v___f_1187_);
lean_dec(v_indName_1170_);
v_a_1297_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1189_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1189_);
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
lean_dec_ref(v_val_1182_);
lean_dec(v_indName_1170_);
v___x_1305_ = lean_box(0);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1305_);
v___x_1307_ = v___x_1180_;
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
lean_del_object(v___x_1180_);
lean_dec(v_a_1178_);
lean_dec(v_indName_1170_);
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2);
v___x_1310_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_1309_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
return v___x_1310_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_indName_1170_);
v_a_1312_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1177_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1177_);
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
uint8_t v___x_6242__boxed_1509_; uint8_t v___x_6243__boxed_1510_; uint8_t v___x_6244__boxed_1511_; lean_object* v_res_1512_; 
v___x_6242__boxed_1509_ = lean_unbox(v___x_1500_);
v___x_6243__boxed_1510_ = lean_unbox(v___x_1501_);
v___x_6244__boxed_1511_ = lean_unbox(v___x_1502_);
v_res_1512_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(v___x_1497_, v_k_1498_, v_zs_1499_, v___x_6242__boxed_1509_, v___x_6243__boxed_1510_, v___x_6244__boxed_1511_, v_h_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
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
uint8_t v___x_6291__boxed_1563_; uint8_t v___x_6292__boxed_1564_; uint8_t v___x_6293__boxed_1565_; lean_object* v_res_1566_; 
v___x_6291__boxed_1563_ = lean_unbox(v___x_1547_);
v___x_6292__boxed_1564_ = lean_unbox(v___x_1548_);
v___x_6293__boxed_1565_ = lean_unbox(v___x_1549_);
v_res_1566_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(v___x_1545_, v_k_1546_, v___x_6291__boxed_1563_, v___x_6292__boxed_1564_, v___x_6293__boxed_1565_, v___x_1550_, v___x_1551_, v___x_1552_, v___x_1553_, v_ctorIdx_1554_, v___x_1555_, v_zs_1556_, v___ctorRet_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
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
uint8_t v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_v_1591_; lean_object* v___x_1592_; lean_object* v_bs_x27_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1585_ = 0;
v___x_1586_ = 1;
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
v___x_1590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v_v_1591_ = lean_array_uget(v_bs_1577_, v_i_1576_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v_bs_x27_1593_ = lean_array_uset(v_bs_1577_, v_i_1576_, v___x_1592_);
v___x_1594_ = lean_usize_to_nat(v_i_1576_);
v___x_1595_ = lean_box(v___x_1585_);
v___x_1596_ = lean_box(v___x_1583_);
v___x_1597_ = lean_box(v___x_1586_);
lean_inc_ref(v_ctorIdx_1572_);
lean_inc_ref(v_k_1571_);
lean_inc_ref(v___x_1570_);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed), 18, 11);
lean_closure_set(v___f_1598_, 0, v___x_1570_);
lean_closure_set(v___f_1598_, 1, v_k_1571_);
lean_closure_set(v___f_1598_, 2, v___x_1595_);
lean_closure_set(v___f_1598_, 3, v___x_1596_);
lean_closure_set(v___f_1598_, 4, v___x_1597_);
lean_closure_set(v___f_1598_, 5, v___x_1587_);
lean_closure_set(v___f_1598_, 6, v___x_1588_);
lean_closure_set(v___f_1598_, 7, v___x_1594_);
lean_closure_set(v___f_1598_, 8, v___x_1589_);
lean_closure_set(v___f_1598_, 9, v_ctorIdx_1572_);
lean_closure_set(v___f_1598_, 10, v___x_1590_);
lean_inc(v_tail_1573_);
v___x_1599_ = l_Lean_mkConst(v_v_1591_, v_tail_1573_);
v___x_1600_ = l_Lean_mkAppN(v___x_1599_, v___x_1574_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
v___x_1601_ = lean_infer_type(v___x_1600_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_a_1602_, v___f_1598_, v___x_1585_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1605_ = ((size_t)1ULL);
v___x_1606_ = lean_usize_add(v_i_1576_, v___x_1605_);
v___x_1607_ = lean_array_uset(v_bs_x27_1593_, v_i_1576_, v_a_1604_);
v_i_1576_ = v___x_1606_;
v_bs_1577_ = v___x_1607_;
goto _start;
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec_ref(v_bs_x27_1593_);
lean_dec(v_tail_1573_);
lean_dec_ref(v_ctorIdx_1572_);
lean_dec_ref(v_k_1571_);
lean_dec_ref(v___x_1570_);
v_a_1609_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1603_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1603_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v___f_1598_);
lean_dec_ref(v_bs_x27_1593_);
lean_dec(v_tail_1573_);
lean_dec_ref(v_ctorIdx_1572_);
lean_dec_ref(v_k_1571_);
lean_dec_ref(v___x_1570_);
v_a_1617_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1601_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1601_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___boxed(lean_object* v___x_1625_, lean_object* v_k_1626_, lean_object* v_ctorIdx_1627_, lean_object* v_tail_1628_, lean_object* v___x_1629_, lean_object* v_sz_1630_, lean_object* v_i_1631_, lean_object* v_bs_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
size_t v_sz_boxed_1638_; size_t v_i_boxed_1639_; lean_object* v_res_1640_; 
v_sz_boxed_1638_ = lean_unbox_usize(v_sz_1630_);
lean_dec(v_sz_1630_);
v_i_boxed_1639_ = lean_unbox_usize(v_i_1631_);
lean_dec(v_i_1631_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1625_, v_k_1626_, v_ctorIdx_1627_, v_tail_1628_, v___x_1629_, v_sz_boxed_1638_, v_i_boxed_1639_, v_bs_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v___x_1629_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(lean_object* v___x_1641_, lean_object* v___x_1642_, lean_object* v_a_1643_, lean_object* v_name_1644_, lean_object* v___x_1645_, lean_object* v___x_1646_, lean_object* v_ctors_1647_, lean_object* v___x_1648_, lean_object* v_ctorIdx_1649_, lean_object* v_tail_1650_, lean_object* v_h_1651_, lean_object* v_k_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_inc_ref(v___x_1641_);
v___x_1658_ = l_Lean_mkAppN(v___x_1641_, v___x_1642_);
v___x_1659_ = l_Lean_mkArrow(v_a_1643_, v___x_1658_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; uint8_t v___x_1661_; uint8_t v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = 0;
v___x_1662_ = 1;
v___x_1663_ = 1;
v___x_1664_ = l_Lean_Meta_mkLambdaFVars(v___x_1642_, v_a_1660_, v___x_1661_, v___x_1662_, v___x_1661_, v___x_1662_, v___x_1663_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; size_t v_sz_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = l_Lean_mkConst(v_name_1644_, v___x_1645_);
v___x_1667_ = l_Lean_mkAppN(v___x_1666_, v___x_1646_);
v___x_1668_ = l_Lean_Expr_app___override(v___x_1667_, v_a_1665_);
v___x_1669_ = l_Lean_mkAppN(v___x_1668_, v___x_1642_);
v___x_1670_ = lean_array_mk(v_ctors_1647_);
v_sz_1671_ = lean_array_size(v___x_1670_);
v___x_1672_ = ((size_t)0ULL);
lean_inc_ref(v_ctorIdx_1649_);
lean_inc_ref(v_k_1652_);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_1648_, v_k_1652_, v_ctorIdx_1649_, v_tail_1650_, v___x_1646_, v_sz_1671_, v___x_1672_, v___x_1670_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1675_ = l_Lean_mkAppN(v___x_1669_, v_a_1674_);
lean_dec(v_a_1674_);
lean_inc_ref(v_h_1651_);
v___x_1676_ = l_Lean_Expr_app___override(v___x_1675_, v_h_1651_);
v___x_1677_ = lean_unsigned_to_nat(2u);
v___x_1678_ = lean_mk_empty_array_with_capacity(v___x_1677_);
lean_inc_ref(v___x_1678_);
v___x_1679_ = lean_array_push(v___x_1678_, v___x_1641_);
v___x_1680_ = lean_array_push(v___x_1679_, v_ctorIdx_1649_);
v___x_1681_ = l_Array_append___redArg(v___x_1646_, v___x_1680_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = l_Array_append___redArg(v___x_1681_, v___x_1642_);
v___x_1683_ = lean_array_push(v___x_1678_, v_h_1651_);
v___x_1684_ = lean_array_push(v___x_1683_, v_k_1652_);
v___x_1685_ = l_Array_append___redArg(v___x_1682_, v___x_1684_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l_Lean_Meta_mkLambdaFVars(v___x_1685_, v___x_1676_, v___x_1661_, v___x_1662_, v___x_1661_, v___x_1662_, v___x_1663_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec_ref(v___x_1685_);
return v___x_1686_;
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v___x_1669_);
lean_dec_ref(v_k_1652_);
lean_dec_ref(v_h_1651_);
lean_dec_ref(v_ctorIdx_1649_);
lean_dec_ref(v___x_1646_);
lean_dec_ref(v___x_1641_);
v_a_1687_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1673_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1673_);
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
else
{
lean_dec_ref(v_k_1652_);
lean_dec_ref(v_h_1651_);
lean_dec(v_tail_1650_);
lean_dec_ref(v_ctorIdx_1649_);
lean_dec_ref(v___x_1648_);
lean_dec(v_ctors_1647_);
lean_dec_ref(v___x_1646_);
lean_dec(v___x_1645_);
lean_dec(v_name_1644_);
lean_dec_ref(v___x_1641_);
return v___x_1664_;
}
}
else
{
lean_dec_ref(v_k_1652_);
lean_dec_ref(v_h_1651_);
lean_dec(v_tail_1650_);
lean_dec_ref(v_ctorIdx_1649_);
lean_dec_ref(v___x_1648_);
lean_dec(v_ctors_1647_);
lean_dec_ref(v___x_1646_);
lean_dec(v___x_1645_);
lean_dec(v_name_1644_);
lean_dec_ref(v___x_1641_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed(lean_object** _args){
lean_object* v___x_1695_ = _args[0];
lean_object* v___x_1696_ = _args[1];
lean_object* v_a_1697_ = _args[2];
lean_object* v_name_1698_ = _args[3];
lean_object* v___x_1699_ = _args[4];
lean_object* v___x_1700_ = _args[5];
lean_object* v_ctors_1701_ = _args[6];
lean_object* v___x_1702_ = _args[7];
lean_object* v_ctorIdx_1703_ = _args[8];
lean_object* v_tail_1704_ = _args[9];
lean_object* v_h_1705_ = _args[10];
lean_object* v_k_1706_ = _args[11];
lean_object* v___y_1707_ = _args[12];
lean_object* v___y_1708_ = _args[13];
lean_object* v___y_1709_ = _args[14];
lean_object* v___y_1710_ = _args[15];
lean_object* v___y_1711_ = _args[16];
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(v___x_1695_, v___x_1696_, v_a_1697_, v_name_1698_, v___x_1699_, v___x_1700_, v_ctors_1701_, v___x_1702_, v_ctorIdx_1703_, v_tail_1704_, v_h_1705_, v_k_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec_ref(v___x_1696_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(lean_object* v___x_1716_, lean_object* v___x_1717_, lean_object* v_a_1718_, lean_object* v_name_1719_, lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v_ctors_1722_, lean_object* v___x_1723_, lean_object* v_ctorIdx_1724_, lean_object* v_tail_1725_, lean_object* v___x_1726_, lean_object* v_h_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___f_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___f_1733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1733_, 0, v___x_1716_);
lean_closure_set(v___f_1733_, 1, v___x_1717_);
lean_closure_set(v___f_1733_, 2, v_a_1718_);
lean_closure_set(v___f_1733_, 3, v_name_1719_);
lean_closure_set(v___f_1733_, 4, v___x_1720_);
lean_closure_set(v___f_1733_, 5, v___x_1721_);
lean_closure_set(v___f_1733_, 6, v_ctors_1722_);
lean_closure_set(v___f_1733_, 7, v___x_1723_);
lean_closure_set(v___f_1733_, 8, v_ctorIdx_1724_);
lean_closure_set(v___f_1733_, 9, v_tail_1725_);
lean_closure_set(v___f_1733_, 10, v_h_1727_);
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1));
v___x_1735_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1734_, v___x_1726_, v___f_1733_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed(lean_object** _args){
lean_object* v___x_1736_ = _args[0];
lean_object* v___x_1737_ = _args[1];
lean_object* v_a_1738_ = _args[2];
lean_object* v_name_1739_ = _args[3];
lean_object* v___x_1740_ = _args[4];
lean_object* v___x_1741_ = _args[5];
lean_object* v_ctors_1742_ = _args[6];
lean_object* v___x_1743_ = _args[7];
lean_object* v_ctorIdx_1744_ = _args[8];
lean_object* v_tail_1745_ = _args[9];
lean_object* v___x_1746_ = _args[10];
lean_object* v_h_1747_ = _args[11];
lean_object* v___y_1748_ = _args[12];
lean_object* v___y_1749_ = _args[13];
lean_object* v___y_1750_ = _args[14];
lean_object* v___y_1751_ = _args[15];
lean_object* v___y_1752_ = _args[16];
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(v___x_1736_, v___x_1737_, v_a_1738_, v_name_1739_, v___x_1740_, v___x_1741_, v_ctors_1742_, v___x_1743_, v_ctorIdx_1744_, v_tail_1745_, v___x_1746_, v_h_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(lean_object* v___x_1754_, lean_object* v___x_1755_, lean_object* v___x_1756_, lean_object* v___x_1757_, lean_object* v_indName_1758_, lean_object* v_tail_1759_, lean_object* v___x_1760_, lean_object* v_name_1761_, lean_object* v_ctors_1762_, lean_object* v_ctorIdx_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_inc(v___x_1755_);
v___x_1769_ = l_Lean_mkConst(v___x_1754_, v___x_1755_);
lean_inc_ref(v___x_1757_);
lean_inc_ref_n(v___x_1756_, 2);
v___x_1770_ = lean_array_push(v___x_1756_, v___x_1757_);
v___x_1771_ = l_Lean_mkAppN(v___x_1769_, v___x_1770_);
lean_dec_ref(v___x_1770_);
lean_inc_ref_n(v_ctorIdx_1763_, 2);
lean_inc_ref(v___x_1771_);
v___x_1772_ = l_Lean_Expr_app___override(v___x_1771_, v_ctorIdx_1763_);
v___x_1773_ = l_Lean_mkCtorIdxName(v_indName_1758_);
lean_inc(v_tail_1759_);
v___x_1774_ = l_Lean_mkConst(v___x_1773_, v_tail_1759_);
v___x_1775_ = l_Array_append___redArg(v___x_1756_, v___x_1760_);
v___x_1776_ = l_Lean_mkAppN(v___x_1774_, v___x_1775_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = l_Lean_Meta_mkEq(v_ctorIdx_1763_, v___x_1776_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___f_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc_n(v_a_1778_, 2);
lean_dec_ref_known(v___x_1777_, 1);
v___f_1779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed), 17, 11);
lean_closure_set(v___f_1779_, 0, v___x_1757_);
lean_closure_set(v___f_1779_, 1, v___x_1760_);
lean_closure_set(v___f_1779_, 2, v_a_1778_);
lean_closure_set(v___f_1779_, 3, v_name_1761_);
lean_closure_set(v___f_1779_, 4, v___x_1755_);
lean_closure_set(v___f_1779_, 5, v___x_1756_);
lean_closure_set(v___f_1779_, 6, v_ctors_1762_);
lean_closure_set(v___f_1779_, 7, v___x_1771_);
lean_closure_set(v___f_1779_, 8, v_ctorIdx_1763_);
lean_closure_set(v___f_1779_, 9, v_tail_1759_);
lean_closure_set(v___f_1779_, 10, v___x_1772_);
v___x_1780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_1781_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1780_, v_a_1778_, v___f_1779_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1781_;
}
else
{
lean_dec_ref(v___x_1772_);
lean_dec_ref(v___x_1771_);
lean_dec_ref(v_ctorIdx_1763_);
lean_dec(v_ctors_1762_);
lean_dec(v_name_1761_);
lean_dec_ref(v___x_1760_);
lean_dec(v_tail_1759_);
lean_dec_ref(v___x_1757_);
lean_dec_ref(v___x_1756_);
lean_dec(v___x_1755_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed(lean_object* v___x_1782_, lean_object* v___x_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v_indName_1786_, lean_object* v_tail_1787_, lean_object* v___x_1788_, lean_object* v_name_1789_, lean_object* v_ctors_1790_, lean_object* v_ctorIdx_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(v___x_1782_, v___x_1783_, v___x_1784_, v___x_1785_, v_indName_1786_, v_tail_1787_, v___x_1788_, v_name_1789_, v_ctors_1790_, v_ctorIdx_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(lean_object* v_val_1798_, lean_object* v___x_1799_, lean_object* v___x_1800_, lean_object* v___x_1801_, lean_object* v_indName_1802_, lean_object* v_tail_1803_, lean_object* v_name_1804_, lean_object* v___x_1805_, lean_object* v_xs_1806_, lean_object* v_x_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_numParams_1813_; lean_object* v_numIndices_1814_; lean_object* v_ctors_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___f_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_numParams_1813_ = lean_ctor_get(v_val_1798_, 1);
lean_inc_n(v_numParams_1813_, 2);
v_numIndices_1814_ = lean_ctor_get(v_val_1798_, 2);
lean_inc(v_numIndices_1814_);
v_ctors_1815_ = lean_ctor_get(v_val_1798_, 4);
lean_inc(v_ctors_1815_);
lean_dec_ref(v_val_1798_);
v___x_1816_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_1806_, 2);
v___x_1817_ = l_Array_toSubarray___redArg(v_xs_1806_, v___x_1816_, v_numParams_1813_);
v___x_1818_ = l_Subarray_copy___redArg(v___x_1817_);
v___x_1819_ = lean_array_get(v___x_1799_, v_xs_1806_, v_numParams_1813_);
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = lean_nat_add(v_numParams_1813_, v___x_1820_);
lean_dec(v_numParams_1813_);
v___x_1822_ = lean_nat_add(v___x_1821_, v_numIndices_1814_);
lean_dec(v_numIndices_1814_);
lean_inc(v___x_1822_);
v___x_1823_ = l_Array_toSubarray___redArg(v_xs_1806_, v___x_1821_, v___x_1822_);
v___x_1824_ = l_Subarray_copy___redArg(v___x_1823_);
v___x_1825_ = lean_array_get(v___x_1799_, v_xs_1806_, v___x_1822_);
lean_dec(v___x_1822_);
lean_dec_ref(v_xs_1806_);
v___x_1826_ = lean_array_push(v___x_1824_, v___x_1825_);
v___f_1827_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed), 15, 9);
lean_closure_set(v___f_1827_, 0, v___x_1800_);
lean_closure_set(v___f_1827_, 1, v___x_1801_);
lean_closure_set(v___f_1827_, 2, v___x_1818_);
lean_closure_set(v___f_1827_, 3, v___x_1819_);
lean_closure_set(v___f_1827_, 4, v_indName_1802_);
lean_closure_set(v___f_1827_, 5, v_tail_1803_);
lean_closure_set(v___f_1827_, 6, v___x_1826_);
lean_closure_set(v___f_1827_, 7, v_name_1804_);
lean_closure_set(v___f_1827_, 8, v_ctors_1815_);
v___x_1828_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1));
v___x_1829_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3));
v___x_1830_ = l_Lean_mkConst(v___x_1829_, v___x_1805_);
v___x_1831_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_1828_, v___x_1830_, v___f_1827_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed(lean_object* v_val_1832_, lean_object* v___x_1833_, lean_object* v___x_1834_, lean_object* v___x_1835_, lean_object* v_indName_1836_, lean_object* v_tail_1837_, lean_object* v_name_1838_, lean_object* v___x_1839_, lean_object* v_xs_1840_, lean_object* v_x_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(v_val_1832_, v___x_1833_, v___x_1834_, v___x_1835_, v_indName_1836_, v_tail_1837_, v_name_1838_, v___x_1839_, v_xs_1840_, v_x_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec_ref(v_x_1841_);
lean_dec_ref(v___x_1833_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
if (lean_obj_tag(v_a_1848_) == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = l_List_reverse___redArg(v_a_1849_);
return v___x_1850_;
}
else
{
lean_object* v_head_1851_; lean_object* v_tail_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1861_; 
v_head_1851_ = lean_ctor_get(v_a_1848_, 0);
v_tail_1852_ = lean_ctor_get(v_a_1848_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_a_1848_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1854_ = v_a_1848_;
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_tail_1852_);
lean_inc(v_head_1851_);
lean_dec(v_a_1848_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1856_ = l_Lean_mkLevelParam(v_head_1851_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 1, v_a_1849_);
lean_ctor_set(v___x_1854_, 0, v___x_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_a_1849_);
v___x_1858_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
v_a_1848_ = v_tail_1852_;
v_a_1849_ = v___x_1858_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_1865_ = lean_unsigned_to_nat(58u);
v___x_1866_ = lean_unsigned_to_nat(113u);
v___x_1867_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1869_ = l_mkPanicMessageWithDecl(v___x_1868_, v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1869_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1870_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_1871_ = lean_unsigned_to_nat(60u);
v___x_1872_ = lean_unsigned_to_nat(109u);
v___x_1873_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0));
v___x_1874_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_1875_ = l_mkPanicMessageWithDecl(v___x_1874_, v___x_1873_, v___x_1872_, v___x_1871_, v___x_1870_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(lean_object* v_indName_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_1876_);
v___x_1883_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
if (lean_obj_tag(v_a_1884_) == 5)
{
lean_object* v_val_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_val_1885_ = lean_ctor_get(v_a_1884_, 0);
lean_inc_ref(v_val_1885_);
lean_dec_ref_known(v_a_1884_, 1);
lean_inc_n(v_indName_1876_, 2);
v___x_1886_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_1876_);
v___x_1887_ = l_Lean_mkCasesOnName(v_indName_1876_);
v___x_1888_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_1887_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v_name_1890_; lean_object* v_levelParams_1891_; lean_object* v_type_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v_name_1890_ = lean_ctor_get(v_a_1889_, 0);
lean_inc(v_name_1890_);
v_levelParams_1891_ = lean_ctor_get(v_a_1889_, 1);
lean_inc_n(v_levelParams_1891_, 2);
v_type_1892_ = lean_ctor_get(v_a_1889_, 2);
lean_inc_ref(v_type_1892_);
lean_dec(v_a_1889_);
v___x_1893_ = lean_box(0);
v___x_1894_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_1891_, v___x_1893_);
if (lean_obj_tag(v___x_1894_) == 1)
{
lean_object* v_tail_1895_; lean_object* v___f_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; 
v_tail_1895_ = lean_ctor_get(v___x_1894_, 1);
lean_inc(v_tail_1895_);
lean_inc(v_indName_1876_);
v___f_1896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed), 15, 8);
lean_closure_set(v___f_1896_, 0, v_val_1885_);
lean_closure_set(v___f_1896_, 1, v___x_1882_);
lean_closure_set(v___f_1896_, 2, v___x_1886_);
lean_closure_set(v___f_1896_, 3, v___x_1894_);
lean_closure_set(v___f_1896_, 4, v_indName_1876_);
lean_closure_set(v___f_1896_, 5, v_tail_1895_);
lean_closure_set(v___f_1896_, 6, v_name_1890_);
lean_closure_set(v___f_1896_, 7, v___x_1893_);
v___x_1897_ = 0;
v___x_1898_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_1892_, v___f_1896_, v___x_1897_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc_n(v_a_1899_, 2);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = l_Lean_mkCtorElimName(v_indName_1876_);
lean_inc(v_a_1880_);
lean_inc_ref(v_a_1879_);
lean_inc(v_a_1878_);
lean_inc_ref(v_a_1877_);
v___x_1901_ = lean_infer_type(v_a_1899_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_2019_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = lean_box(1);
lean_inc(v___x_1900_);
v___x_1904_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_1900_, v_levelParams_1891_, v_a_1902_, v_a_1899_, v___x_1903_, v_a_1880_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_2019_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_2019_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 1);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_2018_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
uint8_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = 1;
v___x_1912_ = l_Lean_addAndCompile(v___x_1910_, v___x_1911_, v___x_1897_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; lean_object* v_env_1914_; lean_object* v_nextMacroScope_1915_; lean_object* v_ngen_1916_; lean_object* v_auxDeclNGen_1917_; lean_object* v_traceState_1918_; lean_object* v_recordedDeps_1919_; lean_object* v_messages_1920_; lean_object* v_infoState_1921_; lean_object* v_snapshotTasks_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref_known(v___x_1912_, 1);
v___x_1913_ = lean_st_ref_take(v_a_1880_);
v_env_1914_ = lean_ctor_get(v___x_1913_, 0);
v_nextMacroScope_1915_ = lean_ctor_get(v___x_1913_, 1);
v_ngen_1916_ = lean_ctor_get(v___x_1913_, 2);
v_auxDeclNGen_1917_ = lean_ctor_get(v___x_1913_, 3);
v_traceState_1918_ = lean_ctor_get(v___x_1913_, 4);
v_recordedDeps_1919_ = lean_ctor_get(v___x_1913_, 6);
v_messages_1920_ = lean_ctor_get(v___x_1913_, 7);
v_infoState_1921_ = lean_ctor_get(v___x_1913_, 8);
v_snapshotTasks_1922_ = lean_ctor_get(v___x_1913_, 9);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v___x_1913_, 5);
lean_dec(v_unused_2017_);
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_2016_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snapshotTasks_1922_);
lean_inc(v_infoState_1921_);
lean_inc(v_messages_1920_);
lean_inc(v_recordedDeps_1919_);
lean_inc(v_traceState_1918_);
lean_inc(v_auxDeclNGen_1917_);
lean_inc(v_ngen_1916_);
lean_inc(v_nextMacroScope_1915_);
lean_inc(v_env_1914_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_2016_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
lean_inc(v___x_1900_);
v___x_1926_ = l_Lean_markAuxRecursor(v_env_1914_, v___x_1900_);
v___x_1927_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 5, v___x_1927_);
lean_ctor_set(v___x_1924_, 0, v___x_1926_);
v___x_1929_ = v___x_1924_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_nextMacroScope_1915_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_ngen_1916_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_auxDeclNGen_1917_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_traceState_1918_);
lean_ctor_set(v_reuseFailAlloc_2015_, 5, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_2015_, 6, v_recordedDeps_1919_);
lean_ctor_set(v_reuseFailAlloc_2015_, 7, v_messages_1920_);
lean_ctor_set(v_reuseFailAlloc_2015_, 8, v_infoState_1921_);
lean_ctor_set(v_reuseFailAlloc_2015_, 9, v_snapshotTasks_1922_);
v___x_1929_ = v_reuseFailAlloc_2015_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v_mctx_1932_; lean_object* v_zetaDeltaFVarIds_1933_; lean_object* v_postponed_1934_; lean_object* v_diag_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_2013_; 
v___x_1930_ = lean_st_ref_put(v_a_1880_, v___x_1929_);
v___x_1931_ = lean_st_ref_take(v_a_1878_);
v_mctx_1932_ = lean_ctor_get(v___x_1931_, 0);
v_zetaDeltaFVarIds_1933_ = lean_ctor_get(v___x_1931_, 2);
v_postponed_1934_ = lean_ctor_get(v___x_1931_, 3);
v_diag_1935_ = lean_ctor_get(v___x_1931_, 4);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v___x_1931_, 1);
lean_dec(v_unused_2014_);
v___x_1937_ = v___x_1931_;
v_isShared_1938_ = v_isSharedCheck_2013_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_diag_1935_);
lean_inc(v_postponed_1934_);
lean_inc(v_zetaDeltaFVarIds_1933_);
lean_inc(v_mctx_1932_);
lean_dec(v___x_1931_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_2013_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___x_1939_);
v___x_1941_ = v___x_1937_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_mctx_1932_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_zetaDeltaFVarIds_1933_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_postponed_1934_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_diag_1935_);
v___x_1941_ = v_reuseFailAlloc_2012_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_env_1944_; lean_object* v_nextMacroScope_1945_; lean_object* v_ngen_1946_; lean_object* v_auxDeclNGen_1947_; lean_object* v_traceState_1948_; lean_object* v_recordedDeps_1949_; lean_object* v_messages_1950_; lean_object* v_infoState_1951_; lean_object* v_snapshotTasks_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_2010_; 
v___x_1942_ = lean_st_ref_put(v_a_1878_, v___x_1941_);
v___x_1943_ = lean_st_ref_take(v_a_1880_);
v_env_1944_ = lean_ctor_get(v___x_1943_, 0);
v_nextMacroScope_1945_ = lean_ctor_get(v___x_1943_, 1);
v_ngen_1946_ = lean_ctor_get(v___x_1943_, 2);
v_auxDeclNGen_1947_ = lean_ctor_get(v___x_1943_, 3);
v_traceState_1948_ = lean_ctor_get(v___x_1943_, 4);
v_recordedDeps_1949_ = lean_ctor_get(v___x_1943_, 6);
v_messages_1950_ = lean_ctor_get(v___x_1943_, 7);
v_infoState_1951_ = lean_ctor_get(v___x_1943_, 8);
v_snapshotTasks_1952_ = lean_ctor_get(v___x_1943_, 9);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v___x_1943_, 5);
lean_dec(v_unused_2011_);
v___x_1954_ = v___x_1943_;
v_isShared_1955_ = v_isSharedCheck_2010_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_snapshotTasks_1952_);
lean_inc(v_infoState_1951_);
lean_inc(v_messages_1950_);
lean_inc(v_recordedDeps_1949_);
lean_inc(v_traceState_1948_);
lean_inc(v_auxDeclNGen_1947_);
lean_inc(v_ngen_1946_);
lean_inc(v_nextMacroScope_1945_);
lean_inc(v_env_1944_);
lean_dec(v___x_1943_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_2010_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
lean_inc(v___x_1900_);
v___x_1956_ = l_Lean_Meta_addToCompletionBlackList(v_env_1944_, v___x_1900_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 5, v___x_1927_);
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_nextMacroScope_1945_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_ngen_1946_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_auxDeclNGen_1947_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_traceState_1948_);
lean_ctor_set(v_reuseFailAlloc_2009_, 5, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_2009_, 6, v_recordedDeps_1949_);
lean_ctor_set(v_reuseFailAlloc_2009_, 7, v_messages_1950_);
lean_ctor_set(v_reuseFailAlloc_2009_, 8, v_infoState_1951_);
lean_ctor_set(v_reuseFailAlloc_2009_, 9, v_snapshotTasks_1952_);
v___x_1958_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v_mctx_1961_; lean_object* v_zetaDeltaFVarIds_1962_; lean_object* v_postponed_1963_; lean_object* v_diag_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_2007_; 
v___x_1959_ = lean_st_ref_put(v_a_1880_, v___x_1958_);
v___x_1960_ = lean_st_ref_take(v_a_1878_);
v_mctx_1961_ = lean_ctor_get(v___x_1960_, 0);
v_zetaDeltaFVarIds_1962_ = lean_ctor_get(v___x_1960_, 2);
v_postponed_1963_ = lean_ctor_get(v___x_1960_, 3);
v_diag_1964_ = lean_ctor_get(v___x_1960_, 4);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v___x_1960_, 1);
lean_dec(v_unused_2008_);
v___x_1966_ = v___x_1960_;
v_isShared_1967_ = v_isSharedCheck_2007_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_diag_1964_);
lean_inc(v_postponed_1963_);
lean_inc(v_zetaDeltaFVarIds_1962_);
lean_inc(v_mctx_1961_);
lean_dec(v___x_1960_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_2007_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v___x_1939_);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_mctx_1961_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_zetaDeltaFVarIds_1962_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_postponed_1963_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_diag_1964_);
v___x_1969_ = v_reuseFailAlloc_2006_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v_env_1972_; lean_object* v_nextMacroScope_1973_; lean_object* v_ngen_1974_; lean_object* v_auxDeclNGen_1975_; lean_object* v_traceState_1976_; lean_object* v_recordedDeps_1977_; lean_object* v_messages_1978_; lean_object* v_infoState_1979_; lean_object* v_snapshotTasks_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2004_; 
v___x_1970_ = lean_st_ref_put(v_a_1878_, v___x_1969_);
v___x_1971_ = lean_st_ref_take(v_a_1880_);
v_env_1972_ = lean_ctor_get(v___x_1971_, 0);
v_nextMacroScope_1973_ = lean_ctor_get(v___x_1971_, 1);
v_ngen_1974_ = lean_ctor_get(v___x_1971_, 2);
v_auxDeclNGen_1975_ = lean_ctor_get(v___x_1971_, 3);
v_traceState_1976_ = lean_ctor_get(v___x_1971_, 4);
v_recordedDeps_1977_ = lean_ctor_get(v___x_1971_, 6);
v_messages_1978_ = lean_ctor_get(v___x_1971_, 7);
v_infoState_1979_ = lean_ctor_get(v___x_1971_, 8);
v_snapshotTasks_1980_ = lean_ctor_get(v___x_1971_, 9);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1971_, 5);
lean_dec(v_unused_2005_);
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_2004_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_snapshotTasks_1980_);
lean_inc(v_infoState_1979_);
lean_inc(v_messages_1978_);
lean_inc(v_recordedDeps_1977_);
lean_inc(v_traceState_1976_);
lean_inc(v_auxDeclNGen_1975_);
lean_inc(v_ngen_1974_);
lean_inc(v_nextMacroScope_1973_);
lean_inc(v_env_1972_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2004_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
lean_inc(v___x_1900_);
v___x_1984_ = l_Lean_addProtected(v_env_1972_, v___x_1900_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 5, v___x_1927_);
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_nextMacroScope_1973_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_ngen_1974_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_auxDeclNGen_1975_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_traceState_1976_);
lean_ctor_set(v_reuseFailAlloc_2003_, 5, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_2003_, 6, v_recordedDeps_1977_);
lean_ctor_set(v_reuseFailAlloc_2003_, 7, v_messages_1978_);
lean_ctor_set(v_reuseFailAlloc_2003_, 8, v_infoState_1979_);
lean_ctor_set(v_reuseFailAlloc_2003_, 9, v_snapshotTasks_1980_);
v___x_1986_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v_mctx_1989_; lean_object* v_zetaDeltaFVarIds_1990_; lean_object* v_postponed_1991_; lean_object* v_diag_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2001_; 
v___x_1987_ = lean_st_ref_put(v_a_1880_, v___x_1986_);
v___x_1988_ = lean_st_ref_take(v_a_1878_);
v_mctx_1989_ = lean_ctor_get(v___x_1988_, 0);
v_zetaDeltaFVarIds_1990_ = lean_ctor_get(v___x_1988_, 2);
v_postponed_1991_ = lean_ctor_get(v___x_1988_, 3);
v_diag_1992_ = lean_ctor_get(v___x_1988_, 4);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v___x_1988_, 1);
lean_dec(v_unused_2002_);
v___x_1994_ = v___x_1988_;
v_isShared_1995_ = v_isSharedCheck_2001_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_diag_1992_);
lean_inc(v_postponed_1991_);
lean_inc(v_zetaDeltaFVarIds_1990_);
lean_inc(v_mctx_1989_);
lean_dec(v___x_1988_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2001_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 1, v___x_1939_);
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_mctx_1989_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_zetaDeltaFVarIds_1990_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_postponed_1991_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_diag_1992_);
v___x_1997_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_st_ref_put(v_a_1878_, v___x_1997_);
v___x_1999_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_1900_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1999_;
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
lean_dec(v___x_1900_);
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v___x_1900_);
lean_dec(v_a_1899_);
lean_dec(v_levelParams_1891_);
v_a_2020_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1901_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1901_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_levelParams_1891_);
lean_dec(v_indName_1876_);
v_a_2028_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_1898_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_1898_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec(v___x_1894_);
lean_dec_ref(v_type_1892_);
lean_dec(v_levelParams_1891_);
lean_dec(v_name_1890_);
lean_dec(v___x_1886_);
lean_dec_ref(v_val_1885_);
lean_dec(v_indName_1876_);
v___x_2036_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2);
v___x_2037_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2036_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_2037_;
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v___x_1886_);
lean_dec_ref(v_val_1885_);
lean_dec(v_indName_1876_);
v_a_2038_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_1888_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_1888_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v_a_1884_);
lean_dec(v_indName_1876_);
v___x_2046_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3);
v___x_2047_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2046_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_2047_;
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_indName_1876_);
v_a_2048_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_1883_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_1883_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___boxed(lean_object* v_indName_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(lean_object* v___x_2063_, lean_object* v_k_2064_, lean_object* v_ctorIdx_2065_, lean_object* v_tail_2066_, lean_object* v___x_2067_, lean_object* v_as_2068_, size_t v_sz_2069_, size_t v_i_2070_, lean_object* v_bs_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_2063_, v_k_2064_, v_ctorIdx_2065_, v_tail_2066_, v___x_2067_, v_sz_2069_, v_i_2070_, v_bs_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___boxed(lean_object* v___x_2078_, lean_object* v_k_2079_, lean_object* v_ctorIdx_2080_, lean_object* v_tail_2081_, lean_object* v___x_2082_, lean_object* v_as_2083_, lean_object* v_sz_2084_, lean_object* v_i_2085_, lean_object* v_bs_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
size_t v_sz_boxed_2092_; size_t v_i_boxed_2093_; lean_object* v_res_2094_; 
v_sz_boxed_2092_ = lean_unbox_usize(v_sz_2084_);
lean_dec(v_sz_2084_);
v_i_boxed_2093_ = lean_unbox_usize(v_i_2085_);
lean_dec(v_i_2085_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(v___x_2078_, v_k_2079_, v_ctorIdx_2080_, v_tail_2081_, v___x_2082_, v_as_2083_, v_sz_boxed_2092_, v_i_boxed_2093_, v_bs_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_as_2083_);
lean_dec_ref(v___x_2082_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v___x_2099_, lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v___f_2102_, lean_object* v___x_2103_, lean_object* v___y_2104_, uint8_t v___x_2105_, lean_object* v_h_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_inc(v___x_2096_);
v___x_2112_ = l_Lean_mkConst(v___x_2095_, v___x_2096_);
v___x_2113_ = l_Lean_mkAppN(v___x_2112_, v___x_2097_);
lean_inc_ref(v___x_2098_);
v___x_2114_ = l_Lean_Expr_app___override(v___x_2113_, v___x_2098_);
lean_inc_ref(v___x_2099_);
v___x_2115_ = l_Lean_Expr_app___override(v___x_2114_, v___x_2099_);
v___x_2116_ = l_Lean_mkAppN(v___x_2115_, v___x_2100_);
lean_inc_ref(v_h_2106_);
v___x_2117_ = l_Lean_Meta_mkEqSymm(v_h_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2119_ = l_Lean_Expr_app___override(v___x_2116_, v_a_2118_);
v___x_2120_ = l_Lean_mkConst(v___x_2101_, v___x_2096_);
lean_inc_ref(v___x_2098_);
lean_inc_ref(v___x_2097_);
v___x_2121_ = lean_array_push(v___x_2097_, v___x_2098_);
v___x_2122_ = lean_array_push(v___x_2121_, v___x_2099_);
v___x_2123_ = l_Lean_mkAppN(v___x_2120_, v___x_2122_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(v___x_2123_, v___f_2102_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = l_Lean_Expr_app___override(v___x_2119_, v_a_2125_);
v___x_2127_ = lean_mk_empty_array_with_capacity(v___x_2103_);
v___x_2128_ = lean_array_push(v___x_2127_, v___x_2098_);
v___x_2129_ = l_Array_append___redArg(v___x_2097_, v___x_2128_);
lean_dec_ref(v___x_2128_);
v___x_2130_ = l_Array_append___redArg(v___x_2129_, v___x_2100_);
v___x_2131_ = lean_unsigned_to_nat(2u);
v___x_2132_ = lean_mk_empty_array_with_capacity(v___x_2131_);
v___x_2133_ = lean_array_push(v___x_2132_, v_h_2106_);
v___x_2134_ = lean_array_push(v___x_2133_, v___y_2104_);
v___x_2135_ = l_Array_append___redArg(v___x_2130_, v___x_2134_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = 0;
v___x_2137_ = 1;
v___x_2138_ = l_Lean_Meta_mkLambdaFVars(v___x_2135_, v___x_2126_, v___x_2136_, v___x_2105_, v___x_2136_, v___x_2105_, v___x_2137_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec_ref(v___x_2135_);
return v___x_2138_;
}
else
{
lean_dec_ref(v___x_2119_);
lean_dec_ref(v_h_2106_);
lean_dec_ref(v___y_2104_);
lean_dec_ref(v___x_2098_);
lean_dec_ref(v___x_2097_);
return v___x_2124_;
}
}
else
{
lean_dec_ref(v___x_2116_);
lean_dec_ref(v_h_2106_);
lean_dec_ref(v___y_2104_);
lean_dec_ref(v___f_2102_);
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2099_);
lean_dec_ref(v___x_2098_);
lean_dec_ref(v___x_2097_);
lean_dec(v___x_2096_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_2139_ = _args[0];
lean_object* v___x_2140_ = _args[1];
lean_object* v___x_2141_ = _args[2];
lean_object* v___x_2142_ = _args[3];
lean_object* v___x_2143_ = _args[4];
lean_object* v___x_2144_ = _args[5];
lean_object* v___x_2145_ = _args[6];
lean_object* v___f_2146_ = _args[7];
lean_object* v___x_2147_ = _args[8];
lean_object* v___y_2148_ = _args[9];
lean_object* v___x_2149_ = _args[10];
lean_object* v_h_2150_ = _args[11];
lean_object* v___y_2151_ = _args[12];
lean_object* v___y_2152_ = _args[13];
lean_object* v___y_2153_ = _args[14];
lean_object* v___y_2154_ = _args[15];
lean_object* v___y_2155_ = _args[16];
_start:
{
uint8_t v___x_10314__boxed_2156_; lean_object* v_res_2157_; 
v___x_10314__boxed_2156_ = lean_unbox(v___x_2149_);
v_res_2157_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(v___x_2139_, v___x_2140_, v___x_2141_, v___x_2142_, v___x_2143_, v___x_2144_, v___x_2145_, v___f_2146_, v___x_2147_, v___y_2148_, v___x_10314__boxed_2156_, v_h_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___x_2147_);
lean_dec_ref(v___x_2144_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(lean_object* v___y_2158_, lean_object* v_x_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___y_2158_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2166_, lean_object* v_x_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(v___y_2166_, v_x_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec_ref(v_x_2167_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(lean_object* v___x_2174_, lean_object* v_numParams_2175_, lean_object* v___x_2176_, lean_object* v___x_2177_, lean_object* v_numIndices_2178_, lean_object* v_indName_2179_, lean_object* v_tail_2180_, lean_object* v_i_2181_, lean_object* v___x_2182_, lean_object* v___x_2183_, lean_object* v___x_2184_, uint8_t v___x_2185_, lean_object* v_xs_2186_, lean_object* v_x_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v_start_2202_; lean_object* v_stop_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___y_2208_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
lean_inc(v_numParams_2175_);
lean_inc_ref_n(v_xs_2186_, 2);
v___x_2193_ = l_Array_toSubarray___redArg(v_xs_2186_, v___x_2174_, v_numParams_2175_);
v___x_2194_ = lean_array_get(v___x_2176_, v_xs_2186_, v_numParams_2175_);
v___x_2195_ = lean_nat_add(v_numParams_2175_, v___x_2177_);
lean_dec(v_numParams_2175_);
v___x_2196_ = lean_nat_add(v___x_2195_, v_numIndices_2178_);
lean_inc(v___x_2196_);
v___x_2197_ = l_Array_toSubarray___redArg(v_xs_2186_, v___x_2195_, v___x_2196_);
v___x_2198_ = lean_array_get(v___x_2176_, v_xs_2186_, v___x_2196_);
v___x_2199_ = lean_nat_add(v___x_2196_, v___x_2177_);
lean_dec(v___x_2196_);
v___x_2200_ = lean_array_get_size(v_xs_2186_);
v___x_2201_ = l_Array_toSubarray___redArg(v_xs_2186_, v___x_2199_, v___x_2200_);
v_start_2202_ = lean_ctor_get(v___x_2201_, 1);
v_stop_2203_ = lean_ctor_get(v___x_2201_, 2);
v___x_2204_ = l_Subarray_copy___redArg(v___x_2193_);
v___x_2205_ = l_Subarray_copy___redArg(v___x_2197_);
v___x_2206_ = lean_array_push(v___x_2205_, v___x_2198_);
v___x_2221_ = lean_nat_sub(v_stop_2203_, v_start_2202_);
v___x_2222_ = lean_nat_dec_lt(v_i_2181_, v___x_2221_);
lean_dec(v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec_ref(v___x_2201_);
v___x_2223_ = l_outOfBounds___redArg(v___x_2176_);
v___y_2208_ = v___x_2223_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Subarray_get___redArg(v___x_2201_, v_i_2181_);
lean_dec_ref(v___x_2201_);
v___y_2208_ = v___x_2224_;
goto v___jp_2207_;
}
v___jp_2207_:
{
lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___f_2216_; lean_object* v___x_2217_; 
lean_inc_ref(v___y_2208_);
v___f_2209_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2209_, 0, v___y_2208_);
v___x_2210_ = l_Lean_mkCtorIdxName(v_indName_2179_);
v___x_2211_ = l_Lean_mkConst(v___x_2210_, v_tail_2180_);
lean_inc_ref(v___x_2204_);
v___x_2212_ = l_Array_append___redArg(v___x_2204_, v___x_2206_);
v___x_2213_ = l_Lean_mkAppN(v___x_2211_, v___x_2212_);
lean_dec_ref(v___x_2212_);
v___x_2214_ = l_Lean_mkRawNatLit(v_i_2181_);
v___x_2215_ = lean_box(v___x_2185_);
lean_inc_ref(v___x_2214_);
v___f_2216_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed), 17, 11);
lean_closure_set(v___f_2216_, 0, v___x_2182_);
lean_closure_set(v___f_2216_, 1, v___x_2183_);
lean_closure_set(v___f_2216_, 2, v___x_2204_);
lean_closure_set(v___f_2216_, 3, v___x_2194_);
lean_closure_set(v___f_2216_, 4, v___x_2214_);
lean_closure_set(v___f_2216_, 5, v___x_2206_);
lean_closure_set(v___f_2216_, 6, v___x_2184_);
lean_closure_set(v___f_2216_, 7, v___f_2209_);
lean_closure_set(v___f_2216_, 8, v___x_2177_);
lean_closure_set(v___f_2216_, 9, v___y_2208_);
lean_closure_set(v___f_2216_, 10, v___x_2215_);
v___x_2217_ = l_Lean_Meta_mkEq(v___x_2213_, v___x_2214_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1));
v___x_2220_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___redArg(v___x_2219_, v_a_2218_, v___f_2216_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
return v___x_2220_;
}
else
{
lean_dec_ref(v___f_2216_);
return v___x_2217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2225_ = _args[0];
lean_object* v_numParams_2226_ = _args[1];
lean_object* v___x_2227_ = _args[2];
lean_object* v___x_2228_ = _args[3];
lean_object* v_numIndices_2229_ = _args[4];
lean_object* v_indName_2230_ = _args[5];
lean_object* v_tail_2231_ = _args[6];
lean_object* v_i_2232_ = _args[7];
lean_object* v___x_2233_ = _args[8];
lean_object* v___x_2234_ = _args[9];
lean_object* v___x_2235_ = _args[10];
lean_object* v___x_2236_ = _args[11];
lean_object* v_xs_2237_ = _args[12];
lean_object* v_x_2238_ = _args[13];
lean_object* v___y_2239_ = _args[14];
lean_object* v___y_2240_ = _args[15];
lean_object* v___y_2241_ = _args[16];
lean_object* v___y_2242_ = _args[17];
lean_object* v___y_2243_ = _args[18];
_start:
{
uint8_t v___x_10441__boxed_2244_; lean_object* v_res_2245_; 
v___x_10441__boxed_2244_ = lean_unbox(v___x_2236_);
v_res_2245_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(v___x_2225_, v_numParams_2226_, v___x_2227_, v___x_2228_, v_numIndices_2229_, v_indName_2230_, v_tail_2231_, v_i_2232_, v___x_2233_, v___x_2234_, v___x_2235_, v___x_10441__boxed_2244_, v_xs_2237_, v_x_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v_x_2238_);
lean_dec(v_numIndices_2229_);
lean_dec_ref(v___x_2227_);
return v_res_2245_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0));
v___x_2248_ = l_Lean_stringToMessageData(v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2));
v___x_2251_ = l_Lean_stringToMessageData(v___x_2250_);
return v___x_2251_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4));
v___x_2254_ = l_Lean_stringToMessageData(v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(lean_object* v_attrName_2255_, lean_object* v_declName_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2262_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2263_ = l_Lean_MessageData_ofName(v_attrName_2255_);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = 0;
v___x_2268_ = l_Lean_MessageData_ofConstName(v_declName_2256_, v___x_2267_);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2266_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2271_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_2273_, lean_object* v_declName_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2273_, v_declName_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2280_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0));
v___x_2283_ = l_Lean_stringToMessageData(v___x_2282_);
return v___x_2283_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2));
v___x_2286_ = l_Lean_stringToMessageData(v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(lean_object* v_attrName_2287_, lean_object* v_declName_2288_, lean_object* v_asyncPrefix_x3f_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___y_2296_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2289_) == 0)
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_MessageData_nil;
v___y_2296_ = v___x_2309_;
goto v___jp_2295_;
}
else
{
lean_object* v_val_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_val_2310_ = lean_ctor_get(v_asyncPrefix_x3f_2289_, 0);
lean_inc(v_val_2310_);
lean_dec_ref_known(v_asyncPrefix_x3f_2289_, 1);
v___x_2311_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3);
v___x_2312_ = l_Lean_MessageData_ofName(v_val_2310_);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___y_2296_ = v___x_2315_;
goto v___jp_2295_;
}
v___jp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2297_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
v___x_2298_ = l_Lean_MessageData_ofName(v_attrName_2287_);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = 0;
v___x_2303_ = l_Lean_MessageData_ofConstName(v_declName_2288_, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2301_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___y_2296_);
v___x_2308_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_2307_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
return v___x_2308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_2316_, lean_object* v_declName_2317_, lean_object* v_asyncPrefix_x3f_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2316_, v_declName_2317_, v_asyncPrefix_x3f_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0(lean_object* v_addEntryFn_2325_, lean_object* v_decl_2326_, lean_object* v_s_2327_){
_start:
{
lean_object* v_importedEntries_2328_; lean_object* v_state_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2337_; 
v_importedEntries_2328_ = lean_ctor_get(v_s_2327_, 0);
v_state_2329_ = lean_ctor_get(v_s_2327_, 1);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_s_2327_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2331_ = v_s_2327_;
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_state_2329_);
lean_inc(v_importedEntries_2328_);
lean_dec(v_s_2327_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v_state_2333_; lean_object* v___x_2335_; 
v_state_2333_ = lean_apply_2(v_addEntryFn_2325_, v_state_2329_, v_decl_2326_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v_state_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_importedEntries_2328_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_state_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(lean_object* v_attr_2338_, lean_object* v_decl_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___x_2400_; lean_object* v_env_2401_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___x_2416_; 
v___x_2400_ = lean_st_ref_get(v___y_2343_);
v_env_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc_ref(v_env_2401_);
lean_dec(v___x_2400_);
v___x_2416_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2401_, v_decl_2339_);
if (lean_obj_tag(v___x_2416_) == 0)
{
v___y_2403_ = v___y_2340_;
v___y_2404_ = v___y_2341_;
v___y_2405_ = v___y_2342_;
v___y_2406_ = v___y_2343_;
goto v___jp_2402_;
}
else
{
lean_object* v_attr_2417_; lean_object* v_toAttributeImplCore_2418_; lean_object* v_name_2419_; lean_object* v___x_2420_; 
lean_dec_ref_known(v___x_2416_, 1);
lean_dec_ref(v_env_2401_);
v_attr_2417_ = lean_ctor_get(v_attr_2338_, 0);
lean_inc_ref(v_attr_2417_);
lean_dec_ref(v_attr_2338_);
v_toAttributeImplCore_2418_ = lean_ctor_get(v_attr_2417_, 0);
lean_inc_ref(v_toAttributeImplCore_2418_);
lean_dec_ref(v_attr_2417_);
v_name_2419_ = lean_ctor_get(v_toAttributeImplCore_2418_, 1);
lean_inc(v_name_2419_);
lean_dec_ref(v_toAttributeImplCore_2418_);
v___x_2420_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_name_2419_, v_decl_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
return v___x_2420_;
}
v___jp_2345_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v_mctx_2361_; lean_object* v_zetaDeltaFVarIds_2362_; lean_object* v_postponed_2363_; lean_object* v_diag_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2375_; 
v___x_2357_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
v___x_2358_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2358_, 0, v___y_2356_);
lean_ctor_set(v___x_2358_, 1, v___y_2354_);
lean_ctor_set(v___x_2358_, 2, v___y_2349_);
lean_ctor_set(v___x_2358_, 3, v___y_2346_);
lean_ctor_set(v___x_2358_, 4, v___y_2353_);
lean_ctor_set(v___x_2358_, 5, v___x_2357_);
lean_ctor_set(v___x_2358_, 6, v___y_2351_);
lean_ctor_set(v___x_2358_, 7, v___y_2352_);
lean_ctor_set(v___x_2358_, 8, v___y_2348_);
lean_ctor_set(v___x_2358_, 9, v___y_2355_);
v___x_2359_ = lean_st_ref_put(v___y_2347_, v___x_2358_);
v___x_2360_ = lean_st_ref_take(v___y_2350_);
v_mctx_2361_ = lean_ctor_get(v___x_2360_, 0);
v_zetaDeltaFVarIds_2362_ = lean_ctor_get(v___x_2360_, 2);
v_postponed_2363_ = lean_ctor_get(v___x_2360_, 3);
v_diag_2364_ = lean_ctor_get(v___x_2360_, 4);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v___x_2360_, 1);
lean_dec(v_unused_2376_);
v___x_2366_ = v___x_2360_;
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_diag_2364_);
lean_inc(v_postponed_2363_);
lean_inc(v_zetaDeltaFVarIds_2362_);
lean_inc(v_mctx_2361_);
lean_dec(v___x_2360_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2369_);
v___x_2371_ = v___x_2366_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_mctx_2361_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_zetaDeltaFVarIds_2362_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_postponed_2363_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v_diag_2364_);
v___x_2371_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_st_ref_put(v___y_2350_, v___x_2371_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2368_);
return v___x_2373_;
}
}
}
v___jp_2377_:
{
lean_object* v___x_2380_; lean_object* v_ext_2381_; lean_object* v_toEnvExtension_2382_; lean_object* v_env_2383_; lean_object* v_nextMacroScope_2384_; lean_object* v_ngen_2385_; lean_object* v_auxDeclNGen_2386_; lean_object* v_traceState_2387_; lean_object* v_recordedDeps_2388_; lean_object* v_messages_2389_; lean_object* v_infoState_2390_; lean_object* v_snapshotTasks_2391_; lean_object* v_addEntryFn_2392_; lean_object* v_asyncMode_2393_; uint8_t v_logWrites_2394_; lean_object* v___f_2395_; uint8_t v___x_2396_; 
v___x_2380_ = lean_st_ref_take(v___y_2379_);
v_ext_2381_ = lean_ctor_get(v_attr_2338_, 1);
lean_inc_ref(v_ext_2381_);
lean_dec_ref(v_attr_2338_);
v_toEnvExtension_2382_ = lean_ctor_get(v_ext_2381_, 0);
lean_inc_ref(v_toEnvExtension_2382_);
v_env_2383_ = lean_ctor_get(v___x_2380_, 0);
lean_inc_ref(v_env_2383_);
v_nextMacroScope_2384_ = lean_ctor_get(v___x_2380_, 1);
lean_inc(v_nextMacroScope_2384_);
v_ngen_2385_ = lean_ctor_get(v___x_2380_, 2);
lean_inc_ref(v_ngen_2385_);
v_auxDeclNGen_2386_ = lean_ctor_get(v___x_2380_, 3);
lean_inc_ref(v_auxDeclNGen_2386_);
v_traceState_2387_ = lean_ctor_get(v___x_2380_, 4);
lean_inc_ref(v_traceState_2387_);
v_recordedDeps_2388_ = lean_ctor_get(v___x_2380_, 6);
lean_inc_ref(v_recordedDeps_2388_);
v_messages_2389_ = lean_ctor_get(v___x_2380_, 7);
lean_inc_ref(v_messages_2389_);
v_infoState_2390_ = lean_ctor_get(v___x_2380_, 8);
lean_inc_ref(v_infoState_2390_);
v_snapshotTasks_2391_ = lean_ctor_get(v___x_2380_, 9);
lean_inc_ref(v_snapshotTasks_2391_);
lean_dec(v___x_2380_);
v_addEntryFn_2392_ = lean_ctor_get(v_ext_2381_, 3);
lean_inc(v_addEntryFn_2392_);
lean_dec_ref(v_ext_2381_);
v_asyncMode_2393_ = lean_ctor_get(v_toEnvExtension_2382_, 2);
lean_inc(v_asyncMode_2393_);
v_logWrites_2394_ = lean_ctor_get_uint8(v_toEnvExtension_2382_, sizeof(void*)*6);
lean_inc(v_decl_2339_);
v___f_2395_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2395_, 0, v_addEntryFn_2392_);
lean_closure_set(v___f_2395_, 1, v_decl_2339_);
v___x_2396_ = 1;
if (v_logWrites_2394_ == 0)
{
lean_object* v___x_2397_; 
v___x_2397_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2382_, v_env_2383_, v___f_2395_, v_asyncMode_2393_, v_decl_2339_, v___x_2396_);
lean_dec(v_asyncMode_2393_);
v___y_2346_ = v_auxDeclNGen_2386_;
v___y_2347_ = v___y_2379_;
v___y_2348_ = v_infoState_2390_;
v___y_2349_ = v_ngen_2385_;
v___y_2350_ = v___y_2378_;
v___y_2351_ = v_recordedDeps_2388_;
v___y_2352_ = v_messages_2389_;
v___y_2353_ = v_traceState_2387_;
v___y_2354_ = v_nextMacroScope_2384_;
v___y_2355_ = v_snapshotTasks_2391_;
v___y_2356_ = v___x_2397_;
goto v___jp_2345_;
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_inc_ref(v_toEnvExtension_2382_);
v___x_2398_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2382_, v_env_2383_);
lean_dec_ref(v_env_2383_);
v___x_2399_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2382_, v___x_2398_, v___f_2395_, v_asyncMode_2393_, v_decl_2339_, v___x_2396_);
lean_dec(v_asyncMode_2393_);
v___y_2346_ = v_auxDeclNGen_2386_;
v___y_2347_ = v___y_2379_;
v___y_2348_ = v_infoState_2390_;
v___y_2349_ = v_ngen_2385_;
v___y_2350_ = v___y_2378_;
v___y_2351_ = v_recordedDeps_2388_;
v___y_2352_ = v_messages_2389_;
v___y_2353_ = v_traceState_2387_;
v___y_2354_ = v_nextMacroScope_2384_;
v___y_2355_ = v_snapshotTasks_2391_;
v___y_2356_ = v___x_2399_;
goto v___jp_2345_;
}
}
v___jp_2402_:
{
lean_object* v_ext_2407_; lean_object* v_toEnvExtension_2408_; lean_object* v_attr_2409_; lean_object* v_asyncMode_2410_; uint8_t v___x_2411_; 
v_ext_2407_ = lean_ctor_get(v_attr_2338_, 1);
v_toEnvExtension_2408_ = lean_ctor_get(v_ext_2407_, 0);
v_attr_2409_ = lean_ctor_get(v_attr_2338_, 0);
v_asyncMode_2410_ = lean_ctor_get(v_toEnvExtension_2408_, 2);
lean_inc(v_decl_2339_);
lean_inc_ref(v_env_2401_);
v___x_2411_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2401_, v_decl_2339_, v_asyncMode_2410_);
if (v___x_2411_ == 0)
{
lean_object* v_toAttributeImplCore_2412_; lean_object* v_name_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_inc_ref(v_attr_2409_);
lean_dec_ref(v_attr_2338_);
v_toAttributeImplCore_2412_ = lean_ctor_get(v_attr_2409_, 0);
lean_inc_ref(v_toAttributeImplCore_2412_);
lean_dec_ref(v_attr_2409_);
v_name_2413_ = lean_ctor_get(v_toAttributeImplCore_2412_, 1);
lean_inc(v_name_2413_);
lean_dec_ref(v_toAttributeImplCore_2412_);
v___x_2414_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2401_);
v___x_2415_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_name_2413_, v_decl_2339_, v___x_2414_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2415_;
}
else
{
lean_dec_ref(v_env_2401_);
v___y_2378_ = v___y_2404_;
v___y_2379_ = v___y_2406_;
goto v___jp_2377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___boxed(lean_object* v_attr_2421_, lean_object* v_decl_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v_attr_2421_, v_decl_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(lean_object* v_val_2429_, lean_object* v_indName_2430_, lean_object* v_tail_2431_, lean_object* v___x_2432_, lean_object* v___x_2433_, lean_object* v___x_2434_, lean_object* v_a_2435_, lean_object* v_range_2436_, lean_object* v_b_2437_, lean_object* v_i_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_stop_2444_; lean_object* v_step_2445_; uint8_t v___x_2446_; 
v_stop_2444_ = lean_ctor_get(v_range_2436_, 1);
v_step_2445_ = lean_ctor_get(v_range_2436_, 2);
v___x_2446_ = lean_nat_dec_lt(v_i_2438_, v_stop_2444_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; 
lean_dec(v_i_2438_);
lean_dec_ref(v_a_2435_);
lean_dec(v___x_2434_);
lean_dec(v___x_2433_);
lean_dec(v___x_2432_);
lean_dec(v_tail_2431_);
lean_dec(v_indName_2430_);
lean_dec_ref(v_val_2429_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v_b_2437_);
return v___x_2447_;
}
else
{
lean_object* v_numParams_2448_; lean_object* v_numIndices_2449_; lean_object* v_ctors_2450_; lean_object* v_levelParams_2451_; lean_object* v_type_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; lean_object* v___x_2463_; 
v_numParams_2448_ = lean_ctor_get(v_val_2429_, 1);
v_numIndices_2449_ = lean_ctor_get(v_val_2429_, 2);
v_ctors_2450_ = lean_ctor_get(v_val_2429_, 4);
v_levelParams_2451_ = lean_ctor_get(v_a_2435_, 1);
v_type_2452_ = lean_ctor_get(v_a_2435_, 2);
v___x_2453_ = lean_unsigned_to_nat(0u);
v___x_2454_ = l_Lean_instInhabitedExpr;
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_box(0);
v___x_2458_ = lean_box(v___x_2446_);
lean_inc(v___x_2434_);
lean_inc(v___x_2433_);
lean_inc(v___x_2432_);
lean_inc_n(v_i_2438_, 2);
lean_inc(v_tail_2431_);
lean_inc_n(v_indName_2430_, 2);
lean_inc(v_numIndices_2449_);
lean_inc(v_numParams_2448_);
v___f_2459_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed), 19, 12);
lean_closure_set(v___f_2459_, 0, v___x_2453_);
lean_closure_set(v___f_2459_, 1, v_numParams_2448_);
lean_closure_set(v___f_2459_, 2, v___x_2454_);
lean_closure_set(v___f_2459_, 3, v___x_2455_);
lean_closure_set(v___f_2459_, 4, v_numIndices_2449_);
lean_closure_set(v___f_2459_, 5, v_indName_2430_);
lean_closure_set(v___f_2459_, 6, v_tail_2431_);
lean_closure_set(v___f_2459_, 7, v_i_2438_);
lean_closure_set(v___f_2459_, 8, v___x_2432_);
lean_closure_set(v___f_2459_, 9, v___x_2433_);
lean_closure_set(v___f_2459_, 10, v___x_2434_);
lean_closure_set(v___f_2459_, 11, v___x_2458_);
v___x_2460_ = l_List_get_x21Internal___redArg(v___x_2456_, v_ctors_2450_, v_i_2438_);
v___x_2461_ = l_Lean_mkConstructorElimName(v_indName_2430_, v___x_2460_);
v___x_2462_ = 0;
lean_inc_ref(v_type_2452_);
v___x_2463_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_2452_, v___f_2459_, v___x_2462_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_n(v_a_2464_, 2);
lean_dec_ref_known(v___x_2463_, 1);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2441_);
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
v___x_2465_ = lean_infer_type(v_a_2464_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2620_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_box(1);
lean_inc(v_levelParams_2451_);
lean_inc(v___x_2461_);
v___x_2468_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_2461_, v_levelParams_2451_, v_a_2466_, v_a_2464_, v___x_2467_, v___y_2442_);
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2620_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2620_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set_tag(v___x_2471_, 1);
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_addAndCompile(v___x_2474_, v___x_2446_, v___x_2462_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; lean_object* v_env_2477_; lean_object* v_nextMacroScope_2478_; lean_object* v_ngen_2479_; lean_object* v_auxDeclNGen_2480_; lean_object* v_traceState_2481_; lean_object* v_recordedDeps_2482_; lean_object* v_messages_2483_; lean_object* v_infoState_2484_; lean_object* v_snapshotTasks_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2617_; 
lean_dec_ref_known(v___x_2475_, 1);
v___x_2476_ = lean_st_ref_take(v___y_2442_);
v_env_2477_ = lean_ctor_get(v___x_2476_, 0);
v_nextMacroScope_2478_ = lean_ctor_get(v___x_2476_, 1);
v_ngen_2479_ = lean_ctor_get(v___x_2476_, 2);
v_auxDeclNGen_2480_ = lean_ctor_get(v___x_2476_, 3);
v_traceState_2481_ = lean_ctor_get(v___x_2476_, 4);
v_recordedDeps_2482_ = lean_ctor_get(v___x_2476_, 6);
v_messages_2483_ = lean_ctor_get(v___x_2476_, 7);
v_infoState_2484_ = lean_ctor_get(v___x_2476_, 8);
v_snapshotTasks_2485_ = lean_ctor_get(v___x_2476_, 9);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v___x_2476_, 5);
lean_dec(v_unused_2618_);
v___x_2487_ = v___x_2476_;
v_isShared_2488_ = v_isSharedCheck_2617_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_snapshotTasks_2485_);
lean_inc(v_infoState_2484_);
lean_inc(v_messages_2483_);
lean_inc(v_recordedDeps_2482_);
lean_inc(v_traceState_2481_);
lean_inc(v_auxDeclNGen_2480_);
lean_inc(v_ngen_2479_);
lean_inc(v_nextMacroScope_2478_);
lean_inc(v_env_2477_);
lean_dec(v___x_2476_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2617_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
lean_inc(v___x_2461_);
v___x_2489_ = l_Lean_markAuxRecursor(v_env_2477_, v___x_2461_);
v___x_2490_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 5, v___x_2490_);
lean_ctor_set(v___x_2487_, 0, v___x_2489_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_nextMacroScope_2478_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_ngen_2479_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_auxDeclNGen_2480_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_traceState_2481_);
lean_ctor_set(v_reuseFailAlloc_2616_, 5, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2616_, 6, v_recordedDeps_2482_);
lean_ctor_set(v_reuseFailAlloc_2616_, 7, v_messages_2483_);
lean_ctor_set(v_reuseFailAlloc_2616_, 8, v_infoState_2484_);
lean_ctor_set(v_reuseFailAlloc_2616_, 9, v_snapshotTasks_2485_);
v___x_2492_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_mctx_2495_; lean_object* v_zetaDeltaFVarIds_2496_; lean_object* v_postponed_2497_; lean_object* v_diag_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2614_; 
v___x_2493_ = lean_st_ref_put(v___y_2442_, v___x_2492_);
v___x_2494_ = lean_st_ref_take(v___y_2440_);
v_mctx_2495_ = lean_ctor_get(v___x_2494_, 0);
v_zetaDeltaFVarIds_2496_ = lean_ctor_get(v___x_2494_, 2);
v_postponed_2497_ = lean_ctor_get(v___x_2494_, 3);
v_diag_2498_ = lean_ctor_get(v___x_2494_, 4);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2494_, 1);
lean_dec(v_unused_2615_);
v___x_2500_ = v___x_2494_;
v_isShared_2501_ = v_isSharedCheck_2614_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_diag_2498_);
lean_inc(v_postponed_2497_);
lean_inc(v_zetaDeltaFVarIds_2496_);
lean_inc(v_mctx_2495_);
lean_dec(v___x_2494_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2614_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v___x_2502_);
v___x_2504_ = v___x_2500_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_mctx_2495_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_zetaDeltaFVarIds_2496_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_postponed_2497_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_diag_2498_);
v___x_2504_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v_env_2507_; lean_object* v_nextMacroScope_2508_; lean_object* v_ngen_2509_; lean_object* v_auxDeclNGen_2510_; lean_object* v_traceState_2511_; lean_object* v_recordedDeps_2512_; lean_object* v_messages_2513_; lean_object* v_infoState_2514_; lean_object* v_snapshotTasks_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2611_; 
v___x_2505_ = lean_st_ref_put(v___y_2440_, v___x_2504_);
v___x_2506_ = lean_st_ref_take(v___y_2442_);
v_env_2507_ = lean_ctor_get(v___x_2506_, 0);
v_nextMacroScope_2508_ = lean_ctor_get(v___x_2506_, 1);
v_ngen_2509_ = lean_ctor_get(v___x_2506_, 2);
v_auxDeclNGen_2510_ = lean_ctor_get(v___x_2506_, 3);
v_traceState_2511_ = lean_ctor_get(v___x_2506_, 4);
v_recordedDeps_2512_ = lean_ctor_get(v___x_2506_, 6);
v_messages_2513_ = lean_ctor_get(v___x_2506_, 7);
v_infoState_2514_ = lean_ctor_get(v___x_2506_, 8);
v_snapshotTasks_2515_ = lean_ctor_get(v___x_2506_, 9);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v___x_2506_, 5);
lean_dec(v_unused_2612_);
v___x_2517_ = v___x_2506_;
v_isShared_2518_ = v_isSharedCheck_2611_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_snapshotTasks_2515_);
lean_inc(v_infoState_2514_);
lean_inc(v_messages_2513_);
lean_inc(v_recordedDeps_2512_);
lean_inc(v_traceState_2511_);
lean_inc(v_auxDeclNGen_2510_);
lean_inc(v_ngen_2509_);
lean_inc(v_nextMacroScope_2508_);
lean_inc(v_env_2507_);
lean_dec(v___x_2506_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2611_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_inc(v___x_2461_);
v___x_2519_ = l_Lean_markSparseCasesOn(v_env_2507_, v___x_2461_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 5, v___x_2490_);
lean_ctor_set(v___x_2517_, 0, v___x_2519_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_nextMacroScope_2508_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_ngen_2509_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_auxDeclNGen_2510_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_traceState_2511_);
lean_ctor_set(v_reuseFailAlloc_2610_, 5, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2610_, 6, v_recordedDeps_2512_);
lean_ctor_set(v_reuseFailAlloc_2610_, 7, v_messages_2513_);
lean_ctor_set(v_reuseFailAlloc_2610_, 8, v_infoState_2514_);
lean_ctor_set(v_reuseFailAlloc_2610_, 9, v_snapshotTasks_2515_);
v___x_2521_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_mctx_2524_; lean_object* v_zetaDeltaFVarIds_2525_; lean_object* v_postponed_2526_; lean_object* v_diag_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2608_; 
v___x_2522_ = lean_st_ref_put(v___y_2442_, v___x_2521_);
v___x_2523_ = lean_st_ref_take(v___y_2440_);
v_mctx_2524_ = lean_ctor_get(v___x_2523_, 0);
v_zetaDeltaFVarIds_2525_ = lean_ctor_get(v___x_2523_, 2);
v_postponed_2526_ = lean_ctor_get(v___x_2523_, 3);
v_diag_2527_ = lean_ctor_get(v___x_2523_, 4);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v___x_2523_, 1);
lean_dec(v_unused_2609_);
v___x_2529_ = v___x_2523_;
v_isShared_2530_ = v_isSharedCheck_2608_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_diag_2527_);
lean_inc(v_postponed_2526_);
lean_inc(v_zetaDeltaFVarIds_2525_);
lean_inc(v_mctx_2524_);
lean_dec(v___x_2523_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2608_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2502_);
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_mctx_2524_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_zetaDeltaFVarIds_2525_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_postponed_2526_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v_diag_2527_);
v___x_2532_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_env_2535_; lean_object* v_nextMacroScope_2536_; lean_object* v_ngen_2537_; lean_object* v_auxDeclNGen_2538_; lean_object* v_traceState_2539_; lean_object* v_recordedDeps_2540_; lean_object* v_messages_2541_; lean_object* v_infoState_2542_; lean_object* v_snapshotTasks_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2605_; 
v___x_2533_ = lean_st_ref_put(v___y_2440_, v___x_2532_);
v___x_2534_ = lean_st_ref_take(v___y_2442_);
v_env_2535_ = lean_ctor_get(v___x_2534_, 0);
v_nextMacroScope_2536_ = lean_ctor_get(v___x_2534_, 1);
v_ngen_2537_ = lean_ctor_get(v___x_2534_, 2);
v_auxDeclNGen_2538_ = lean_ctor_get(v___x_2534_, 3);
v_traceState_2539_ = lean_ctor_get(v___x_2534_, 4);
v_recordedDeps_2540_ = lean_ctor_get(v___x_2534_, 6);
v_messages_2541_ = lean_ctor_get(v___x_2534_, 7);
v_infoState_2542_ = lean_ctor_get(v___x_2534_, 8);
v_snapshotTasks_2543_ = lean_ctor_get(v___x_2534_, 9);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2534_, 5);
lean_dec(v_unused_2606_);
v___x_2545_ = v___x_2534_;
v_isShared_2546_ = v_isSharedCheck_2605_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_snapshotTasks_2543_);
lean_inc(v_infoState_2542_);
lean_inc(v_messages_2541_);
lean_inc(v_recordedDeps_2540_);
lean_inc(v_traceState_2539_);
lean_inc(v_auxDeclNGen_2538_);
lean_inc(v_ngen_2537_);
lean_inc(v_nextMacroScope_2536_);
lean_inc(v_env_2535_);
lean_dec(v___x_2534_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2605_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_inc(v___x_2461_);
v___x_2547_ = l_Lean_Meta_addToCompletionBlackList(v_env_2535_, v___x_2461_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 5, v___x_2490_);
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_nextMacroScope_2536_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_ngen_2537_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_auxDeclNGen_2538_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_traceState_2539_);
lean_ctor_set(v_reuseFailAlloc_2604_, 5, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2604_, 6, v_recordedDeps_2540_);
lean_ctor_set(v_reuseFailAlloc_2604_, 7, v_messages_2541_);
lean_ctor_set(v_reuseFailAlloc_2604_, 8, v_infoState_2542_);
lean_ctor_set(v_reuseFailAlloc_2604_, 9, v_snapshotTasks_2543_);
v___x_2549_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_mctx_2552_; lean_object* v_zetaDeltaFVarIds_2553_; lean_object* v_postponed_2554_; lean_object* v_diag_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2602_; 
v___x_2550_ = lean_st_ref_put(v___y_2442_, v___x_2549_);
v___x_2551_ = lean_st_ref_take(v___y_2440_);
v_mctx_2552_ = lean_ctor_get(v___x_2551_, 0);
v_zetaDeltaFVarIds_2553_ = lean_ctor_get(v___x_2551_, 2);
v_postponed_2554_ = lean_ctor_get(v___x_2551_, 3);
v_diag_2555_ = lean_ctor_get(v___x_2551_, 4);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v___x_2551_, 1);
lean_dec(v_unused_2603_);
v___x_2557_ = v___x_2551_;
v_isShared_2558_ = v_isSharedCheck_2602_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_diag_2555_);
lean_inc(v_postponed_2554_);
lean_inc(v_zetaDeltaFVarIds_2553_);
lean_inc(v_mctx_2552_);
lean_dec(v___x_2551_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2602_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 1, v___x_2502_);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_mctx_2552_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_zetaDeltaFVarIds_2553_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_postponed_2554_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_diag_2555_);
v___x_2560_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_env_2563_; lean_object* v_nextMacroScope_2564_; lean_object* v_ngen_2565_; lean_object* v_auxDeclNGen_2566_; lean_object* v_traceState_2567_; lean_object* v_recordedDeps_2568_; lean_object* v_messages_2569_; lean_object* v_infoState_2570_; lean_object* v_snapshotTasks_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2599_; 
v___x_2561_ = lean_st_ref_put(v___y_2440_, v___x_2560_);
v___x_2562_ = lean_st_ref_take(v___y_2442_);
v_env_2563_ = lean_ctor_get(v___x_2562_, 0);
v_nextMacroScope_2564_ = lean_ctor_get(v___x_2562_, 1);
v_ngen_2565_ = lean_ctor_get(v___x_2562_, 2);
v_auxDeclNGen_2566_ = lean_ctor_get(v___x_2562_, 3);
v_traceState_2567_ = lean_ctor_get(v___x_2562_, 4);
v_recordedDeps_2568_ = lean_ctor_get(v___x_2562_, 6);
v_messages_2569_ = lean_ctor_get(v___x_2562_, 7);
v_infoState_2570_ = lean_ctor_get(v___x_2562_, 8);
v_snapshotTasks_2571_ = lean_ctor_get(v___x_2562_, 9);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v___x_2562_, 5);
lean_dec(v_unused_2600_);
v___x_2573_ = v___x_2562_;
v_isShared_2574_ = v_isSharedCheck_2599_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snapshotTasks_2571_);
lean_inc(v_infoState_2570_);
lean_inc(v_messages_2569_);
lean_inc(v_recordedDeps_2568_);
lean_inc(v_traceState_2567_);
lean_inc(v_auxDeclNGen_2566_);
lean_inc(v_ngen_2565_);
lean_inc(v_nextMacroScope_2564_);
lean_inc(v_env_2563_);
lean_dec(v___x_2562_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2599_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
lean_inc(v___x_2461_);
v___x_2575_ = l_Lean_addProtected(v_env_2563_, v___x_2461_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 5, v___x_2490_);
lean_ctor_set(v___x_2573_, 0, v___x_2575_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_nextMacroScope_2564_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_ngen_2565_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_auxDeclNGen_2566_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_traceState_2567_);
lean_ctor_set(v_reuseFailAlloc_2598_, 5, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2598_, 6, v_recordedDeps_2568_);
lean_ctor_set(v_reuseFailAlloc_2598_, 7, v_messages_2569_);
lean_ctor_set(v_reuseFailAlloc_2598_, 8, v_infoState_2570_);
lean_ctor_set(v_reuseFailAlloc_2598_, 9, v_snapshotTasks_2571_);
v___x_2577_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_mctx_2580_; lean_object* v_zetaDeltaFVarIds_2581_; lean_object* v_postponed_2582_; lean_object* v_diag_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2596_; 
v___x_2578_ = lean_st_ref_put(v___y_2442_, v___x_2577_);
v___x_2579_ = lean_st_ref_take(v___y_2440_);
v_mctx_2580_ = lean_ctor_get(v___x_2579_, 0);
v_zetaDeltaFVarIds_2581_ = lean_ctor_get(v___x_2579_, 2);
v_postponed_2582_ = lean_ctor_get(v___x_2579_, 3);
v_diag_2583_ = lean_ctor_get(v___x_2579_, 4);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v___x_2579_, 1);
lean_dec(v_unused_2597_);
v___x_2585_ = v___x_2579_;
v_isShared_2586_ = v_isSharedCheck_2596_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_diag_2583_);
lean_inc(v_postponed_2582_);
lean_inc(v_zetaDeltaFVarIds_2581_);
lean_inc(v_mctx_2580_);
lean_dec(v___x_2579_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2596_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 1, v___x_2502_);
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_mctx_2580_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2595_, 2, v_zetaDeltaFVarIds_2581_);
lean_ctor_set(v_reuseFailAlloc_2595_, 3, v_postponed_2582_);
lean_ctor_set(v_reuseFailAlloc_2595_, 4, v_diag_2583_);
v___x_2588_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_st_ref_put(v___y_2440_, v___x_2588_);
v___x_2590_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v___x_2461_);
v___x_2591_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v___x_2590_, v___x_2461_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref_known(v___x_2591_, 1);
v___x_2592_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_2461_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec_ref(v___x_2592_);
v___x_2593_ = lean_nat_add(v_i_2438_, v_step_2445_);
lean_dec(v_i_2438_);
v_b_2437_ = v___x_2457_;
v_i_2438_ = v___x_2593_;
goto _start;
}
else
{
lean_dec(v___x_2461_);
lean_dec(v_i_2438_);
lean_dec_ref(v_a_2435_);
lean_dec(v___x_2434_);
lean_dec(v___x_2433_);
lean_dec(v___x_2432_);
lean_dec(v_tail_2431_);
lean_dec(v_indName_2430_);
lean_dec_ref(v_val_2429_);
return v___x_2591_;
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
lean_dec(v___x_2461_);
lean_dec(v_i_2438_);
lean_dec_ref(v_a_2435_);
lean_dec(v___x_2434_);
lean_dec(v___x_2433_);
lean_dec(v___x_2432_);
lean_dec(v_tail_2431_);
lean_dec(v_indName_2430_);
lean_dec_ref(v_val_2429_);
return v___x_2475_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2464_);
lean_dec(v___x_2461_);
lean_dec(v_i_2438_);
lean_dec_ref(v_a_2435_);
lean_dec(v___x_2434_);
lean_dec(v___x_2433_);
lean_dec(v___x_2432_);
lean_dec(v_tail_2431_);
lean_dec(v_indName_2430_);
lean_dec_ref(v_val_2429_);
v_a_2621_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2465_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2465_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v___x_2461_);
lean_dec(v_i_2438_);
lean_dec_ref(v_a_2435_);
lean_dec(v___x_2434_);
lean_dec(v___x_2433_);
lean_dec(v___x_2432_);
lean_dec(v_tail_2431_);
lean_dec(v_indName_2430_);
lean_dec_ref(v_val_2429_);
v_a_2629_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2463_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2463_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___boxed(lean_object* v_val_2637_, lean_object* v_indName_2638_, lean_object* v_tail_2639_, lean_object* v___x_2640_, lean_object* v___x_2641_, lean_object* v___x_2642_, lean_object* v_a_2643_, lean_object* v_range_2644_, lean_object* v_b_2645_, lean_object* v_i_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2637_, v_indName_2638_, v_tail_2639_, v___x_2640_, v___x_2641_, v___x_2642_, v_a_2643_, v_range_2644_, v_b_2645_, v_i_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec_ref(v_range_2644_);
return v_res_2652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1));
v___x_2655_ = lean_unsigned_to_nat(58u);
v___x_2656_ = lean_unsigned_to_nat(169u);
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2658_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2659_ = l_mkPanicMessageWithDecl(v___x_2658_, v___x_2657_, v___x_2656_, v___x_2655_, v___x_2654_);
return v___x_2659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1));
v___x_2661_ = lean_unsigned_to_nat(60u);
v___x_2662_ = lean_unsigned_to_nat(166u);
v___x_2663_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0));
v___x_2664_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0));
v___x_2665_ = l_mkPanicMessageWithDecl(v___x_2664_, v___x_2663_, v___x_2662_, v___x_2661_, v___x_2660_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(lean_object* v_indName_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v___x_2672_; 
lean_inc(v_indName_2666_);
v___x_2672_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
if (lean_obj_tag(v_a_2673_) == 5)
{
lean_object* v_val_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_val_2674_ = lean_ctor_get(v_a_2673_, 0);
lean_inc_ref(v_val_2674_);
lean_dec_ref_known(v_a_2673_, 1);
lean_inc(v_indName_2666_);
v___x_2675_ = l_Lean_mkCasesOnName(v_indName_2666_);
lean_inc(v___x_2675_);
v___x_2676_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2675_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v_levelParams_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2715_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v_levelParams_2678_ = lean_ctor_get(v_a_2677_, 1);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_a_2677_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; lean_object* v_unused_2717_; 
v_unused_2716_ = lean_ctor_get(v_a_2677_, 2);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_a_2677_, 0);
lean_dec(v_unused_2717_);
v___x_2680_ = v_a_2677_;
v_isShared_2681_ = v_isSharedCheck_2715_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_levelParams_2678_);
lean_dec(v_a_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2715_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_box(0);
v___x_2683_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_2678_, v___x_2682_);
if (lean_obj_tag(v___x_2683_) == 1)
{
lean_object* v_tail_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v_tail_2684_ = lean_ctor_get(v___x_2683_, 1);
lean_inc(v_tail_2684_);
lean_inc_n(v_indName_2666_, 2);
v___x_2685_ = l_Lean_mkCtorElimName(v_indName_2666_);
v___x_2686_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_2666_);
v___x_2687_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v___x_2675_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = l_Lean_InductiveVal_numCtors(v_val_2674_);
v___x_2691_ = lean_unsigned_to_nat(1u);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 2, v___x_2691_);
lean_ctor_set(v___x_2680_, 1, v___x_2690_);
lean_ctor_set(v___x_2680_, 0, v___x_2689_);
v___x_2693_ = v___x_2680_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2674_, v_indName_2666_, v_tail_2684_, v___x_2685_, v___x_2683_, v___x_2686_, v_a_2688_, v___x_2693_, v___x_2694_, v___x_2689_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
lean_dec_ref(v___x_2693_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2695_, 0);
lean_dec(v_unused_2703_);
v___x_2697_ = v___x_2695_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_dec(v___x_2695_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2694_);
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2694_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
return v___x_2695_;
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v___x_2686_);
lean_dec(v___x_2685_);
lean_dec_ref_known(v___x_2683_, 2);
lean_dec(v_tail_2684_);
lean_del_object(v___x_2680_);
lean_dec_ref(v_val_2674_);
lean_dec(v_indName_2666_);
v_a_2705_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2687_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2687_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec(v___x_2683_);
lean_del_object(v___x_2680_);
lean_dec(v___x_2675_);
lean_dec_ref(v_val_2674_);
lean_dec(v_indName_2666_);
v___x_2713_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1);
v___x_2714_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2713_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
return v___x_2714_;
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v___x_2675_);
lean_dec_ref(v_val_2674_);
lean_dec(v_indName_2666_);
v_a_2718_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2676_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2676_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_dec(v_a_2673_);
lean_dec(v_indName_2666_);
v___x_2726_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2);
v___x_2727_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_2726_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
return v___x_2727_;
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_indName_2666_);
v_a_2728_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2672_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2672_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___boxed(lean_object* v_indName_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(lean_object* v_val_2743_, lean_object* v_indName_2744_, lean_object* v_tail_2745_, lean_object* v___x_2746_, lean_object* v___x_2747_, lean_object* v___x_2748_, lean_object* v_a_2749_, lean_object* v_range_2750_, lean_object* v_b_2751_, lean_object* v_i_2752_, lean_object* v_hs_2753_, lean_object* v_hl_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_2743_, v_indName_2744_, v_tail_2745_, v___x_2746_, v___x_2747_, v___x_2748_, v_a_2749_, v_range_2750_, v_b_2751_, v_i_2752_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___boxed(lean_object** _args){
lean_object* v_val_2761_ = _args[0];
lean_object* v_indName_2762_ = _args[1];
lean_object* v_tail_2763_ = _args[2];
lean_object* v___x_2764_ = _args[3];
lean_object* v___x_2765_ = _args[4];
lean_object* v___x_2766_ = _args[5];
lean_object* v_a_2767_ = _args[6];
lean_object* v_range_2768_ = _args[7];
lean_object* v_b_2769_ = _args[8];
lean_object* v_i_2770_ = _args[9];
lean_object* v_hs_2771_ = _args[10];
lean_object* v_hl_2772_ = _args[11];
lean_object* v___y_2773_ = _args[12];
lean_object* v___y_2774_ = _args[13];
lean_object* v___y_2775_ = _args[14];
lean_object* v___y_2776_ = _args[15];
lean_object* v___y_2777_ = _args[16];
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(v_val_2761_, v_indName_2762_, v_tail_2763_, v___x_2764_, v___x_2765_, v___x_2766_, v_a_2767_, v_range_2768_, v_b_2769_, v_i_2770_, v_hs_2771_, v_hl_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v_range_2768_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(lean_object* v_00_u03b1_2779_, lean_object* v_attrName_2780_, lean_object* v_declName_2781_, lean_object* v_asyncPrefix_x3f_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_2780_, v_declName_2781_, v_asyncPrefix_x3f_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_attrName_2790_, lean_object* v_declName_2791_, lean_object* v_asyncPrefix_x3f_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(v_00_u03b1_2789_, v_attrName_2790_, v_declName_2791_, v_asyncPrefix_x3f_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(lean_object* v_00_u03b1_2799_, lean_object* v_attrName_2800_, lean_object* v_declName_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_2800_, v_declName_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2808_, lean_object* v_attrName_2809_, lean_object* v_declName_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(v_00_u03b1_2808_, v_attrName_2809_, v_declName_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(lean_object* v___y_2817_, uint8_t v_isExporting_2818_, lean_object* v___x_2819_, lean_object* v___y_2820_, lean_object* v___x_2821_, lean_object* v_a_x3f_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v_env_2825_; lean_object* v_nextMacroScope_2826_; lean_object* v_ngen_2827_; lean_object* v_auxDeclNGen_2828_; lean_object* v_traceState_2829_; lean_object* v_recordedDeps_2830_; lean_object* v_messages_2831_; lean_object* v_infoState_2832_; lean_object* v_snapshotTasks_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2858_; 
v___x_2824_ = lean_st_ref_take(v___y_2817_);
v_env_2825_ = lean_ctor_get(v___x_2824_, 0);
v_nextMacroScope_2826_ = lean_ctor_get(v___x_2824_, 1);
v_ngen_2827_ = lean_ctor_get(v___x_2824_, 2);
v_auxDeclNGen_2828_ = lean_ctor_get(v___x_2824_, 3);
v_traceState_2829_ = lean_ctor_get(v___x_2824_, 4);
v_recordedDeps_2830_ = lean_ctor_get(v___x_2824_, 6);
v_messages_2831_ = lean_ctor_get(v___x_2824_, 7);
v_infoState_2832_ = lean_ctor_get(v___x_2824_, 8);
v_snapshotTasks_2833_ = lean_ctor_get(v___x_2824_, 9);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2824_, 5);
lean_dec(v_unused_2859_);
v___x_2835_ = v___x_2824_;
v_isShared_2836_ = v_isSharedCheck_2858_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_snapshotTasks_2833_);
lean_inc(v_infoState_2832_);
lean_inc(v_messages_2831_);
lean_inc(v_recordedDeps_2830_);
lean_inc(v_traceState_2829_);
lean_inc(v_auxDeclNGen_2828_);
lean_inc(v_ngen_2827_);
lean_inc(v_nextMacroScope_2826_);
lean_inc(v_env_2825_);
lean_dec(v___x_2824_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2858_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2837_ = l_Lean_Environment_setExporting(v_env_2825_, v_isExporting_2818_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 5, v___x_2819_);
lean_ctor_set(v___x_2835_, 0, v___x_2837_);
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_nextMacroScope_2826_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_ngen_2827_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_auxDeclNGen_2828_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_traceState_2829_);
lean_ctor_set(v_reuseFailAlloc_2857_, 5, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2857_, 6, v_recordedDeps_2830_);
lean_ctor_set(v_reuseFailAlloc_2857_, 7, v_messages_2831_);
lean_ctor_set(v_reuseFailAlloc_2857_, 8, v_infoState_2832_);
lean_ctor_set(v_reuseFailAlloc_2857_, 9, v_snapshotTasks_2833_);
v___x_2839_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_mctx_2842_; lean_object* v_zetaDeltaFVarIds_2843_; lean_object* v_postponed_2844_; lean_object* v_diag_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2855_; 
v___x_2840_ = lean_st_ref_put(v___y_2817_, v___x_2839_);
v___x_2841_ = lean_st_ref_take(v___y_2820_);
v_mctx_2842_ = lean_ctor_get(v___x_2841_, 0);
v_zetaDeltaFVarIds_2843_ = lean_ctor_get(v___x_2841_, 2);
v_postponed_2844_ = lean_ctor_get(v___x_2841_, 3);
v_diag_2845_ = lean_ctor_get(v___x_2841_, 4);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2841_, 1);
lean_dec(v_unused_2856_);
v___x_2847_ = v___x_2841_;
v_isShared_2848_ = v_isSharedCheck_2855_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_diag_2845_);
lean_inc(v_postponed_2844_);
lean_inc(v_zetaDeltaFVarIds_2843_);
lean_inc(v_mctx_2842_);
lean_dec(v___x_2841_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2855_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2849_ = lean_box(0);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 1, v___x_2821_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_mctx_2842_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_zetaDeltaFVarIds_2843_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_postponed_2844_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_diag_2845_);
v___x_2851_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_st_ref_put(v___y_2820_, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2849_);
return v___x_2853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0___boxed(lean_object* v___y_2860_, lean_object* v_isExporting_2861_, lean_object* v___x_2862_, lean_object* v___y_2863_, lean_object* v___x_2864_, lean_object* v_a_x3f_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v_isExporting_boxed_2867_; lean_object* v_res_2868_; 
v_isExporting_boxed_2867_ = lean_unbox(v_isExporting_2861_);
v_res_2868_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2860_, v_isExporting_boxed_2867_, v___x_2862_, v___y_2863_, v___x_2864_, v_a_x3f_2865_);
lean_dec(v_a_x3f_2865_);
lean_dec(v___y_2863_);
lean_dec(v___y_2860_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(lean_object* v_x_2869_, uint8_t v_isExporting_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; lean_object* v_env_2877_; lean_object* v___x_2878_; uint8_t v_isModule_2879_; 
v___x_2876_ = lean_st_ref_get(v___y_2874_);
v_env_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc_ref(v_env_2877_);
lean_dec(v___x_2876_);
v___x_2878_ = l_Lean_Environment_header(v_env_2877_);
v_isModule_2879_ = lean_ctor_get_uint8(v___x_2878_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2878_);
if (v_isModule_2879_ == 0)
{
lean_object* v___x_2880_; 
lean_dec_ref(v_env_2877_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_2880_ = lean_apply_5(v_x_2869_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, lean_box(0));
return v___x_2880_;
}
else
{
uint8_t v_isExporting_2881_; 
v_isExporting_2881_ = lean_ctor_get_uint8(v_env_2877_, sizeof(void*)*13);
lean_dec_ref(v_env_2877_);
if (v_isExporting_2870_ == 0)
{
if (v_isExporting_2881_ == 0)
{
lean_object* v___x_2948_; 
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_2948_ = lean_apply_5(v_x_2869_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, lean_box(0));
return v___x_2948_;
}
else
{
goto v___jp_2882_;
}
}
else
{
if (v_isExporting_2881_ == 0)
{
goto v___jp_2882_;
}
else
{
lean_object* v___x_2949_; 
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_2949_ = lean_apply_5(v_x_2869_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, lean_box(0));
return v___x_2949_;
}
}
v___jp_2882_:
{
lean_object* v___x_2883_; lean_object* v_env_2884_; lean_object* v_nextMacroScope_2885_; lean_object* v_ngen_2886_; lean_object* v_auxDeclNGen_2887_; lean_object* v_traceState_2888_; lean_object* v_recordedDeps_2889_; lean_object* v_messages_2890_; lean_object* v_infoState_2891_; lean_object* v_snapshotTasks_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2946_; 
v___x_2883_ = lean_st_ref_take(v___y_2874_);
v_env_2884_ = lean_ctor_get(v___x_2883_, 0);
v_nextMacroScope_2885_ = lean_ctor_get(v___x_2883_, 1);
v_ngen_2886_ = lean_ctor_get(v___x_2883_, 2);
v_auxDeclNGen_2887_ = lean_ctor_get(v___x_2883_, 3);
v_traceState_2888_ = lean_ctor_get(v___x_2883_, 4);
v_recordedDeps_2889_ = lean_ctor_get(v___x_2883_, 6);
v_messages_2890_ = lean_ctor_get(v___x_2883_, 7);
v_infoState_2891_ = lean_ctor_get(v___x_2883_, 8);
v_snapshotTasks_2892_ = lean_ctor_get(v___x_2883_, 9);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v___x_2883_, 5);
lean_dec(v_unused_2947_);
v___x_2894_ = v___x_2883_;
v_isShared_2895_ = v_isSharedCheck_2946_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_snapshotTasks_2892_);
lean_inc(v_infoState_2891_);
lean_inc(v_messages_2890_);
lean_inc(v_recordedDeps_2889_);
lean_inc(v_traceState_2888_);
lean_inc(v_auxDeclNGen_2887_);
lean_inc(v_ngen_2886_);
lean_inc(v_nextMacroScope_2885_);
lean_inc(v_env_2884_);
lean_dec(v___x_2883_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2946_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2896_ = l_Lean_Environment_setExporting(v_env_2884_, v_isExporting_2870_);
v___x_2897_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 5, v___x_2897_);
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2899_ = v___x_2894_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_nextMacroScope_2885_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_ngen_2886_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_auxDeclNGen_2887_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_traceState_2888_);
lean_ctor_set(v_reuseFailAlloc_2945_, 5, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2945_, 6, v_recordedDeps_2889_);
lean_ctor_set(v_reuseFailAlloc_2945_, 7, v_messages_2890_);
lean_ctor_set(v_reuseFailAlloc_2945_, 8, v_infoState_2891_);
lean_ctor_set(v_reuseFailAlloc_2945_, 9, v_snapshotTasks_2892_);
v___x_2899_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v_mctx_2902_; lean_object* v_zetaDeltaFVarIds_2903_; lean_object* v_postponed_2904_; lean_object* v_diag_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2943_; 
v___x_2900_ = lean_st_ref_put(v___y_2874_, v___x_2899_);
v___x_2901_ = lean_st_ref_take(v___y_2872_);
v_mctx_2902_ = lean_ctor_get(v___x_2901_, 0);
v_zetaDeltaFVarIds_2903_ = lean_ctor_get(v___x_2901_, 2);
v_postponed_2904_ = lean_ctor_get(v___x_2901_, 3);
v_diag_2905_ = lean_ctor_get(v___x_2901_, 4);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; 
v_unused_2944_ = lean_ctor_get(v___x_2901_, 1);
lean_dec(v_unused_2944_);
v___x_2907_ = v___x_2901_;
v_isShared_2908_ = v_isSharedCheck_2943_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_diag_2905_);
lean_inc(v_postponed_2904_);
lean_inc(v_zetaDeltaFVarIds_2903_);
lean_inc(v_mctx_2902_);
lean_dec(v___x_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2943_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2909_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_2909_);
v___x_2911_ = v___x_2907_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_mctx_2902_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2942_, 2, v_zetaDeltaFVarIds_2903_);
lean_ctor_set(v_reuseFailAlloc_2942_, 3, v_postponed_2904_);
lean_ctor_set(v_reuseFailAlloc_2942_, 4, v_diag_2905_);
v___x_2911_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v_r_2913_; 
v___x_2912_ = lean_st_ref_put(v___y_2872_, v___x_2911_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v_r_2913_ = lean_apply_5(v_x_2869_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, lean_box(0));
if (lean_obj_tag(v_r_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2930_; 
v_a_2914_ = lean_ctor_get(v_r_2913_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_r_2913_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2916_ = v_r_2913_;
v_isShared_2917_ = v_isSharedCheck_2930_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v_r_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2930_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
lean_inc(v_a_2914_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set_tag(v___x_2916_, 1);
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
v___x_2920_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2874_, v_isExporting_2881_, v___x_2897_, v___y_2872_, v___x_2909_, v___x_2919_);
lean_dec_ref(v___x_2919_);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; 
v_unused_2928_ = lean_ctor_get(v___x_2920_, 0);
lean_dec(v_unused_2928_);
v___x_2922_ = v___x_2920_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v___x_2920_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v_a_2914_);
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2914_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
v_a_2931_ = lean_ctor_get(v_r_2913_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v_r_2913_, 1);
v___x_2932_ = lean_box(0);
v___x_2933_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___lam__0(v___y_2874_, v_isExporting_2881_, v___x_2897_, v___y_2872_, v___x_2909_, v___x_2932_);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v___x_2933_, 0);
lean_dec(v_unused_2941_);
v___x_2935_ = v___x_2933_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_dec(v___x_2933_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set_tag(v___x_2935_, 1);
lean_ctor_set(v___x_2935_, 0, v_a_2931_);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2931_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg___boxed(lean_object* v_x_2950_, lean_object* v_isExporting_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
uint8_t v_isExporting_boxed_2957_; lean_object* v_res_2958_; 
v_isExporting_boxed_2957_ = lean_unbox(v_isExporting_2951_);
v_res_2958_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_2950_, v_isExporting_boxed_2957_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(lean_object* v_00_u03b1_2959_, lean_object* v_x_2960_, uint8_t v_isExporting_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v_x_2960_, v_isExporting_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___boxed(lean_object* v_00_u03b1_2968_, lean_object* v_x_2969_, lean_object* v_isExporting_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
uint8_t v_isExporting_boxed_2976_; lean_object* v_res_2977_; 
v_isExporting_boxed_2976_ = lean_unbox(v_isExporting_2970_);
v_res_2977_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1(v_00_u03b1_2968_, v_x_2969_, v_isExporting_boxed_2976_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0(lean_object* v_indName_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v___x_2984_; 
lean_inc(v_indName_2978_);
v___x_2984_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(v_indName_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2985_; 
lean_dec_ref_known(v___x_2984_, 1);
lean_inc(v_indName_2978_);
v___x_2985_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(v_indName_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v___x_2986_; 
lean_dec_ref_known(v___x_2985_, 1);
v___x_2986_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(v_indName_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
return v___x_2986_;
}
else
{
lean_dec(v_indName_2978_);
return v___x_2985_;
}
}
else
{
lean_dec(v_indName_2978_);
return v___x_2984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___lam__0___boxed(lean_object* v_indName_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_mkCtorElim___lam__0(v_indName_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(lean_object* v_declName_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v___x_3000_; 
lean_inc(v_declName_2994_);
v___x_3000_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_declName_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3036_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3036_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3036_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
if (lean_obj_tag(v_a_3001_) == 5)
{
lean_object* v_val_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_del_object(v___x_3003_);
v_val_3005_ = lean_ctor_get(v_a_3001_, 0);
lean_inc_ref(v_val_3005_);
lean_dec_ref_known(v_a_3001_, 1);
v___x_3006_ = l_Lean_mkRecName(v_declName_2994_);
v___x_3007_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v___x_3006_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_toConstantVal_3008_; lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3022_; 
v_toConstantVal_3008_ = lean_ctor_get(v_val_3005_, 0);
lean_inc_ref(v_toConstantVal_3008_);
lean_dec_ref(v_val_3005_);
v_a_3009_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3011_ = v___x_3007_;
v_isShared_3012_ = v_isSharedCheck_3022_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3007_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3022_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v_levelParams_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v_levelParams_3013_ = lean_ctor_get(v_toConstantVal_3008_, 1);
lean_inc(v_levelParams_3013_);
lean_dec_ref(v_toConstantVal_3008_);
v___x_3014_ = l_List_lengthTR___redArg(v_levelParams_3013_);
lean_dec(v_levelParams_3013_);
v___x_3015_ = l_Lean_ConstantInfo_levelParams(v_a_3009_);
lean_dec(v_a_3009_);
v___x_3016_ = l_List_lengthTR___redArg(v___x_3015_);
lean_dec(v___x_3015_);
v___x_3017_ = lean_nat_dec_lt(v___x_3014_, v___x_3016_);
lean_dec(v___x_3016_);
lean_dec(v___x_3014_);
v___x_3018_ = lean_box(v___x_3017_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3018_);
v___x_3020_ = v___x_3011_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v_val_3005_);
v_a_3023_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3007_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3007_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
uint8_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
lean_dec(v_a_3001_);
lean_dec(v_declName_2994_);
v___x_3031_ = 0;
v___x_3032_ = lean_box(v___x_3031_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3032_);
v___x_3034_ = v___x_3003_;
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
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_declName_2994_);
v_a_3037_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3000_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3000_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
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
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0___boxed(lean_object* v_declName_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_declName_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim(lean_object* v_indName_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___f_3058_; lean_object* v___x_3059_; lean_object* v_env_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; uint8_t v___x_3063_; 
lean_inc_n(v_indName_3052_, 2);
v___f_3058_ = lean_alloc_closure((void*)(l_Lean_mkCtorElim___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3058_, 0, v_indName_3052_);
v___x_3059_ = lean_st_ref_get(v_a_3056_);
v_env_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc_ref(v_env_3060_);
lean_dec(v___x_3059_);
v___x_3061_ = l_Lean_mkCtorIdxName(v_indName_3052_);
v___x_3062_ = 1;
v___x_3063_ = l_Lean_Environment_contains(v_env_3060_, v___x_3061_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec_ref(v___f_3058_);
lean_dec(v_indName_3052_);
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; 
lean_inc(v_indName_3052_);
v___x_3066_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3128_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3128_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3128_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
if (lean_obj_tag(v_a_3067_) == 5)
{
lean_object* v_val_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v_val_3071_ = lean_ctor_get(v_a_3067_, 0);
lean_inc_ref(v_val_3071_);
lean_dec_ref_known(v_a_3067_, 1);
v___x_3072_ = lean_unsigned_to_nat(1u);
v___x_3073_ = l_Lean_InductiveVal_numCtors(v_val_3071_);
v___x_3074_ = lean_nat_dec_lt(v___x_3072_, v___x_3073_);
lean_dec(v___x_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3077_; 
lean_dec_ref(v_val_3071_);
lean_dec_ref(v___f_3058_);
lean_dec(v_indName_3052_);
v___x_3075_ = lean_box(0);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3075_);
v___x_3077_ = v___x_3069_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
else
{
lean_object* v_toConstantVal_3079_; lean_object* v_type_3080_; lean_object* v___x_3081_; 
lean_del_object(v___x_3069_);
v_toConstantVal_3079_ = lean_ctor_get(v_val_3071_, 0);
lean_inc_ref(v_toConstantVal_3079_);
lean_dec_ref(v_val_3071_);
v_type_3080_ = lean_ctor_get(v_toConstantVal_3079_, 2);
lean_inc_ref(v_type_3080_);
lean_dec_ref(v_toConstantVal_3079_);
v___x_3081_ = l_Lean_Meta_isPropFormerType(v_type_3080_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3115_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3115_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3115_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
uint8_t v___x_3086_; 
v___x_3086_ = lean_unbox(v_a_3082_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; 
lean_del_object(v___x_3084_);
lean_inc(v_indName_3052_);
v___x_3087_ = l_Lean_isLargeEliminating___at___00Lean_mkCtorElim_spec__0(v_indName_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3102_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3102_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3102_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
uint8_t v___x_3092_; 
v___x_3092_ = lean_unbox(v_a_3088_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
lean_dec(v_a_3088_);
lean_dec(v_a_3082_);
lean_dec_ref(v___f_3058_);
lean_dec(v_indName_3052_);
v___x_3093_ = lean_box(0);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3093_);
v___x_3095_ = v___x_3090_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
else
{
uint8_t v___x_3097_; 
lean_del_object(v___x_3090_);
v___x_3097_ = l_Lean_isPrivateName(v_indName_3052_);
lean_dec(v_indName_3052_);
if (v___x_3097_ == 0)
{
uint8_t v___x_3098_; lean_object* v___x_3099_; 
lean_dec(v_a_3082_);
v___x_3098_ = lean_unbox(v_a_3088_);
lean_dec(v_a_3088_);
v___x_3099_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3058_, v___x_3098_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
return v___x_3099_;
}
else
{
uint8_t v___x_3100_; lean_object* v___x_3101_; 
lean_dec(v_a_3088_);
v___x_3100_ = lean_unbox(v_a_3082_);
lean_dec(v_a_3082_);
v___x_3101_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__1___redArg(v___f_3058_, v___x_3100_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v_a_3082_);
lean_dec_ref(v___f_3058_);
lean_dec(v_indName_3052_);
v_a_3103_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3087_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3087_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
lean_dec(v_a_3082_);
lean_dec_ref(v___f_3058_);
lean_dec(v_indName_3052_);
v___x_3111_ = lean_box(0);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3111_);
v___x_3113_ = v___x_3084_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec_ref(v___f_3058_);
lean_dec(v_indName_3052_);
v_a_3116_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3081_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3081_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
lean_dec(v_a_3067_);
lean_dec_ref(v___f_3058_);
lean_dec(v_indName_3052_);
v___x_3124_ = lean_box(0);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3124_);
v___x_3126_ = v___x_3069_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref(v___f_3058_);
lean_dec(v_indName_3052_);
v_a_3129_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3066_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3066_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorElim___boxed(lean_object* v_indName_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_mkCtorElim(v_indName_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v_decl_3144_, lean_object* v_____r_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; 
lean_inc(v_decl_3144_);
v___x_3151_ = l_Lean_mkCtorIdx(v_decl_3144_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v___x_3152_; 
lean_dec_ref_known(v___x_3151_, 1);
v___x_3152_ = l_Lean_mkCtorElim(v_decl_3144_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
return v___x_3152_;
}
else
{
lean_dec(v_decl_3144_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_decl_3153_, lean_object* v_____r_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3153_, v_____r_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
return v_res_3160_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_3163_ = l_Lean_stringToMessageData(v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_3166_ = l_Lean_stringToMessageData(v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_3170_, uint8_t v_kind_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___y_3183_; 
v___x_3177_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_3178_ = l_Lean_MessageData_ofName(v_name_3170_);
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
switch(v_kind_3171_)
{
case 0:
{
lean_object* v___x_3190_; 
v___x_3190_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_3183_ = v___x_3190_;
goto v___jp_3182_;
}
case 1:
{
lean_object* v___x_3191_; 
v___x_3191_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_3183_ = v___x_3191_;
goto v___jp_3182_;
}
default: 
{
lean_object* v___x_3192_; 
v___x_3192_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_3183_ = v___x_3192_;
goto v___jp_3182_;
}
}
v___jp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_inc_ref(v___y_3183_);
v___x_3184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___y_3183_);
v___x_3185_ = l_Lean_MessageData_ofFormat(v___x_3184_);
v___x_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3181_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3186_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_3188_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_3193_, lean_object* v_kind_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
uint8_t v_kind_boxed_3200_; lean_object* v_res_3201_; 
v_kind_boxed_3200_ = lean_unbox(v_kind_3194_);
v_res_3201_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3193_, v_kind_boxed_3200_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
return v_res_3201_;
}
}
static uint64_t _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3208_; uint64_t v___x_3209_; 
v___x_3208_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3208_);
return v___x_3209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_uint64_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3211_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3212_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set_uint64(v___x_3212_, sizeof(void*)*1, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3216_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
lean_ctor_set(v___x_3216_, 2, v___x_3215_);
lean_ctor_set(v___x_3216_, 3, v___x_3215_);
lean_ctor_set(v___x_3216_, 4, v___x_3215_);
lean_ctor_set(v___x_3216_, 5, v___x_3215_);
lean_ctor_set(v___x_3216_, 6, v___x_3215_);
return v___x_3216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
lean_ctor_set(v___x_3218_, 2, v___x_3217_);
lean_ctor_set(v___x_3218_, 3, v___x_3217_);
lean_ctor_set(v___x_3218_, 4, v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3219_, lean_object* v___x_3220_, lean_object* v___x_3221_, lean_object* v_decl_3222_, lean_object* v___stx_3223_, uint8_t v_kind_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
uint8_t v___x_3228_; uint8_t v___x_3229_; uint8_t v___x_3230_; uint8_t v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___y_3251_; 
v___x_3228_ = 0;
v___x_3229_ = l_Lean_instBEqAttributeKind_beq(v_kind_3224_, v___x_3228_);
v___x_3230_ = 1;
v___x_3231_ = 0;
v___x_3232_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3233_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3234_ = lean_unsigned_to_nat(32u);
v___x_3235_ = lean_mk_empty_array_with_capacity(v___x_3234_);
v___x_3236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3237_ = ((size_t)5ULL);
lean_inc_n(v___x_3219_, 6);
v___x_3238_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3235_);
lean_ctor_set(v___x_3238_, 2, v___x_3219_);
lean_ctor_set(v___x_3238_, 3, v___x_3219_);
lean_ctor_set_usize(v___x_3238_, 4, v___x_3237_);
v___x_3239_ = lean_box(1);
lean_inc_ref(v___x_3238_);
v___x_3240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3233_);
lean_ctor_set(v___x_3240_, 1, v___x_3238_);
lean_ctor_set(v___x_3240_, 2, v___x_3239_);
v___x_3241_ = lean_mk_empty_array_with_capacity(v___x_3219_);
v___x_3242_ = lean_box(0);
lean_inc(v___x_3220_);
v___x_3243_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3243_, 0, v___x_3232_);
lean_ctor_set(v___x_3243_, 1, v___x_3220_);
lean_ctor_set(v___x_3243_, 2, v___x_3240_);
lean_ctor_set(v___x_3243_, 3, v___x_3241_);
lean_ctor_set(v___x_3243_, 4, v___x_3242_);
lean_ctor_set(v___x_3243_, 5, v___x_3219_);
lean_ctor_set(v___x_3243_, 6, v___x_3242_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7, v___x_3231_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 1, v___x_3231_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 2, v___x_3231_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 3, v___x_3230_);
v___x_3244_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3245_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3219_);
lean_ctor_set(v___x_3245_, 1, v___x_3219_);
lean_ctor_set(v___x_3245_, 2, v___x_3219_);
lean_ctor_set(v___x_3245_, 3, v___x_3219_);
lean_ctor_set(v___x_3245_, 4, v___x_3233_);
lean_ctor_set(v___x_3245_, 5, v___x_3233_);
lean_ctor_set(v___x_3245_, 6, v___x_3233_);
lean_ctor_set(v___x_3245_, 7, v___x_3233_);
lean_ctor_set(v___x_3245_, 8, v___x_3233_);
lean_ctor_set(v___x_3245_, 9, v___x_3233_);
lean_ctor_set(v___x_3245_, 10, v___x_3233_);
lean_ctor_set(v___x_3245_, 11, v___x_3244_);
v___x_3246_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3247_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3245_);
lean_ctor_set(v___x_3248_, 1, v___x_3246_);
lean_ctor_set(v___x_3248_, 2, v___x_3220_);
lean_ctor_set(v___x_3248_, 3, v___x_3238_);
lean_ctor_set(v___x_3248_, 4, v___x_3247_);
v___x_3249_ = lean_st_mk_ref(v___x_3248_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3261_; 
lean_dec(v_decl_3222_);
v___x_3261_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v___x_3221_, v_kind_3224_, v___x_3243_, v___x_3249_, v___y_3225_, v___y_3226_);
lean_dec(v___x_3249_);
lean_dec_ref_known(v___x_3243_, 7);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
lean_dec(v___x_3221_);
v___x_3262_ = lean_box(0);
v___x_3263_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_3222_, v___x_3262_, v___x_3243_, v___x_3249_, v___y_3225_, v___y_3226_);
lean_dec_ref_known(v___x_3243_, 7);
v___y_3251_ = v___x_3263_;
goto v___jp_3250_;
}
v___jp_3250_:
{
if (lean_obj_tag(v___y_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3260_; 
v_a_3252_ = lean_ctor_get(v___y_3251_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___y_3251_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3254_ = v___y_3251_;
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___y_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3256_ = lean_st_ref_get(v___x_3249_);
lean_dec(v___x_3249_);
lean_dec(v___x_3256_);
if (v_isShared_3255_ == 0)
{
v___x_3258_ = v___x_3254_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3252_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
else
{
lean_dec(v___x_3249_);
return v___y_3251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v___x_3266_, lean_object* v_decl_3267_, lean_object* v___stx_3268_, lean_object* v_kind_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v_kind_boxed_3273_; lean_object* v_res_3274_; 
v_kind_boxed_3273_ = lean_unbox(v_kind_3269_);
v_res_3274_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3264_, v___x_3265_, v___x_3266_, v_decl_3267_, v___stx_3268_, v_kind_boxed_3273_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___stx_3268_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; lean_object* v_toCold_3280_; lean_object* v_env_3281_; lean_object* v_options_3282_; uint8_t v___x_3283_; lean_object* v_env_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3279_ = lean_st_ref_get(v___y_3277_);
v_toCold_3280_ = lean_ctor_get(v___y_3276_, 0);
v_env_3281_ = lean_ctor_get(v___x_3279_, 0);
lean_inc_ref(v_env_3281_);
lean_dec(v___x_3279_);
v_options_3282_ = lean_ctor_get(v_toCold_3280_, 2);
v___x_3283_ = 0;
v_env_3284_ = l_Lean_Environment_setRecordingDeps(v_env_3281_, v___x_3283_);
v___x_3285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3286_ = lean_unsigned_to_nat(32u);
v___x_3287_ = lean_mk_empty_array_with_capacity(v___x_3286_);
lean_dec_ref(v___x_3287_);
v___x_3288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
lean_inc_ref(v_options_3282_);
v___x_3289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3289_, 0, v_env_3284_);
lean_ctor_set(v___x_3289_, 1, v___x_3285_);
lean_ctor_set(v___x_3289_, 2, v___x_3288_);
lean_ctor_set(v___x_3289_, 3, v_options_3282_);
v___x_3290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_ctor_set(v___x_3290_, 1, v_msgData_3275_);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_ref_3301_; lean_object* v___x_3302_; lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3311_; 
v_ref_3301_ = lean_ctor_get(v___y_3298_, 2);
v___x_3302_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msg_3297_, v___y_3298_, v___y_3299_);
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3307_; lean_object* v___x_3309_; 
lean_inc(v_ref_3301_);
v___x_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3307_, 0, v_ref_3301_);
lean_ctor_set(v___x_3307_, 1, v_a_3303_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 1);
lean_ctor_set(v___x_3305_, 0, v___x_3307_);
v___x_3309_ = v___x_3305_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
return v_res_3316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(lean_object* v___x_3323_, lean_object* v_decl_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3328_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3329_ = l_Lean_MessageData_ofName(v___x_3323_);
v___x_3330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
v___x_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3330_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v___x_3332_, v___y_3325_, v___y_3326_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v___x_3334_, lean_object* v_decl_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_3334_, v_decl_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v_decl_3335_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3421_ = l_Lean_registerBuiltinAttribute(v___x_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3424_, lean_object* v_msg_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_3425_, v___y_3426_, v___y_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3430_, lean_object* v_msg_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(v_00_u03b1_3430_, v_msg_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_3436_, lean_object* v_name_3437_, uint8_t v_kind_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_3437_, v_kind_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_3445_, lean_object* v_name_3446_, lean_object* v_kind_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v_kind_boxed_3453_; lean_object* v_res_3454_; 
v_kind_boxed_3453_ = lean_unbox(v_kind_3447_);
v_res_3454_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(v_00_u03b1_3445_, v_name_3446_, v_kind_boxed_3453_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3457_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3458_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_));
v___x_3459_ = l_Lean_addBuiltinDocString(v___x_3457_, v___x_3458_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(lean_object* v_a_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
return v_res_3461_;
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
