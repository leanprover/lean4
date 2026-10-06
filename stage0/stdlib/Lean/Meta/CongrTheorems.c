// Lean compiler output
// Module: Lean.Meta.CongrTheorems
// Imports: public import Lean.AddDecl public import Lean.ReservedNameAction import Lean.Structure import Lean.Meta.Tactic.Subst import Lean.Meta.FunInfo
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_isClass(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo_default;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x21(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedCongrArgKind_default;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedCongrArgKind;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.CongrArgKind.fixed"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.CongrArgKind.fixedNoParam"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.CongrArgKind.eq"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.CongrArgKind.cast"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__6 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__7 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.CongrArgKind.heq"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__8 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__9 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__9_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.CongrArgKind.subsingletonInst"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__10 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__11 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__11_value;
static lean_once_cell_t l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__12;
static lean_once_cell_t l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCongrArgKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCongrArgKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCongrArgKind___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCongrArgKind = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqCongrArgKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqCongrArgKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqCongrArgKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqCongrArgKind___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqCongrArgKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqCongrArgKind = (const lean_object*)&l_Lean_Meta_instBEqCongrArgKind___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 154, 90, 102, 217, 192, 49, 255)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1_value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "failed to generate `hcongr` theorem: expected "};
static const lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " arguments, but got "};
static const lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " for"};
static const lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_getCongrSimpKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_getCongrSimpKinds___closed__0 = (const lean_object*)&l_Lean_Meta_getCongrSimpKinds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(79, 85, 152, 16, 239, 41, 62, 212)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "_private.Lean.Meta.CongrTheorems.0.Lean.Meta.mkCongrSimpCore\?.mkProof.go"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.CongrTheorems"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.CongrTheorems.0.Lean.Meta.mkCongrSimpCore\?.mk\?.go"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "e_"};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_hcongrThmSuffixBase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hcongr"};
static const lean_object* l_Lean_Meta_hcongrThmSuffixBase___closed__0 = (const lean_object*)&l_Lean_Meta_hcongrThmSuffixBase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_hcongrThmSuffixBase = (const lean_object*)&l_Lean_Meta_hcongrThmSuffixBase___closed__0_value;
static const lean_string_object l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hcongr_"};
static const lean_object* l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0 = (const lean_object*)&l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_hcongrThmSuffixBasePrefix = (const lean_object*)&l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_congrSimpSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "congr_simp"};
static const lean_object* l_Lean_Meta_congrSimpSuffix___closed__0 = (const lean_object*)&l_Lean_Meta_congrSimpSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_congrSimpSuffix = (const lean_object*)&l_Lean_Meta_congrSimpSuffix___closed__0_value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 141, 208, 58, 7, 230, 107, 112)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "CongrTheorems"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 224, 213, 6, 189, 51, 239, 200)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(146, 140, 44, 156, 105, 54, 226, 29)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 41, 252, 212, 29, 253, 12, 67)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 81, 65, 75, 45, 89, 43, 189)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 167, 132, 254, 103, 165, 136, 43)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 26, 60, 185, 66, 206, 188, 95)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 26, 15, 119, 133, 253, 114, 42)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 116, 182, 41, 116, 135, 13, 170)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 27, 116, 143, 64, 80, 226, 54)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "congrKindsExt"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 7, 195, 199, 246, 152, 65, 143)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrKindsExt;
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declared `"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.mkHCongrWithArityForConst\?"};
static const lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.mkCongrSimpForConst\?"};
static const lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "failed to generate `"};
static const lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1;
static const lean_string_object l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Meta_CongrArgKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_CongrArgKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Meta_CongrArgKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg(lean_object* v_fixed_22_){
_start:
{
lean_inc(v_fixed_22_);
return v_fixed_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg___boxed(lean_object* v_fixed_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_CongrArgKind_fixed_elim___redArg(v_fixed_23_);
lean_dec(v_fixed_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_fixed_28_){
_start:
{
lean_inc(v_fixed_28_);
return v_fixed_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_fixed_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Meta_CongrArgKind_fixed_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_fixed_32_);
lean_dec(v_fixed_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(lean_object* v_fixedNoParam_35_){
_start:
{
lean_inc(v_fixedNoParam_35_);
return v_fixedNoParam_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg___boxed(lean_object* v_fixedNoParam_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(v_fixedNoParam_36_);
lean_dec(v_fixedNoParam_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_fixedNoParam_41_){
_start:
{
lean_inc(v_fixedNoParam_41_);
return v_fixedNoParam_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_fixedNoParam_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_fixedNoParam_45_);
lean_dec(v_fixedNoParam_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg(lean_object* v_eq_48_){
_start:
{
lean_inc(v_eq_48_);
return v_eq_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg___boxed(lean_object* v_eq_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_CongrArgKind_eq_elim___redArg(v_eq_49_);
lean_dec(v_eq_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_eq_54_){
_start:
{
lean_inc(v_eq_54_);
return v_eq_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_eq_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Meta_CongrArgKind_eq_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_eq_58_);
lean_dec(v_eq_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg(lean_object* v_cast_61_){
_start:
{
lean_inc(v_cast_61_);
return v_cast_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg___boxed(lean_object* v_cast_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Meta_CongrArgKind_cast_elim___redArg(v_cast_62_);
lean_dec(v_cast_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_cast_67_){
_start:
{
lean_inc(v_cast_67_);
return v_cast_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_cast_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Meta_CongrArgKind_cast_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_cast_71_);
lean_dec(v_cast_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg(lean_object* v_heq_74_){
_start:
{
lean_inc(v_heq_74_);
return v_heq_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg___boxed(lean_object* v_heq_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Meta_CongrArgKind_heq_elim___redArg(v_heq_75_);
lean_dec(v_heq_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_heq_80_){
_start:
{
lean_inc(v_heq_80_);
return v_heq_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_heq_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l_Lean_Meta_CongrArgKind_heq_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_heq_84_);
lean_dec(v_heq_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(lean_object* v_subsingletonInst_87_){
_start:
{
lean_inc(v_subsingletonInst_87_);
return v_subsingletonInst_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg___boxed(lean_object* v_subsingletonInst_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(v_subsingletonInst_88_);
lean_dec(v_subsingletonInst_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim(lean_object* v_motive_90_, uint8_t v_t_91_, lean_object* v_h_92_, lean_object* v_subsingletonInst_93_){
_start:
{
lean_inc(v_subsingletonInst_93_);
return v_subsingletonInst_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_subsingletonInst_97_){
_start:
{
uint8_t v_t_boxed_98_; lean_object* v_res_99_; 
v_t_boxed_98_ = lean_unbox(v_t_95_);
v_res_99_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim(v_motive_94_, v_t_boxed_98_, v_h_96_, v_subsingletonInst_97_);
lean_dec(v_subsingletonInst_97_);
return v_res_99_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind_default(void){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind(void){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_to_int(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_to_int(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr(uint8_t v_x_124_, lean_object* v_prec_125_){
_start:
{
lean_object* v___y_127_; lean_object* v___y_134_; lean_object* v___y_141_; lean_object* v___y_148_; lean_object* v___y_155_; lean_object* v___y_162_; 
switch(v_x_124_)
{
case 0:
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(1024u);
v___x_169_ = lean_nat_dec_le(v___x_168_, v_prec_125_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_127_ = v___x_170_;
goto v___jp_126_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_127_ = v___x_171_;
goto v___jp_126_;
}
}
case 1:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_125_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_134_ = v___x_174_;
goto v___jp_133_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_134_ = v___x_175_;
goto v___jp_133_;
}
}
case 2:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1024u);
v___x_177_ = lean_nat_dec_le(v___x_176_, v_prec_125_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_141_ = v___x_178_;
goto v___jp_140_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_141_ = v___x_179_;
goto v___jp_140_;
}
}
case 3:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1024u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v_prec_125_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_148_ = v___x_182_;
goto v___jp_147_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_148_ = v___x_183_;
goto v___jp_147_;
}
}
case 4:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1024u);
v___x_185_ = lean_nat_dec_le(v___x_184_, v_prec_125_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_155_ = v___x_186_;
goto v___jp_154_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_155_ = v___x_187_;
goto v___jp_154_;
}
}
default: 
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(1024u);
v___x_189_ = lean_nat_dec_le(v___x_188_, v_prec_125_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_162_ = v___x_190_;
goto v___jp_161_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_162_ = v___x_191_;
goto v___jp_161_;
}
}
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_128_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__1));
lean_inc(v___y_127_);
v___x_129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_129_, 0, v___y_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = 0;
v___x_131_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_130_);
v___x_132_ = l_Repr_addAppParen(v___x_131_, v_prec_125_);
return v___x_132_;
}
v___jp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_135_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__3));
lean_inc(v___y_134_);
v___x_136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_136_, 0, v___y_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = 0;
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_137_);
v___x_139_ = l_Repr_addAppParen(v___x_138_, v_prec_125_);
return v___x_139_;
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_142_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__5));
lean_inc(v___y_141_);
v___x_143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_143_, 0, v___y_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = 0;
v___x_145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set_uint8(v___x_145_, sizeof(void*)*1, v___x_144_);
v___x_146_ = l_Repr_addAppParen(v___x_145_, v_prec_125_);
return v___x_146_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_149_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__7));
lean_inc(v___y_148_);
v___x_150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_150_, 0, v___y_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = 0;
v___x_152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_151_);
v___x_153_ = l_Repr_addAppParen(v___x_152_, v_prec_125_);
return v___x_153_;
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__9));
lean_inc(v___y_155_);
v___x_157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_157_, 0, v___y_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = 0;
v___x_159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_158_);
v___x_160_ = l_Repr_addAppParen(v___x_159_, v_prec_125_);
return v___x_160_;
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_163_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__11));
lean_inc(v___y_162_);
v___x_164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_164_, 0, v___y_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_165_);
v___x_167_ = l_Repr_addAppParen(v___x_166_, v_prec_125_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr___boxed(lean_object* v_x_192_, lean_object* v_prec_193_){
_start:
{
uint8_t v_x_333__boxed_194_; lean_object* v_res_195_; 
v_x_333__boxed_194_ = lean_unbox(v_x_192_);
v_res_195_ = l_Lean_Meta_instReprCongrArgKind_repr(v_x_333__boxed_194_, v_prec_193_);
lean_dec(v_prec_193_);
return v_res_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t v_x_198_, uint8_t v_y_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_200_ = lean_box(v_x_198_);
v___x_201_ = lean_obj_tag_nat(v___x_200_);
lean_dec(v___x_200_);
v___x_202_ = lean_box(v_y_199_);
v___x_203_ = lean_obj_tag_nat(v___x_202_);
lean_dec(v___x_202_);
v___x_204_ = lean_nat_dec_eq(v___x_201_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqCongrArgKind_beq___boxed(lean_object* v_x_205_, lean_object* v_y_206_){
_start:
{
uint8_t v_x_24__boxed_207_; uint8_t v_y_25__boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_x_24__boxed_207_ = lean_unbox(v_x_205_);
v_y_25__boxed_208_ = lean_unbox(v_y_206_);
v_res_209_ = l_Lean_Meta_instBEqCongrArgKind_beq(v_x_24__boxed_207_, v_y_25__boxed_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(lean_object* v_as_214_, size_t v_sz_215_, size_t v_i_216_, lean_object* v_b_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_usize_dec_lt(v_i_216_, v_sz_215_);
if (v___x_218_ == 0)
{
return v_b_217_;
}
else
{
lean_object* v_a_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; size_t v___x_226_; size_t v___x_227_; 
v_a_219_ = lean_array_uget_borrowed(v_as_214_, v_i_216_);
lean_inc_ref(v_b_217_);
v___x_220_ = l_Lean_LocalContext_getFVar_x21(v_b_217_, v_a_219_);
v___x_221_ = l_Lean_LocalDecl_fvarId(v___x_220_);
v___x_222_ = l_Lean_LocalDecl_userName(v___x_220_);
lean_dec_ref(v___x_220_);
v___x_223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0));
v___x_224_ = lean_name_append_after(v___x_222_, v___x_223_);
v___x_225_ = l_Lean_LocalContext_setUserName(v_b_217_, v___x_221_, v___x_224_);
v___x_226_ = ((size_t)1ULL);
v___x_227_ = lean_usize_add(v_i_216_, v___x_226_);
v_i_216_ = v___x_227_;
v_b_217_ = v___x_225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(lean_object* v_as_229_, lean_object* v_sz_230_, lean_object* v_i_231_, lean_object* v_b_232_){
_start:
{
size_t v_sz_boxed_233_; size_t v_i_boxed_234_; lean_object* v_res_235_; 
v_sz_boxed_233_ = lean_unbox_usize(v_sz_230_);
lean_dec(v_sz_230_);
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_res_235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_as_229_, v_sz_boxed_233_, v_i_boxed_234_, v_b_232_);
lean_dec_ref(v_as_229_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(lean_object* v_ys_236_, lean_object* v_lctx_237_){
_start:
{
size_t v_sz_238_; size_t v___x_239_; lean_object* v___x_240_; 
v_sz_238_ = lean_array_size(v_ys_236_);
v___x_239_ = ((size_t)0ULL);
v___x_240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_ys_236_, v_sz_238_, v___x_239_, v_lctx_237_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(lean_object* v_ys_241_, lean_object* v_lctx_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_241_, v_lctx_242_);
lean_dec_ref(v_ys_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(lean_object* v_as_244_, size_t v_sz_245_, size_t v_i_246_, lean_object* v_b_247_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = lean_usize_dec_lt(v_i_246_, v_sz_245_);
if (v___x_248_ == 0)
{
return v_b_247_;
}
else
{
lean_object* v_a_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; size_t v___x_254_; size_t v___x_255_; 
v_a_249_ = lean_array_uget_borrowed(v_as_244_, v_i_246_);
lean_inc_ref(v_b_247_);
v___x_250_ = l_Lean_LocalContext_getFVar_x21(v_b_247_, v_a_249_);
v___x_251_ = l_Lean_LocalDecl_fvarId(v___x_250_);
lean_dec_ref(v___x_250_);
v___x_252_ = 0;
v___x_253_ = l_Lean_LocalContext_setBinderInfo(v_b_247_, v___x_251_, v___x_252_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_246_, v___x_254_);
v_i_246_ = v___x_255_;
v_b_247_ = v___x_253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(lean_object* v_as_257_, lean_object* v_sz_258_, lean_object* v_i_259_, lean_object* v_b_260_){
_start:
{
size_t v_sz_boxed_261_; size_t v_i_boxed_262_; lean_object* v_res_263_; 
v_sz_boxed_261_ = lean_unbox_usize(v_sz_258_);
lean_dec(v_sz_258_);
v_i_boxed_262_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_as_257_, v_sz_boxed_261_, v_i_boxed_262_, v_b_260_);
lean_dec_ref(v_as_257_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(lean_object* v_ys_264_, lean_object* v_lctx_265_){
_start:
{
size_t v_sz_266_; size_t v___x_267_; lean_object* v___x_268_; 
v_sz_266_ = lean_array_size(v_ys_264_);
v___x_267_ = ((size_t)0ULL);
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_ys_264_, v_sz_266_, v___x_267_, v_lctx_265_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(lean_object* v_ys_269_, lean_object* v_lctx_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_269_, v_lctx_270_);
lean_dec_ref(v_ys_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_272_, lean_object* v_b_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
lean_inc(v___y_275_);
lean_inc_ref(v___y_274_);
v___x_279_ = lean_apply_6(v_k_272_, v_b_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, lean_box(0));
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_280_, lean_object* v_b_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_280_, v_b_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(lean_object* v_name_288_, uint8_t v_bi_289_, lean_object* v_type_290_, lean_object* v_k_291_, uint8_t v_kind_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___f_298_; lean_object* v___x_299_; 
v___f_298_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_298_, 0, v_k_291_);
v___x_299_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_288_, v_bi_289_, v_type_290_, v___f_298_, v_kind_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_a_308_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_299_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_299_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_316_, lean_object* v_bi_317_, lean_object* v_type_318_, lean_object* v_k_319_, lean_object* v_kind_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
uint8_t v_bi_boxed_326_; uint8_t v_kind_boxed_327_; lean_object* v_res_328_; 
v_bi_boxed_326_ = lean_unbox(v_bi_317_);
v_kind_boxed_327_ = lean_unbox(v_kind_320_);
v_res_328_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_316_, v_bi_boxed_326_, v_type_318_, v_k_319_, v_kind_boxed_327_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(lean_object* v_name_329_, lean_object* v_type_330_, lean_object* v_k_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = 0;
v___x_338_ = 0;
v___x_339_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_329_, v___x_337_, v_type_330_, v_k_331_, v___x_338_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg___boxed(lean_object* v_name_340_, lean_object* v_type_341_, lean_object* v_k_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_340_, v_type_341_, v_k_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_eqs_352_, lean_object* v_kinds_353_, lean_object* v_xs_354_, lean_object* v_ys_355_, lean_object* v_k_356_, lean_object* v___x_357_, lean_object* v_h_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(v_eqs_352_, v_kinds_353_, v_xs_354_, v_ys_355_, v_k_356_, v___x_357_, v_h_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___x_357_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(lean_object* v_eqs_365_, lean_object* v_kinds_366_, lean_object* v_xs_367_, lean_object* v_ys_368_, lean_object* v_k_369_, lean_object* v___x_370_, lean_object* v_h_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_377_ = lean_array_push(v_eqs_365_, v_h_371_);
v___x_378_ = 2;
v___x_379_ = lean_box(v___x_378_);
v___x_380_ = lean_array_push(v_kinds_366_, v___x_379_);
v___x_381_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_367_, v_ys_368_, v_k_369_, v___x_370_, v___x_377_, v___x_380_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(lean_object* v_eqs_382_, lean_object* v_kinds_383_, lean_object* v_xs_384_, lean_object* v_ys_385_, lean_object* v_k_386_, lean_object* v___x_387_, lean_object* v_h_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(v_eqs_382_, v_kinds_383_, v_xs_384_, v_ys_385_, v_k_386_, v___x_387_, v_h_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___x_387_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(lean_object* v_xs_395_, lean_object* v_ys_396_, lean_object* v_k_397_, lean_object* v_i_398_, lean_object* v_eqs_399_, lean_object* v_kinds_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_array_get_size(v_xs_395_);
v___x_407_ = lean_nat_dec_lt(v_i_398_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec_ref(v_ys_396_);
lean_dec_ref(v_xs_395_);
lean_inc(v_a_404_);
lean_inc_ref(v_a_403_);
lean_inc(v_a_402_);
lean_inc_ref(v_a_401_);
v___x_408_ = lean_apply_7(v_k_397_, v_eqs_399_, v_kinds_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, lean_box(0));
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v_x_410_; lean_object* v_y_411_; lean_object* v___x_412_; 
v___x_409_ = l_Lean_instInhabitedExpr;
v_x_410_ = lean_array_get_borrowed(v___x_409_, v_xs_395_, v_i_398_);
v_y_411_ = lean_array_get_borrowed(v___x_409_, v_ys_396_, v_i_398_);
lean_inc(v_a_404_);
lean_inc_ref(v_a_403_);
lean_inc(v_a_402_);
lean_inc_ref(v_a_401_);
lean_inc(v_x_410_);
v___x_412_ = lean_infer_type(v_x_410_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = l_Lean_Expr_cleanupAnnotations(v_a_413_);
lean_inc(v_a_404_);
lean_inc_ref(v_a_403_);
lean_inc(v_a_402_);
lean_inc_ref(v_a_401_);
lean_inc(v_y_411_);
v___x_415_ = lean_infer_type(v_y_411_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_415_, 1);
v___x_417_ = l_Lean_Expr_cleanupAnnotations(v_a_416_);
v___x_418_ = lean_expr_eqv(v___x_414_, v___x_417_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_414_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_inc(v_y_411_);
lean_inc(v_x_410_);
v___x_419_ = l_Lean_Meta_mkHEq(v_x_410_, v_y_411_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1));
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_i_398_, v___x_422_);
lean_inc(v___x_423_);
v___f_424_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_424_, 0, v_eqs_399_);
lean_closure_set(v___f_424_, 1, v_kinds_400_);
lean_closure_set(v___f_424_, 2, v_xs_395_);
lean_closure_set(v___f_424_, 3, v_ys_396_);
lean_closure_set(v___f_424_, 4, v_k_397_);
lean_closure_set(v___f_424_, 5, v___x_423_);
v___x_425_ = lean_name_append_index_after(v___x_421_, v___x_423_);
v___x_426_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_425_, v_a_420_, v___f_424_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_426_;
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v_kinds_400_);
lean_dec_ref(v_eqs_399_);
lean_dec_ref(v_k_397_);
lean_dec_ref(v_ys_396_);
lean_dec_ref(v_xs_395_);
v_a_427_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_419_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_419_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v___x_435_; 
lean_inc(v_y_411_);
lean_inc(v_x_410_);
v___x_435_ = l_Lean_Meta_mkEq(v_x_410_, v_y_411_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1));
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_i_398_, v___x_438_);
lean_inc(v___x_439_);
v___f_440_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_440_, 0, v_eqs_399_);
lean_closure_set(v___f_440_, 1, v_kinds_400_);
lean_closure_set(v___f_440_, 2, v_xs_395_);
lean_closure_set(v___f_440_, 3, v_ys_396_);
lean_closure_set(v___f_440_, 4, v_k_397_);
lean_closure_set(v___f_440_, 5, v___x_439_);
v___x_441_ = lean_name_append_index_after(v___x_437_, v___x_439_);
v___x_442_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_441_, v_a_436_, v___f_440_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_kinds_400_);
lean_dec_ref(v_eqs_399_);
lean_dec_ref(v_k_397_);
lean_dec_ref(v_ys_396_);
lean_dec_ref(v_xs_395_);
v_a_443_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_435_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_435_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v___x_414_);
lean_dec_ref(v_kinds_400_);
lean_dec_ref(v_eqs_399_);
lean_dec_ref(v_k_397_);
lean_dec_ref(v_ys_396_);
lean_dec_ref(v_xs_395_);
v_a_451_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_415_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_415_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v_kinds_400_);
lean_dec_ref(v_eqs_399_);
lean_dec_ref(v_k_397_);
lean_dec_ref(v_ys_396_);
lean_dec_ref(v_xs_395_);
v_a_459_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_412_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_412_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(lean_object* v_eqs_467_, lean_object* v_kinds_468_, lean_object* v_xs_469_, lean_object* v_ys_470_, lean_object* v_k_471_, lean_object* v___x_472_, lean_object* v_h_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_479_ = lean_array_push(v_eqs_467_, v_h_473_);
v___x_480_ = 4;
v___x_481_ = lean_box(v___x_480_);
v___x_482_ = lean_array_push(v_kinds_468_, v___x_481_);
v___x_483_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_469_, v_ys_470_, v_k_471_, v___x_472_, v___x_479_, v___x_482_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(lean_object* v_xs_484_, lean_object* v_ys_485_, lean_object* v_k_486_, lean_object* v_i_487_, lean_object* v_eqs_488_, lean_object* v_kinds_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_484_, v_ys_485_, v_k_486_, v_i_487_, v_eqs_488_, v_kinds_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_i_487_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_object* v_00_u03b1_496_, lean_object* v_xs_497_, lean_object* v_ys_498_, lean_object* v_k_499_, lean_object* v_i_500_, lean_object* v_eqs_501_, lean_object* v_kinds_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_497_, v_ys_498_, v_k_499_, v_i_500_, v_eqs_501_, v_kinds_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(lean_object* v_00_u03b1_509_, lean_object* v_xs_510_, lean_object* v_ys_511_, lean_object* v_k_512_, lean_object* v_i_513_, lean_object* v_eqs_514_, lean_object* v_kinds_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(v_00_u03b1_509_, v_xs_510_, v_ys_511_, v_k_512_, v_i_513_, v_eqs_514_, v_kinds_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_i_513_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(lean_object* v_00_u03b1_522_, lean_object* v_name_523_, uint8_t v_bi_524_, lean_object* v_type_525_, lean_object* v_k_526_, uint8_t v_kind_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_523_, v_bi_524_, v_type_525_, v_k_526_, v_kind_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_534_, lean_object* v_name_535_, lean_object* v_bi_536_, lean_object* v_type_537_, lean_object* v_k_538_, lean_object* v_kind_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
uint8_t v_bi_boxed_545_; uint8_t v_kind_boxed_546_; lean_object* v_res_547_; 
v_bi_boxed_545_ = lean_unbox(v_bi_536_);
v_kind_boxed_546_ = lean_unbox(v_kind_539_);
v_res_547_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_534_, v_name_535_, v_bi_boxed_545_, v_type_537_, v_k_538_, v_kind_boxed_546_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(lean_object* v_00_u03b1_548_, lean_object* v_name_549_, lean_object* v_type_550_, lean_object* v_k_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_549_, v_type_550_, v_k_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___boxed(lean_object* v_00_u03b1_558_, lean_object* v_name_559_, lean_object* v_type_560_, lean_object* v_k_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(v_00_u03b1_558_, v_name_559_, v_type_560_, v_k_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(lean_object* v_xs_570_, lean_object* v_ys_571_, lean_object* v_k_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_580_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_570_, v_ys_571_, v_k_572_, v___x_578_, v___x_579_, v___x_579_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___boxed(lean_object* v_xs_581_, lean_object* v_ys_582_, lean_object* v_k_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_581_, v_ys_582_, v_k_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(lean_object* v_00_u03b1_590_, lean_object* v_xs_591_, lean_object* v_ys_592_, lean_object* v_k_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_591_, v_ys_592_, v_k_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed(lean_object* v_00_u03b1_600_, lean_object* v_xs_601_, lean_object* v_ys_602_, lean_object* v_k_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(v_00_u03b1_600_, v_xs_601_, v_ys_602_, v_k_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(lean_object* v_k_610_, lean_object* v_b_611_, lean_object* v_c_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc(v___y_614_);
lean_inc_ref(v___y_613_);
v___x_618_ = lean_apply_7(v_k_610_, v_b_611_, v_c_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, lean_box(0));
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed(lean_object* v_k_619_, lean_object* v_b_620_, lean_object* v_c_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(v_k_619_, v_b_620_, v_c_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(lean_object* v_type_628_, lean_object* v_maxFVars_x3f_629_, lean_object* v_k_630_, uint8_t v_cleanupAnnotations_631_, uint8_t v_whnfType_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___f_638_; lean_object* v___x_639_; 
v___f_638_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_638_, 0, v_k_630_);
v___x_639_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_628_, v_maxFVars_x3f_629_, v___f_638_, v_cleanupAnnotations_631_, v_whnfType_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_639_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_639_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___boxed(lean_object* v_type_656_, lean_object* v_maxFVars_x3f_657_, lean_object* v_k_658_, lean_object* v_cleanupAnnotations_659_, lean_object* v_whnfType_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_666_; uint8_t v_whnfType_boxed_667_; lean_object* v_res_668_; 
v_cleanupAnnotations_boxed_666_ = lean_unbox(v_cleanupAnnotations_659_);
v_whnfType_boxed_667_ = lean_unbox(v_whnfType_660_);
v_res_668_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_656_, v_maxFVars_x3f_657_, v_k_658_, v_cleanupAnnotations_boxed_666_, v_whnfType_boxed_667_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(lean_object* v_00_u03b1_669_, lean_object* v_type_670_, lean_object* v_maxFVars_x3f_671_, lean_object* v_k_672_, uint8_t v_cleanupAnnotations_673_, uint8_t v_whnfType_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_670_, v_maxFVars_x3f_671_, v_k_672_, v_cleanupAnnotations_673_, v_whnfType_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___boxed(lean_object* v_00_u03b1_681_, lean_object* v_type_682_, lean_object* v_maxFVars_x3f_683_, lean_object* v_k_684_, lean_object* v_cleanupAnnotations_685_, lean_object* v_whnfType_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_692_; uint8_t v_whnfType_boxed_693_; lean_object* v_res_694_; 
v_cleanupAnnotations_boxed_692_ = lean_unbox(v_cleanupAnnotations_685_);
v_whnfType_boxed_693_ = lean_unbox(v_whnfType_686_);
v_res_694_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(v_00_u03b1_681_, v_type_682_, v_maxFVars_x3f_683_, v_k_684_, v_cleanupAnnotations_boxed_692_, v_whnfType_boxed_693_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v_a_708_, lean_object* v_type_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_1746__boxed_715_; lean_object* v_res_716_; 
v___x_1746__boxed_715_ = lean_unbox(v___x_705_);
v_res_716_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(v___x_703_, v___x_704_, v___x_1746__boxed_715_, v___x_706_, v___x_707_, v_a_708_, v_type_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_a_708_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(lean_object* v_type_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_724_ = lean_unsigned_to_nat(3u);
v___x_725_ = l_Lean_Expr_isAppOfArity(v_type_717_, v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3));
v___x_727_ = lean_unsigned_to_nat(4u);
v___x_728_ = l_Lean_Expr_isAppOfArity(v_type_717_, v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___f_733_; uint8_t v___x_734_; lean_object* v___x_735_; 
v___x_729_ = l_Lean_instInhabitedExpr;
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_732_ = lean_box(v___x_728_);
v___f_733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed), 12, 5);
lean_closure_set(v___f_733_, 0, v___x_729_);
lean_closure_set(v___f_733_, 1, v___x_730_);
lean_closure_set(v___f_733_, 2, v___x_732_);
lean_closure_set(v___f_733_, 3, v___x_724_);
lean_closure_set(v___f_733_, 4, v___x_731_);
v___x_734_ = 1;
v___x_735_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_717_, v___x_731_, v___f_733_, v___x_734_, v___x_728_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_736_ = l_Lean_Expr_appFn_x21(v_type_717_);
lean_dec_ref(v_type_717_);
v___x_737_ = l_Lean_Expr_appFn_x21(v___x_736_);
lean_dec_ref(v___x_736_);
v___x_738_ = l_Lean_Expr_appArg_x21(v___x_737_);
lean_dec_ref(v___x_737_);
v___x_739_ = l_Lean_Meta_mkHEqRefl(v___x_738_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_739_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = l_Lean_Expr_appFn_x21(v_type_717_);
lean_dec_ref(v_type_717_);
v___x_741_ = l_Lean_Expr_appArg_x21(v___x_740_);
lean_dec_ref(v___x_740_);
v___x_742_ = l_Lean_Meta_mkEqRefl(v___x_741_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(lean_object* v_type_743_, lean_object* v_motive_744_, lean_object* v___x_745_, lean_object* v_b_746_, uint8_t v___x_747_, lean_object* v___x_748_, lean_object* v_a_749_, lean_object* v_eqPr_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_type_756_; lean_object* v_motive_757_; lean_object* v___x_758_; 
v_type_756_ = l_Lean_Expr_bindingBody_x21(v_type_743_);
v_motive_757_ = l_Lean_Expr_bindingBody_x21(v_motive_744_);
v___x_758_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_756_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v_major_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___x_779_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc_ref(v_eqPr_750_);
v___x_779_ = lean_infer_type(v_eqPr_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
v___x_781_ = lean_whnf(v_a_780_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; uint8_t v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_Expr_isHEq(v_a_782_);
lean_dec(v_a_782_);
if (v___x_783_ == 0)
{
lean_inc_ref(v_eqPr_750_);
v_major_761_ = v_eqPr_750_;
v___y_762_ = v___y_751_;
v___y_763_ = v___y_752_;
v___y_764_ = v___y_753_;
v___y_765_ = v___y_754_;
goto v___jp_760_;
}
else
{
lean_object* v___x_784_; 
lean_inc_ref(v_eqPr_750_);
v___x_784_ = l_Lean_Meta_mkEqOfHEq(v_eqPr_750_, v___x_783_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v_major_761_ = v_a_785_;
v___y_762_ = v___y_751_;
v___y_763_ = v___y_752_;
v___y_764_ = v___y_753_;
v___y_765_ = v___y_754_;
goto v___jp_760_;
}
else
{
lean_dec(v_a_759_);
lean_dec_ref(v_motive_757_);
lean_dec_ref(v_eqPr_750_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_b_746_);
return v___x_784_;
}
}
}
else
{
lean_dec(v_a_759_);
lean_dec_ref(v_motive_757_);
lean_dec_ref(v_eqPr_750_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_b_746_);
return v___x_781_;
}
}
else
{
lean_dec(v_a_759_);
lean_dec_ref(v_motive_757_);
lean_dec_ref(v_eqPr_750_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_b_746_);
return v___x_779_;
}
v___jp_760_:
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; 
v___x_766_ = lean_mk_empty_array_with_capacity(v___x_745_);
lean_inc_ref(v_b_746_);
v___x_767_ = lean_array_push(v___x_766_, v_b_746_);
v___x_768_ = 1;
v___x_769_ = 1;
v___x_770_ = l_Lean_Meta_mkLambdaFVars(v___x_767_, v_motive_757_, v___x_747_, v___x_768_, v___x_747_, v___x_768_, v___x_769_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec_ref(v___x_767_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = l_Lean_Meta_mkEqNDRec(v_a_771_, v_a_759_, v_major_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
v___x_774_ = lean_mk_empty_array_with_capacity(v___x_748_);
v___x_775_ = lean_array_push(v___x_774_, v_a_749_);
v___x_776_ = lean_array_push(v___x_775_, v_b_746_);
v___x_777_ = lean_array_push(v___x_776_, v_eqPr_750_);
v___x_778_ = l_Lean_Meta_mkLambdaFVars(v___x_777_, v_a_773_, v___x_747_, v___x_768_, v___x_747_, v___x_768_, v___x_769_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec_ref(v___x_777_);
return v___x_778_;
}
else
{
lean_dec_ref(v_eqPr_750_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_b_746_);
return v___x_772_;
}
}
else
{
lean_dec_ref(v_major_761_);
lean_dec(v_a_759_);
lean_dec_ref(v_eqPr_750_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_b_746_);
return v___x_770_;
}
}
}
else
{
lean_dec_ref(v_motive_757_);
lean_dec_ref(v_eqPr_750_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_b_746_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(lean_object* v_type_786_, lean_object* v_motive_787_, lean_object* v___x_788_, lean_object* v_b_789_, lean_object* v___x_790_, lean_object* v___x_791_, lean_object* v_a_792_, lean_object* v_eqPr_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
uint8_t v___x_1802__boxed_799_; lean_object* v_res_800_; 
v___x_1802__boxed_799_ = lean_unbox(v___x_790_);
v_res_800_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(v_type_786_, v_motive_787_, v___x_788_, v_b_789_, v___x_1802__boxed_799_, v___x_791_, v_a_792_, v_eqPr_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___x_791_);
lean_dec(v___x_788_);
lean_dec_ref(v_motive_787_);
lean_dec_ref(v_type_786_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(lean_object* v___x_801_, lean_object* v___x_802_, lean_object* v_type_803_, lean_object* v_a_804_, lean_object* v___x_805_, uint8_t v___x_806_, lean_object* v___x_807_, lean_object* v_b_808_, lean_object* v_motive_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_b_815_; lean_object* v___x_816_; lean_object* v_type_817_; lean_object* v___x_818_; lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_b_815_ = lean_array_get_borrowed(v___x_801_, v_b_808_, v___x_802_);
v___x_816_ = l_Lean_Expr_bindingBody_x21(v_type_803_);
v_type_817_ = lean_expr_instantiate1(v___x_816_, v_a_804_);
lean_dec_ref(v___x_816_);
v___x_818_ = lean_box(v___x_806_);
lean_inc(v_b_815_);
lean_inc_ref(v_motive_809_);
v___f_819_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed), 13, 7);
lean_closure_set(v___f_819_, 0, v_type_817_);
lean_closure_set(v___f_819_, 1, v_motive_809_);
lean_closure_set(v___f_819_, 2, v___x_805_);
lean_closure_set(v___f_819_, 3, v_b_815_);
lean_closure_set(v___f_819_, 4, v___x_818_);
lean_closure_set(v___f_819_, 5, v___x_807_);
lean_closure_set(v___f_819_, 6, v_a_804_);
v___x_820_ = l_Lean_Expr_bindingName_x21(v_motive_809_);
v___x_821_ = l_Lean_Expr_bindingDomain_x21(v_motive_809_);
lean_dec_ref(v_motive_809_);
v___x_822_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_820_, v___x_821_, v___f_819_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(lean_object* v___x_823_, lean_object* v___x_824_, lean_object* v_type_825_, lean_object* v_a_826_, lean_object* v___x_827_, lean_object* v___x_828_, lean_object* v___x_829_, lean_object* v_b_830_, lean_object* v_motive_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v___x_1761__boxed_837_; lean_object* v_res_838_; 
v___x_1761__boxed_837_ = lean_unbox(v___x_828_);
v_res_838_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(v___x_823_, v___x_824_, v_type_825_, v_a_826_, v___x_827_, v___x_1761__boxed_837_, v___x_829_, v_b_830_, v_motive_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v_b_830_);
lean_dec_ref(v_type_825_);
lean_dec(v___x_824_);
lean_dec_ref(v___x_823_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object* v___x_839_, lean_object* v___x_840_, uint8_t v___x_841_, lean_object* v___x_842_, lean_object* v___x_843_, lean_object* v_a_844_, lean_object* v_type_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_a_852_; lean_object* v___x_853_; lean_object* v___f_854_; uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_851_ = lean_unsigned_to_nat(0u);
v_a_852_ = lean_array_get(v___x_839_, v_a_844_, v___x_851_);
v___x_853_ = lean_box(v___x_841_);
lean_inc_ref(v_type_845_);
v___f_854_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed), 14, 7);
lean_closure_set(v___f_854_, 0, v___x_839_);
lean_closure_set(v___f_854_, 1, v___x_851_);
lean_closure_set(v___f_854_, 2, v_type_845_);
lean_closure_set(v___f_854_, 3, v_a_852_);
lean_closure_set(v___f_854_, 4, v___x_840_);
lean_closure_set(v___f_854_, 5, v___x_853_);
lean_closure_set(v___f_854_, 6, v___x_842_);
v___x_855_ = 1;
v___x_856_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_845_, v___x_843_, v___f_854_, v___x_855_, v___x_841_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___boxed(lean_object* v_type_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(lean_object* v_lctx_864_, lean_object* v_localInsts_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_864_, v_localInsts_865_, v_x_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_872_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_872_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(lean_object* v_lctx_889_, lean_object* v_localInsts_890_, lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_889_, v_localInsts_890_, v_x_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_object* v_00_u03b1_898_, lean_object* v_lctx_899_, lean_object* v_localInsts_900_, lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_899_, v_localInsts_900_, v_x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(lean_object* v_00_u03b1_908_, lean_object* v_lctx_909_, lean_object* v_localInsts_910_, lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(v_00_u03b1_908_, v_lctx_909_, v_localInsts_910_, v_x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(lean_object* v_as_918_, size_t v_sz_919_, size_t v_i_920_, lean_object* v_b_921_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_lt(v_i_920_, v_sz_919_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_b_921_);
return v___x_924_;
}
else
{
lean_object* v_snd_925_; lean_object* v_snd_926_; lean_object* v_fst_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_997_; 
v_snd_925_ = lean_ctor_get(v_b_921_, 1);
lean_inc(v_snd_925_);
v_snd_926_ = lean_ctor_get(v_snd_925_, 1);
lean_inc(v_snd_926_);
v_fst_927_ = lean_ctor_get(v_b_921_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_b_921_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_b_921_, 1);
lean_dec(v_unused_998_);
v___x_929_ = v_b_921_;
v_isShared_930_ = v_isSharedCheck_997_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_fst_927_);
lean_dec(v_b_921_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_997_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_fst_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_995_; 
v_fst_931_ = lean_ctor_get(v_snd_925_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v_snd_925_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v_snd_925_, 1);
lean_dec(v_unused_996_);
v___x_933_ = v_snd_925_;
v_isShared_934_ = v_isSharedCheck_995_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_fst_931_);
lean_dec(v_snd_925_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_995_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_array_935_; lean_object* v_start_936_; lean_object* v_stop_937_; uint8_t v___x_938_; 
v_array_935_ = lean_ctor_get(v_snd_926_, 0);
v_start_936_ = lean_ctor_get(v_snd_926_, 1);
v_stop_937_ = lean_ctor_get(v_snd_926_, 2);
v___x_938_ = lean_nat_dec_lt(v_start_936_, v_stop_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_940_; 
if (v_isShared_934_ == 0)
{
v___x_940_ = v___x_933_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_fst_931_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_snd_926_);
v___x_940_ = v_reuseFailAlloc_945_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_940_);
v___x_942_ = v___x_929_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_fst_927_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v___x_940_);
v___x_942_ = v_reuseFailAlloc_944_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; 
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
}
else
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_991_; 
lean_inc(v_stop_937_);
lean_inc(v_start_936_);
lean_inc_ref(v_array_935_);
v_isSharedCheck_991_ = !lean_is_exclusive(v_snd_926_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; lean_object* v_unused_993_; lean_object* v_unused_994_; 
v_unused_992_ = lean_ctor_get(v_snd_926_, 2);
lean_dec(v_unused_992_);
v_unused_993_ = lean_ctor_get(v_snd_926_, 1);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_snd_926_, 0);
lean_dec(v_unused_994_);
v___x_947_ = v_snd_926_;
v_isShared_948_ = v_isSharedCheck_991_;
goto v_resetjp_946_;
}
else
{
lean_dec(v_snd_926_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_991_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_array_949_; lean_object* v_start_950_; lean_object* v_stop_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v_array_949_ = lean_ctor_get(v_fst_931_, 0);
v_start_950_ = lean_ctor_get(v_fst_931_, 1);
v_stop_951_ = lean_ctor_get(v_fst_931_, 2);
v___x_952_ = lean_array_fget(v_array_935_, v_start_936_);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_start_936_, v___x_953_);
lean_dec(v_start_936_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_954_);
v___x_956_ = v___x_947_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_array_935_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_stop_937_);
v___x_956_ = v_reuseFailAlloc_990_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
uint8_t v___x_957_; 
v___x_957_ = lean_nat_dec_lt(v_start_950_, v_stop_951_);
if (v___x_957_ == 0)
{
lean_object* v___x_959_; 
lean_dec(v___x_952_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_956_);
v___x_959_ = v___x_933_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_fst_931_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_956_);
v___x_959_ = v_reuseFailAlloc_964_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_959_);
v___x_961_ = v___x_929_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_fst_927_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_959_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
}
else
{
lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_986_; 
lean_inc(v_stop_951_);
lean_inc(v_start_950_);
lean_inc_ref(v_array_949_);
v_isSharedCheck_986_ = !lean_is_exclusive(v_fst_931_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; 
v_unused_987_ = lean_ctor_get(v_fst_931_, 2);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_fst_931_, 1);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_fst_931_, 0);
lean_dec(v_unused_989_);
v___x_966_ = v_fst_931_;
v_isShared_967_ = v_isSharedCheck_986_;
goto v_resetjp_965_;
}
else
{
lean_dec(v_fst_931_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_986_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_a_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v_a_968_ = lean_array_uget_borrowed(v_as_918_, v_i_920_);
v___x_969_ = lean_array_fget(v_array_949_, v_start_950_);
v___x_970_ = lean_nat_add(v_start_950_, v___x_953_);
lean_dec(v_start_950_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v___x_970_);
v___x_972_ = v___x_966_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_array_949_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_stop_951_);
v___x_972_ = v_reuseFailAlloc_985_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
lean_inc(v_a_968_);
v___x_973_ = lean_array_push(v_fst_927_, v_a_968_);
v___x_974_ = lean_array_push(v___x_973_, v___x_969_);
v___x_975_ = lean_array_push(v___x_974_, v___x_952_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_956_);
lean_ctor_set(v___x_933_, 0, v___x_972_);
v___x_977_ = v___x_933_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_956_);
v___x_977_ = v_reuseFailAlloc_984_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_977_);
lean_ctor_set(v___x_929_, 0, v___x_975_);
v___x_979_ = v___x_929_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_983_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
size_t v___x_980_; size_t v___x_981_; 
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_add(v_i_920_, v___x_980_);
v_i_920_ = v___x_981_;
v_b_921_ = v___x_979_;
goto _start;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(lean_object* v_as_999_, lean_object* v_sz_1000_, lean_object* v_i_1001_, lean_object* v_b_1002_, lean_object* v___y_1003_){
_start:
{
size_t v_sz_boxed_1004_; size_t v_i_boxed_1005_; lean_object* v_res_1006_; 
v_sz_boxed_1004_ = lean_unbox_usize(v_sz_1000_);
lean_dec(v_sz_1000_);
v_i_boxed_1005_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_999_, v_sz_boxed_1004_, v_i_boxed_1005_, v_b_1002_);
lean_dec_ref(v_as_999_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object* v_ys_1007_, lean_object* v_xs_1008_, lean_object* v_f_1009_, uint8_t v___x_1010_, uint8_t v___x_1011_, lean_object* v_eqs_1012_, lean_object* v_argKinds_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; size_t v_sz_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_1021_ = lean_array_get_size(v_ys_1007_);
lean_inc_ref(v_ys_1007_);
v___x_1022_ = l_Array_toSubarray___redArg(v_ys_1007_, v___x_1019_, v___x_1021_);
v___x_1023_ = lean_array_get_size(v_eqs_1012_);
v___x_1024_ = l_Array_toSubarray___redArg(v_eqs_1012_, v___x_1019_, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1022_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1020_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v_sz_1027_ = lean_array_size(v_xs_1008_);
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_xs_1008_, v_sz_1027_, v___x_1028_, v___x_1026_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v_fst_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v_fst_1031_ = lean_ctor_get(v_a_1030_, 0);
lean_inc(v_fst_1031_);
lean_dec(v_a_1030_);
lean_inc_ref(v_f_1009_);
v___x_1032_ = l_Lean_mkAppN(v_f_1009_, v_xs_1008_);
v___x_1033_ = l_Lean_mkAppN(v_f_1009_, v_ys_1007_);
lean_dec_ref(v_ys_1007_);
v___x_1034_ = l_Lean_Meta_mkHEq(v___x_1032_, v___x_1033_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = 1;
v___x_1037_ = l_Lean_Meta_mkForallFVars(v_fst_1031_, v_a_1035_, v___x_1010_, v___x_1011_, v___x_1011_, v___x_1036_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v_fst_1031_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc_n(v_a_1038_, 2);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_a_1038_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1044_, 0, v_a_1038_);
lean_ctor_set(v___x_1044_, 1, v_a_1040_);
lean_ctor_set(v___x_1044_, 2, v_argKinds_1013_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_a_1038_);
lean_dec_ref(v_argKinds_1013_);
v_a_1049_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1039_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1039_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_argKinds_1013_);
v_a_1057_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1037_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1037_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_fst_1031_);
lean_dec_ref(v_argKinds_1013_);
v_a_1065_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1034_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1034_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_argKinds_1013_);
lean_dec_ref(v_f_1009_);
lean_dec_ref(v_ys_1007_);
v_a_1073_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1029_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1029_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object* v_ys_1081_, lean_object* v_xs_1082_, lean_object* v_f_1083_, lean_object* v___x_1084_, lean_object* v___x_1085_, lean_object* v_eqs_1086_, lean_object* v_argKinds_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v___x_4552__boxed_1093_; uint8_t v___x_4553__boxed_1094_; lean_object* v_res_1095_; 
v___x_4552__boxed_1093_ = lean_unbox(v___x_1084_);
v___x_4553__boxed_1094_ = lean_unbox(v___x_1085_);
v_res_1095_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1081_, v_xs_1082_, v_f_1083_, v___x_4552__boxed_1093_, v___x_4553__boxed_1094_, v_eqs_1086_, v_argKinds_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec_ref(v_xs_1082_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(lean_object* v_msgData_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v_env_1103_; uint8_t v___x_1104_; lean_object* v_env_1105_; lean_object* v___x_1106_; lean_object* v_toCold_1107_; lean_object* v_mctx_1108_; lean_object* v_lctx_1109_; lean_object* v_options_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1102_ = lean_st_ref_get(v___y_1100_);
v_env_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1102_);
v___x_1104_ = 0;
v_env_1105_ = l_Lean_Environment_setRecordingDeps(v_env_1103_, v___x_1104_);
v___x_1106_ = lean_st_ref_get(v___y_1098_);
v_toCold_1107_ = lean_ctor_get(v___y_1099_, 0);
v_mctx_1108_ = lean_ctor_get(v___x_1106_, 0);
lean_inc_ref(v_mctx_1108_);
lean_dec(v___x_1106_);
v_lctx_1109_ = lean_ctor_get(v___y_1097_, 2);
v_options_1110_ = lean_ctor_get(v_toCold_1107_, 2);
lean_inc_ref(v_options_1110_);
lean_inc_ref(v_lctx_1109_);
v___x_1111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1111_, 0, v_env_1105_);
lean_ctor_set(v___x_1111_, 1, v_mctx_1108_);
lean_ctor_set(v___x_1111_, 2, v_lctx_1109_);
lean_ctor_set(v___x_1111_, 3, v_options_1110_);
v___x_1112_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v_msgData_1096_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0___boxed(lean_object* v_msgData_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msgData_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object* v_msg_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_ref_1127_; lean_object* v___x_1128_; lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_ref_1127_ = lean_ctor_get(v___y_1124_, 2);
v___x_1128_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_inc(v_ref_1127_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_ref_1127_);
lean_ctor_set(v___x_1133_, 1, v_a_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 1);
lean_ctor_set(v___x_1131_, 0, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object* v_msg_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1(lean_object* v_xs_1154_, lean_object* v_numArgs_1155_, lean_object* v_f_1156_, lean_object* v_ys_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_array_get_size(v_xs_1154_);
v___x_1165_ = lean_nat_dec_eq(v___x_1164_, v_numArgs_1155_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec_ref(v_ys_1157_);
lean_dec_ref(v_xs_1154_);
v___x_1166_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1);
v___x_1167_ = l_Nat_reprFast(v_numArgs_1155_);
v___x_1168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
v___x_1169_ = l_Lean_MessageData_ofFormat(v___x_1168_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1166_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Nat_reprFast(v___x_1164_);
v___x_1174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
v___x_1175_ = l_Lean_MessageData_ofFormat(v___x_1174_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1172_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_indentExpr(v_f_1156_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v___x_1180_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1181_;
}
else
{
lean_object* v_lctx_1182_; lean_object* v_localInstances_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v_numArgs_1155_);
v_lctx_1182_ = lean_ctor_get(v___y_1159_, 2);
v_localInstances_1183_ = lean_ctor_get(v___y_1159_, 3);
v___x_1184_ = 0;
v___x_1185_ = lean_box(v___x_1184_);
v___x_1186_ = lean_box(v___x_1165_);
lean_inc_ref(v_xs_1154_);
lean_inc_ref(v_ys_1157_);
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1187_, 0, v_ys_1157_);
lean_closure_set(v___f_1187_, 1, v_xs_1154_);
lean_closure_set(v___f_1187_, 2, v_f_1156_);
lean_closure_set(v___f_1187_, 3, v___x_1185_);
lean_closure_set(v___f_1187_, 4, v___x_1186_);
lean_inc_ref(v_lctx_1182_);
v___x_1188_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_1157_, v_lctx_1182_);
v___x_1189_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_1157_, v___x_1188_);
v___x_1190_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_xs_1154_, v___x_1189_);
v___x_1191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed), 9, 4);
lean_closure_set(v___x_1191_, 0, lean_box(0));
lean_closure_set(v___x_1191_, 1, v_xs_1154_);
lean_closure_set(v___x_1191_, 2, v_ys_1157_);
lean_closure_set(v___x_1191_, 3, v___f_1187_);
lean_inc_ref(v_localInstances_1183_);
v___x_1192_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v___x_1190_, v_localInstances_1183_, v___x_1191_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object* v_xs_1193_, lean_object* v_numArgs_1194_, lean_object* v_f_1195_, lean_object* v_ys_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Meta_mkHCongrWithArity___lam__1(v_xs_1193_, v_numArgs_1194_, v_f_1195_, v_ys_1196_, v_x_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v_x_1197_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object* v_numArgs_1204_, lean_object* v_f_1205_, lean_object* v_a_1206_, lean_object* v___x_1207_, lean_object* v_xs_1208_, lean_object* v_x_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___f_1215_; uint8_t v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; 
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1215_, 0, v_xs_1208_);
lean_closure_set(v___f_1215_, 1, v_numArgs_1204_);
lean_closure_set(v___f_1215_, 2, v_f_1205_);
v___x_1216_ = 1;
v___x_1217_ = 0;
v___x_1218_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1206_, v___x_1207_, v___f_1215_, v___x_1216_, v___x_1217_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object* v_numArgs_1219_, lean_object* v_f_1220_, lean_object* v_a_1221_, lean_object* v___x_1222_, lean_object* v_xs_1223_, lean_object* v_x_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Meta_mkHCongrWithArity___lam__2(v_numArgs_1219_, v_f_1220_, v_a_1221_, v___x_1222_, v_xs_1223_, v_x_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec_ref(v_x_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object* v_f_1231_, lean_object* v_numArgs_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1238_; 
lean_inc(v_a_1236_);
lean_inc_ref(v_a_1235_);
lean_inc(v_a_1234_);
lean_inc_ref(v_a_1233_);
lean_inc_ref(v_f_1231_);
v___x_1238_ = lean_infer_type(v_f_1231_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; lean_object* v___f_1241_; uint8_t v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_n(v_a_1239_, 2);
lean_dec_ref_known(v___x_1238_, 1);
lean_inc(v_numArgs_1232_);
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_numArgs_1232_);
lean_inc_ref(v___x_1240_);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1241_, 0, v_numArgs_1232_);
lean_closure_set(v___f_1241_, 1, v_f_1231_);
lean_closure_set(v___f_1241_, 2, v_a_1239_);
lean_closure_set(v___f_1241_, 3, v___x_1240_);
v___x_1242_ = 1;
v___x_1243_ = 0;
v___x_1244_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1239_, v___x_1240_, v___f_1241_, v___x_1242_, v___x_1243_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
return v___x_1244_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_numArgs_1232_);
lean_dec_ref(v_f_1231_);
v_a_1245_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1238_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1238_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___boxed(lean_object* v_f_1253_, lean_object* v_numArgs_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Meta_mkHCongrWithArity(v_f_1253_, v_numArgs_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object* v_00_u03b1_1261_, lean_object* v_msg_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_msg_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(v_00_u03b1_1269_, v_msg_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object* v_as_1277_, size_t v_sz_1278_, size_t v_i_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_1277_, v_sz_1278_, v_i_1279_, v_b_1280_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object* v_as_1287_, lean_object* v_sz_1288_, lean_object* v_i_1289_, lean_object* v_b_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
size_t v_sz_boxed_1296_; size_t v_i_boxed_1297_; lean_object* v_res_1298_; 
v_sz_boxed_1296_ = lean_unbox_usize(v_sz_1288_);
lean_dec(v_sz_1288_);
v_i_boxed_1297_ = lean_unbox_usize(v_i_1289_);
lean_dec(v_i_1289_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(v_as_1287_, v_sz_boxed_1296_, v_i_boxed_1297_, v_b_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec_ref(v_as_1287_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object* v_f_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_box(0);
lean_inc_ref(v_f_1299_);
v___x_1306_ = l_Lean_Meta_getFunInfo(v_f_1299_, v___x_1305_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_Meta_FunInfo_getArity(v_a_1307_);
lean_dec(v_a_1307_);
v___x_1309_ = l_Lean_Meta_mkHCongrWithArity(v_f_1299_, v___x_1308_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
return v___x_1309_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_f_1299_);
v_a_1310_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1306_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1306_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr___boxed(lean_object* v_f_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_mkHCongr(v_f_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
return v_res_1324_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object* v_a_1325_, lean_object* v_as_1326_, size_t v_i_1327_, size_t v_stop_1328_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_usize_dec_eq(v_i_1327_, v_stop_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_array_uget_borrowed(v_as_1326_, v_i_1327_);
v___x_1331_ = lean_nat_dec_eq(v_a_1325_, v___x_1330_);
if (v___x_1331_ == 0)
{
size_t v___x_1332_; size_t v___x_1333_; 
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_add(v_i_1327_, v___x_1332_);
v_i_1327_ = v___x_1333_;
goto _start;
}
else
{
return v___x_1331_;
}
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = 0;
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object* v_a_1336_, lean_object* v_as_1337_, lean_object* v_i_1338_, lean_object* v_stop_1339_){
_start:
{
size_t v_i_boxed_1340_; size_t v_stop_boxed_1341_; uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_i_boxed_1340_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_stop_boxed_1341_ = lean_unbox_usize(v_stop_1339_);
lean_dec(v_stop_1339_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1336_, v_as_1337_, v_i_boxed_1340_, v_stop_boxed_1341_);
lean_dec_ref(v_as_1337_);
lean_dec(v_a_1336_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object* v_as_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_array_get_size(v_as_1344_);
v___x_1348_ = lean_nat_dec_lt(v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
return v___x_1348_;
}
else
{
if (v___x_1348_ == 0)
{
return v___x_1348_;
}
else
{
size_t v___x_1349_; size_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1347_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1345_, v_as_1344_, v___x_1349_, v___x_1350_);
return v___x_1351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object* v_as_1352_, lean_object* v_a_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_as_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_as_1352_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(lean_object* v_next_1356_, lean_object* v_upperBound_1357_, lean_object* v___x_1358_, lean_object* v_a_1359_, lean_object* v_b_1360_){
_start:
{
lean_object* v_a_1362_; uint8_t v___x_1370_; 
v___x_1370_ = lean_nat_dec_lt(v_a_1359_, v_upperBound_1357_);
if (v___x_1370_ == 0)
{
lean_dec(v_a_1359_);
return v_b_1360_;
}
else
{
lean_object* v___x_1371_; lean_object* v_backDeps_1372_; uint8_t v___x_1373_; 
v___x_1371_ = lean_array_fget_borrowed(v___x_1358_, v_a_1359_);
v_backDeps_1372_ = lean_ctor_get(v___x_1371_, 0);
v___x_1373_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_backDeps_1372_, v_next_1356_);
if (v___x_1373_ == 0)
{
v_a_1362_ = v_b_1360_;
goto v___jp_1361_;
}
else
{
uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1374_ = 0;
v___x_1375_ = lean_box(v___x_1374_);
v___x_1376_ = lean_array_get(v___x_1375_, v_b_1360_, v_a_1359_);
lean_dec(v___x_1375_);
v___x_1377_ = lean_unbox(v___x_1376_);
lean_dec(v___x_1376_);
switch(v___x_1377_)
{
case 2:
{
lean_dec(v_a_1359_);
goto v___jp_1366_;
}
case 0:
{
lean_dec(v_a_1359_);
goto v___jp_1366_;
}
default: 
{
v_a_1362_ = v_b_1360_;
goto v___jp_1361_;
}
}
}
}
v___jp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_unsigned_to_nat(1u);
v___x_1364_ = lean_nat_add(v_a_1359_, v___x_1363_);
lean_dec(v_a_1359_);
v_a_1359_ = v___x_1364_;
v_b_1360_ = v_a_1362_;
goto _start;
}
v___jp_1366_:
{
uint8_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = 0;
v___x_1368_ = lean_box(v___x_1367_);
v___x_1369_ = lean_array_set(v_b_1360_, v_next_1356_, v___x_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(lean_object* v_next_1378_, lean_object* v_upperBound_1379_, lean_object* v___x_1380_, lean_object* v_a_1381_, lean_object* v_b_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1378_, v_upperBound_1379_, v___x_1380_, v_a_1381_, v_b_1382_);
lean_dec_ref(v___x_1380_);
lean_dec(v_upperBound_1379_);
lean_dec(v_next_1378_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object* v_upperBound_1384_, lean_object* v___x_1385_, lean_object* v___x_1386_, lean_object* v_a_1387_, lean_object* v_b_1388_){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_nat_dec_lt(v_a_1387_, v_upperBound_1384_);
if (v___x_1389_ == 0)
{
lean_dec(v_a_1387_);
return v_b_1388_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_unsigned_to_nat(1u);
v___x_1391_ = lean_nat_add(v_a_1387_, v___x_1390_);
lean_inc(v___x_1391_);
v___x_1392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_a_1387_, v___x_1385_, v___x_1386_, v___x_1391_, v_b_1388_);
lean_dec(v_a_1387_);
v_a_1387_ = v___x_1391_;
v_b_1388_ = v___x_1392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object* v_upperBound_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v_a_1397_, lean_object* v_b_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1394_, v___x_1395_, v___x_1396_, v_a_1397_, v_b_1398_);
lean_dec_ref(v___x_1396_);
lean_dec(v___x_1395_);
lean_dec(v_upperBound_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object* v_info_1400_, lean_object* v_kinds_1401_){
_start:
{
lean_object* v_paramInfo_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_paramInfo_1402_ = lean_ctor_get(v_info_1400_, 0);
v___x_1403_ = lean_array_get_size(v_paramInfo_1402_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v___x_1403_, v___x_1403_, v_paramInfo_1402_, v___x_1404_, v_kinds_1401_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object* v_info_1406_, lean_object* v_kinds_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_1406_, v_kinds_1407_);
lean_dec_ref(v_info_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(lean_object* v_next_1409_, lean_object* v_upperBound_1410_, lean_object* v___x_1411_, lean_object* v_inst_1412_, lean_object* v_R_1413_, lean_object* v_a_1414_, lean_object* v_b_1415_, lean_object* v_c_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1409_, v_upperBound_1410_, v___x_1411_, v_a_1414_, v_b_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(lean_object* v_next_1418_, lean_object* v_upperBound_1419_, lean_object* v___x_1420_, lean_object* v_inst_1421_, lean_object* v_R_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_, lean_object* v_c_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(v_next_1418_, v_upperBound_1419_, v___x_1420_, v_inst_1421_, v_R_1422_, v_a_1423_, v_b_1424_, v_c_1425_);
lean_dec_ref(v___x_1420_);
lean_dec(v_upperBound_1419_);
lean_dec(v_next_1418_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object* v_upperBound_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v_inst_1430_, lean_object* v_R_1431_, lean_object* v_a_1432_, lean_object* v_b_1433_, lean_object* v_c_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1427_, v___x_1428_, v___x_1429_, v_a_1432_, v_b_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object* v_upperBound_1436_, lean_object* v___x_1437_, lean_object* v___x_1438_, lean_object* v_inst_1439_, lean_object* v_R_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_, lean_object* v_c_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(v_upperBound_1436_, v___x_1437_, v___x_1438_, v_inst_1439_, v_R_1440_, v_a_1441_, v_b_1442_, v_c_1443_);
lean_dec_ref(v___x_1438_);
lean_dec(v___x_1437_);
lean_dec(v_upperBound_1436_);
return v_res_1444_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object* v_as_1445_, size_t v_i_1446_, size_t v_stop_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = 1;
v___x_1450_ = lean_array_uget_borrowed(v_as_1445_, v_i_1446_);
v___x_1451_ = lean_unbox(v___x_1450_);
switch(v___x_1451_)
{
case 3:
{
return v___x_1449_;
}
case 5:
{
return v___x_1449_;
}
default: 
{
size_t v___x_1452_; size_t v___x_1453_; 
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_add(v_i_1446_, v___x_1452_);
v_i_1446_ = v___x_1453_;
goto _start;
}
}
}
else
{
uint8_t v___x_1455_; 
v___x_1455_ = 0;
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object* v_as_1456_, lean_object* v_i_1457_, lean_object* v_stop_1458_){
_start:
{
size_t v_i_boxed_1459_; size_t v_stop_boxed_1460_; uint8_t v_res_1461_; lean_object* v_r_1462_; 
v_i_boxed_1459_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_stop_boxed_1460_ = lean_unbox_usize(v_stop_1458_);
lean_dec(v_stop_1458_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_as_1456_, v_i_boxed_1459_, v_stop_boxed_1460_);
lean_dec_ref(v_as_1456_);
v_r_1462_ = lean_box(v_res_1461_);
return v_r_1462_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object* v_kinds_1463_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_array_get_size(v_kinds_1463_);
v___x_1466_ = lean_nat_dec_lt(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
return v___x_1466_;
}
else
{
if (v___x_1466_ == 0)
{
return v___x_1466_;
}
else
{
size_t v___x_1467_; size_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = lean_usize_of_nat(v___x_1465_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_kinds_1463_, v___x_1467_, v___x_1468_);
return v___x_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object* v_kinds_1470_){
_start:
{
uint8_t v_res_1471_; lean_object* v_r_1472_; 
v_res_1471_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_1470_);
lean_dec_ref(v_kinds_1470_);
v_r_1472_ = lean_box(v_res_1471_);
return v_r_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object* v___x_1473_, lean_object* v_k_1474_, lean_object* v_xs_1475_, lean_object* v_type_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = lean_array_get_borrowed(v___x_1473_, v_xs_1475_, v___x_1482_);
lean_inc(v___y_1480_);
lean_inc_ref(v___y_1479_);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc(v___x_1483_);
v___x_1484_ = lean_apply_7(v_k_1474_, v___x_1483_, v_type_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, lean_box(0));
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object* v___x_1485_, lean_object* v_k_1486_, lean_object* v_xs_1487_, lean_object* v_type_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(v___x_1485_, v_k_1486_, v_xs_1487_, v_type_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v_xs_1487_);
lean_dec_ref(v___x_1485_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object* v_type_1495_, lean_object* v_k_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v___f_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1502_ = l_Lean_instInhabitedExpr;
v___f_1503_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1503_, 0, v___x_1502_);
lean_closure_set(v___f_1503_, 1, v_k_1496_);
v___x_1504_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_1505_ = 1;
v___x_1506_ = 0;
v___x_1507_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_1495_, v___x_1504_, v___f_1503_, v___x_1505_, v___x_1506_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(lean_object* v_type_1508_, lean_object* v_k_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1508_, v_k_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object* v_00_u03b1_1516_, lean_object* v_type_1517_, lean_object* v_k_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1517_, v_k_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(lean_object* v_00_u03b1_1525_, lean_object* v_type_1526_, lean_object* v_k_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(v_00_u03b1_1525_, v_type_1526_, v_k_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object* v_kinds_1537_, uint8_t v___x_1538_, lean_object* v_as_1539_, size_t v_sz_1540_, size_t v_i_1541_, lean_object* v_b_1542_){
_start:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_usize_dec_lt(v_i_1541_, v_sz_1540_);
if (v___x_1543_ == 0)
{
lean_inc_ref(v_b_1542_);
return v_b_1542_;
}
else
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1544_ = 0;
v___x_1545_ = lean_box(0);
v_a_1546_ = lean_array_uget_borrowed(v_as_1539_, v_i_1541_);
v___x_1547_ = lean_box(v___x_1544_);
v___x_1548_ = lean_array_get(v___x_1547_, v_kinds_1537_, v_a_1546_);
lean_dec(v___x_1547_);
v___x_1549_ = lean_unbox(v___x_1548_);
lean_dec(v___x_1548_);
if (v___x_1549_ == 2)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_box(v___x_1538_);
v___x_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v___x_1545_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; 
v___x_1553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v___x_1554_ = ((size_t)1ULL);
v___x_1555_ = lean_usize_add(v_i_1541_, v___x_1554_);
v_i_1541_ = v___x_1555_;
v_b_1542_ = v___x_1553_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object* v_kinds_1557_, lean_object* v___x_1558_, lean_object* v_as_1559_, lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_b_1562_){
_start:
{
uint8_t v___x_569__boxed_1563_; size_t v_sz_boxed_1564_; size_t v_i_boxed_1565_; lean_object* v_res_1566_; 
v___x_569__boxed_1563_ = lean_unbox(v___x_1558_);
v_sz_boxed_1564_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1565_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1557_, v___x_569__boxed_1563_, v_as_1559_, v_sz_boxed_1564_, v_i_boxed_1565_, v_b_1562_);
lean_dec_ref(v_b_1562_);
lean_dec_ref(v_as_1559_);
lean_dec_ref(v_kinds_1557_);
return v_res_1566_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object* v_info_1567_, lean_object* v_kinds_1568_, lean_object* v_i_1569_){
_start:
{
lean_object* v_paramInfo_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v_isDecInst_1573_; 
v_paramInfo_1570_ = lean_ctor_get(v_info_1567_, 0);
v___x_1571_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_1572_ = lean_array_get_borrowed(v___x_1571_, v_paramInfo_1570_, v_i_1569_);
v_isDecInst_1573_ = lean_ctor_get_uint8(v___x_1572_, sizeof(void*)*1 + 3);
if (v_isDecInst_1573_ == 0)
{
return v_isDecInst_1573_;
}
else
{
lean_object* v_backDeps_1574_; lean_object* v___x_1575_; size_t v_sz_1576_; size_t v___x_1577_; lean_object* v___x_1578_; lean_object* v_fst_1579_; 
v_backDeps_1574_ = lean_ctor_get(v___x_1572_, 0);
v___x_1575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v_sz_1576_ = lean_array_size(v_backDeps_1574_);
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1568_, v_isDecInst_1573_, v_backDeps_1574_, v_sz_1576_, v___x_1577_, v___x_1575_);
v_fst_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_fst_1579_);
lean_dec_ref(v___x_1578_);
if (lean_obj_tag(v_fst_1579_) == 0)
{
uint8_t v___x_1580_; 
v___x_1580_ = 0;
return v___x_1580_;
}
else
{
lean_object* v_val_1581_; uint8_t v___x_1582_; 
v_val_1581_ = lean_ctor_get(v_fst_1579_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v_fst_1579_, 1);
v___x_1582_ = lean_unbox(v_val_1581_);
lean_dec(v_val_1581_);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object* v_info_1583_, lean_object* v_kinds_1584_, lean_object* v_i_1585_){
_start:
{
uint8_t v_res_1586_; lean_object* v_r_1587_; 
v_res_1586_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_1583_, v_kinds_1584_, v_i_1585_);
lean_dec(v_i_1585_);
lean_dec_ref(v_kinds_1584_);
lean_dec_ref(v_info_1583_);
v_r_1587_ = lean_box(v_res_1586_);
return v_r_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(lean_object* v_type_1588_, lean_object* v_k_1589_, uint8_t v_cleanupAnnotations_1590_, uint8_t v_whnfType_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___f_1597_; lean_object* v___x_1598_; 
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1597_, 0, v_k_1589_);
v___x_1598_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1588_, v___f_1597_, v_cleanupAnnotations_1590_, v_whnfType_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1598_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1598_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(lean_object* v_type_1615_, lean_object* v_k_1616_, lean_object* v_cleanupAnnotations_1617_, lean_object* v_whnfType_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1624_; uint8_t v_whnfType_boxed_1625_; lean_object* v_res_1626_; 
v_cleanupAnnotations_boxed_1624_ = lean_unbox(v_cleanupAnnotations_1617_);
v_whnfType_boxed_1625_ = lean_unbox(v_whnfType_1618_);
v_res_1626_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1615_, v_k_1616_, v_cleanupAnnotations_boxed_1624_, v_whnfType_boxed_1625_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_object* v_00_u03b1_1627_, lean_object* v_type_1628_, lean_object* v_k_1629_, uint8_t v_cleanupAnnotations_1630_, uint8_t v_whnfType_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1628_, v_k_1629_, v_cleanupAnnotations_1630_, v_whnfType_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(lean_object* v_00_u03b1_1638_, lean_object* v_type_1639_, lean_object* v_k_1640_, lean_object* v_cleanupAnnotations_1641_, lean_object* v_whnfType_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1648_; uint8_t v_whnfType_boxed_1649_; lean_object* v_res_1650_; 
v_cleanupAnnotations_boxed_1648_ = lean_unbox(v_cleanupAnnotations_1641_);
v_whnfType_boxed_1649_ = lean_unbox(v_whnfType_1642_);
v_res_1650_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(v_00_u03b1_1638_, v_type_1639_, v_k_1640_, v_cleanupAnnotations_boxed_1648_, v_whnfType_boxed_1649_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(lean_object* v_upperBound_1651_, lean_object* v_val_1652_, lean_object* v_xs_1653_, lean_object* v___x_1654_, lean_object* v___x_1655_, uint8_t v___x_1656_, lean_object* v_a_1657_, lean_object* v_b_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_a_1664_; uint8_t v___x_1668_; 
v___x_1668_ = lean_nat_dec_lt(v_a_1657_, v_upperBound_1651_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
lean_dec(v_a_1657_);
lean_dec(v___x_1655_);
lean_dec_ref(v___x_1654_);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_b_1658_);
return v___x_1669_;
}
else
{
lean_object* v_numParams_1670_; uint8_t v___x_1671_; 
v_numParams_1670_ = lean_ctor_get(v_val_1652_, 3);
v___x_1671_ = lean_nat_dec_lt(v_a_1657_, v_numParams_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_array_fget_borrowed(v_xs_1653_, v_a_1657_);
v___x_1673_ = l_Lean_Expr_fvarId_x21(v___x_1672_);
v___x_1674_ = l_Lean_FVarId_getDecl___redArg(v___x_1673_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; uint8_t v___y_1677_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
v___x_1680_ = l_Lean_LocalDecl_userName(v_a_1675_);
lean_dec(v_a_1675_);
lean_inc(v___x_1655_);
lean_inc_ref(v___x_1654_);
v___x_1681_ = l_Lean_isSubobjectField_x3f(v___x_1654_, v___x_1655_, v___x_1680_);
if (lean_obj_tag(v___x_1681_) == 0)
{
v___y_1677_ = v___x_1671_;
goto v___jp_1676_;
}
else
{
lean_dec_ref_known(v___x_1681_, 1);
v___y_1677_ = v___x_1656_;
goto v___jp_1676_;
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_box(v___y_1677_);
v___x_1679_ = lean_array_push(v_b_1658_, v___x_1678_);
v_a_1664_ = v___x_1679_;
goto v___jp_1663_;
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v_b_1658_);
lean_dec(v_a_1657_);
lean_dec(v___x_1655_);
lean_dec_ref(v___x_1654_);
v_a_1682_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1674_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1674_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = 0;
v___x_1691_ = lean_box(v___x_1690_);
v___x_1692_ = lean_array_push(v_b_1658_, v___x_1691_);
v_a_1664_ = v___x_1692_;
goto v___jp_1663_;
}
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_add(v_a_1657_, v___x_1665_);
lean_dec(v_a_1657_);
v_a_1657_ = v___x_1666_;
v_b_1658_ = v_a_1664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_1693_, lean_object* v_val_1694_, lean_object* v_xs_1695_, lean_object* v___x_1696_, lean_object* v___x_1697_, lean_object* v___x_1698_, lean_object* v_a_1699_, lean_object* v_b_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v___x_5160__boxed_1705_; lean_object* v_res_1706_; 
v___x_5160__boxed_1705_ = lean_unbox(v___x_1698_);
v_res_1706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1693_, v_val_1694_, v_xs_1695_, v___x_1696_, v___x_1697_, v___x_5160__boxed_1705_, v_a_1699_, v_b_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v_xs_1695_);
lean_dec_ref(v_val_1694_);
lean_dec(v_upperBound_1693_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object* v_val_1709_, lean_object* v_induct_1710_, uint8_t v___x_1711_, lean_object* v_xs_1712_, lean_object* v_x_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v_env_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1719_ = lean_st_ref_get(v___y_1717_);
v_env_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc_ref(v_env_1720_);
lean_dec(v___x_1719_);
v___x_1721_ = lean_array_get_size(v_xs_1712_);
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0));
v___x_1724_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v___x_1721_, v_val_1709_, v_xs_1712_, v_env_1720_, v_induct_1710_, v___x_1711_, v___x_1722_, v___x_1723_, v___y_1714_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_a_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_a_1734_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1724_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1724_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object* v_val_1742_, lean_object* v_induct_1743_, lean_object* v___x_1744_, lean_object* v_xs_1745_, lean_object* v_x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_5247__boxed_1752_; lean_object* v_res_1753_; 
v___x_5247__boxed_1752_ = lean_unbox(v___x_1744_);
v_res_1753_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1742_, v_induct_1743_, v___x_5247__boxed_1752_, v_xs_1745_, v_x_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec_ref(v_x_1746_);
lean_dec_ref(v_xs_1745_);
lean_dec_ref(v_val_1742_);
return v_res_1753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
lean_ctor_set(v___x_1760_, 2, v___x_1759_);
lean_ctor_set(v___x_1760_, 3, v___x_1759_);
lean_ctor_set(v___x_1760_, 4, v___x_1758_);
lean_ctor_set(v___x_1760_, 5, v___x_1758_);
lean_ctor_set(v___x_1760_, 6, v___x_1758_);
lean_ctor_set(v___x_1760_, 7, v___x_1758_);
lean_ctor_set(v___x_1760_, 8, v___x_1758_);
lean_ctor_set(v___x_1760_, 9, v___x_1758_);
lean_ctor_set(v___x_1760_, 10, v___x_1758_);
lean_ctor_set(v___x_1760_, 11, v___x_1757_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_unsigned_to_nat(32u);
v___x_1762_ = lean_mk_empty_array_with_capacity(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1764_ = ((size_t)5ULL);
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_unsigned_to_nat(32u);
v___x_1767_ = lean_mk_empty_array_with_capacity(v___x_1766_);
v___x_1768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1769_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___x_1767_);
lean_ctor_set(v___x_1769_, 2, v___x_1765_);
lean_ctor_set(v___x_1769_, 3, v___x_1765_);
lean_ctor_set_usize(v___x_1769_, 4, v___x_1764_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1770_ = lean_box(1);
v___x_1771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___x_1771_);
lean_ctor_set(v___x_1773_, 2, v___x_1770_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1779_ = l_Lean_stringToMessageData(v___x_1778_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1785_ = l_Lean_stringToMessageData(v___x_1784_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1795_, lean_object* v_declHint_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v_env_1801_; uint8_t v___x_1802_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_st_ref_get(v___y_1797_);
v_env_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc_ref(v_env_1801_);
lean_dec(v___x_1800_);
v___x_1802_ = l_Lean_Name_isAnonymous(v_declHint_1796_);
if (v___x_1802_ == 0)
{
uint8_t v_isExporting_1803_; 
v_isExporting_1803_ = lean_ctor_get_uint8(v_env_1801_, sizeof(void*)*13);
if (v_isExporting_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v_env_1801_);
lean_dec(v_declHint_1796_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_msg_1795_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
lean_inc_ref(v_env_1801_);
v___x_1805_ = l_Lean_Environment_setExporting(v_env_1801_, v___x_1802_);
lean_inc(v_declHint_1796_);
lean_inc_ref(v___x_1805_);
v___x_1806_ = l_Lean_Environment_contains(v___x_1805_, v_declHint_1796_, v_isExporting_1803_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v___x_1805_);
lean_dec_ref(v_env_1801_);
lean_dec(v_declHint_1796_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_msg_1795_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_c_1813_; lean_object* v___x_1814_; 
v___x_1808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1810_ = l_Lean_Options_empty;
v___x_1811_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1805_);
lean_ctor_set(v___x_1811_, 1, v___x_1808_);
lean_ctor_set(v___x_1811_, 2, v___x_1809_);
lean_ctor_set(v___x_1811_, 3, v___x_1810_);
lean_inc(v_declHint_1796_);
v___x_1812_ = l_Lean_MessageData_ofConstName(v_declHint_1796_, v___x_1802_);
v_c_1813_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1813_, 0, v___x_1811_);
lean_ctor_set(v_c_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1801_, v_declHint_1796_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v_env_1801_);
lean_dec(v_declHint_1796_);
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v_c_1813_);
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_MessageData_note(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_msg_1795_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
else
{
lean_object* v_val_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1856_; 
v_val_1822_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1824_ = v___x_1814_;
v_isShared_1825_ = v_isSharedCheck_1856_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_val_1822_);
lean_dec(v___x_1814_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1856_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v_mod_1828_; uint8_t v___x_1829_; 
v___x_1826_ = l_Lean_Environment_header(v_env_1801_);
lean_dec_ref(v_env_1801_);
v___x_1827_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1826_);
v_mod_1828_ = lean_array_get(v___x_1799_, v___x_1827_, v_val_1822_);
lean_dec(v_val_1822_);
lean_dec_ref(v___x_1827_);
v___x_1829_ = l_Lean_isPrivateName(v_declHint_1796_);
lean_dec(v_declHint_1796_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set(v___x_1831_, 1, v_c_1813_);
v___x_1832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_MessageData_ofName(v_mod_1828_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_MessageData_note(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_msg_1795_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1839_);
v___x_1841_ = v___x_1824_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v_c_1813_);
v___x_1845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Lean_MessageData_ofName(v_mod_1828_);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_MessageData_note(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_msg_1795_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1852_);
v___x_1854_ = v___x_1824_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1857_; 
lean_dec_ref(v_env_1801_);
lean_dec(v_declHint_1796_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_msg_1795_);
return v___x_1857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1858_, lean_object* v_declHint_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1858_, v_declHint_1859_, v___y_1860_);
lean_dec(v___y_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msg_1863_, lean_object* v_declHint_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1880_; 
v___x_1870_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1863_, v_declHint_1864_, v___y_1868_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1875_ = l_Lean_unknownIdentifierMessageTag;
v___x_1876_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_a_1871_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1881_, lean_object* v_declHint_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1881_, v_declHint_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1889_, lean_object* v_msg_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_toCold_1896_; lean_object* v_currRecDepth_1897_; lean_object* v_ref_1898_; uint16_t v_optionFlags_1899_; uint8_t v_suppressElabErrors_1900_; uint8_t v_isRecordingDeps_1901_; lean_object* v_ref_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_toCold_1896_ = lean_ctor_get(v___y_1893_, 0);
v_currRecDepth_1897_ = lean_ctor_get(v___y_1893_, 1);
v_ref_1898_ = lean_ctor_get(v___y_1893_, 2);
v_optionFlags_1899_ = lean_ctor_get_uint16(v___y_1893_, sizeof(void*)*3);
v_suppressElabErrors_1900_ = lean_ctor_get_uint8(v___y_1893_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1901_ = lean_ctor_get_uint8(v___y_1893_, sizeof(void*)*3 + 3);
v_ref_1902_ = l_Lean_replaceRef(v_ref_1889_, v_ref_1898_);
lean_inc(v_currRecDepth_1897_);
lean_inc_ref(v_toCold_1896_);
v___x_1903_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1903_, 0, v_toCold_1896_);
lean_ctor_set(v___x_1903_, 1, v_currRecDepth_1897_);
lean_ctor_set(v___x_1903_, 2, v_ref_1902_);
lean_ctor_set_uint16(v___x_1903_, sizeof(void*)*3, v_optionFlags_1899_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*3 + 2, v_suppressElabErrors_1900_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*3 + 3, v_isRecordingDeps_1901_);
v___x_1904_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1890_, v___y_1891_, v___y_1892_, v___x_1903_, v___y_1894_);
lean_dec_ref_known(v___x_1903_, 3);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1905_, lean_object* v_msg_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1905_, v_msg_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_ref_1905_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1913_, lean_object* v_msg_1914_, lean_object* v_declHint_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1923_; 
v___x_1921_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1914_, v_declHint_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1921_);
v___x_1923_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1913_, v_a_1922_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1924_, lean_object* v_msg_1925_, lean_object* v_declHint_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1924_, v_msg_1925_, v_declHint_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v_ref_1924_);
return v_res_1932_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1935_ = l_Lean_stringToMessageData(v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1938_ = l_Lean_stringToMessageData(v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1939_, lean_object* v_constName_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1946_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1947_ = 0;
lean_inc(v_constName_1940_);
v___x_1948_ = l_Lean_MessageData_ofConstName(v_constName_1940_, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1946_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1939_, v___x_1951_, v_constName_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1953_, lean_object* v_constName_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1953_, v_constName_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v_ref_1953_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_ref_1967_; lean_object* v___x_1968_; 
v_ref_1967_ = lean_ctor_get(v___y_1964_, 2);
v___x_1968_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1967_, v_constName_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v_env_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_st_ref_get(v___y_1980_);
v_env_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc_ref(v_env_1983_);
lean_dec(v___x_1982_);
v___x_1984_ = 0;
lean_inc(v_constName_1976_);
v___x_1985_ = l_Lean_Environment_find_x3f(v_env_1983_, v_constName_1976_, v___x_1984_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
return v___x_1986_;
}
else
{
lean_object* v_val_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_constName_1976_);
v_val_1987_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1985_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_val_1987_);
lean_dec(v___x_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 0);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_val_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
if (lean_obj_tag(v_f_2002_) == 4)
{
lean_object* v_declName_2008_; lean_object* v___x_2009_; 
v_declName_2008_ = lean_ctor_get(v_f_2002_, 0);
lean_inc(v_declName_2008_);
lean_dec_ref_known(v_f_2002_, 2);
v___x_2009_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2008_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2033_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2033_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2033_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
if (lean_obj_tag(v_a_2010_) == 6)
{
lean_object* v_val_2014_; lean_object* v___x_2015_; lean_object* v_env_2016_; lean_object* v_toConstantVal_2017_; lean_object* v_induct_2018_; uint8_t v___x_2019_; 
v_val_2014_ = lean_ctor_get(v_a_2010_, 0);
lean_inc_ref(v_val_2014_);
lean_dec_ref_known(v_a_2010_, 1);
v___x_2015_ = lean_st_ref_get(v_a_2006_);
v_env_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_env_2016_);
lean_dec(v___x_2015_);
v_toConstantVal_2017_ = lean_ctor_get(v_val_2014_, 0);
v_induct_2018_ = lean_ctor_get(v_val_2014_, 1);
lean_inc(v_induct_2018_);
v___x_2019_ = l_Lean_isClass(v_env_2016_, v_induct_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
lean_dec(v_induct_2018_);
lean_dec_ref(v_val_2014_);
v___x_2020_ = lean_box(0);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2020_);
v___x_2022_ = v___x_2012_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
else
{
lean_object* v_type_2024_; lean_object* v___x_2025_; lean_object* v___f_2026_; uint8_t v___x_2027_; lean_object* v___x_2028_; 
lean_del_object(v___x_2012_);
v_type_2024_ = lean_ctor_get(v_toConstantVal_2017_, 2);
lean_inc_ref(v_type_2024_);
v___x_2025_ = lean_box(v___x_2019_);
v___f_2026_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2026_, 0, v_val_2014_);
lean_closure_set(v___f_2026_, 1, v_induct_2018_);
lean_closure_set(v___f_2026_, 2, v___x_2025_);
v___x_2027_ = 0;
v___x_2028_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2024_, v___f_2026_, v___x_2019_, v___x_2027_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
return v___x_2028_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
lean_dec(v_a_2010_);
v___x_2029_ = lean_box(0);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2029_);
v___x_2031_ = v___x_2012_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
v_a_2034_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2009_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2009_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec_ref(v_f_2002_);
v___x_2042_ = lean_box(0);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2051_, lean_object* v_val_2052_, lean_object* v_xs_2053_, lean_object* v___x_2054_, lean_object* v___x_2055_, uint8_t v___x_2056_, lean_object* v_inst_2057_, lean_object* v_R_2058_, lean_object* v_a_2059_, lean_object* v_b_2060_, lean_object* v_c_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2051_, v_val_2052_, v_xs_2053_, v___x_2054_, v___x_2055_, v___x_2056_, v_a_2059_, v_b_2060_, v___y_2062_, v___y_2064_, v___y_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2068_, lean_object* v_val_2069_, lean_object* v_xs_2070_, lean_object* v___x_2071_, lean_object* v___x_2072_, lean_object* v___x_2073_, lean_object* v_inst_2074_, lean_object* v_R_2075_, lean_object* v_a_2076_, lean_object* v_b_2077_, lean_object* v_c_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v___x_5832__boxed_2084_; lean_object* v_res_2085_; 
v___x_5832__boxed_2084_ = lean_unbox(v___x_2073_);
v_res_2085_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2068_, v_val_2069_, v_xs_2070_, v___x_2071_, v___x_2072_, v___x_5832__boxed_2084_, v_inst_2074_, v_R_2075_, v_a_2076_, v_b_2077_, v_c_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_xs_2070_);
lean_dec_ref(v_val_2069_);
lean_dec(v_upperBound_2068_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2086_, lean_object* v_constName_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2094_, lean_object* v_constName_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2094_, v_constName_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2102_, lean_object* v_ref_2103_, lean_object* v_constName_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2103_, v_constName_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2111_, lean_object* v_ref_2112_, lean_object* v_constName_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2111_, v_ref_2112_, v_constName_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v_ref_2112_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2120_, lean_object* v_ref_2121_, lean_object* v_msg_2122_, lean_object* v_declHint_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2121_, v_msg_2122_, v_declHint_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2130_, lean_object* v_ref_2131_, lean_object* v_msg_2132_, lean_object* v_declHint_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2130_, v_ref_2131_, v_msg_2132_, v_declHint_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v_ref_2131_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2140_, lean_object* v_declHint_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2140_, v_declHint_2141_, v___y_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2148_, lean_object* v_declHint_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2148_, v_declHint_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2156_, lean_object* v_ref_2157_, lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2157_, v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2165_, lean_object* v_ref_2166_, lean_object* v_msg_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2165_, v_ref_2166_, v_msg_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v_ref_2166_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2174_, lean_object* v_a_2175_, lean_object* v_____r_2176_, lean_object* v_result_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
uint8_t v___x_2183_; 
v___x_2183_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2174_, v_result_2177_, v_a_2175_);
if (v___x_2183_ == 0)
{
uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2184_ = 0;
v___x_2185_ = lean_box(v___x_2184_);
v___x_2186_ = lean_array_push(v_result_2177_, v___x_2185_);
v___x_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
return v___x_2188_;
}
else
{
uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2189_ = 5;
v___x_2190_ = lean_box(v___x_2189_);
v___x_2191_ = lean_array_push(v_result_2177_, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2194_, lean_object* v_a_2195_, lean_object* v_____r_2196_, lean_object* v_result_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2194_, v_a_2195_, v_____r_2196_, v_result_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v_a_2195_);
lean_dec_ref(v_info_2194_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2204_, lean_object* v_upperBound_2205_, lean_object* v___x_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_b_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_a_2216_; lean_object* v___y_2221_; uint8_t v___x_2240_; 
v___x_2240_ = lean_nat_dec_lt(v_a_2208_, v_upperBound_2205_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
lean_dec(v_a_2208_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v_b_2209_);
return v___x_2241_;
}
else
{
lean_object* v_resultDeps_2242_; uint8_t v___x_2243_; 
v_resultDeps_2242_ = lean_ctor_get(v_info_2204_, 1);
v___x_2243_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2242_, v_a_2208_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; uint8_t v_isProp_2245_; 
v___x_2244_ = lean_array_fget_borrowed(v___x_2206_, v_a_2208_);
v_isProp_2245_ = lean_ctor_get_uint8(v___x_2244_, sizeof(void*)*1 + 2);
if (v_isProp_2245_ == 0)
{
uint8_t v_isInstance_2246_; 
v_isInstance_2246_ = lean_ctor_get_uint8(v___x_2244_, sizeof(void*)*1 + 4);
if (v_isInstance_2246_ == 0)
{
uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = 2;
v___x_2248_ = lean_box(v___x_2247_);
v___x_2249_ = lean_array_push(v_b_2209_, v___x_2248_);
v_a_2216_ = v___x_2249_;
goto v___jp_2215_;
}
else
{
if (lean_obj_tag(v_a_2207_) == 1)
{
lean_object* v_val_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_val_2250_ = lean_ctor_get(v_a_2207_, 0);
v___x_2251_ = lean_array_get_size(v_val_2250_);
v___x_2252_ = lean_nat_dec_lt(v_a_2208_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_box(0);
v___x_2254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2204_, v_a_2208_, v___x_2253_, v_b_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
v___y_2221_ = v___x_2254_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_array_fget_borrowed(v_val_2250_, v_a_2208_);
v___x_2256_ = lean_unbox(v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_box(0);
v___x_2258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2204_, v_a_2208_, v___x_2257_, v_b_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
v___y_2221_ = v___x_2258_;
goto v___jp_2220_;
}
else
{
uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = 2;
v___x_2260_ = lean_box(v___x_2259_);
v___x_2261_ = lean_array_push(v_b_2209_, v___x_2260_);
v_a_2216_ = v___x_2261_;
goto v___jp_2215_;
}
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_box(0);
v___x_2263_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2204_, v_a_2208_, v___x_2262_, v_b_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
v___y_2221_ = v___x_2263_;
goto v___jp_2220_;
}
}
}
else
{
uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = 3;
v___x_2265_ = lean_box(v___x_2264_);
v___x_2266_ = lean_array_push(v_b_2209_, v___x_2265_);
v_a_2216_ = v___x_2266_;
goto v___jp_2215_;
}
}
else
{
uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = 0;
v___x_2268_ = lean_box(v___x_2267_);
v___x_2269_ = lean_array_push(v_b_2209_, v___x_2268_);
v_a_2216_ = v___x_2269_;
goto v___jp_2215_;
}
}
v___jp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_unsigned_to_nat(1u);
v___x_2218_ = lean_nat_add(v_a_2208_, v___x_2217_);
lean_dec(v_a_2208_);
v_a_2208_ = v___x_2218_;
v_b_2209_ = v_a_2216_;
goto _start;
}
v___jp_2220_:
{
if (lean_obj_tag(v___y_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2231_; 
v_a_2222_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2224_ = v___y_2221_;
v_isShared_2225_ = v_isSharedCheck_2231_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___y_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2231_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; 
lean_dec(v_a_2208_);
v_a_2226_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v_a_2222_, 1);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v_a_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v_a_2230_; 
lean_del_object(v___x_2224_);
v_a_2230_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v_a_2222_, 1);
v_a_2216_ = v_a_2230_;
goto v___jp_2215_;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_a_2208_);
v_a_2232_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___y_2221_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___y_2221_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2270_, lean_object* v_upperBound_2271_, lean_object* v___x_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_b_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2270_, v_upperBound_2271_, v___x_2272_, v_a_2273_, v_a_2274_, v_b_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v_a_2273_);
lean_dec_ref(v___x_2272_);
lean_dec(v_upperBound_2271_);
lean_dec_ref(v_info_2270_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2284_, lean_object* v_info_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v___x_2291_; lean_object* v_result_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v_result_2292_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2293_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2284_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v_paramInfo_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v_paramInfo_2295_ = lean_ctor_get(v_info_2285_, 0);
v___x_2296_ = lean_array_get_size(v_paramInfo_2295_);
v___x_2297_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2285_, v___x_2296_, v_paramInfo_2295_, v_a_2294_, v___x_2291_, v_result_2292_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2294_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2306_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2285_, v_a_2298_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
return v___x_2297_;
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v_a_2307_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2293_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2293_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2315_, lean_object* v_info_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Meta_getCongrSimpKinds(v_f_2315_, v_info_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec_ref(v_info_2316_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2323_, lean_object* v_upperBound_2324_, lean_object* v___x_2325_, lean_object* v_a_2326_, lean_object* v_inst_2327_, lean_object* v_R_2328_, lean_object* v_a_2329_, lean_object* v_b_2330_, lean_object* v_c_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2323_, v_upperBound_2324_, v___x_2325_, v_a_2326_, v_a_2329_, v_b_2330_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2338_, lean_object* v_upperBound_2339_, lean_object* v___x_2340_, lean_object* v_a_2341_, lean_object* v_inst_2342_, lean_object* v_R_2343_, lean_object* v_a_2344_, lean_object* v_b_2345_, lean_object* v_c_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2338_, v_upperBound_2339_, v___x_2340_, v_a_2341_, v_inst_2342_, v_R_2343_, v_a_2344_, v_b_2345_, v_c_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v_a_2341_);
lean_dec_ref(v___x_2340_);
lean_dec(v_upperBound_2339_);
lean_dec_ref(v_info_2338_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2353_, lean_object* v_info_2354_, lean_object* v___x_2355_, lean_object* v_a_2356_, lean_object* v_b_2357_){
_start:
{
lean_object* v_a_2360_; uint8_t v___x_2364_; 
v___x_2364_ = lean_nat_dec_lt(v_a_2356_, v_upperBound_2353_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_dec(v_a_2356_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v_b_2357_);
return v___x_2365_;
}
else
{
lean_object* v_resultDeps_2366_; uint8_t v___x_2367_; 
v_resultDeps_2366_ = lean_ctor_get(v_info_2354_, 1);
v___x_2367_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2366_, v_a_2356_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = lean_unsigned_to_nat(0u);
v___x_2369_ = lean_nat_dec_eq(v_a_2356_, v___x_2368_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; uint8_t v_isProp_2371_; 
v___x_2370_ = lean_array_fget_borrowed(v___x_2355_, v_a_2356_);
v_isProp_2371_ = lean_ctor_get_uint8(v___x_2370_, sizeof(void*)*1 + 2);
if (v_isProp_2371_ == 0)
{
uint8_t v_isInstance_2372_; 
v_isInstance_2372_ = lean_ctor_get_uint8(v___x_2370_, sizeof(void*)*1 + 4);
if (v_isInstance_2372_ == 0)
{
uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = 0;
v___x_2374_ = lean_box(v___x_2373_);
v___x_2375_ = lean_array_push(v_b_2357_, v___x_2374_);
v_a_2360_ = v___x_2375_;
goto v___jp_2359_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2354_, v_b_2357_, v_a_2356_);
if (v___x_2376_ == 0)
{
uint8_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = 0;
v___x_2378_ = lean_box(v___x_2377_);
v___x_2379_ = lean_array_push(v_b_2357_, v___x_2378_);
v_a_2360_ = v___x_2379_;
goto v___jp_2359_;
}
else
{
uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = 5;
v___x_2381_ = lean_box(v___x_2380_);
v___x_2382_ = lean_array_push(v_b_2357_, v___x_2381_);
v_a_2360_ = v___x_2382_;
goto v___jp_2359_;
}
}
}
else
{
uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = 3;
v___x_2384_ = lean_box(v___x_2383_);
v___x_2385_ = lean_array_push(v_b_2357_, v___x_2384_);
v_a_2360_ = v___x_2385_;
goto v___jp_2359_;
}
}
else
{
uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = 2;
v___x_2387_ = lean_box(v___x_2386_);
v___x_2388_ = lean_array_push(v_b_2357_, v___x_2387_);
v_a_2360_ = v___x_2388_;
goto v___jp_2359_;
}
}
else
{
uint8_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = 0;
v___x_2390_ = lean_box(v___x_2389_);
v___x_2391_ = lean_array_push(v_b_2357_, v___x_2390_);
v_a_2360_ = v___x_2391_;
goto v___jp_2359_;
}
}
v___jp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_unsigned_to_nat(1u);
v___x_2362_ = lean_nat_add(v_a_2356_, v___x_2361_);
lean_dec(v_a_2356_);
v_a_2356_ = v___x_2362_;
v_b_2357_ = v_a_2360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2392_, lean_object* v_info_2393_, lean_object* v___x_2394_, lean_object* v_a_2395_, lean_object* v_b_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2392_, v_info_2393_, v___x_2394_, v_a_2395_, v_b_2396_);
lean_dec_ref(v___x_2394_);
lean_dec_ref(v_info_2393_);
lean_dec(v_upperBound_2392_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_paramInfo_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v_result_2408_; lean_object* v___x_2409_; 
v_paramInfo_2405_ = lean_ctor_get(v_info_2399_, 0);
v___x_2406_ = lean_array_get_size(v_paramInfo_2405_);
v___x_2407_ = lean_unsigned_to_nat(0u);
v_result_2408_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2409_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2406_, v_info_2399_, v_paramInfo_2405_, v___x_2407_, v_result_2408_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2418_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2418_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2418_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2399_, v_a_2410_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2414_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
else
{
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec_ref(v_info_2419_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2426_, lean_object* v_info_2427_, lean_object* v___x_2428_, lean_object* v_inst_2429_, lean_object* v_R_2430_, lean_object* v_a_2431_, lean_object* v_b_2432_, lean_object* v_c_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2426_, v_info_2427_, v___x_2428_, v_a_2431_, v_b_2432_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2440_, lean_object* v_info_2441_, lean_object* v___x_2442_, lean_object* v_inst_2443_, lean_object* v_R_2444_, lean_object* v_a_2445_, lean_object* v_b_2446_, lean_object* v_c_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2440_, v_info_2441_, v___x_2442_, v_inst_2443_, v_R_2444_, v_a_2445_, v_b_2446_, v_c_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec_ref(v___x_2442_);
lean_dec_ref(v_info_2441_);
lean_dec(v_upperBound_2440_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl(lean_object* v_x_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_obj_tag_nat(v_x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl___boxed(lean_object* v_x_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl(v_x_2456_);
lean_dec_ref(v_x_2456_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2458_, lean_object* v_k_2459_){
_start:
{
if (lean_obj_tag(v_t_2458_) == 0)
{
lean_object* v_fvarId_2460_; lean_object* v___x_2461_; 
v_fvarId_2460_ = lean_ctor_get(v_t_2458_, 0);
lean_inc(v_fvarId_2460_);
lean_dec_ref_known(v_t_2458_, 1);
v___x_2461_ = lean_apply_1(v_k_2459_, v_fvarId_2460_);
return v___x_2461_;
}
else
{
lean_object* v_lhs_2462_; lean_object* v_rhs_2463_; lean_object* v___x_2464_; 
v_lhs_2462_ = lean_ctor_get(v_t_2458_, 0);
lean_inc(v_lhs_2462_);
v_rhs_2463_ = lean_ctor_get(v_t_2458_, 1);
lean_inc(v_rhs_2463_);
lean_dec_ref_known(v_t_2458_, 2);
v___x_2464_ = lean_apply_2(v_k_2459_, v_lhs_2462_, v_rhs_2463_);
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2465_, lean_object* v_ctorIdx_2466_, lean_object* v_t_2467_, lean_object* v_h_2468_, lean_object* v_k_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2467_, v_k_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2471_, lean_object* v_ctorIdx_2472_, lean_object* v_t_2473_, lean_object* v_h_2474_, lean_object* v_k_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2471_, v_ctorIdx_2472_, v_t_2473_, v_h_2474_, v_k_2475_);
lean_dec(v_ctorIdx_2472_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2477_, lean_object* v_hyp_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2477_, v_hyp_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2480_, lean_object* v_t_2481_, lean_object* v_h_2482_, lean_object* v_hyp_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2481_, v_hyp_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2485_, lean_object* v_decSubsingleton_2486_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2485_, v_decSubsingleton_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2488_, lean_object* v_t_2489_, lean_object* v_h_2490_, lean_object* v_decSubsingleton_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2489_, v_decSubsingleton_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2493_, lean_object* v_fvarId_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2493_, v_fvarId_2494_);
if (lean_obj_tag(v___x_2495_) == 1)
{
lean_object* v_val_2496_; lean_object* v___x_2497_; 
v_val_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_val_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = l_Lean_Expr_fvarId_x21(v_val_2496_);
lean_dec(v_val_2496_);
return v___x_2497_;
}
else
{
lean_dec(v___x_2495_);
lean_inc(v_fvarId_2494_);
return v_fvarId_2494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2498_, lean_object* v_fvarId_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2498_, v_fvarId_2499_);
lean_dec(v_fvarId_2499_);
lean_dec(v_s_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2501_, lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2501_, v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
v_a_2517_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2508_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2508_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2525_, lean_object* v_x_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2525_, v_x_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2533_, lean_object* v_mvarId_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2534_, v_x_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2542_, lean_object* v_mvarId_2543_, lean_object* v_x_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2542_, v_mvarId_2543_, v_x_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2551_, lean_object* v___y_2552_){
_start:
{
uint8_t v___x_2554_; 
v___x_2554_ = l_Lean_Expr_hasMVar(v_e_2551_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_e_2551_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; lean_object* v_mctx_2557_; lean_object* v___x_2558_; lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2561_; lean_object* v_cache_2562_; lean_object* v_zetaDeltaFVarIds_2563_; lean_object* v_postponed_2564_; lean_object* v_diag_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2574_; 
v___x_2556_ = lean_st_ref_get(v___y_2552_);
v_mctx_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_ref(v_mctx_2557_);
lean_dec(v___x_2556_);
v___x_2558_ = l_Lean_instantiateMVarsCore(v_mctx_2557_, v_e_2551_);
v_fst_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_fst_2559_);
v_snd_2560_ = lean_ctor_get(v___x_2558_, 1);
lean_inc(v_snd_2560_);
lean_dec_ref(v___x_2558_);
v___x_2561_ = lean_st_ref_take(v___y_2552_);
v_cache_2562_ = lean_ctor_get(v___x_2561_, 1);
v_zetaDeltaFVarIds_2563_ = lean_ctor_get(v___x_2561_, 2);
v_postponed_2564_ = lean_ctor_get(v___x_2561_, 3);
v_diag_2565_ = lean_ctor_get(v___x_2561_, 4);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; 
v_unused_2575_ = lean_ctor_get(v___x_2561_, 0);
lean_dec(v_unused_2575_);
v___x_2567_ = v___x_2561_;
v_isShared_2568_ = v_isSharedCheck_2574_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_diag_2565_);
lean_inc(v_postponed_2564_);
lean_inc(v_zetaDeltaFVarIds_2563_);
lean_inc(v_cache_2562_);
lean_dec(v___x_2561_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2574_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v_snd_2560_);
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_snd_2560_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_cache_2562_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_zetaDeltaFVarIds_2563_);
lean_ctor_set(v_reuseFailAlloc_2573_, 3, v_postponed_2564_);
lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_diag_2565_);
v___x_2570_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_st_ref_put(v___y_2552_, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_fst_2559_);
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2576_, v___y_2577_);
lean_dec(v___y_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2580_, v___y_2582_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_){
_start:
{
lean_object* v_ks_2598_; lean_object* v_vs_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2623_; 
v_ks_2598_ = lean_ctor_get(v_x_2594_, 0);
v_vs_2599_ = lean_ctor_get(v_x_2594_, 1);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_x_2594_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2601_ = v_x_2594_;
v_isShared_2602_ = v_isSharedCheck_2623_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_vs_2599_);
lean_inc(v_ks_2598_);
lean_dec(v_x_2594_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2623_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = lean_array_get_size(v_ks_2598_);
v___x_2604_ = lean_nat_dec_lt(v_x_2595_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_dec(v_x_2595_);
v___x_2605_ = lean_array_push(v_ks_2598_, v_x_2596_);
v___x_2606_ = lean_array_push(v_vs_2599_, v_x_2597_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 1, v___x_2606_);
lean_ctor_set(v___x_2601_, 0, v___x_2605_);
v___x_2608_ = v___x_2601_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
else
{
lean_object* v_k_x27_2610_; uint8_t v___x_2611_; 
v_k_x27_2610_ = lean_array_fget_borrowed(v_ks_2598_, v_x_2595_);
v___x_2611_ = l_Lean_instBEqMVarId_beq(v_x_2596_, v_k_x27_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2613_; 
if (v_isShared_2602_ == 0)
{
v___x_2613_ = v___x_2601_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_ks_2598_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_vs_2599_);
v___x_2613_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_unsigned_to_nat(1u);
v___x_2615_ = lean_nat_add(v_x_2595_, v___x_2614_);
lean_dec(v_x_2595_);
v_x_2594_ = v___x_2613_;
v_x_2595_ = v___x_2615_;
goto _start;
}
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2618_ = lean_array_fset(v_ks_2598_, v_x_2595_, v_x_2596_);
v___x_2619_ = lean_array_fset(v_vs_2599_, v_x_2595_, v_x_2597_);
lean_dec(v_x_2595_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 1, v___x_2619_);
lean_ctor_set(v___x_2601_, 0, v___x_2618_);
v___x_2621_ = v___x_2601_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2624_, lean_object* v_k_2625_, lean_object* v_v_2626_){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = lean_unsigned_to_nat(0u);
v___x_2628_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2624_, v___x_2627_, v_k_2625_, v_v_2626_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2630_, size_t v_x_2631_, size_t v_x_2632_, lean_object* v_x_2633_, lean_object* v_x_2634_){
_start:
{
if (lean_obj_tag(v_x_2630_) == 0)
{
lean_object* v_es_2635_; size_t v___x_2636_; size_t v___x_2637_; lean_object* v_j_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v_es_2635_ = lean_ctor_get(v_x_2630_, 0);
v___x_2636_ = ((size_t)31ULL);
v___x_2637_ = lean_usize_land(v_x_2631_, v___x_2636_);
v_j_2638_ = lean_usize_to_nat(v___x_2637_);
v___x_2639_ = lean_array_get_size(v_es_2635_);
v___x_2640_ = lean_nat_dec_lt(v_j_2638_, v___x_2639_);
if (v___x_2640_ == 0)
{
lean_dec(v_j_2638_);
lean_dec(v_x_2634_);
lean_dec(v_x_2633_);
return v_x_2630_;
}
else
{
lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2679_; 
lean_inc_ref(v_es_2635_);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_x_2630_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v_x_2630_, 0);
lean_dec(v_unused_2680_);
v___x_2642_ = v_x_2630_;
v_isShared_2643_ = v_isSharedCheck_2679_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v_x_2630_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2679_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_v_2644_; lean_object* v___x_2645_; lean_object* v_xs_x27_2646_; lean_object* v___y_2648_; 
v_v_2644_ = lean_array_fget(v_es_2635_, v_j_2638_);
v___x_2645_ = lean_box(0);
v_xs_x27_2646_ = lean_array_fset(v_es_2635_, v_j_2638_, v___x_2645_);
switch(lean_obj_tag(v_v_2644_))
{
case 0:
{
lean_object* v_key_2653_; lean_object* v_val_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2664_; 
v_key_2653_ = lean_ctor_get(v_v_2644_, 0);
v_val_2654_ = lean_ctor_get(v_v_2644_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_v_2644_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2656_ = v_v_2644_;
v_isShared_2657_ = v_isSharedCheck_2664_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_val_2654_);
lean_inc(v_key_2653_);
lean_dec(v_v_2644_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2664_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
uint8_t v___x_2658_; 
v___x_2658_ = l_Lean_instBEqMVarId_beq(v_x_2633_, v_key_2653_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_del_object(v___x_2656_);
v___x_2659_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2653_, v_val_2654_, v_x_2633_, v_x_2634_);
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
v___y_2648_ = v___x_2660_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2662_; 
lean_dec(v_val_2654_);
lean_dec(v_key_2653_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v_x_2634_);
lean_ctor_set(v___x_2656_, 0, v_x_2633_);
v___x_2662_ = v___x_2656_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_x_2633_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_x_2634_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
v___y_2648_ = v___x_2662_;
goto v___jp_2647_;
}
}
}
}
case 1:
{
lean_object* v_node_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2677_; 
v_node_2665_ = lean_ctor_get(v_v_2644_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_v_2644_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2667_ = v_v_2644_;
v_isShared_2668_ = v_isSharedCheck_2677_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_node_2665_);
lean_dec(v_v_2644_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2677_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
size_t v___x_2669_; size_t v___x_2670_; size_t v___x_2671_; size_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2669_ = ((size_t)5ULL);
v___x_2670_ = lean_usize_shift_right(v_x_2631_, v___x_2669_);
v___x_2671_ = ((size_t)1ULL);
v___x_2672_ = lean_usize_add(v_x_2632_, v___x_2671_);
v___x_2673_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2665_, v___x_2670_, v___x_2672_, v_x_2633_, v_x_2634_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2673_);
v___x_2675_ = v___x_2667_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
v___y_2648_ = v___x_2675_;
goto v___jp_2647_;
}
}
}
default: 
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_x_2633_);
lean_ctor_set(v___x_2678_, 1, v_x_2634_);
v___y_2648_ = v___x_2678_;
goto v___jp_2647_;
}
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_array_fset(v_xs_x27_2646_, v_j_2638_, v___y_2648_);
lean_dec(v_j_2638_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2649_);
v___x_2651_ = v___x_2642_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
else
{
lean_object* v_ks_2681_; lean_object* v_vs_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2700_; 
v_ks_2681_ = lean_ctor_get(v_x_2630_, 0);
v_vs_2682_ = lean_ctor_get(v_x_2630_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_x_2630_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2684_ = v_x_2630_;
v_isShared_2685_ = v_isSharedCheck_2700_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_vs_2682_);
lean_inc(v_ks_2681_);
lean_dec(v_x_2630_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2700_;
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
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_ks_2681_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_vs_2682_);
v___x_2687_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v_newNode_2688_; size_t v___x_2689_; uint8_t v___x_2690_; 
v_newNode_2688_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2687_, v_x_2633_, v_x_2634_);
v___x_2689_ = ((size_t)7ULL);
v___x_2690_ = lean_usize_dec_le(v___x_2689_, v_x_2632_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2691_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2688_);
v___x_2692_ = lean_unsigned_to_nat(4u);
v___x_2693_ = lean_nat_dec_lt(v___x_2691_, v___x_2692_);
lean_dec(v___x_2691_);
if (v___x_2693_ == 0)
{
lean_object* v_ks_2694_; lean_object* v_vs_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_ks_2694_ = lean_ctor_get(v_newNode_2688_, 0);
lean_inc_ref(v_ks_2694_);
v_vs_2695_ = lean_ctor_get(v_newNode_2688_, 1);
lean_inc_ref(v_vs_2695_);
lean_dec_ref(v_newNode_2688_);
v___x_2696_ = lean_unsigned_to_nat(0u);
v___x_2697_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2632_, v_ks_2694_, v_vs_2695_, v___x_2696_, v___x_2697_);
lean_dec_ref(v_vs_2695_);
lean_dec_ref(v_ks_2694_);
return v___x_2698_;
}
else
{
return v_newNode_2688_;
}
}
else
{
return v_newNode_2688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_2701_, lean_object* v_keys_2702_, lean_object* v_vals_2703_, lean_object* v_i_2704_, lean_object* v_entries_2705_){
_start:
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = lean_array_get_size(v_keys_2702_);
v___x_2707_ = lean_nat_dec_lt(v_i_2704_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_dec(v_i_2704_);
return v_entries_2705_;
}
else
{
lean_object* v_k_2708_; lean_object* v_v_2709_; uint64_t v___x_2710_; size_t v_h_2711_; size_t v___x_2712_; lean_object* v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v_h_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_k_2708_ = lean_array_fget_borrowed(v_keys_2702_, v_i_2704_);
v_v_2709_ = lean_array_fget_borrowed(v_vals_2703_, v_i_2704_);
v___x_2710_ = l_Lean_instHashableMVarId_hash(v_k_2708_);
v_h_2711_ = lean_uint64_to_usize(v___x_2710_);
v___x_2712_ = ((size_t)5ULL);
v___x_2713_ = lean_unsigned_to_nat(1u);
v___x_2714_ = ((size_t)1ULL);
v___x_2715_ = lean_usize_sub(v_depth_2701_, v___x_2714_);
v___x_2716_ = lean_usize_mul(v___x_2712_, v___x_2715_);
v_h_2717_ = lean_usize_shift_right(v_h_2711_, v___x_2716_);
v___x_2718_ = lean_nat_add(v_i_2704_, v___x_2713_);
lean_dec(v_i_2704_);
lean_inc(v_v_2709_);
lean_inc(v_k_2708_);
v___x_2719_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_2705_, v_h_2717_, v_depth_2701_, v_k_2708_, v_v_2709_);
v_i_2704_ = v___x_2718_;
v_entries_2705_ = v___x_2719_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2721_, lean_object* v_keys_2722_, lean_object* v_vals_2723_, lean_object* v_i_2724_, lean_object* v_entries_2725_){
_start:
{
size_t v_depth_boxed_2726_; lean_object* v_res_2727_; 
v_depth_boxed_2726_ = lean_unbox_usize(v_depth_2721_);
lean_dec(v_depth_2721_);
v_res_2727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_2726_, v_keys_2722_, v_vals_2723_, v_i_2724_, v_entries_2725_);
lean_dec_ref(v_vals_2723_);
lean_dec_ref(v_keys_2722_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_){
_start:
{
size_t v_x_3887__boxed_2733_; size_t v_x_3888__boxed_2734_; lean_object* v_res_2735_; 
v_x_3887__boxed_2733_ = lean_unbox_usize(v_x_2729_);
lean_dec(v_x_2729_);
v_x_3888__boxed_2734_ = lean_unbox_usize(v_x_2730_);
lean_dec(v_x_2730_);
v_res_2735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2728_, v_x_3887__boxed_2733_, v_x_3888__boxed_2734_, v_x_2731_, v_x_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object* v_x_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_){
_start:
{
uint64_t v___x_2739_; size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2739_ = l_Lean_instHashableMVarId_hash(v_x_2737_);
v___x_2740_ = lean_uint64_to_usize(v___x_2739_);
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2736_, v___x_2740_, v___x_2741_, v_x_2737_, v_x_2738_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object* v_mvarId_2743_, lean_object* v_val_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v_mctx_2748_; lean_object* v_cache_2749_; lean_object* v_zetaDeltaFVarIds_2750_; lean_object* v_postponed_2751_; lean_object* v_diag_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2782_; 
v___x_2747_ = lean_st_ref_take(v___y_2745_);
v_mctx_2748_ = lean_ctor_get(v___x_2747_, 0);
v_cache_2749_ = lean_ctor_get(v___x_2747_, 1);
v_zetaDeltaFVarIds_2750_ = lean_ctor_get(v___x_2747_, 2);
v_postponed_2751_ = lean_ctor_get(v___x_2747_, 3);
v_diag_2752_ = lean_ctor_get(v___x_2747_, 4);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2754_ = v___x_2747_;
v_isShared_2755_ = v_isSharedCheck_2782_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_diag_2752_);
lean_inc(v_postponed_2751_);
lean_inc(v_zetaDeltaFVarIds_2750_);
lean_inc(v_cache_2749_);
lean_inc(v_mctx_2748_);
lean_dec(v___x_2747_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2782_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_depth_2756_; lean_object* v_levelAssignDepth_2757_; lean_object* v_lmvarCounter_2758_; lean_object* v_mvarCounter_2759_; lean_object* v_lDecls_2760_; lean_object* v_decls_2761_; lean_object* v_userNames_2762_; lean_object* v_lAssignment_2763_; lean_object* v_eAssignment_2764_; lean_object* v_dAssignment_2765_; lean_object* v_instanceTypedMVars_2766_; lean_object* v_synthNormMemo_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2781_; 
v_depth_2756_ = lean_ctor_get(v_mctx_2748_, 0);
v_levelAssignDepth_2757_ = lean_ctor_get(v_mctx_2748_, 1);
v_lmvarCounter_2758_ = lean_ctor_get(v_mctx_2748_, 2);
v_mvarCounter_2759_ = lean_ctor_get(v_mctx_2748_, 3);
v_lDecls_2760_ = lean_ctor_get(v_mctx_2748_, 4);
v_decls_2761_ = lean_ctor_get(v_mctx_2748_, 5);
v_userNames_2762_ = lean_ctor_get(v_mctx_2748_, 6);
v_lAssignment_2763_ = lean_ctor_get(v_mctx_2748_, 7);
v_eAssignment_2764_ = lean_ctor_get(v_mctx_2748_, 8);
v_dAssignment_2765_ = lean_ctor_get(v_mctx_2748_, 9);
v_instanceTypedMVars_2766_ = lean_ctor_get(v_mctx_2748_, 10);
v_synthNormMemo_2767_ = lean_ctor_get(v_mctx_2748_, 11);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_mctx_2748_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2769_ = v_mctx_2748_;
v_isShared_2770_ = v_isSharedCheck_2781_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_synthNormMemo_2767_);
lean_inc(v_instanceTypedMVars_2766_);
lean_inc(v_dAssignment_2765_);
lean_inc(v_eAssignment_2764_);
lean_inc(v_lAssignment_2763_);
lean_inc(v_userNames_2762_);
lean_inc(v_decls_2761_);
lean_inc(v_lDecls_2760_);
lean_inc(v_mvarCounter_2759_);
lean_inc(v_lmvarCounter_2758_);
lean_inc(v_levelAssignDepth_2757_);
lean_inc(v_depth_2756_);
lean_dec(v_mctx_2748_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2781_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2771_ = lean_box(0);
v___x_2772_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2764_, v_mvarId_2743_, v_val_2744_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 8, v___x_2772_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_depth_2756_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_levelAssignDepth_2757_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_lmvarCounter_2758_);
lean_ctor_set(v_reuseFailAlloc_2780_, 3, v_mvarCounter_2759_);
lean_ctor_set(v_reuseFailAlloc_2780_, 4, v_lDecls_2760_);
lean_ctor_set(v_reuseFailAlloc_2780_, 5, v_decls_2761_);
lean_ctor_set(v_reuseFailAlloc_2780_, 6, v_userNames_2762_);
lean_ctor_set(v_reuseFailAlloc_2780_, 7, v_lAssignment_2763_);
lean_ctor_set(v_reuseFailAlloc_2780_, 8, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2780_, 9, v_dAssignment_2765_);
lean_ctor_set(v_reuseFailAlloc_2780_, 10, v_instanceTypedMVars_2766_);
lean_ctor_set(v_reuseFailAlloc_2780_, 11, v_synthNormMemo_2767_);
v___x_2774_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2776_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2774_);
v___x_2776_ = v___x_2754_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_cache_2749_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v_zetaDeltaFVarIds_2750_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v_postponed_2751_);
lean_ctor_set(v_reuseFailAlloc_2779_, 4, v_diag_2752_);
v___x_2776_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_st_ref_put(v___y_2745_, v___x_2776_);
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2771_);
return v___x_2778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2783_, lean_object* v_val_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2783_, v_val_2784_, v___y_2785_);
lean_dec(v___y_2785_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2796_, lean_object* v_as_2797_, size_t v_sz_2798_, size_t v_i_2799_, lean_object* v_b_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_a_2807_; uint8_t v___x_2811_; 
v___x_2811_ = lean_usize_dec_lt(v_i_2799_, v_sz_2798_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v_b_2800_);
return v___x_2812_;
}
else
{
lean_object* v_fst_2813_; lean_object* v_snd_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; lean_object* v_a_2817_; 
v_fst_2813_ = lean_ctor_get(v_b_2800_, 0);
lean_inc(v_fst_2813_);
v_snd_2814_ = lean_ctor_get(v_b_2800_, 1);
lean_inc(v_snd_2814_);
lean_dec_ref(v_b_2800_);
v___x_2815_ = lean_unsigned_to_nat(0u);
v___x_2816_ = lean_nat_dec_eq(v___x_2796_, v___x_2815_);
v_a_2817_ = lean_array_uget_borrowed(v_as_2797_, v_i_2799_);
if (lean_obj_tag(v_a_2817_) == 0)
{
lean_object* v_fvarId_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_fvarId_2818_ = lean_ctor_get(v_a_2817_, 0);
v___x_2819_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2814_, v_fvarId_2818_);
v___x_2820_ = l_Lean_Meta_substCore(v_fst_2813_, v___x_2819_, v___x_2811_, v_snd_2814_, v___x_2811_, v___x_2816_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v_fst_2822_; lean_object* v_snd_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v_fst_2822_ = lean_ctor_get(v_a_2821_, 0);
v_snd_2823_ = lean_ctor_get(v_a_2821_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_a_2821_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v_a_2821_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_snd_2823_);
lean_inc(v_fst_2822_);
lean_dec(v_a_2821_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 1, v_fst_2822_);
lean_ctor_set(v___x_2825_, 0, v_snd_2823_);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_snd_2823_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_fst_2822_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
v_a_2807_ = v___x_2828_;
goto v___jp_2806_;
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
v_a_2831_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2820_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2820_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
lean_object* v_lhs_2839_; lean_object* v_rhs_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v_lhs_2839_ = lean_ctor_get(v_a_2817_, 0);
v_rhs_2840_ = lean_ctor_get(v_a_2817_, 1);
v___x_2841_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2814_, v_lhs_2839_);
v___x_2842_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2814_, v_rhs_2840_);
v___x_2843_ = l_Lean_mkFVar(v___x_2841_);
v___x_2844_ = l_Lean_mkFVar(v___x_2842_);
lean_inc_ref(v___x_2844_);
lean_inc_ref(v___x_2843_);
v___x_2845_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2845_, 0, v___x_2843_);
lean_closure_set(v___x_2845_, 1, v___x_2844_);
lean_inc(v_fst_2813_);
v___x_2846_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2813_, v___x_2845_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2849_ = lean_unsigned_to_nat(2u);
v___x_2850_ = lean_mk_empty_array_with_capacity(v___x_2849_);
v___x_2851_ = lean_array_push(v___x_2850_, v___x_2843_);
v___x_2852_ = lean_array_push(v___x_2851_, v___x_2844_);
v___x_2853_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2853_, 0, v___x_2848_);
lean_closure_set(v___x_2853_, 1, v___x_2852_);
lean_inc(v_fst_2813_);
v___x_2854_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2813_, v___x_2853_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
v___x_2857_ = l_Lean_MVarId_assert(v_fst_2813_, v___x_2856_, v_a_2847_, v_a_2855_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = l_Lean_Meta_intro1Core(v_a_2858_, v___x_2816_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v_fst_2861_; lean_object* v_snd_2862_; lean_object* v___x_2863_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v_fst_2861_ = lean_ctor_get(v_a_2860_, 0);
lean_inc(v_fst_2861_);
v_snd_2862_ = lean_ctor_get(v_a_2860_, 1);
lean_inc(v_snd_2862_);
lean_dec(v_a_2860_);
v___x_2863_ = l_Lean_Meta_substCore(v_snd_2862_, v_fst_2861_, v___x_2811_, v_snd_2814_, v___x_2811_, v___x_2816_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v_fst_2865_ = lean_ctor_get(v_a_2864_, 0);
v_snd_2866_ = lean_ctor_get(v_a_2864_, 1);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_a_2864_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v_a_2864_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_snd_2866_);
lean_inc(v_fst_2865_);
lean_dec(v_a_2864_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v_fst_2865_);
lean_ctor_set(v___x_2868_, 0, v_snd_2866_);
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_snd_2866_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_fst_2865_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
v_a_2807_ = v___x_2871_;
goto v___jp_2806_;
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
v_a_2874_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2863_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2863_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_snd_2814_);
v_a_2882_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2859_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2859_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_snd_2814_);
v_a_2890_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2857_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2857_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
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
lean_dec(v_a_2847_);
lean_dec(v_snd_2814_);
lean_dec(v_fst_2813_);
v_a_2898_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2854_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2854_);
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
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v___x_2844_);
lean_dec_ref(v___x_2843_);
lean_dec(v_snd_2814_);
lean_dec(v_fst_2813_);
v_a_2906_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2846_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2846_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
v___jp_2806_:
{
size_t v___x_2808_; size_t v___x_2809_; 
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_add(v_i_2799_, v___x_2808_);
v_i_2799_ = v___x_2809_;
v_b_2800_ = v_a_2807_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_2914_, lean_object* v_as_2915_, lean_object* v_sz_2916_, lean_object* v_i_2917_, lean_object* v_b_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
size_t v_sz_boxed_2924_; size_t v_i_boxed_2925_; lean_object* v_res_2926_; 
v_sz_boxed_2924_ = lean_unbox_usize(v_sz_2916_);
lean_dec(v_sz_2916_);
v_i_boxed_2925_ = lean_unbox_usize(v_i_2917_);
lean_dec(v_i_2917_);
v_res_2926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2914_, v_as_2915_, v_sz_boxed_2924_, v_i_boxed_2925_, v_b_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec_ref(v_as_2915_);
lean_dec(v___x_2914_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_2927_, lean_object* v_as_2928_, size_t v_i_2929_, size_t v_stop_2930_, lean_object* v_b_2931_){
_start:
{
lean_object* v___y_2933_; uint8_t v___x_2937_; 
v___x_2937_ = lean_usize_dec_eq(v_i_2929_, v_stop_2930_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_array_uget_borrowed(v_as_2928_, v_i_2929_);
v___x_2940_ = lean_array_get_borrowed(v___x_2938_, v_eqs_2927_, v___x_2939_);
if (lean_obj_tag(v___x_2940_) == 0)
{
v___y_2933_ = v_b_2931_;
goto v___jp_2932_;
}
else
{
lean_object* v_val_2941_; lean_object* v___x_2942_; 
v_val_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_val_2941_);
v___x_2942_ = lean_array_push(v_b_2931_, v_val_2941_);
v___y_2933_ = v___x_2942_;
goto v___jp_2932_;
}
}
else
{
return v_b_2931_;
}
v___jp_2932_:
{
size_t v___x_2934_; size_t v___x_2935_; 
v___x_2934_ = ((size_t)1ULL);
v___x_2935_ = lean_usize_add(v_i_2929_, v___x_2934_);
v_i_2929_ = v___x_2935_;
v_b_2931_ = v___y_2933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_2943_, lean_object* v_as_2944_, lean_object* v_i_2945_, lean_object* v_stop_2946_, lean_object* v_b_2947_){
_start:
{
size_t v_i_boxed_2948_; size_t v_stop_boxed_2949_; lean_object* v_res_2950_; 
v_i_boxed_2948_ = lean_unbox_usize(v_i_2945_);
lean_dec(v_i_2945_);
v_stop_boxed_2949_ = lean_unbox_usize(v_stop_2946_);
lean_dec(v_stop_2946_);
v_res_2950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2943_, v_as_2944_, v_i_boxed_2948_, v_stop_boxed_2949_, v_b_2947_);
lean_dec_ref(v_as_2944_);
lean_dec_ref(v_eqs_2943_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_2953_, lean_object* v_as_2954_, lean_object* v_start_2955_, lean_object* v_stop_2956_){
_start:
{
lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2957_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_2958_ = lean_nat_dec_lt(v_start_2955_, v_stop_2956_);
if (v___x_2958_ == 0)
{
return v___x_2957_;
}
else
{
lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = lean_array_get_size(v_as_2954_);
v___x_2960_ = lean_nat_dec_le(v_stop_2956_, v___x_2959_);
if (v___x_2960_ == 0)
{
uint8_t v___x_2961_; 
v___x_2961_ = lean_nat_dec_lt(v_start_2955_, v___x_2959_);
if (v___x_2961_ == 0)
{
return v___x_2957_;
}
else
{
size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = lean_usize_of_nat(v_start_2955_);
v___x_2963_ = lean_usize_of_nat(v___x_2959_);
v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2953_, v_as_2954_, v___x_2962_, v___x_2963_, v___x_2957_);
return v___x_2964_;
}
}
else
{
size_t v___x_2965_; size_t v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = lean_usize_of_nat(v_start_2955_);
v___x_2966_ = lean_usize_of_nat(v_stop_2956_);
v___x_2967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2953_, v_as_2954_, v___x_2965_, v___x_2966_, v___x_2957_);
return v___x_2967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_2968_, lean_object* v_as_2969_, lean_object* v_start_2970_, lean_object* v_stop_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2968_, v_as_2969_, v_start_2970_, v_stop_2971_);
lean_dec(v_stop_2971_);
lean_dec(v_start_2970_);
lean_dec_ref(v_as_2969_);
lean_dec_ref(v_eqs_2968_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_2973_, lean_object* v_type_2974_, lean_object* v_deps_2975_, lean_object* v_eqs_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_eqs_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2982_ = lean_unsigned_to_nat(0u);
v___x_2983_ = lean_array_get_size(v_deps_2975_);
v_eqs_2984_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2976_, v_deps_2975_, v___x_2982_, v___x_2983_);
v___x_2985_ = lean_array_get_size(v_eqs_2984_);
v___x_2986_ = lean_nat_dec_eq(v___x_2985_, v___x_2982_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_type_2974_);
v___x_2988_ = 0;
v___x_2989_ = lean_box(0);
v___x_2990_ = l_Lean_Meta_mkFreshExprMVar(v___x_2987_, v___x_2988_, v___x_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; size_t v_sz_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = l_Lean_Expr_mvarId_x21(v_a_2991_);
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2992_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v_sz_2995_ = lean_array_size(v_eqs_2984_);
v___x_2996_ = ((size_t)0ULL);
v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2985_, v_eqs_2984_, v_sz_2995_, v___x_2996_, v___x_2994_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
lean_dec_ref(v_eqs_2984_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v_fst_2999_; lean_object* v_snd_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v_fst_2999_ = lean_ctor_get(v_a_2998_, 0);
lean_inc(v_fst_2999_);
v_snd_3000_ = lean_ctor_get(v_a_2998_, 1);
lean_inc(v_snd_3000_);
lean_dec(v_a_2998_);
v___x_3001_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_3000_, v_fvarId_2973_);
lean_dec(v_fvarId_2973_);
lean_dec(v_snd_3000_);
v___x_3002_ = l_Lean_mkFVar(v___x_3001_);
v___x_3003_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_2999_, v___x_3002_, v_a_2978_);
lean_dec_ref(v___x_3003_);
v___x_3004_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_2991_, v_a_2978_);
return v___x_3004_;
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec(v_a_2991_);
lean_dec(v_fvarId_2973_);
v_a_3005_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2997_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2997_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
else
{
lean_dec_ref(v_eqs_2984_);
lean_dec(v_fvarId_2973_);
return v___x_2990_;
}
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec_ref(v_eqs_2984_);
lean_dec_ref(v_type_2974_);
v___x_3013_ = l_Lean_mkFVar(v_fvarId_2973_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3015_, lean_object* v_type_3016_, lean_object* v_deps_3017_, lean_object* v_eqs_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3015_, v_type_3016_, v_deps_3017_, v_eqs_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec_ref(v_eqs_3018_);
lean_dec_ref(v_deps_3017_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3025_, lean_object* v_val_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3025_, v_val_3026_, v___y_3028_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3033_, lean_object* v_val_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3033_, v_val_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3041_, lean_object* v_x_3042_, lean_object* v_x_3043_, lean_object* v_x_3044_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3042_, v_x_3043_, v_x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3046_, lean_object* v_x_3047_, size_t v_x_3048_, size_t v_x_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3047_, v_x_3048_, v_x_3049_, v_x_3050_, v_x_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3053_, lean_object* v_x_3054_, lean_object* v_x_3055_, lean_object* v_x_3056_, lean_object* v_x_3057_, lean_object* v_x_3058_){
_start:
{
size_t v_x_4488__boxed_3059_; size_t v_x_4489__boxed_3060_; lean_object* v_res_3061_; 
v_x_4488__boxed_3059_ = lean_unbox_usize(v_x_3055_);
lean_dec(v_x_3055_);
v_x_4489__boxed_3060_ = lean_unbox_usize(v_x_3056_);
lean_dec(v_x_3056_);
v_res_3061_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3053_, v_x_3054_, v_x_4488__boxed_3059_, v_x_4489__boxed_3060_, v_x_3057_, v_x_3058_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3062_, lean_object* v_n_3063_, lean_object* v_k_3064_, lean_object* v_v_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3063_, v_k_3064_, v_v_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3067_, size_t v_depth_3068_, lean_object* v_keys_3069_, lean_object* v_vals_3070_, lean_object* v_heq_3071_, lean_object* v_i_3072_, lean_object* v_entries_3073_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3068_, v_keys_3069_, v_vals_3070_, v_i_3072_, v_entries_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3075_, lean_object* v_depth_3076_, lean_object* v_keys_3077_, lean_object* v_vals_3078_, lean_object* v_heq_3079_, lean_object* v_i_3080_, lean_object* v_entries_3081_){
_start:
{
size_t v_depth_boxed_3082_; lean_object* v_res_3083_; 
v_depth_boxed_3082_ = lean_unbox_usize(v_depth_3076_);
lean_dec(v_depth_3076_);
v_res_3083_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3075_, v_depth_boxed_3082_, v_keys_3077_, v_vals_3078_, v_heq_3079_, v_i_3080_, v_entries_3081_);
lean_dec_ref(v_vals_3078_);
lean_dec_ref(v_keys_3077_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3084_, lean_object* v_x_3085_, lean_object* v_x_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3085_, v_x_3086_, v_x_3087_, v_x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___f_3097_; lean_object* v___x_1366__overap_3098_; lean_object* v___x_3099_; 
v___f_3097_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1366__overap_3098_ = lean_panic_fn_borrowed(v___f_3097_, v_msg_3091_);
lean_inc(v___y_3095_);
lean_inc_ref(v___y_3094_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
v___x_3099_ = lean_apply_5(v___x_1366__overap_3098_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, lean_box(0));
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
return v_res_3106_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3110_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3111_ = lean_unsigned_to_nat(34u);
v___x_3112_ = lean_unsigned_to_nat(360u);
v___x_3113_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3114_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3115_ = l_mkPanicMessageWithDecl(v___x_3114_, v___x_3113_, v___x_3112_, v___x_3111_, v___x_3110_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v_i_3119_, lean_object* v_kinds_3120_, lean_object* v___x_3121_, lean_object* v_lhs_3122_, lean_object* v_rhs_3123_, lean_object* v_type_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
uint8_t v___x_1560__boxed_3130_; uint8_t v___x_1561__boxed_3131_; lean_object* v_res_3132_; 
v___x_1560__boxed_3130_ = lean_unbox(v___x_3117_);
v___x_1561__boxed_3131_ = lean_unbox(v___x_3118_);
v_res_3132_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3116_, v___x_1560__boxed_3130_, v___x_1561__boxed_3131_, v_i_3119_, v_kinds_3120_, v___x_3121_, v_lhs_3122_, v_rhs_3123_, v_type_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3133_, uint8_t v___x_3134_, uint8_t v___x_3135_, lean_object* v_i_3136_, lean_object* v___x_3137_, lean_object* v_kinds_3138_, lean_object* v_typeSub_3139_, lean_object* v_lhs_3140_, lean_object* v_rhs_3141_, lean_object* v_type_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; 
lean_inc_ref(v_rhs_3141_);
v___x_3148_ = lean_array_push(v___x_3133_, v_rhs_3141_);
v___x_3149_ = 1;
v___x_3150_ = l_Lean_Meta_mkLambdaFVars(v___x_3148_, v_type_3142_, v___x_3134_, v___x_3135_, v___x_3134_, v___x_3135_, v___x_3149_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec_ref(v___x_3148_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v___x_3152_ = lean_nat_add(v_i_3136_, v___x_3137_);
v___x_3153_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3138_, v___x_3152_, v_typeSub_3139_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3156_ = lean_unsigned_to_nat(2u);
v___x_3157_ = lean_mk_empty_array_with_capacity(v___x_3156_);
v___x_3158_ = lean_array_push(v___x_3157_, v_lhs_3140_);
v___x_3159_ = lean_array_push(v___x_3158_, v_rhs_3141_);
lean_inc_ref(v___x_3159_);
v___x_3160_ = l_Lean_Meta_mkAppM(v___x_3155_, v___x_3159_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3162_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v___x_3162_ = l_Lean_Meta_mkEqNDRec(v_a_3151_, v_a_3154_, v_a_3161_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = l_Lean_Meta_mkLambdaFVars(v___x_3159_, v_a_3163_, v___x_3134_, v___x_3135_, v___x_3134_, v___x_3135_, v___x_3149_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec_ref(v___x_3159_);
return v___x_3164_;
}
else
{
lean_dec_ref(v___x_3159_);
return v___x_3162_;
}
}
else
{
lean_dec_ref(v___x_3159_);
lean_dec(v_a_3154_);
lean_dec(v_a_3151_);
return v___x_3160_;
}
}
else
{
lean_dec(v_a_3151_);
lean_dec_ref(v_rhs_3141_);
lean_dec_ref(v_lhs_3140_);
return v___x_3153_;
}
}
else
{
lean_dec_ref(v_rhs_3141_);
lean_dec_ref(v_lhs_3140_);
lean_dec_ref(v_typeSub_3139_);
lean_dec_ref(v_kinds_3138_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3165_, lean_object* v___x_3166_, lean_object* v___x_3167_, lean_object* v_i_3168_, lean_object* v___x_3169_, lean_object* v_kinds_3170_, lean_object* v_typeSub_3171_, lean_object* v_lhs_3172_, lean_object* v_rhs_3173_, lean_object* v_type_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v___x_1624__boxed_3180_; uint8_t v___x_1625__boxed_3181_; lean_object* v_res_3182_; 
v___x_1624__boxed_3180_ = lean_unbox(v___x_3166_);
v___x_1625__boxed_3181_ = lean_unbox(v___x_3167_);
v_res_3182_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3165_, v___x_1624__boxed_3180_, v___x_1625__boxed_3181_, v_i_3168_, v___x_3169_, v_kinds_3170_, v_typeSub_3171_, v_lhs_3172_, v_rhs_3173_, v_type_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___x_3169_);
lean_dec(v_i_3168_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(uint8_t v___x_3183_, lean_object* v_kinds_3184_, lean_object* v_i_3185_, uint8_t v___x_3186_, uint8_t v___x_3187_, lean_object* v_lhs_3188_, lean_object* v_type_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3198_ = lean_box(v___x_3183_);
v___x_3199_ = lean_array_get(v___x_3198_, v_kinds_3184_, v_i_3185_);
lean_dec(v___x_3198_);
v___x_3200_ = lean_unbox(v___x_3199_);
lean_dec(v___x_3199_);
switch(v___x_3200_)
{
case 1:
{
lean_dec_ref(v_type_3189_);
lean_dec_ref(v_lhs_3188_);
lean_dec(v_i_3185_);
lean_dec_ref(v_kinds_3184_);
goto v___jp_3195_;
}
case 2:
{
lean_object* v___x_3201_; 
lean_inc_ref(v_lhs_3188_);
v___x_3201_ = l_Lean_Meta_mkEqRefl(v_lhs_3188_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___f_3212_; lean_object* v___x_3213_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___x_3201_, 1);
v___x_3203_ = l_Lean_Expr_bindingBody_x21(v_type_3189_);
v___x_3204_ = l_Lean_Expr_bindingBody_x21(v___x_3203_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = lean_unsigned_to_nat(2u);
v___x_3206_ = lean_mk_empty_array_with_capacity(v___x_3205_);
lean_inc_ref(v___x_3206_);
v___x_3207_ = lean_array_push(v___x_3206_, v_a_3202_);
lean_inc_ref(v_lhs_3188_);
v___x_3208_ = lean_array_push(v___x_3207_, v_lhs_3188_);
v___x_3209_ = lean_expr_instantiate(v___x_3204_, v___x_3208_);
lean_dec_ref(v___x_3208_);
lean_dec_ref(v___x_3204_);
v___x_3210_ = lean_box(v___x_3186_);
v___x_3211_ = lean_box(v___x_3187_);
v___f_3212_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3212_, 0, v___x_3206_);
lean_closure_set(v___f_3212_, 1, v___x_3210_);
lean_closure_set(v___f_3212_, 2, v___x_3211_);
lean_closure_set(v___f_3212_, 3, v_i_3185_);
lean_closure_set(v___f_3212_, 4, v_kinds_3184_);
lean_closure_set(v___f_3212_, 5, v___x_3209_);
lean_closure_set(v___f_3212_, 6, v_lhs_3188_);
v___x_3213_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3189_, v___f_3212_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
return v___x_3213_;
}
else
{
lean_dec_ref(v_type_3189_);
lean_dec_ref(v_lhs_3188_);
lean_dec(v_i_3185_);
lean_dec_ref(v_kinds_3184_);
return v___x_3201_;
}
}
case 4:
{
lean_dec_ref(v_type_3189_);
lean_dec_ref(v_lhs_3188_);
lean_dec(v_i_3185_);
lean_dec_ref(v_kinds_3184_);
goto v___jp_3195_;
}
case 5:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v_typeSub_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; 
v___x_3214_ = l_Lean_Expr_bindingBody_x21(v_type_3189_);
v___x_3215_ = lean_unsigned_to_nat(1u);
v___x_3216_ = lean_mk_empty_array_with_capacity(v___x_3215_);
lean_inc_ref(v_lhs_3188_);
lean_inc_ref(v___x_3216_);
v___x_3217_ = lean_array_push(v___x_3216_, v_lhs_3188_);
v_typeSub_3218_ = lean_expr_instantiate(v___x_3214_, v___x_3217_);
lean_dec_ref(v___x_3217_);
lean_dec_ref(v___x_3214_);
v___x_3219_ = lean_box(v___x_3186_);
v___x_3220_ = lean_box(v___x_3187_);
v___f_3221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3221_, 0, v___x_3216_);
lean_closure_set(v___f_3221_, 1, v___x_3219_);
lean_closure_set(v___f_3221_, 2, v___x_3220_);
lean_closure_set(v___f_3221_, 3, v_i_3185_);
lean_closure_set(v___f_3221_, 4, v___x_3215_);
lean_closure_set(v___f_3221_, 5, v_kinds_3184_);
lean_closure_set(v___f_3221_, 6, v_typeSub_3218_);
lean_closure_set(v___f_3221_, 7, v_lhs_3188_);
v___x_3222_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3189_, v___f_3221_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
return v___x_3222_;
}
default: 
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = lean_unsigned_to_nat(1u);
v___x_3224_ = lean_nat_add(v_i_3185_, v___x_3223_);
lean_dec(v_i_3185_);
v___x_3225_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3184_, v___x_3224_, v_type_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; lean_object* v___x_3230_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v___x_3227_ = lean_mk_empty_array_with_capacity(v___x_3223_);
v___x_3228_ = lean_array_push(v___x_3227_, v_lhs_3188_);
v___x_3229_ = 1;
v___x_3230_ = l_Lean_Meta_mkLambdaFVars(v___x_3228_, v_a_3226_, v___x_3186_, v___x_3187_, v___x_3186_, v___x_3187_, v___x_3229_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec_ref(v___x_3228_);
return v___x_3230_;
}
else
{
lean_dec_ref(v_lhs_3188_);
return v___x_3225_;
}
}
}
v___jp_3195_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3197_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3196_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
return v___x_3197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v___x_3231_, lean_object* v_kinds_3232_, lean_object* v_i_3233_, lean_object* v___x_3234_, lean_object* v___x_3235_, lean_object* v_lhs_3236_, lean_object* v_type_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v___x_1661__boxed_3243_; uint8_t v___x_1662__boxed_3244_; uint8_t v___x_1663__boxed_3245_; lean_object* v_res_3246_; 
v___x_1661__boxed_3243_ = lean_unbox(v___x_3231_);
v___x_1662__boxed_3244_ = lean_unbox(v___x_3234_);
v___x_1663__boxed_3245_ = lean_unbox(v___x_3235_);
v_res_3246_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v___x_1661__boxed_3243_, v_kinds_3232_, v_i_3233_, v___x_1662__boxed_3244_, v___x_1663__boxed_3245_, v_lhs_3236_, v_type_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
return v_res_3246_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3247_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3248_ = lean_unsigned_to_nat(43u);
v___x_3249_ = lean_unsigned_to_nat(355u);
v___x_3250_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3251_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3252_ = l_mkPanicMessageWithDecl(v___x_3251_, v___x_3250_, v___x_3249_, v___x_3248_, v___x_3247_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3253_, lean_object* v_i_3254_, lean_object* v_type_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v___x_3261_; uint8_t v___x_3262_; 
v___x_3261_ = lean_array_get_size(v_kinds_3253_);
v___x_3262_ = lean_nat_dec_eq(v_i_3254_, v___x_3261_);
if (v___x_3262_ == 0)
{
uint8_t v___x_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___f_3268_; lean_object* v___x_3269_; 
v___x_3263_ = 0;
v___x_3264_ = 1;
v___x_3265_ = lean_box(v___x_3263_);
v___x_3266_ = lean_box(v___x_3262_);
v___x_3267_ = lean_box(v___x_3264_);
v___f_3268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 12, 5);
lean_closure_set(v___f_3268_, 0, v___x_3265_);
lean_closure_set(v___f_3268_, 1, v_kinds_3253_);
lean_closure_set(v___f_3268_, 2, v_i_3254_);
lean_closure_set(v___f_3268_, 3, v___x_3266_);
lean_closure_set(v___f_3268_, 4, v___x_3267_);
v___x_3269_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3255_, v___f_3268_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_);
return v___x_3269_;
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; 
lean_dec(v_i_3254_);
lean_dec_ref(v_kinds_3253_);
v___x_3270_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3271_ = lean_unsigned_to_nat(3u);
v___x_3272_ = l_Lean_Expr_isAppOfArity(v_type_3255_, v___x_3270_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_dec_ref(v_type_3255_);
v___x_3273_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3274_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3273_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = l_Lean_Expr_appFn_x21(v_type_3255_);
lean_dec_ref(v_type_3255_);
v___x_3276_ = l_Lean_Expr_appArg_x21(v___x_3275_);
lean_dec_ref(v___x_3275_);
v___x_3277_ = l_Lean_Meta_mkEqRefl(v___x_3276_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_);
return v___x_3277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* v___x_3278_, lean_object* v_rhs_3279_, uint8_t v___x_3280_, uint8_t v___x_3281_, lean_object* v_i_3282_, lean_object* v_kinds_3283_, lean_object* v___x_3284_, lean_object* v_lhs_3285_, lean_object* v_heq_3286_, lean_object* v_type_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; 
lean_inc_ref(v_rhs_3279_);
v___x_3293_ = lean_array_push(v___x_3278_, v_rhs_3279_);
lean_inc_ref(v_heq_3286_);
v___x_3294_ = lean_array_push(v___x_3293_, v_heq_3286_);
v___x_3295_ = 1;
v___x_3296_ = l_Lean_Meta_mkLambdaFVars(v___x_3294_, v_type_3287_, v___x_3280_, v___x_3281_, v___x_3280_, v___x_3281_, v___x_3295_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec_ref(v___x_3294_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v___x_3298_ = lean_unsigned_to_nat(1u);
v___x_3299_ = lean_nat_add(v_i_3282_, v___x_3298_);
v___x_3300_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3283_, v___x_3299_, v___x_3284_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3302_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3300_, 1);
lean_inc_ref(v_heq_3286_);
v___x_3302_ = l_Lean_Meta_mkEqRec(v_a_3297_, v_a_3301_, v_heq_3286_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = lean_unsigned_to_nat(3u);
v___x_3305_ = lean_mk_empty_array_with_capacity(v___x_3304_);
v___x_3306_ = lean_array_push(v___x_3305_, v_lhs_3285_);
v___x_3307_ = lean_array_push(v___x_3306_, v_rhs_3279_);
v___x_3308_ = lean_array_push(v___x_3307_, v_heq_3286_);
v___x_3309_ = l_Lean_Meta_mkLambdaFVars(v___x_3308_, v_a_3303_, v___x_3280_, v___x_3281_, v___x_3280_, v___x_3281_, v___x_3295_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec_ref(v___x_3308_);
return v___x_3309_;
}
else
{
lean_dec_ref(v_heq_3286_);
lean_dec_ref(v_lhs_3285_);
lean_dec_ref(v_rhs_3279_);
return v___x_3302_;
}
}
else
{
lean_dec(v_a_3297_);
lean_dec_ref(v_heq_3286_);
lean_dec_ref(v_lhs_3285_);
lean_dec_ref(v_rhs_3279_);
return v___x_3300_;
}
}
else
{
lean_dec_ref(v_heq_3286_);
lean_dec_ref(v_lhs_3285_);
lean_dec_ref(v___x_3284_);
lean_dec_ref(v_kinds_3283_);
lean_dec_ref(v_rhs_3279_);
return v___x_3296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* v___x_3310_, lean_object* v_rhs_3311_, lean_object* v___x_3312_, lean_object* v___x_3313_, lean_object* v_i_3314_, lean_object* v_kinds_3315_, lean_object* v___x_3316_, lean_object* v_lhs_3317_, lean_object* v_heq_3318_, lean_object* v_type_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
uint8_t v___x_1571__boxed_3325_; uint8_t v___x_1572__boxed_3326_; lean_object* v_res_3327_; 
v___x_1571__boxed_3325_ = lean_unbox(v___x_3312_);
v___x_1572__boxed_3326_ = lean_unbox(v___x_3313_);
v_res_3327_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3310_, v_rhs_3311_, v___x_1571__boxed_3325_, v___x_1572__boxed_3326_, v_i_3314_, v_kinds_3315_, v___x_3316_, v_lhs_3317_, v_heq_3318_, v_type_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v_i_3314_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* v___x_3328_, uint8_t v___x_3329_, uint8_t v___x_3330_, lean_object* v_i_3331_, lean_object* v_kinds_3332_, lean_object* v___x_3333_, lean_object* v_lhs_3334_, lean_object* v_rhs_3335_, lean_object* v_type_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___f_3344_; lean_object* v___x_3345_; 
v___x_3342_ = lean_box(v___x_3329_);
v___x_3343_ = lean_box(v___x_3330_);
v___f_3344_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3344_, 0, v___x_3328_);
lean_closure_set(v___f_3344_, 1, v_rhs_3335_);
lean_closure_set(v___f_3344_, 2, v___x_3342_);
lean_closure_set(v___f_3344_, 3, v___x_3343_);
lean_closure_set(v___f_3344_, 4, v_i_3331_);
lean_closure_set(v___f_3344_, 5, v_kinds_3332_);
lean_closure_set(v___f_3344_, 6, v___x_3333_);
lean_closure_set(v___f_3344_, 7, v_lhs_3334_);
v___x_3345_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3336_, v___f_3344_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object* v_kinds_3346_, lean_object* v_i_3347_, lean_object* v_type_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3346_, v_i_3347_, v_type_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* v_type_3355_, lean_object* v_kinds_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = lean_unsigned_to_nat(0u);
v___x_3363_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3356_, v___x_3362_, v_type_3355_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object* v_type_3364_, lean_object* v_kinds_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3364_, v_kinds_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_msg_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v___f_3378_; lean_object* v___x_1532__overap_3379_; lean_object* v___x_3380_; 
v___f_3378_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1532__overap_3379_ = lean_panic_fn_borrowed(v___f_3378_, v_msg_3372_);
lean_inc(v___y_3376_);
lean_inc_ref(v___y_3375_);
lean_inc(v___y_3374_);
lean_inc_ref(v___y_3373_);
v___x_3380_ = lean_apply_5(v___x_1532__overap_3379_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, lean_box(0));
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_msg_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_msg_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(lean_object* v_bs_3388_, lean_object* v_k_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3388_, v_k_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
v_a_3404_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3395_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3395_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg___boxed(lean_object* v_bs_3412_, lean_object* v_k_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v_bs_3412_, v_k_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v_bs_3412_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(lean_object* v_00_u03b1_3420_, lean_object* v_bs_3421_, lean_object* v_k_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v_bs_3421_, v_k_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3429_, lean_object* v_bs_3430_, lean_object* v_k_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(v_00_u03b1_3429_, v_bs_3430_, v_k_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec_ref(v_bs_3430_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(size_t v_sz_3438_, size_t v_i_3439_, lean_object* v_bs_3440_){
_start:
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_usize_dec_lt(v_i_3439_, v_sz_3438_);
if (v___x_3441_ == 0)
{
return v_bs_3440_;
}
else
{
lean_object* v_v_3442_; lean_object* v___x_3443_; lean_object* v_bs_x27_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; size_t v___x_3449_; size_t v___x_3450_; lean_object* v___x_3451_; 
v_v_3442_ = lean_array_uget(v_bs_3440_, v_i_3439_);
v___x_3443_ = lean_unsigned_to_nat(0u);
v_bs_x27_3444_ = lean_array_uset(v_bs_3440_, v_i_3439_, v___x_3443_);
v___x_3445_ = l_Lean_Expr_fvarId_x21(v_v_3442_);
lean_dec(v_v_3442_);
v___x_3446_ = 1;
v___x_3447_ = lean_box(v___x_3446_);
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3445_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = ((size_t)1ULL);
v___x_3450_ = lean_usize_add(v_i_3439_, v___x_3449_);
v___x_3451_ = lean_array_uset(v_bs_x27_3444_, v_i_3439_, v___x_3448_);
v_i_3439_ = v___x_3450_;
v_bs_3440_ = v___x_3451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1___boxed(lean_object* v_sz_3453_, lean_object* v_i_3454_, lean_object* v_bs_3455_){
_start:
{
size_t v_sz_boxed_3456_; size_t v_i_boxed_3457_; lean_object* v_res_3458_; 
v_sz_boxed_3456_ = lean_unbox_usize(v_sz_3453_);
lean_dec(v_sz_3453_);
v_i_boxed_3457_ = lean_unbox_usize(v_i_3454_);
lean_dec(v_i_3454_);
v_res_3458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(v_sz_boxed_3456_, v_i_boxed_3457_, v_bs_3455_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(lean_object* v_bs_3459_, lean_object* v_k_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
size_t v_sz_3466_; size_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_sz_3466_ = lean_array_size(v_bs_3459_);
v___x_3467_ = ((size_t)0ULL);
v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(v_sz_3466_, v___x_3467_, v_bs_3459_);
v___x_3469_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v___x_3468_, v_k_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
lean_dec_ref(v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg___boxed(lean_object* v_bs_3470_, lean_object* v_k_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v_bs_3470_, v_k_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_00_u03b1_3478_, lean_object* v_bs_3479_, lean_object* v_k_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v_bs_3479_, v_k_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_00_u03b1_3487_, lean_object* v_bs_3488_, lean_object* v_k_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_00_u03b1_3487_, v_bs_3488_, v_k_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
return v_res_3495_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3497_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3498_ = lean_unsigned_to_nat(38u);
v___x_3499_ = lean_unsigned_to_nat(328u);
v___x_3500_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3501_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3502_ = l_mkPanicMessageWithDecl(v___x_3501_, v___x_3500_, v___x_3499_, v___x_3498_, v___x_3497_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3503_, lean_object* v_rhss_3504_, lean_object* v_b_3505_, lean_object* v_eqs_3506_, lean_object* v_hyps_3507_, uint8_t v_subsingletonInstImplicitRhs_3508_, lean_object* v_f_3509_, lean_object* v_info_3510_, lean_object* v_kinds_3511_, lean_object* v_lhss_3512_, lean_object* v_eq_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3519_ = lean_unsigned_to_nat(1u);
v___x_3520_ = lean_nat_add(v_i_3503_, v___x_3519_);
lean_inc_ref(v_b_3505_);
v___x_3521_ = lean_array_push(v_rhss_3504_, v_b_3505_);
v___x_3522_ = l_Lean_Expr_fvarId_x21(v_eq_3513_);
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
v___x_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
v___x_3525_ = lean_array_push(v_eqs_3506_, v___x_3524_);
v___x_3526_ = lean_array_push(v_hyps_3507_, v_b_3505_);
v___x_3527_ = lean_array_push(v___x_3526_, v_eq_3513_);
v___x_3528_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3508_, v_f_3509_, v_info_3510_, v_kinds_3511_, v_lhss_3512_, v___x_3520_, v___x_3521_, v___x_3525_, v___x_3527_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3529_, lean_object* v_rhss_3530_, lean_object* v_b_3531_, lean_object* v_eqs_3532_, lean_object* v_hyps_3533_, lean_object* v_subsingletonInstImplicitRhs_3534_, lean_object* v_f_3535_, lean_object* v_info_3536_, lean_object* v_kinds_3537_, lean_object* v_lhss_3538_, lean_object* v_eq_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3545_; lean_object* v_res_3546_; 
v_subsingletonInstImplicitRhs_boxed_3545_ = lean_unbox(v_subsingletonInstImplicitRhs_3534_);
v_res_3546_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3529_, v_rhss_3530_, v_b_3531_, v_eqs_3532_, v_hyps_3533_, v_subsingletonInstImplicitRhs_boxed_3545_, v_f_3535_, v_info_3536_, v_kinds_3537_, v_lhss_3538_, v_eq_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v_i_3529_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(lean_object* v_i_3548_, lean_object* v_rhss_3549_, lean_object* v_eqs_3550_, lean_object* v_hyps_3551_, uint8_t v_subsingletonInstImplicitRhs_3552_, lean_object* v_f_3553_, lean_object* v_info_3554_, lean_object* v_kinds_3555_, lean_object* v_lhss_3556_, lean_object* v_lhs_3557_, lean_object* v___x_3558_, lean_object* v_b_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; lean_object* v___f_3566_; lean_object* v___x_3567_; 
v___x_3565_ = lean_box(v_subsingletonInstImplicitRhs_3552_);
lean_inc_ref(v_b_3559_);
v___f_3566_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3566_, 0, v_i_3548_);
lean_closure_set(v___f_3566_, 1, v_rhss_3549_);
lean_closure_set(v___f_3566_, 2, v_b_3559_);
lean_closure_set(v___f_3566_, 3, v_eqs_3550_);
lean_closure_set(v___f_3566_, 4, v_hyps_3551_);
lean_closure_set(v___f_3566_, 5, v___x_3565_);
lean_closure_set(v___f_3566_, 6, v_f_3553_);
lean_closure_set(v___f_3566_, 7, v_info_3554_);
lean_closure_set(v___f_3566_, 8, v_kinds_3555_);
lean_closure_set(v___f_3566_, 9, v_lhss_3556_);
v___x_3567_ = l_Lean_Meta_mkEq(v_lhs_3557_, v_b_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0));
v___x_3570_ = l_Lean_Name_appendBefore(v___x_3558_, v___x_3569_);
v___x_3571_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3570_, v_a_3568_, v___f_3566_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
return v___x_3571_;
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec_ref(v___f_3566_);
lean_dec(v___x_3558_);
v_a_3572_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3567_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3567_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed(lean_object** _args){
lean_object* v_i_3580_ = _args[0];
lean_object* v_rhss_3581_ = _args[1];
lean_object* v_eqs_3582_ = _args[2];
lean_object* v_hyps_3583_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3584_ = _args[4];
lean_object* v_f_3585_ = _args[5];
lean_object* v_info_3586_ = _args[6];
lean_object* v_kinds_3587_ = _args[7];
lean_object* v_lhss_3588_ = _args[8];
lean_object* v_lhs_3589_ = _args[9];
lean_object* v___x_3590_ = _args[10];
lean_object* v_b_3591_ = _args[11];
lean_object* v___y_3592_ = _args[12];
lean_object* v___y_3593_ = _args[13];
lean_object* v___y_3594_ = _args[14];
lean_object* v___y_3595_ = _args[15];
lean_object* v___y_3596_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3597_; lean_object* v_res_3598_; 
v_subsingletonInstImplicitRhs_boxed_3597_ = lean_unbox(v_subsingletonInstImplicitRhs_3584_);
v_res_3598_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(v_i_3580_, v_rhss_3581_, v_eqs_3582_, v_hyps_3583_, v_subsingletonInstImplicitRhs_boxed_3597_, v_f_3585_, v_info_3586_, v_kinds_3587_, v_lhss_3588_, v_lhs_3589_, v___x_3590_, v_b_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3599_, lean_object* v_rhss_3600_, lean_object* v_eqs_3601_, lean_object* v_hyps_3602_, uint8_t v_subsingletonInstImplicitRhs_3603_, lean_object* v_f_3604_, lean_object* v_info_3605_, lean_object* v_kinds_3606_, lean_object* v_lhss_3607_, lean_object* v_lhs_3608_, lean_object* v___x_3609_, lean_object* v_name_3610_, uint8_t v_bi_3611_, lean_object* v_type_3612_, uint8_t v_kind_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; 
v___x_3619_ = lean_box(v_subsingletonInstImplicitRhs_3603_);
v___f_3620_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3620_, 0, v_i_3599_);
lean_closure_set(v___f_3620_, 1, v_rhss_3600_);
lean_closure_set(v___f_3620_, 2, v_eqs_3601_);
lean_closure_set(v___f_3620_, 3, v_hyps_3602_);
lean_closure_set(v___f_3620_, 4, v___x_3619_);
lean_closure_set(v___f_3620_, 5, v_f_3604_);
lean_closure_set(v___f_3620_, 6, v_info_3605_);
lean_closure_set(v___f_3620_, 7, v_kinds_3606_);
lean_closure_set(v___f_3620_, 8, v_lhss_3607_);
lean_closure_set(v___f_3620_, 9, v_lhs_3608_);
lean_closure_set(v___f_3620_, 10, v___x_3609_);
v___x_3621_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3610_, v_bi_3611_, v_type_3612_, v___f_3620_, v_kind_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
v_a_3630_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3621_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3621_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3638_, lean_object* v_rhss_3639_, lean_object* v_lhss_3640_, lean_object* v_i_3641_, lean_object* v_eqs_3642_, lean_object* v_hyps_3643_, uint8_t v_subsingletonInstImplicitRhs_3644_, lean_object* v_f_3645_, lean_object* v_info_3646_, lean_object* v_kinds_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; 
lean_inc(v___y_3651_);
lean_inc_ref(v___y_3650_);
lean_inc(v___y_3649_);
lean_inc_ref(v___y_3648_);
lean_inc_ref(v_lhs_3638_);
v___x_3653_ = lean_infer_type(v_lhs_3638_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___y_3661_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v___x_3655_ = lean_array_get_size(v_rhss_3639_);
v___x_3656_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3640_);
v___x_3657_ = l_Array_toSubarray___redArg(v_lhss_3640_, v___x_3656_, v___x_3655_);
v___x_3658_ = l_Subarray_copy___redArg(v___x_3657_);
v___x_3659_ = l_Lean_Expr_replaceFVars(v_a_3654_, v___x_3658_, v_rhss_3639_);
lean_dec_ref(v___x_3658_);
lean_dec(v_a_3654_);
if (v_subsingletonInstImplicitRhs_3644_ == 0)
{
uint8_t v___x_3676_; 
v___x_3676_ = 1;
v___y_3661_ = v___x_3676_;
goto v___jp_3660_;
}
else
{
uint8_t v___x_3677_; 
v___x_3677_ = 3;
v___y_3661_ = v___x_3677_;
goto v___jp_3660_;
}
v___jp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = l_Lean_Expr_fvarId_x21(v_lhs_3638_);
v___x_3663_ = l_Lean_FVarId_getDecl___redArg(v___x_3662_, v___y_3648_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; lean_object* v___x_3667_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
v___x_3665_ = l_Lean_LocalDecl_userName(v_a_3664_);
lean_dec(v_a_3664_);
v___x_3666_ = 0;
v___x_3667_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3641_, v_rhss_3639_, v_lhs_3638_, v_eqs_3642_, v_hyps_3643_, v_subsingletonInstImplicitRhs_3644_, v_f_3645_, v_info_3646_, v_kinds_3647_, v_lhss_3640_, v___x_3665_, v___y_3661_, v___x_3659_, v___x_3666_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
return v___x_3667_;
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec_ref(v___x_3659_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec_ref(v_kinds_3647_);
lean_dec_ref(v_info_3646_);
lean_dec_ref(v_f_3645_);
lean_dec_ref(v_hyps_3643_);
lean_dec_ref(v_eqs_3642_);
lean_dec(v_i_3641_);
lean_dec_ref(v_lhss_3640_);
lean_dec_ref(v_rhss_3639_);
lean_dec_ref(v_lhs_3638_);
v_a_3668_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3663_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3663_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec_ref(v_kinds_3647_);
lean_dec_ref(v_info_3646_);
lean_dec_ref(v_f_3645_);
lean_dec_ref(v_hyps_3643_);
lean_dec_ref(v_eqs_3642_);
lean_dec(v_i_3641_);
lean_dec_ref(v_lhss_3640_);
lean_dec_ref(v_rhss_3639_);
lean_dec_ref(v_lhs_3638_);
v_a_3678_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3653_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3653_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3686_, lean_object* v_rhss_3687_, lean_object* v_lhss_3688_, lean_object* v_i_3689_, lean_object* v_eqs_3690_, lean_object* v_hyps_3691_, lean_object* v_subsingletonInstImplicitRhs_3692_, lean_object* v_f_3693_, lean_object* v_info_3694_, lean_object* v_kinds_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3701_; lean_object* v_res_3702_; 
v_subsingletonInstImplicitRhs_boxed_3701_ = lean_unbox(v_subsingletonInstImplicitRhs_3692_);
v_res_3702_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3686_, v_rhss_3687_, v_lhss_3688_, v_i_3689_, v_eqs_3690_, v_hyps_3691_, v_subsingletonInstImplicitRhs_boxed_3701_, v_f_3693_, v_info_3694_, v_kinds_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3703_, lean_object* v_f_3704_, lean_object* v_info_3705_, lean_object* v_kinds_3706_, lean_object* v_lhss_3707_, lean_object* v_i_3708_, lean_object* v_rhss_3709_, lean_object* v_eqs_3710_, lean_object* v_hyps_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = lean_array_get_size(v_kinds_3706_);
v___x_3725_ = lean_nat_dec_eq(v_i_3708_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; uint8_t v___x_3727_; lean_object* v_lhs_3728_; lean_object* v_hyps_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; 
v___x_3726_ = l_Lean_instInhabitedExpr;
v___x_3727_ = 0;
v_lhs_3728_ = lean_array_get_borrowed(v___x_3726_, v_lhss_3707_, v_i_3708_);
lean_inc(v_lhs_3728_);
v_hyps_3729_ = lean_array_push(v_hyps_3711_, v_lhs_3728_);
v___x_3730_ = lean_box(v___x_3727_);
v___x_3731_ = lean_array_get(v___x_3730_, v_kinds_3706_, v_i_3708_);
lean_dec(v___x_3730_);
v___x_3732_ = lean_unbox(v___x_3731_);
lean_dec(v___x_3731_);
switch(v___x_3732_)
{
case 0:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3733_ = lean_unsigned_to_nat(1u);
v___x_3734_ = lean_nat_add(v_i_3708_, v___x_3733_);
lean_dec(v_i_3708_);
lean_inc(v_lhs_3728_);
v___x_3735_ = lean_array_push(v_rhss_3709_, v_lhs_3728_);
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_array_push(v_eqs_3710_, v___x_3736_);
v_i_3708_ = v___x_3734_;
v_rhss_3709_ = v___x_3735_;
v_eqs_3710_ = v___x_3737_;
v_hyps_3711_ = v_hyps_3729_;
goto _start;
}
case 2:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_inc(v_lhs_3728_);
v___x_3739_ = l_Lean_Expr_fvarId_x21(v_lhs_3728_);
v___x_3740_ = l_Lean_FVarId_getDecl___redArg(v___x_3739_, v_a_3712_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; lean_object* v___x_3746_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v___x_3742_ = l_Lean_LocalDecl_userName(v_a_3741_);
v___x_3743_ = l_Lean_LocalDecl_binderInfo(v_a_3741_);
v___x_3744_ = l_Lean_LocalDecl_type(v_a_3741_);
lean_dec(v_a_3741_);
v___x_3745_ = 0;
lean_inc(v___x_3742_);
v___x_3746_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3708_, v_rhss_3709_, v_eqs_3710_, v_hyps_3729_, v_subsingletonInstImplicitRhs_3703_, v_f_3704_, v_info_3705_, v_kinds_3706_, v_lhss_3707_, v_lhs_3728_, v___x_3742_, v___x_3742_, v___x_3743_, v___x_3744_, v___x_3745_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
return v___x_3746_;
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec_ref(v_hyps_3729_);
lean_dec(v_lhs_3728_);
lean_dec_ref(v_eqs_3710_);
lean_dec_ref(v_rhss_3709_);
lean_dec(v_i_3708_);
lean_dec_ref(v_lhss_3707_);
lean_dec_ref(v_kinds_3706_);
lean_dec_ref(v_info_3705_);
lean_dec_ref(v_f_3704_);
v_a_3747_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3740_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3740_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
case 3:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = l_Lean_Meta_instInhabitedParamInfo_default;
lean_inc(v_a_3715_);
lean_inc_ref(v_a_3714_);
lean_inc(v_a_3713_);
lean_inc_ref(v_a_3712_);
lean_inc(v_lhs_3728_);
v___x_3756_ = lean_infer_type(v_lhs_3728_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v_paramInfo_3758_; lean_object* v___x_3759_; lean_object* v_backDeps_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3756_, 1);
v_paramInfo_3758_ = lean_ctor_get(v_info_3705_, 0);
v___x_3759_ = lean_array_get_borrowed(v___x_3755_, v_paramInfo_3758_, v_i_3708_);
v_backDeps_3760_ = lean_ctor_get(v___x_3759_, 0);
v___x_3761_ = lean_array_get_size(v_rhss_3709_);
v___x_3762_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3707_);
v___x_3763_ = l_Array_toSubarray___redArg(v_lhss_3707_, v___x_3762_, v___x_3761_);
v___x_3764_ = l_Subarray_copy___redArg(v___x_3763_);
v___x_3765_ = l_Lean_Expr_replaceFVars(v_a_3757_, v___x_3764_, v_rhss_3709_);
lean_dec_ref(v___x_3764_);
lean_dec(v_a_3757_);
v___x_3766_ = l_Lean_Expr_fvarId_x21(v_lhs_3728_);
v___x_3767_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3766_, v___x_3765_, v_backDeps_3760_, v_eqs_3710_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v___x_3769_ = lean_unsigned_to_nat(1u);
v___x_3770_ = lean_nat_add(v_i_3708_, v___x_3769_);
lean_dec(v_i_3708_);
v___x_3771_ = lean_array_push(v_rhss_3709_, v_a_3768_);
v___x_3772_ = lean_box(0);
v___x_3773_ = lean_array_push(v_eqs_3710_, v___x_3772_);
v_i_3708_ = v___x_3770_;
v_rhss_3709_ = v___x_3771_;
v_eqs_3710_ = v___x_3773_;
v_hyps_3711_ = v_hyps_3729_;
goto _start;
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v_hyps_3729_);
lean_dec_ref(v_eqs_3710_);
lean_dec_ref(v_rhss_3709_);
lean_dec(v_i_3708_);
lean_dec_ref(v_lhss_3707_);
lean_dec_ref(v_kinds_3706_);
lean_dec_ref(v_info_3705_);
lean_dec_ref(v_f_3704_);
v_a_3775_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3767_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3767_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec_ref(v_hyps_3729_);
lean_dec_ref(v_eqs_3710_);
lean_dec_ref(v_rhss_3709_);
lean_dec(v_i_3708_);
lean_dec_ref(v_lhss_3707_);
lean_dec_ref(v_kinds_3706_);
lean_dec_ref(v_info_3705_);
lean_dec_ref(v_f_3704_);
v_a_3783_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3756_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3756_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
case 5:
{
lean_object* v___x_3791_; lean_object* v___f_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
lean_inc_n(v_lhs_3728_, 2);
v___x_3791_ = lean_box(v_subsingletonInstImplicitRhs_3703_);
v___f_3792_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3792_, 0, v_lhs_3728_);
lean_closure_set(v___f_3792_, 1, v_rhss_3709_);
lean_closure_set(v___f_3792_, 2, v_lhss_3707_);
lean_closure_set(v___f_3792_, 3, v_i_3708_);
lean_closure_set(v___f_3792_, 4, v_eqs_3710_);
lean_closure_set(v___f_3792_, 5, v_hyps_3729_);
lean_closure_set(v___f_3792_, 6, v___x_3791_);
lean_closure_set(v___f_3792_, 7, v_f_3704_);
lean_closure_set(v___f_3792_, 8, v_info_3705_);
lean_closure_set(v___f_3792_, 9, v_kinds_3706_);
v___x_3793_ = lean_unsigned_to_nat(1u);
v___x_3794_ = lean_mk_empty_array_with_capacity(v___x_3793_);
v___x_3795_ = lean_array_push(v___x_3794_, v_lhs_3728_);
v___x_3796_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v___x_3795_, v___f_3792_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
return v___x_3796_;
}
default: 
{
lean_dec_ref(v_hyps_3729_);
lean_dec_ref(v_eqs_3710_);
lean_dec_ref(v_rhss_3709_);
lean_dec(v_i_3708_);
lean_dec_ref(v_lhss_3707_);
lean_dec_ref(v_kinds_3706_);
lean_dec_ref(v_info_3705_);
lean_dec_ref(v_f_3704_);
v___y_3718_ = v_a_3712_;
v___y_3719_ = v_a_3713_;
v___y_3720_ = v_a_3714_;
v___y_3721_ = v_a_3715_;
goto v___jp_3717_;
}
}
}
else
{
lean_object* v_lhs_3797_; lean_object* v_rhs_3798_; lean_object* v___x_3799_; 
lean_dec_ref(v_eqs_3710_);
lean_dec(v_i_3708_);
lean_dec_ref(v_info_3705_);
lean_inc_ref(v_f_3704_);
v_lhs_3797_ = l_Lean_mkAppN(v_f_3704_, v_lhss_3707_);
lean_dec_ref(v_lhss_3707_);
v_rhs_3798_ = l_Lean_mkAppN(v_f_3704_, v_rhss_3709_);
lean_dec_ref(v_rhss_3709_);
v___x_3799_ = l_Lean_Meta_mkEq(v_lhs_3797_, v_rhs_3798_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; uint8_t v___x_3801_; uint8_t v___x_3802_; lean_object* v___x_3803_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3799_, 1);
v___x_3801_ = 0;
v___x_3802_ = 1;
v___x_3803_ = l_Lean_Meta_mkForallFVars(v_hyps_3711_, v_a_3800_, v___x_3801_, v___x_3725_, v___x_3725_, v___x_3802_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
lean_dec_ref(v_hyps_3711_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc_n(v_a_3804_, 2);
lean_dec_ref_known(v___x_3803_, 1);
lean_inc_ref(v_kinds_3706_);
v___x_3805_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3804_, v_kinds_3706_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3814_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3805_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3810_, 0, v_a_3804_);
lean_ctor_set(v___x_3810_, 1, v_a_3806_);
lean_ctor_set(v___x_3810_, 2, v_kinds_3706_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v___x_3810_);
v___x_3812_ = v___x_3808_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec(v_a_3804_);
lean_dec_ref(v_kinds_3706_);
v_a_3815_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3805_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3805_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v_kinds_3706_);
v_a_3823_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3803_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3803_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref(v_hyps_3711_);
lean_dec_ref(v_kinds_3706_);
v_a_3831_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3799_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3799_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
v___jp_3717_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3723_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v___x_3722_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3839_, lean_object* v_rhss_3840_, lean_object* v_lhs_3841_, lean_object* v_eqs_3842_, lean_object* v_hyps_3843_, uint8_t v_subsingletonInstImplicitRhs_3844_, lean_object* v_f_3845_, lean_object* v_info_3846_, lean_object* v_kinds_3847_, lean_object* v_lhss_3848_, lean_object* v_b_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3855_ = lean_unsigned_to_nat(1u);
v___x_3856_ = lean_nat_add(v_i_3839_, v___x_3855_);
lean_inc_ref(v_b_3849_);
v___x_3857_ = lean_array_push(v_rhss_3840_, v_b_3849_);
v___x_3858_ = l_Lean_Expr_fvarId_x21(v_lhs_3841_);
v___x_3859_ = l_Lean_Expr_fvarId_x21(v_b_3849_);
v___x_3860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3858_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
v___x_3862_ = lean_array_push(v_eqs_3842_, v___x_3861_);
v___x_3863_ = lean_array_push(v_hyps_3843_, v_b_3849_);
v___x_3864_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3844_, v_f_3845_, v_info_3846_, v_kinds_3847_, v_lhss_3848_, v___x_3856_, v___x_3857_, v___x_3862_, v___x_3863_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_3865_, lean_object* v_rhss_3866_, lean_object* v_lhs_3867_, lean_object* v_eqs_3868_, lean_object* v_hyps_3869_, lean_object* v_subsingletonInstImplicitRhs_3870_, lean_object* v_f_3871_, lean_object* v_info_3872_, lean_object* v_kinds_3873_, lean_object* v_lhss_3874_, lean_object* v_b_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3881_; lean_object* v_res_3882_; 
v_subsingletonInstImplicitRhs_boxed_3881_ = lean_unbox(v_subsingletonInstImplicitRhs_3870_);
v_res_3882_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3865_, v_rhss_3866_, v_lhs_3867_, v_eqs_3868_, v_hyps_3869_, v_subsingletonInstImplicitRhs_boxed_3881_, v_f_3871_, v_info_3872_, v_kinds_3873_, v_lhss_3874_, v_b_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec_ref(v_lhs_3867_);
lean_dec(v_i_3865_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_3883_, lean_object* v_rhss_3884_, lean_object* v_lhs_3885_, lean_object* v_eqs_3886_, lean_object* v_hyps_3887_, uint8_t v_subsingletonInstImplicitRhs_3888_, lean_object* v_f_3889_, lean_object* v_info_3890_, lean_object* v_kinds_3891_, lean_object* v_lhss_3892_, lean_object* v_name_3893_, uint8_t v_bi_3894_, lean_object* v_type_3895_, uint8_t v_kind_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; lean_object* v___f_3903_; lean_object* v___x_3904_; 
v___x_3902_ = lean_box(v_subsingletonInstImplicitRhs_3888_);
v___f_3903_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3903_, 0, v_i_3883_);
lean_closure_set(v___f_3903_, 1, v_rhss_3884_);
lean_closure_set(v___f_3903_, 2, v_lhs_3885_);
lean_closure_set(v___f_3903_, 3, v_eqs_3886_);
lean_closure_set(v___f_3903_, 4, v_hyps_3887_);
lean_closure_set(v___f_3903_, 5, v___x_3902_);
lean_closure_set(v___f_3903_, 6, v_f_3889_);
lean_closure_set(v___f_3903_, 7, v_info_3890_);
lean_closure_set(v___f_3903_, 8, v_kinds_3891_);
lean_closure_set(v___f_3903_, 9, v_lhss_3892_);
v___x_3904_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3893_, v_bi_3894_, v_type_3895_, v___f_3903_, v_kind_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
v_a_3913_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3904_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3904_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object** _args){
lean_object* v_i_3921_ = _args[0];
lean_object* v_rhss_3922_ = _args[1];
lean_object* v_lhs_3923_ = _args[2];
lean_object* v_eqs_3924_ = _args[3];
lean_object* v_hyps_3925_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3926_ = _args[5];
lean_object* v_f_3927_ = _args[6];
lean_object* v_info_3928_ = _args[7];
lean_object* v_kinds_3929_ = _args[8];
lean_object* v_lhss_3930_ = _args[9];
lean_object* v_name_3931_ = _args[10];
lean_object* v_bi_3932_ = _args[11];
lean_object* v_type_3933_ = _args[12];
lean_object* v_kind_3934_ = _args[13];
lean_object* v___y_3935_ = _args[14];
lean_object* v___y_3936_ = _args[15];
lean_object* v___y_3937_ = _args[16];
lean_object* v___y_3938_ = _args[17];
lean_object* v___y_3939_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3940_; uint8_t v_bi_boxed_3941_; uint8_t v_kind_boxed_3942_; lean_object* v_res_3943_; 
v_subsingletonInstImplicitRhs_boxed_3940_ = lean_unbox(v_subsingletonInstImplicitRhs_3926_);
v_bi_boxed_3941_ = lean_unbox(v_bi_3932_);
v_kind_boxed_3942_ = lean_unbox(v_kind_3934_);
v_res_3943_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3921_, v_rhss_3922_, v_lhs_3923_, v_eqs_3924_, v_hyps_3925_, v_subsingletonInstImplicitRhs_boxed_3940_, v_f_3927_, v_info_3928_, v_kinds_3929_, v_lhss_3930_, v_name_3931_, v_bi_boxed_3941_, v_type_3933_, v_kind_boxed_3942_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_3944_ = _args[0];
lean_object* v_rhss_3945_ = _args[1];
lean_object* v_eqs_3946_ = _args[2];
lean_object* v_hyps_3947_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3948_ = _args[4];
lean_object* v_f_3949_ = _args[5];
lean_object* v_info_3950_ = _args[6];
lean_object* v_kinds_3951_ = _args[7];
lean_object* v_lhss_3952_ = _args[8];
lean_object* v_lhs_3953_ = _args[9];
lean_object* v___x_3954_ = _args[10];
lean_object* v_name_3955_ = _args[11];
lean_object* v_bi_3956_ = _args[12];
lean_object* v_type_3957_ = _args[13];
lean_object* v_kind_3958_ = _args[14];
lean_object* v___y_3959_ = _args[15];
lean_object* v___y_3960_ = _args[16];
lean_object* v___y_3961_ = _args[17];
lean_object* v___y_3962_ = _args[18];
lean_object* v___y_3963_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3964_; uint8_t v_bi_boxed_3965_; uint8_t v_kind_boxed_3966_; lean_object* v_res_3967_; 
v_subsingletonInstImplicitRhs_boxed_3964_ = lean_unbox(v_subsingletonInstImplicitRhs_3948_);
v_bi_boxed_3965_ = lean_unbox(v_bi_3956_);
v_kind_boxed_3966_ = lean_unbox(v_kind_3958_);
v_res_3967_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3944_, v_rhss_3945_, v_eqs_3946_, v_hyps_3947_, v_subsingletonInstImplicitRhs_boxed_3964_, v_f_3949_, v_info_3950_, v_kinds_3951_, v_lhss_3952_, v_lhs_3953_, v___x_3954_, v_name_3955_, v_bi_boxed_3965_, v_type_3957_, v_kind_boxed_3966_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* v_subsingletonInstImplicitRhs_3968_, lean_object* v_f_3969_, lean_object* v_info_3970_, lean_object* v_kinds_3971_, lean_object* v_lhss_3972_, lean_object* v_i_3973_, lean_object* v_rhss_3974_, lean_object* v_eqs_3975_, lean_object* v_hyps_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3982_; lean_object* v_res_3983_; 
v_subsingletonInstImplicitRhs_boxed_3982_ = lean_unbox(v_subsingletonInstImplicitRhs_3968_);
v_res_3983_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_boxed_3982_, v_f_3969_, v_info_3970_, v_kinds_3971_, v_lhss_3972_, v_i_3973_, v_rhss_3974_, v_eqs_3975_, v_hyps_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* v___x_3984_, uint8_t v_subsingletonInstImplicitRhs_3985_, lean_object* v_f_3986_, lean_object* v_info_3987_, lean_object* v_kinds_3988_, lean_object* v_lhss_3989_, lean_object* v_x_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3996_ = lean_array_get_size(v_lhss_3989_);
v___x_3997_ = lean_nat_dec_eq(v___x_3996_, v___x_3984_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_dec_ref(v_lhss_3989_);
lean_dec_ref(v_kinds_3988_);
lean_dec_ref(v_info_3987_);
lean_dec_ref(v_f_3986_);
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
return v___x_3999_;
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = lean_unsigned_to_nat(0u);
v___x_4001_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_4002_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3985_, v_f_3986_, v_info_3987_, v_kinds_3988_, v_lhss_3989_, v___x_4000_, v___x_4001_, v___x_4001_, v___x_4001_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4011_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4005_ = v___x_4002_;
v_isShared_4006_ = v_isSharedCheck_4011_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_4002_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4011_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4007_, 0, v_a_4003_);
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 0, v___x_4007_);
v___x_4009_ = v___x_4005_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4002_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4002_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* v___x_4020_, lean_object* v_subsingletonInstImplicitRhs_4021_, lean_object* v_f_4022_, lean_object* v_info_4023_, lean_object* v_kinds_4024_, lean_object* v_lhss_4025_, lean_object* v_x_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4032_; lean_object* v_res_4033_; 
v_subsingletonInstImplicitRhs_boxed_4032_ = lean_unbox(v_subsingletonInstImplicitRhs_4021_);
v_res_4033_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4020_, v_subsingletonInstImplicitRhs_boxed_4032_, v_f_4022_, v_info_4023_, v_kinds_4024_, v_lhss_4025_, v_x_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec_ref(v_x_4026_);
lean_dec(v___x_4020_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t v_subsingletonInstImplicitRhs_4034_, lean_object* v_f_4035_, lean_object* v_info_4036_, lean_object* v_kinds_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v___y_4044_; uint8_t v___y_4045_; lean_object* v_a_4050_; lean_object* v___x_4053_; 
lean_inc(v_a_4041_);
lean_inc_ref(v_a_4040_);
lean_inc(v_a_4039_);
lean_inc_ref(v_a_4038_);
lean_inc_ref(v_f_4035_);
v___x_4053_ = lean_infer_type(v_f_4035_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4068_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4068_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4068_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___f_4060_; lean_object* v___x_4062_; 
v___x_4058_ = lean_array_get_size(v_kinds_4037_);
v___x_4059_ = lean_box(v_subsingletonInstImplicitRhs_4034_);
v___f_4060_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4060_, 0, v___x_4058_);
lean_closure_set(v___f_4060_, 1, v___x_4059_);
lean_closure_set(v___f_4060_, 2, v_f_4035_);
lean_closure_set(v___f_4060_, 3, v_info_4036_);
lean_closure_set(v___f_4060_, 4, v_kinds_4037_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set_tag(v___x_4056_, 1);
lean_ctor_set(v___x_4056_, 0, v___x_4058_);
v___x_4062_ = v___x_4056_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4058_);
v___x_4062_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
uint8_t v___x_4063_; uint8_t v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = 1;
v___x_4064_ = 0;
v___x_4065_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_4054_, v___x_4062_, v___f_4060_, v___x_4063_, v___x_4064_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_);
if (lean_obj_tag(v___x_4065_) == 0)
{
return v___x_4065_;
}
else
{
lean_object* v_a_4066_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc(v_a_4066_);
lean_dec_ref_known(v___x_4065_, 1);
v_a_4050_ = v_a_4066_;
goto v___jp_4049_;
}
}
}
}
else
{
lean_object* v_a_4069_; 
lean_dec_ref(v_kinds_4037_);
lean_dec_ref(v_info_4036_);
lean_dec_ref(v_f_4035_);
v_a_4069_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4053_, 1);
v_a_4050_ = v_a_4069_;
goto v___jp_4049_;
}
v___jp_4043_:
{
if (v___y_4045_ == 0)
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec_ref(v___y_4044_);
v___x_4046_ = lean_box(0);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
else
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___y_4044_);
return v___x_4048_;
}
}
v___jp_4049_:
{
uint8_t v___x_4051_; 
v___x_4051_ = l_Lean_Exception_isInterrupt(v_a_4050_);
if (v___x_4051_ == 0)
{
uint8_t v___x_4052_; 
lean_inc_ref(v_a_4050_);
v___x_4052_ = l_Lean_Exception_isRuntime(v_a_4050_);
v___y_4044_ = v_a_4050_;
v___y_4045_ = v___x_4052_;
goto v___jp_4043_;
}
else
{
v___y_4044_ = v_a_4050_;
v___y_4045_ = v___x_4051_;
goto v___jp_4043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* v_subsingletonInstImplicitRhs_4070_, lean_object* v_f_4071_, lean_object* v_info_4072_, lean_object* v_kinds_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4079_; lean_object* v_res_4080_; 
v_subsingletonInstImplicitRhs_boxed_4079_ = lean_unbox(v_subsingletonInstImplicitRhs_4070_);
v_res_4080_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_boxed_4079_, v_f_4071_, v_info_4072_, v_kinds_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t v_sz_4081_, size_t v_i_4082_, lean_object* v_bs_4083_){
_start:
{
uint8_t v___x_4084_; 
v___x_4084_ = lean_usize_dec_lt(v_i_4082_, v_sz_4081_);
if (v___x_4084_ == 0)
{
return v_bs_4083_;
}
else
{
lean_object* v_v_4085_; lean_object* v___x_4086_; lean_object* v_bs_x27_4087_; uint8_t v___y_4089_; uint8_t v___x_4095_; 
v_v_4085_ = lean_array_uget(v_bs_4083_, v_i_4082_);
v___x_4086_ = lean_unsigned_to_nat(0u);
v_bs_x27_4087_ = lean_array_uset(v_bs_4083_, v_i_4082_, v___x_4086_);
v___x_4095_ = lean_unbox(v_v_4085_);
switch(v___x_4095_)
{
case 3:
{
uint8_t v___x_4096_; 
lean_dec(v_v_4085_);
v___x_4096_ = 0;
v___y_4089_ = v___x_4096_;
goto v___jp_4088_;
}
case 5:
{
uint8_t v___x_4097_; 
lean_dec(v_v_4085_);
v___x_4097_ = 0;
v___y_4089_ = v___x_4097_;
goto v___jp_4088_;
}
default: 
{
uint8_t v___x_4098_; 
v___x_4098_ = lean_unbox(v_v_4085_);
lean_dec(v_v_4085_);
v___y_4089_ = v___x_4098_;
goto v___jp_4088_;
}
}
v___jp_4088_:
{
size_t v___x_4090_; size_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4090_ = ((size_t)1ULL);
v___x_4091_ = lean_usize_add(v_i_4082_, v___x_4090_);
v___x_4092_ = lean_box(v___y_4089_);
v___x_4093_ = lean_array_uset(v_bs_x27_4087_, v_i_4082_, v___x_4092_);
v_i_4082_ = v___x_4091_;
v_bs_4083_ = v___x_4093_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* v_sz_4099_, lean_object* v_i_4100_, lean_object* v_bs_4101_){
_start:
{
size_t v_sz_boxed_4102_; size_t v_i_boxed_4103_; lean_object* v_res_4104_; 
v_sz_boxed_4102_ = lean_unbox_usize(v_sz_4099_);
lean_dec(v_sz_4099_);
v_i_boxed_4103_ = lean_unbox_usize(v_i_4100_);
lean_dec(v_i_4100_);
v_res_4104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_4102_, v_i_boxed_4103_, v_bs_4101_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* v_f_4105_, lean_object* v_info_4106_, lean_object* v_kinds_4107_, uint8_t v_subsingletonInstImplicitRhs_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v___x_4114_; 
lean_inc_ref(v_kinds_4107_);
lean_inc_ref(v_info_4106_);
lean_inc_ref(v_f_4105_);
v___x_4114_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4108_, v_f_4105_, v_info_4106_, v_kinds_4107_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; 
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
if (lean_obj_tag(v_a_4115_) == 1)
{
lean_dec_ref(v_kinds_4107_);
lean_dec_ref(v_info_4106_);
lean_dec_ref(v_f_4105_);
return v___x_4114_;
}
else
{
lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4128_; 
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; 
v_unused_4129_ = lean_ctor_get(v___x_4114_, 0);
lean_dec(v_unused_4129_);
v___x_4117_ = v___x_4114_;
v_isShared_4118_ = v_isSharedCheck_4128_;
goto v_resetjp_4116_;
}
else
{
lean_dec(v___x_4114_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4128_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
uint8_t v___x_4119_; 
v___x_4119_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_4107_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
lean_dec_ref(v_kinds_4107_);
lean_dec_ref(v_info_4106_);
lean_dec_ref(v_f_4105_);
v___x_4120_ = lean_box(0);
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 0, v___x_4120_);
v___x_4122_ = v___x_4117_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
else
{
size_t v_sz_4124_; size_t v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_del_object(v___x_4117_);
v_sz_4124_ = lean_array_size(v_kinds_4107_);
v___x_4125_ = ((size_t)0ULL);
v___x_4126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4124_, v___x_4125_, v_kinds_4107_);
v___x_4127_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4108_, v_f_4105_, v_info_4106_, v___x_4126_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_);
return v___x_4127_;
}
}
}
}
else
{
lean_dec_ref(v_kinds_4107_);
lean_dec_ref(v_info_4106_);
lean_dec_ref(v_f_4105_);
return v___x_4114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* v_f_4130_, lean_object* v_info_4131_, lean_object* v_kinds_4132_, lean_object* v_subsingletonInstImplicitRhs_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4139_; lean_object* v_res_4140_; 
v_subsingletonInstImplicitRhs_boxed_4139_ = lean_unbox(v_subsingletonInstImplicitRhs_4133_);
v_res_4140_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4130_, v_info_4131_, v_kinds_4132_, v_subsingletonInstImplicitRhs_boxed_4139_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* v_f_4141_, uint8_t v_subsingletonInstImplicitRhs_4142_, lean_object* v_maxArgs_x3f_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v___x_4149_; lean_object* v_a_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4149_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_4141_, v_a_4145_);
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref(v___x_4149_);
v___x_4151_ = l_Lean_Expr_cleanupAnnotations(v_a_4150_);
lean_inc_ref(v___x_4151_);
v___x_4152_ = l_Lean_Meta_getFunInfo(v___x_4151_, v_maxArgs_x3f_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
lean_inc_ref(v___x_4151_);
v___x_4154_ = l_Lean_Meta_getCongrSimpKinds(v___x_4151_, v_a_4153_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___x_4156_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4151_, v_a_4153_, v_a_4155_, v_subsingletonInstImplicitRhs_4142_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
return v___x_4156_;
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec(v_a_4153_);
lean_dec_ref(v___x_4151_);
v_a_4157_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4154_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4154_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec_ref(v___x_4151_);
v_a_4165_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4152_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4152_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* v_f_4173_, lean_object* v_subsingletonInstImplicitRhs_4174_, lean_object* v_maxArgs_x3f_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4181_; lean_object* v_res_4182_; 
v_subsingletonInstImplicitRhs_boxed_4181_ = lean_unbox(v_subsingletonInstImplicitRhs_4174_);
v_res_4182_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4173_, v_subsingletonInstImplicitRhs_boxed_4181_, v_maxArgs_x3f_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
return v_res_4182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4187_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4188_ = lean_string_utf8_byte_size(v_s_4187_);
v___x_4189_ = lean_unsigned_to_nat(7u);
v___x_4190_ = lean_nat_dec_le(v___x_4189_, v___x_4188_);
if (v___x_4190_ == 0)
{
lean_dec_ref(v_s_4187_);
return v___x_4190_;
}
else
{
lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4191_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4192_ = lean_unsigned_to_nat(0u);
v___x_4193_ = lean_string_memcmp(v_s_4187_, v___x_4191_, v___x_4192_, v___x_4192_, v___x_4189_);
if (v___x_4193_ == 0)
{
lean_dec_ref(v_s_4187_);
return v___x_4193_;
}
else
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
lean_inc_ref(v_s_4187_);
v___x_4194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4194_, 0, v_s_4187_);
lean_ctor_set(v___x_4194_, 1, v___x_4192_);
lean_ctor_set(v___x_4194_, 2, v___x_4188_);
v___x_4195_ = l_String_Slice_Pos_nextn(v___x_4194_, v___x_4192_, v___x_4189_);
lean_dec_ref_known(v___x_4194_, 3);
v___x_4196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4196_, 0, v_s_4187_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
lean_ctor_set(v___x_4196_, 2, v___x_4188_);
v___x_4197_ = l_String_Slice_isNat(v___x_4196_);
lean_dec_ref_known(v___x_4196_, 3);
return v___x_4197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* v_s_4198_){
_start:
{
uint8_t v_res_4199_; lean_object* v_r_4200_; 
v_res_4199_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4198_);
v_r_4200_ = lean_box(v_res_4199_);
return v_r_4200_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4250_ = lean_unsigned_to_nat(3482611248u);
v___x_4251_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4252_ = l_Lean_Name_num___override(v___x_4251_, v___x_4250_);
return v___x_4252_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4255_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4256_ = l_Lean_Name_str___override(v___x_4255_, v___x_4254_);
return v___x_4256_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4258_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4259_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4260_ = l_Lean_Name_str___override(v___x_4259_, v___x_4258_);
return v___x_4260_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4261_ = lean_unsigned_to_nat(2u);
v___x_4262_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4263_ = l_Lean_Name_num___override(v___x_4262_, v___x_4261_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4265_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4266_ = 0;
v___x_4267_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4268_ = l_Lean_registerTraceClass(v___x_4265_, v___x_4266_, v___x_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4271_, lean_object* v_as_4272_, size_t v_i_4273_, size_t v_stop_4274_, lean_object* v_b_4275_){
_start:
{
lean_object* v___y_4277_; uint8_t v___x_4281_; 
v___x_4281_ = lean_usize_dec_eq(v_i_4273_, v_stop_4274_);
if (v___x_4281_ == 0)
{
lean_object* v___x_4282_; lean_object* v_fst_4283_; uint8_t v___x_4284_; 
v___x_4282_ = lean_array_uget_borrowed(v_as_4272_, v_i_4273_);
v_fst_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_fst_4283_);
lean_inc_ref(v_env_4271_);
v___x_4284_ = l_Lean_Environment_contains(v_env_4271_, v_fst_4283_, v___x_4281_);
if (v___x_4284_ == 0)
{
v___y_4277_ = v_b_4275_;
goto v___jp_4276_;
}
else
{
lean_object* v___x_4285_; 
lean_inc(v___x_4282_);
v___x_4285_ = lean_array_push(v_b_4275_, v___x_4282_);
v___y_4277_ = v___x_4285_;
goto v___jp_4276_;
}
}
else
{
lean_dec_ref(v_env_4271_);
return v_b_4275_;
}
v___jp_4276_:
{
size_t v___x_4278_; size_t v___x_4279_; 
v___x_4278_ = ((size_t)1ULL);
v___x_4279_ = lean_usize_add(v_i_4273_, v___x_4278_);
v_i_4273_ = v___x_4279_;
v_b_4275_ = v___y_4277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4286_, lean_object* v_as_4287_, lean_object* v_i_4288_, lean_object* v_stop_4289_, lean_object* v_b_4290_){
_start:
{
size_t v_i_boxed_4291_; size_t v_stop_boxed_4292_; lean_object* v_res_4293_; 
v_i_boxed_4291_ = lean_unbox_usize(v_i_4288_);
lean_dec(v_i_4288_);
v_stop_boxed_4292_ = lean_unbox_usize(v_stop_4289_);
lean_dec(v_stop_4289_);
v_res_4293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4286_, v_as_4287_, v_i_boxed_4291_, v_stop_boxed_4292_, v_b_4290_);
lean_dec_ref(v_as_4287_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4294_, lean_object* v_x_4295_){
_start:
{
if (lean_obj_tag(v_x_4295_) == 0)
{
lean_object* v_k_4296_; lean_object* v_v_4297_; lean_object* v_l_4298_; lean_object* v_r_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_k_4296_ = lean_ctor_get(v_x_4295_, 1);
v_v_4297_ = lean_ctor_get(v_x_4295_, 2);
v_l_4298_ = lean_ctor_get(v_x_4295_, 3);
v_r_4299_ = lean_ctor_get(v_x_4295_, 4);
v___x_4300_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4294_, v_l_4298_);
lean_inc(v_v_4297_);
lean_inc(v_k_4296_);
v___x_4301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4301_, 0, v_k_4296_);
lean_ctor_set(v___x_4301_, 1, v_v_4297_);
v___x_4302_ = lean_array_push(v___x_4300_, v___x_4301_);
v_init_4294_ = v___x_4302_;
v_x_4295_ = v_r_4299_;
goto _start;
}
else
{
return v_init_4294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4304_, lean_object* v_x_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4304_, v_x_4305_);
lean_dec(v_x_4305_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4313_, lean_object* v_s_4314_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v___x_4315_ = lean_unsigned_to_nat(0u);
v___x_4316_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4317_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4316_, v_s_4314_);
v___x_4318_ = lean_array_get_size(v___x_4317_);
v___x_4319_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4320_ = lean_nat_dec_lt(v___x_4315_, v___x_4318_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; 
lean_dec_ref(v___x_4317_);
lean_dec_ref(v_env_4313_);
v___x_4321_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4321_;
}
else
{
uint8_t v___x_4322_; 
v___x_4322_ = lean_nat_dec_le(v___x_4318_, v___x_4318_);
if (v___x_4322_ == 0)
{
if (v___x_4320_ == 0)
{
lean_object* v___x_4323_; 
lean_dec_ref(v___x_4317_);
lean_dec_ref(v_env_4313_);
v___x_4323_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4323_;
}
else
{
size_t v___x_4324_; size_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4324_ = ((size_t)0ULL);
v___x_4325_ = lean_usize_of_nat(v___x_4318_);
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4313_, v___x_4317_, v___x_4324_, v___x_4325_, v___x_4319_);
lean_dec_ref(v___x_4317_);
lean_inc_ref_n(v___x_4326_, 2);
v___x_4327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
lean_ctor_set(v___x_4327_, 2, v___x_4326_);
return v___x_4327_;
}
}
else
{
size_t v___x_4328_; size_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4328_ = ((size_t)0ULL);
v___x_4329_ = lean_usize_of_nat(v___x_4318_);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4313_, v___x_4317_, v___x_4328_, v___x_4329_, v___x_4319_);
lean_dec_ref(v___x_4317_);
lean_inc_ref_n(v___x_4330_, 2);
v___x_4331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
lean_ctor_set(v___x_4331_, 2, v___x_4330_);
return v___x_4331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4332_, lean_object* v_s_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4332_, v_s_4333_);
lean_dec(v_s_4333_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; lean_object* v___x_4348_; 
v___f_4344_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4345_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4346_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4347_ = 0;
v___x_4348_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4345_, v___x_4346_, v___x_4347_, v___f_4344_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4351_, lean_object* v_t_4352_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4351_, v_t_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4354_, lean_object* v_t_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4354_, v_t_4355_);
lean_dec(v_t_4355_);
return v_res_4356_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object* v_env_4357_, lean_object* v_n_4358_){
_start:
{
if (lean_obj_tag(v_n_4358_) == 1)
{
lean_object* v_pre_4359_; lean_object* v_str_4360_; uint8_t v___y_4362_; uint8_t v___x_4364_; 
v_pre_4359_ = lean_ctor_get(v_n_4358_, 0);
lean_inc(v_pre_4359_);
v_str_4360_ = lean_ctor_get(v_n_4358_, 1);
lean_inc_ref_n(v_str_4360_, 2);
lean_dec_ref_known(v_n_4358_, 2);
v___x_4364_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4360_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; uint8_t v___x_4366_; 
v___x_4365_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4366_ = lean_string_dec_eq(v_str_4360_, v___x_4365_);
lean_dec_ref(v_str_4360_);
v___y_4362_ = v___x_4366_;
goto v___jp_4361_;
}
else
{
lean_dec_ref(v_str_4360_);
v___y_4362_ = v___x_4364_;
goto v___jp_4361_;
}
v___jp_4361_:
{
if (v___y_4362_ == 0)
{
lean_dec(v_pre_4359_);
lean_dec_ref(v_env_4357_);
return v___y_4362_;
}
else
{
uint8_t v___x_4363_; 
v___x_4363_ = l_Lean_Environment_contains(v_env_4357_, v_pre_4359_, v___y_4362_);
return v___x_4363_;
}
}
}
else
{
uint8_t v___x_4367_; 
lean_dec(v_n_4358_);
lean_dec_ref(v_env_4357_);
v___x_4367_ = 0;
return v___x_4367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_env_4368_, lean_object* v_n_4369_){
_start:
{
uint8_t v_res_4370_; lean_object* v_r_4371_; 
v_res_4370_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4368_, v_n_4369_);
v_r_4371_ = lean_box(v_res_4370_);
return v_r_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4374_; lean_object* v___x_4375_; 
v___f_4374_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_));
v___x_4375_ = l_Lean_registerReservedNamePredicate(v___f_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_a_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object* v_thm_4378_, lean_object* v___y_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v_env_4382_; lean_object* v_toConstantVal_4383_; lean_object* v_value_4384_; lean_object* v_all_4385_; uint8_t v___y_4387_; lean_object* v_type_4395_; uint8_t v___x_4396_; 
v___x_4381_ = lean_st_ref_get(v___y_4379_);
v_env_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc_ref_n(v_env_4382_, 2);
lean_dec(v___x_4381_);
v_toConstantVal_4383_ = lean_ctor_get(v_thm_4378_, 0);
v_value_4384_ = lean_ctor_get(v_thm_4378_, 1);
v_all_4385_ = lean_ctor_get(v_thm_4378_, 2);
v_type_4395_ = lean_ctor_get(v_toConstantVal_4383_, 2);
v___x_4396_ = l_Lean_Environment_hasUnsafe(v_env_4382_, v_type_4395_);
if (v___x_4396_ == 0)
{
uint8_t v___x_4397_; 
v___x_4397_ = l_Lean_Environment_hasUnsafe(v_env_4382_, v_value_4384_);
v___y_4387_ = v___x_4397_;
goto v___jp_4386_;
}
else
{
lean_dec_ref(v_env_4382_);
v___y_4387_ = v___x_4396_;
goto v___jp_4386_;
}
v___jp_4386_:
{
if (v___y_4387_ == 0)
{
lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4388_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4388_, 0, v_thm_4378_);
v___x_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
return v___x_4389_;
}
else
{
lean_object* v___x_4390_; uint8_t v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
lean_inc(v_all_4385_);
lean_inc_ref(v_value_4384_);
lean_inc_ref(v_toConstantVal_4383_);
lean_dec_ref(v_thm_4378_);
v___x_4390_ = lean_box(0);
v___x_4391_ = 0;
v___x_4392_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4392_, 0, v_toConstantVal_4383_);
lean_ctor_set(v___x_4392_, 1, v_value_4384_);
lean_ctor_set(v___x_4392_, 2, v___x_4390_);
lean_ctor_set(v___x_4392_, 3, v_all_4385_);
lean_ctor_set_uint8(v___x_4392_, sizeof(void*)*4, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
v___x_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
return v___x_4394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_thm_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4398_, v___y_4399_);
lean_dec(v___y_4399_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_thm_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4402_, v___y_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object* v_thm_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
return v_res_4415_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_4416_; double v___x_4417_; 
v___x_4416_ = lean_unsigned_to_nat(0u);
v___x_4417_ = lean_float_of_nat(v___x_4416_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_cls_4421_, lean_object* v_msg_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v_ref_4428_; lean_object* v___x_4429_; lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4475_; 
v_ref_4428_ = lean_ctor_get(v___y_4425_, 2);
v___x_4429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4432_ = v___x_4429_;
v_isShared_4433_ = v_isSharedCheck_4475_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4475_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4434_; lean_object* v_traceState_4435_; lean_object* v_env_4436_; lean_object* v_nextMacroScope_4437_; lean_object* v_ngen_4438_; lean_object* v_auxDeclNGen_4439_; lean_object* v_cache_4440_; lean_object* v_recordedDeps_4441_; lean_object* v_messages_4442_; lean_object* v_infoState_4443_; lean_object* v_snapshotTasks_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4474_; 
v___x_4434_ = lean_st_ref_take(v___y_4426_);
v_traceState_4435_ = lean_ctor_get(v___x_4434_, 4);
v_env_4436_ = lean_ctor_get(v___x_4434_, 0);
v_nextMacroScope_4437_ = lean_ctor_get(v___x_4434_, 1);
v_ngen_4438_ = lean_ctor_get(v___x_4434_, 2);
v_auxDeclNGen_4439_ = lean_ctor_get(v___x_4434_, 3);
v_cache_4440_ = lean_ctor_get(v___x_4434_, 5);
v_recordedDeps_4441_ = lean_ctor_get(v___x_4434_, 6);
v_messages_4442_ = lean_ctor_get(v___x_4434_, 7);
v_infoState_4443_ = lean_ctor_get(v___x_4434_, 8);
v_snapshotTasks_4444_ = lean_ctor_get(v___x_4434_, 9);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4446_ = v___x_4434_;
v_isShared_4447_ = v_isSharedCheck_4474_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_snapshotTasks_4444_);
lean_inc(v_infoState_4443_);
lean_inc(v_messages_4442_);
lean_inc(v_recordedDeps_4441_);
lean_inc(v_cache_4440_);
lean_inc(v_traceState_4435_);
lean_inc(v_auxDeclNGen_4439_);
lean_inc(v_ngen_4438_);
lean_inc(v_nextMacroScope_4437_);
lean_inc(v_env_4436_);
lean_dec(v___x_4434_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4474_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
uint64_t v_tid_4448_; lean_object* v_traces_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4473_; 
v_tid_4448_ = lean_ctor_get_uint64(v_traceState_4435_, sizeof(void*)*1);
v_traces_4449_ = lean_ctor_get(v_traceState_4435_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_traceState_4435_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4451_ = v_traceState_4435_;
v_isShared_4452_ = v_isSharedCheck_4473_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_traces_4449_);
lean_dec(v_traceState_4435_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4473_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; double v___x_4455_; uint8_t v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4453_ = lean_box(0);
v___x_4454_ = lean_box(0);
v___x_4455_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0);
v___x_4456_ = 0;
v___x_4457_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1));
v___x_4458_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4458_, 0, v_cls_4421_);
lean_ctor_set(v___x_4458_, 1, v___x_4454_);
lean_ctor_set(v___x_4458_, 2, v___x_4457_);
lean_ctor_set_float(v___x_4458_, sizeof(void*)*3, v___x_4455_);
lean_ctor_set_float(v___x_4458_, sizeof(void*)*3 + 8, v___x_4455_);
lean_ctor_set_uint8(v___x_4458_, sizeof(void*)*3 + 16, v___x_4456_);
v___x_4459_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2));
v___x_4460_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4458_);
lean_ctor_set(v___x_4460_, 1, v_a_4430_);
lean_ctor_set(v___x_4460_, 2, v___x_4459_);
lean_inc(v_ref_4428_);
v___x_4461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4461_, 0, v_ref_4428_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v___x_4462_ = l_Lean_PersistentArray_push___redArg(v_traces_4449_, v___x_4461_);
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 0, v___x_4462_);
v___x_4464_ = v___x_4451_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4462_);
lean_ctor_set_uint64(v_reuseFailAlloc_4472_, sizeof(void*)*1, v_tid_4448_);
v___x_4464_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
lean_object* v___x_4466_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 4, v___x_4464_);
v___x_4466_ = v___x_4446_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_env_4436_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_nextMacroScope_4437_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_ngen_4438_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v_auxDeclNGen_4439_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4471_, 5, v_cache_4440_);
lean_ctor_set(v_reuseFailAlloc_4471_, 6, v_recordedDeps_4441_);
lean_ctor_set(v_reuseFailAlloc_4471_, 7, v_messages_4442_);
lean_ctor_set(v_reuseFailAlloc_4471_, 8, v_infoState_4443_);
lean_ctor_set(v_reuseFailAlloc_4471_, 9, v_snapshotTasks_4444_);
v___x_4466_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4467_ = lean_st_ref_put(v___y_4426_, v___x_4466_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4453_);
v___x_4469_ = v___x_4432_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4453_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_4476_, lean_object* v_msg_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4476_, v_msg_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
return v_res_4483_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
return v___x_4485_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
lean_ctor_set(v___x_4487_, 1, v___x_4486_);
return v___x_4487_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4492_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4493_ = l_Lean_Name_append(v___x_4492_, v___x_4491_);
return v___x_4493_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4496_ = l_Lean_stringToMessageData(v___x_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v_name_4497_, lean_object* v_argKinds_4498_, uint8_t v___x_4499_, lean_object* v___x_4500_, lean_object* v___x_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v___x_4546_; lean_object* v_a_4547_; lean_object* v___x_4548_; 
v___x_4546_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_4501_, v___y_4505_);
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_a_4547_);
lean_dec_ref(v___x_4546_);
v___x_4548_ = l_Lean_addDecl(v_a_4547_, v___x_4499_, v___y_4504_, v___y_4505_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_toCold_4549_; lean_object* v_options_4550_; uint8_t v_hasTrace_4551_; 
lean_dec_ref_known(v___x_4548_, 1);
v_toCold_4549_ = lean_ctor_get(v___y_4504_, 0);
v_options_4550_ = lean_ctor_get(v_toCold_4549_, 2);
v_hasTrace_4551_ = lean_ctor_get_uint8(v_options_4550_, sizeof(void*)*1);
if (v_hasTrace_4551_ == 0)
{
goto v___jp_4507_;
}
else
{
lean_object* v_inheritedTraceOptions_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; uint8_t v___x_4555_; 
v_inheritedTraceOptions_4552_ = lean_ctor_get(v_toCold_4549_, 11);
v___x_4553_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4554_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4555_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4552_, v_options_4550_, v___x_4554_);
if (v___x_4555_ == 0)
{
goto v___jp_4507_;
}
else
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4556_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4497_);
v___x_4557_ = l_Lean_MessageData_ofName(v_name_4497_);
v___x_4558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4556_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_4553_, v___x_4560_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_dec_ref_known(v___x_4561_, 1);
goto v___jp_4507_;
}
else
{
lean_dec_ref(v___x_4500_);
lean_dec_ref(v_argKinds_4498_);
lean_dec(v_name_4497_);
return v___x_4561_;
}
}
}
}
else
{
lean_dec_ref(v___x_4500_);
lean_dec_ref(v_argKinds_4498_);
lean_dec(v_name_4497_);
return v___x_4548_;
}
v___jp_4507_:
{
lean_object* v___x_4508_; lean_object* v_env_4509_; lean_object* v_nextMacroScope_4510_; lean_object* v_ngen_4511_; lean_object* v_auxDeclNGen_4512_; lean_object* v_traceState_4513_; lean_object* v_recordedDeps_4514_; lean_object* v_messages_4515_; lean_object* v_infoState_4516_; lean_object* v_snapshotTasks_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4544_; 
v___x_4508_ = lean_st_ref_take(v___y_4505_);
v_env_4509_ = lean_ctor_get(v___x_4508_, 0);
v_nextMacroScope_4510_ = lean_ctor_get(v___x_4508_, 1);
v_ngen_4511_ = lean_ctor_get(v___x_4508_, 2);
v_auxDeclNGen_4512_ = lean_ctor_get(v___x_4508_, 3);
v_traceState_4513_ = lean_ctor_get(v___x_4508_, 4);
v_recordedDeps_4514_ = lean_ctor_get(v___x_4508_, 6);
v_messages_4515_ = lean_ctor_get(v___x_4508_, 7);
v_infoState_4516_ = lean_ctor_get(v___x_4508_, 8);
v_snapshotTasks_4517_ = lean_ctor_get(v___x_4508_, 9);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4544_ == 0)
{
lean_object* v_unused_4545_; 
v_unused_4545_ = lean_ctor_get(v___x_4508_, 5);
lean_dec(v_unused_4545_);
v___x_4519_ = v___x_4508_;
v_isShared_4520_ = v_isSharedCheck_4544_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_snapshotTasks_4517_);
lean_inc(v_infoState_4516_);
lean_inc(v_messages_4515_);
lean_inc(v_recordedDeps_4514_);
lean_inc(v_traceState_4513_);
lean_inc(v_auxDeclNGen_4512_);
lean_inc(v_ngen_4511_);
lean_inc(v_nextMacroScope_4510_);
lean_inc(v_env_4509_);
lean_dec(v___x_4508_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4544_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4525_; 
v___x_4521_ = l_Lean_Meta_congrKindsExt;
v___x_4522_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4521_, v_env_4509_, v_name_4497_, v_argKinds_4498_, v___x_4499_);
v___x_4523_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 5, v___x_4523_);
lean_ctor_set(v___x_4519_, 0, v___x_4522_);
v___x_4525_ = v___x_4519_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_nextMacroScope_4510_);
lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_ngen_4511_);
lean_ctor_set(v_reuseFailAlloc_4543_, 3, v_auxDeclNGen_4512_);
lean_ctor_set(v_reuseFailAlloc_4543_, 4, v_traceState_4513_);
lean_ctor_set(v_reuseFailAlloc_4543_, 5, v___x_4523_);
lean_ctor_set(v_reuseFailAlloc_4543_, 6, v_recordedDeps_4514_);
lean_ctor_set(v_reuseFailAlloc_4543_, 7, v_messages_4515_);
lean_ctor_set(v_reuseFailAlloc_4543_, 8, v_infoState_4516_);
lean_ctor_set(v_reuseFailAlloc_4543_, 9, v_snapshotTasks_4517_);
v___x_4525_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v_mctx_4528_; lean_object* v_zetaDeltaFVarIds_4529_; lean_object* v_postponed_4530_; lean_object* v_diag_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4541_; 
v___x_4526_ = lean_st_ref_put(v___y_4505_, v___x_4525_);
v___x_4527_ = lean_st_ref_take(v___y_4503_);
v_mctx_4528_ = lean_ctor_get(v___x_4527_, 0);
v_zetaDeltaFVarIds_4529_ = lean_ctor_get(v___x_4527_, 2);
v_postponed_4530_ = lean_ctor_get(v___x_4527_, 3);
v_diag_4531_ = lean_ctor_get(v___x_4527_, 4);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4541_ == 0)
{
lean_object* v_unused_4542_; 
v_unused_4542_ = lean_ctor_get(v___x_4527_, 1);
lean_dec(v_unused_4542_);
v___x_4533_ = v___x_4527_;
v_isShared_4534_ = v_isSharedCheck_4541_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_diag_4531_);
lean_inc(v_postponed_4530_);
lean_inc(v_zetaDeltaFVarIds_4529_);
lean_inc(v_mctx_4528_);
lean_dec(v___x_4527_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4541_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4535_; lean_object* v___x_4537_; 
v___x_4535_ = lean_box(0);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 1, v___x_4500_);
v___x_4537_ = v___x_4533_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_mctx_4528_);
lean_ctor_set(v_reuseFailAlloc_4540_, 1, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4540_, 2, v_zetaDeltaFVarIds_4529_);
lean_ctor_set(v_reuseFailAlloc_4540_, 3, v_postponed_4530_);
lean_ctor_set(v_reuseFailAlloc_4540_, 4, v_diag_4531_);
v___x_4537_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = lean_st_ref_put(v___y_4503_, v___x_4537_);
v___x_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4535_);
return v___x_4539_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_name_4562_, lean_object* v_argKinds_4563_, lean_object* v___x_4564_, lean_object* v___x_4565_, lean_object* v___x_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
uint8_t v___x_11999__boxed_4572_; lean_object* v_res_4573_; 
v___x_11999__boxed_4572_ = lean_unbox(v___x_4564_);
v_res_4573_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_4562_, v_argKinds_4563_, v___x_11999__boxed_4572_, v___x_4565_, v___x_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_a_4574_, lean_object* v_a_4575_){
_start:
{
if (lean_obj_tag(v_a_4574_) == 0)
{
lean_object* v___x_4576_; 
v___x_4576_ = l_List_reverse___redArg(v_a_4575_);
return v___x_4576_;
}
else
{
lean_object* v_head_4577_; lean_object* v_tail_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4587_; 
v_head_4577_ = lean_ctor_get(v_a_4574_, 0);
v_tail_4578_ = lean_ctor_get(v_a_4574_, 1);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_a_4574_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4580_ = v_a_4574_;
v_isShared_4581_ = v_isSharedCheck_4587_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_tail_4578_);
lean_inc(v_head_4577_);
lean_dec(v_a_4574_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4587_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4582_; lean_object* v___x_4584_; 
v___x_4582_ = l_Lean_mkLevelParam(v_head_4577_);
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 1, v_a_4575_);
lean_ctor_set(v___x_4580_, 0, v___x_4582_);
v___x_4584_ = v___x_4580_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_a_4575_);
v___x_4584_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
v_a_4574_ = v_tail_4578_;
v_a_4575_ = v___x_4584_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4590_ = lean_box(1);
v___x_4591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4592_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
lean_ctor_set(v___x_4593_, 1, v___x_4591_);
lean_ctor_set(v___x_4593_, 2, v___x_4590_);
return v___x_4593_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4596_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4597_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4598_ = lean_unsigned_to_nat(0u);
v___x_4599_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
lean_ctor_set(v___x_4599_, 2, v___x_4598_);
lean_ctor_set(v___x_4599_, 3, v___x_4598_);
lean_ctor_set(v___x_4599_, 4, v___x_4597_);
lean_ctor_set(v___x_4599_, 5, v___x_4597_);
lean_ctor_set(v___x_4599_, 6, v___x_4597_);
lean_ctor_set(v___x_4599_, 7, v___x_4597_);
lean_ctor_set(v___x_4599_, 8, v___x_4597_);
lean_ctor_set(v___x_4599_, 9, v___x_4597_);
lean_ctor_set(v___x_4599_, 10, v___x_4597_);
lean_ctor_set(v___x_4599_, 11, v___x_4596_);
return v___x_4599_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4600_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4601_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
lean_ctor_set(v___x_4601_, 2, v___x_4600_);
lean_ctor_set(v___x_4601_, 3, v___x_4600_);
lean_ctor_set(v___x_4601_, 4, v___x_4600_);
lean_ctor_set(v___x_4601_, 5, v___x_4600_);
return v___x_4601_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
lean_ctor_set(v___x_4603_, 2, v___x_4602_);
lean_ctor_set(v___x_4603_, 3, v___x_4602_);
lean_ctor_set(v___x_4603_, 4, v___x_4602_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4604_, lean_object* v_name_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
if (lean_obj_tag(v_name_4605_) == 1)
{
lean_object* v_pre_4609_; lean_object* v_str_4610_; lean_object* v___x_4611_; lean_object* v_env_4612_; uint8_t v___x_4613_; uint8_t v___x_4614_; 
v_pre_4609_ = lean_ctor_get(v_name_4605_, 0);
lean_inc_n(v_pre_4609_, 2);
v_str_4610_ = lean_ctor_get(v_name_4605_, 1);
v___x_4611_ = lean_st_ref_get(v___y_4607_);
v_env_4612_ = lean_ctor_get(v___x_4611_, 0);
lean_inc_ref(v_env_4612_);
lean_dec(v___x_4611_);
v___x_4613_ = 1;
v___x_4614_ = l_Lean_Environment_contains(v_env_4612_, v_pre_4609_, v___x_4613_);
if (v___x_4614_ == 0)
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
lean_dec(v_pre_4609_);
lean_dec_ref_known(v_name_4605_, 2);
lean_dec(v___x_4604_);
v___x_4615_ = lean_box(v___x_4614_);
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
return v___x_4616_;
}
else
{
uint8_t v___x_4617_; lean_object* v___y_4619_; uint8_t v___y_4620_; lean_object* v_a_4625_; 
lean_inc_ref(v_str_4610_);
v___x_4617_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4610_);
if (v___x_4617_ == 0)
{
lean_object* v___x_4628_; uint8_t v___x_4629_; 
v___x_4628_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4629_ = lean_string_dec_eq(v_str_4610_, v___x_4628_);
if (v___x_4629_ == 0)
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
lean_dec(v_pre_4609_);
lean_dec_ref_known(v_name_4605_, 2);
lean_dec(v___x_4604_);
v___x_4630_ = lean_box(v___x_4629_);
v___x_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
return v___x_4631_;
}
else
{
uint8_t v___x_4632_; uint8_t v___x_4633_; uint8_t v___x_4634_; lean_object* v___x_4635_; uint64_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; uint8_t v_a_4650_; lean_object* v___x_4654_; 
v___x_4632_ = 1;
v___x_4633_ = 0;
v___x_4634_ = 2;
v___x_4635_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4635_, 0, v___x_4617_);
lean_ctor_set_uint8(v___x_4635_, 1, v___x_4617_);
lean_ctor_set_uint8(v___x_4635_, 2, v___x_4617_);
lean_ctor_set_uint8(v___x_4635_, 3, v___x_4617_);
lean_ctor_set_uint8(v___x_4635_, 4, v___x_4617_);
lean_ctor_set_uint8(v___x_4635_, 5, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 6, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 7, v___x_4617_);
lean_ctor_set_uint8(v___x_4635_, 8, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 9, v___x_4632_);
lean_ctor_set_uint8(v___x_4635_, 10, v___x_4633_);
lean_ctor_set_uint8(v___x_4635_, 11, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 12, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 13, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 14, v___x_4634_);
lean_ctor_set_uint8(v___x_4635_, 15, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 16, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 17, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 18, v___x_4629_);
lean_ctor_set_uint8(v___x_4635_, 19, v___x_4617_);
v___x_4636_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4635_);
v___x_4637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4637_, 0, v___x_4635_);
lean_ctor_set_uint64(v___x_4637_, sizeof(void*)*1, v___x_4636_);
v___x_4638_ = lean_unsigned_to_nat(0u);
v___x_4639_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4640_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4641_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4642_ = lean_box(0);
lean_inc(v___x_4604_);
v___x_4643_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4643_, 0, v___x_4637_);
lean_ctor_set(v___x_4643_, 1, v___x_4604_);
lean_ctor_set(v___x_4643_, 2, v___x_4640_);
lean_ctor_set(v___x_4643_, 3, v___x_4641_);
lean_ctor_set(v___x_4643_, 4, v___x_4642_);
lean_ctor_set(v___x_4643_, 5, v___x_4638_);
lean_ctor_set(v___x_4643_, 6, v___x_4642_);
lean_ctor_set_uint8(v___x_4643_, sizeof(void*)*7, v___x_4617_);
lean_ctor_set_uint8(v___x_4643_, sizeof(void*)*7 + 1, v___x_4617_);
lean_ctor_set_uint8(v___x_4643_, sizeof(void*)*7 + 2, v___x_4617_);
lean_ctor_set_uint8(v___x_4643_, sizeof(void*)*7 + 3, v___x_4613_);
v___x_4644_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4645_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4646_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4644_);
lean_ctor_set(v___x_4647_, 1, v___x_4645_);
lean_ctor_set(v___x_4647_, 2, v___x_4604_);
lean_ctor_set(v___x_4647_, 3, v___x_4639_);
lean_ctor_set(v___x_4647_, 4, v___x_4646_);
v___x_4648_ = lean_st_mk_ref(v___x_4647_);
lean_inc(v_pre_4609_);
v___x_4654_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4609_, v___x_4643_, v___x_4648_, v___y_4606_, v___y_4607_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_object* v_a_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v_a_4655_ = lean_ctor_get(v___x_4654_, 0);
lean_inc(v_a_4655_);
lean_dec_ref_known(v___x_4654_, 1);
v___x_4656_ = l_Lean_ConstantInfo_levelParams(v_a_4655_);
lean_dec(v_a_4655_);
v___x_4657_ = lean_box(0);
lean_inc(v___x_4656_);
v___x_4658_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4656_, v___x_4657_);
lean_inc(v_pre_4609_);
v___x_4659_ = l_Lean_mkConst(v_pre_4609_, v___x_4658_);
lean_inc_ref(v___x_4659_);
v___x_4660_ = l_Lean_Meta_getFunInfo(v___x_4659_, v___x_4642_, v___x_4643_, v___x_4648_, v___y_4606_, v___y_4607_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4662_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
lean_inc_ref(v___x_4659_);
v___x_4662_ = l_Lean_Meta_getCongrSimpKinds(v___x_4659_, v_a_4661_, v___x_4643_, v___x_4648_, v___y_4606_, v___y_4607_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4664_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
v___x_4664_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4659_, v_a_4661_, v_a_4663_, v___x_4613_, v___x_4643_, v___x_4648_, v___y_4606_, v___y_4607_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
if (lean_obj_tag(v_a_4665_) == 1)
{
lean_object* v_val_4666_; lean_object* v_type_4667_; lean_object* v_proof_4668_; lean_object* v_argKinds_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4682_; 
v_val_4666_ = lean_ctor_get(v_a_4665_, 0);
lean_inc(v_val_4666_);
lean_dec_ref_known(v_a_4665_, 1);
v_type_4667_ = lean_ctor_get(v_val_4666_, 0);
v_proof_4668_ = lean_ctor_get(v_val_4666_, 1);
v_argKinds_4669_ = lean_ctor_get(v_val_4666_, 2);
v_isSharedCheck_4682_ = !lean_is_exclusive(v_val_4666_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4671_ = v_val_4666_;
v_isShared_4672_ = v_isSharedCheck_4682_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_argKinds_4669_);
lean_inc(v_proof_4668_);
lean_inc(v_type_4667_);
lean_dec(v_val_4666_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4682_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
lean_inc_ref(v_name_4605_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 2, v_type_4667_);
lean_ctor_set(v___x_4671_, 1, v___x_4656_);
lean_ctor_set(v___x_4671_, 0, v_name_4605_);
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_name_4605_);
lean_ctor_set(v_reuseFailAlloc_4681_, 1, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4681_, 2, v_type_4667_);
v___x_4674_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___f_4678_; lean_object* v___x_4679_; 
lean_inc_ref_n(v_name_4605_, 2);
v___x_4675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4675_, 0, v_name_4605_);
lean_ctor_set(v___x_4675_, 1, v___x_4657_);
v___x_4676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4674_);
lean_ctor_set(v___x_4676_, 1, v_proof_4668_);
lean_ctor_set(v___x_4676_, 2, v___x_4675_);
v___x_4677_ = lean_box(v___x_4617_);
v___f_4678_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4678_, 0, v_name_4605_);
lean_closure_set(v___f_4678_, 1, v_argKinds_4669_);
lean_closure_set(v___f_4678_, 2, v___x_4677_);
lean_closure_set(v___f_4678_, 3, v___x_4645_);
lean_closure_set(v___f_4678_, 4, v___x_4676_);
v___x_4679_ = l_Lean_Meta_realizeConst(v_pre_4609_, v_name_4605_, v___f_4678_, v___x_4643_, v___x_4648_, v___y_4606_, v___y_4607_);
lean_dec_ref_known(v___x_4643_, 7);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_dec_ref_known(v___x_4679_, 1);
v_a_4650_ = v___x_4613_;
goto v___jp_4649_;
}
else
{
lean_object* v_a_4680_; 
lean_dec(v___x_4648_);
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref_known(v___x_4679_, 1);
v_a_4625_ = v_a_4680_;
goto v___jp_4624_;
}
}
}
}
else
{
lean_dec(v_a_4665_);
lean_dec(v___x_4656_);
lean_dec_ref_known(v___x_4643_, 7);
lean_dec(v_pre_4609_);
lean_dec_ref_known(v_name_4605_, 2);
v_a_4650_ = v___x_4617_;
goto v___jp_4649_;
}
}
else
{
lean_object* v_a_4683_; 
lean_dec(v___x_4656_);
lean_dec(v___x_4648_);
lean_dec_ref_known(v___x_4643_, 7);
lean_dec_ref_known(v_name_4605_, 2);
lean_dec(v_pre_4609_);
v_a_4683_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4683_);
lean_dec_ref_known(v___x_4664_, 1);
v_a_4625_ = v_a_4683_;
goto v___jp_4624_;
}
}
else
{
lean_object* v_a_4684_; 
lean_dec(v_a_4661_);
lean_dec_ref(v___x_4659_);
lean_dec(v___x_4656_);
lean_dec(v___x_4648_);
lean_dec_ref_known(v___x_4643_, 7);
lean_dec(v_pre_4609_);
lean_dec_ref_known(v_name_4605_, 2);
v_a_4684_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4662_, 1);
v_a_4625_ = v_a_4684_;
goto v___jp_4624_;
}
}
else
{
lean_object* v_a_4685_; 
lean_dec_ref(v___x_4659_);
lean_dec(v___x_4656_);
lean_dec(v___x_4648_);
lean_dec_ref_known(v___x_4643_, 7);
lean_dec(v_pre_4609_);
lean_dec_ref_known(v_name_4605_, 2);
v_a_4685_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4660_, 1);
v_a_4625_ = v_a_4685_;
goto v___jp_4624_;
}
}
else
{
lean_object* v_a_4686_; 
lean_dec(v___x_4648_);
lean_dec_ref_known(v___x_4643_, 7);
lean_dec(v_pre_4609_);
lean_dec_ref_known(v_name_4605_, 2);
v_a_4686_ = lean_ctor_get(v___x_4654_, 0);
lean_inc(v_a_4686_);
lean_dec_ref_known(v___x_4654_, 1);
v_a_4625_ = v_a_4686_;
goto v___jp_4624_;
}
v___jp_4649_:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = lean_st_ref_get(v___x_4648_);
lean_dec(v___x_4648_);
lean_dec(v___x_4651_);
v___x_4652_ = lean_box(v_a_4650_);
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
return v___x_4653_;
}
}
}
else
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; uint8_t v___x_4694_; lean_object* v___y_4696_; uint8_t v___y_4697_; lean_object* v_a_4702_; uint8_t v___x_4705_; uint8_t v___x_4706_; uint8_t v___x_4707_; lean_object* v___x_4708_; uint64_t v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4687_ = lean_unsigned_to_nat(7u);
v___x_4688_ = lean_unsigned_to_nat(0u);
v___x_4689_ = lean_string_utf8_byte_size(v_str_4610_);
lean_inc_ref_n(v_str_4610_, 2);
v___x_4690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4690_, 0, v_str_4610_);
lean_ctor_set(v___x_4690_, 1, v___x_4688_);
lean_ctor_set(v___x_4690_, 2, v___x_4689_);
v___x_4691_ = l_String_Slice_Pos_nextn(v___x_4690_, v___x_4688_, v___x_4687_);
lean_dec_ref_known(v___x_4690_, 3);
v___x_4692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4692_, 0, v_str_4610_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
lean_ctor_set(v___x_4692_, 2, v___x_4689_);
v___x_4693_ = l_String_Slice_toNat_x21(v___x_4692_);
lean_dec_ref_known(v___x_4692_, 3);
v___x_4694_ = 0;
v___x_4705_ = 1;
v___x_4706_ = 0;
v___x_4707_ = 2;
v___x_4708_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4708_, 0, v___x_4694_);
lean_ctor_set_uint8(v___x_4708_, 1, v___x_4694_);
lean_ctor_set_uint8(v___x_4708_, 2, v___x_4694_);
lean_ctor_set_uint8(v___x_4708_, 3, v___x_4694_);
lean_ctor_set_uint8(v___x_4708_, 4, v___x_4694_);
lean_ctor_set_uint8(v___x_4708_, 5, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 6, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 7, v___x_4694_);
lean_ctor_set_uint8(v___x_4708_, 8, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 9, v___x_4705_);
lean_ctor_set_uint8(v___x_4708_, 10, v___x_4706_);
lean_ctor_set_uint8(v___x_4708_, 11, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 12, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 13, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 14, v___x_4707_);
lean_ctor_set_uint8(v___x_4708_, 15, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 16, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 17, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 18, v___x_4617_);
lean_ctor_set_uint8(v___x_4708_, 19, v___x_4694_);
v___x_4709_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4708_);
v___x_4710_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4710_, 0, v___x_4708_);
lean_ctor_set_uint64(v___x_4710_, sizeof(void*)*1, v___x_4709_);
v___x_4711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4712_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4713_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4714_ = lean_box(0);
lean_inc(v___x_4604_);
v___x_4715_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4715_, 0, v___x_4710_);
lean_ctor_set(v___x_4715_, 1, v___x_4604_);
lean_ctor_set(v___x_4715_, 2, v___x_4712_);
lean_ctor_set(v___x_4715_, 3, v___x_4713_);
lean_ctor_set(v___x_4715_, 4, v___x_4714_);
lean_ctor_set(v___x_4715_, 5, v___x_4688_);
lean_ctor_set(v___x_4715_, 6, v___x_4714_);
lean_ctor_set_uint8(v___x_4715_, sizeof(void*)*7, v___x_4694_);
lean_ctor_set_uint8(v___x_4715_, sizeof(void*)*7 + 1, v___x_4694_);
lean_ctor_set_uint8(v___x_4715_, sizeof(void*)*7 + 2, v___x_4694_);
lean_ctor_set_uint8(v___x_4715_, sizeof(void*)*7 + 3, v___x_4613_);
v___x_4716_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4717_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4718_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4716_);
lean_ctor_set(v___x_4719_, 1, v___x_4717_);
lean_ctor_set(v___x_4719_, 2, v___x_4604_);
lean_ctor_set(v___x_4719_, 3, v___x_4711_);
lean_ctor_set(v___x_4719_, 4, v___x_4718_);
v___x_4720_ = lean_st_mk_ref(v___x_4719_);
lean_inc(v_pre_4609_);
v___x_4721_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4609_, v___x_4715_, v___x_4720_, v___y_4606_, v___y_4607_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4722_);
lean_dec_ref_known(v___x_4721_, 1);
v___x_4723_ = l_Lean_ConstantInfo_levelParams(v_a_4722_);
lean_dec(v_a_4722_);
v___x_4724_ = lean_box(0);
lean_inc(v___x_4723_);
v___x_4725_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4723_, v___x_4724_);
lean_inc(v_pre_4609_);
v___x_4726_ = l_Lean_mkConst(v_pre_4609_, v___x_4725_);
v___x_4727_ = l_Lean_Meta_mkHCongrWithArity(v___x_4726_, v___x_4693_, v___x_4715_, v___x_4720_, v___y_4606_, v___y_4607_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v_type_4729_; lean_object* v_proof_4730_; lean_object* v_argKinds_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4754_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4728_);
lean_dec_ref_known(v___x_4727_, 1);
v_type_4729_ = lean_ctor_get(v_a_4728_, 0);
v_proof_4730_ = lean_ctor_get(v_a_4728_, 1);
v_argKinds_4731_ = lean_ctor_get(v_a_4728_, 2);
v_isSharedCheck_4754_ = !lean_is_exclusive(v_a_4728_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4733_ = v_a_4728_;
v_isShared_4734_ = v_isSharedCheck_4754_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_argKinds_4731_);
lean_inc(v_proof_4730_);
lean_inc(v_type_4729_);
lean_dec(v_a_4728_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4754_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
lean_inc_ref(v_name_4605_);
if (v_isShared_4734_ == 0)
{
lean_ctor_set(v___x_4733_, 2, v_type_4729_);
lean_ctor_set(v___x_4733_, 1, v___x_4723_);
lean_ctor_set(v___x_4733_, 0, v_name_4605_);
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_name_4605_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_type_4729_);
v___x_4736_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___f_4740_; lean_object* v___x_4741_; 
lean_inc_ref_n(v_name_4605_, 2);
v___x_4737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4737_, 0, v_name_4605_);
lean_ctor_set(v___x_4737_, 1, v___x_4724_);
v___x_4738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4736_);
lean_ctor_set(v___x_4738_, 1, v_proof_4730_);
lean_ctor_set(v___x_4738_, 2, v___x_4737_);
v___x_4739_ = lean_box(v___x_4694_);
v___f_4740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4740_, 0, v_name_4605_);
lean_closure_set(v___f_4740_, 1, v_argKinds_4731_);
lean_closure_set(v___f_4740_, 2, v___x_4739_);
lean_closure_set(v___f_4740_, 3, v___x_4717_);
lean_closure_set(v___f_4740_, 4, v___x_4738_);
v___x_4741_ = l_Lean_Meta_realizeConst(v_pre_4609_, v_name_4605_, v___f_4740_, v___x_4715_, v___x_4720_, v___y_4606_, v___y_4607_);
lean_dec_ref_known(v___x_4715_, 7);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4750_; 
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; 
v_unused_4751_ = lean_ctor_get(v___x_4741_, 0);
lean_dec(v_unused_4751_);
v___x_4743_ = v___x_4741_;
v_isShared_4744_ = v_isSharedCheck_4750_;
goto v_resetjp_4742_;
}
else
{
lean_dec(v___x_4741_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4750_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4748_; 
v___x_4745_ = lean_st_ref_get(v___x_4720_);
lean_dec(v___x_4720_);
lean_dec(v___x_4745_);
v___x_4746_ = lean_box(v___x_4613_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v___x_4746_);
v___x_4748_ = v___x_4743_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4746_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
else
{
lean_object* v_a_4752_; 
lean_dec(v___x_4720_);
v_a_4752_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4752_);
lean_dec_ref_known(v___x_4741_, 1);
v_a_4702_ = v_a_4752_;
goto v___jp_4701_;
}
}
}
}
else
{
lean_object* v_a_4755_; 
lean_dec(v___x_4723_);
lean_dec(v___x_4720_);
lean_dec_ref_known(v___x_4715_, 7);
lean_dec(v_pre_4609_);
lean_dec_ref_known(v_name_4605_, 2);
v_a_4755_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4727_, 1);
v_a_4702_ = v_a_4755_;
goto v___jp_4701_;
}
}
else
{
lean_object* v_a_4756_; 
lean_dec(v___x_4720_);
lean_dec_ref_known(v___x_4715_, 7);
lean_dec(v___x_4693_);
lean_dec(v_pre_4609_);
lean_dec_ref_known(v_name_4605_, 2);
v_a_4756_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4756_);
lean_dec_ref_known(v___x_4721_, 1);
v_a_4702_ = v_a_4756_;
goto v___jp_4701_;
}
v___jp_4695_:
{
if (v___y_4697_ == 0)
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
lean_dec_ref(v___y_4696_);
v___x_4698_ = lean_box(v___x_4694_);
v___x_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
return v___x_4699_;
}
else
{
lean_object* v___x_4700_; 
v___x_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4700_, 0, v___y_4696_);
return v___x_4700_;
}
}
v___jp_4701_:
{
uint8_t v___x_4703_; 
v___x_4703_ = l_Lean_Exception_isInterrupt(v_a_4702_);
if (v___x_4703_ == 0)
{
uint8_t v___x_4704_; 
lean_inc_ref(v_a_4702_);
v___x_4704_ = l_Lean_Exception_isRuntime(v_a_4702_);
v___y_4696_ = v_a_4702_;
v___y_4697_ = v___x_4704_;
goto v___jp_4695_;
}
else
{
v___y_4696_ = v_a_4702_;
v___y_4697_ = v___x_4703_;
goto v___jp_4695_;
}
}
}
v___jp_4618_:
{
if (v___y_4620_ == 0)
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
lean_dec_ref(v___y_4619_);
v___x_4621_ = lean_box(v___x_4617_);
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
return v___x_4622_;
}
else
{
lean_object* v___x_4623_; 
v___x_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___y_4619_);
return v___x_4623_;
}
}
v___jp_4624_:
{
uint8_t v___x_4626_; 
v___x_4626_ = l_Lean_Exception_isInterrupt(v_a_4625_);
if (v___x_4626_ == 0)
{
uint8_t v___x_4627_; 
lean_inc_ref(v_a_4625_);
v___x_4627_ = l_Lean_Exception_isRuntime(v_a_4625_);
v___y_4619_ = v_a_4625_;
v___y_4620_ = v___x_4627_;
goto v___jp_4618_;
}
else
{
v___y_4619_ = v_a_4625_;
v___y_4620_ = v___x_4626_;
goto v___jp_4618_;
}
}
}
}
else
{
uint8_t v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec(v_name_4605_);
lean_dec(v___x_4604_);
v___x_4757_ = 0;
v___x_4758_ = lean_box(v___x_4757_);
v___x_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4758_);
return v___x_4759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4760_, lean_object* v_name_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4760_, v_name_4761_, v___y_4762_, v___y_4763_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4769_; lean_object* v___x_4770_; 
v___f_4769_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4770_ = l_Lean_registerReservedNameAction(v___f_4769_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* v_msg_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v___f_4779_; lean_object* v___x_1735__overap_4780_; lean_object* v___x_4781_; 
v___f_4779_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1735__overap_4780_ = lean_panic_fn_borrowed(v___f_4779_, v_msg_4773_);
lean_inc(v___y_4777_);
lean_inc_ref(v___y_4776_);
lean_inc(v___y_4775_);
lean_inc_ref(v___y_4774_);
v___x_4781_ = lean_apply_5(v___x_1735__overap_4780_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, lean_box(0));
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
return v_res_4788_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4790_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4791_ = lean_unsigned_to_nat(8u);
v___x_4792_ = lean_unsigned_to_nat(461u);
v___x_4793_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0));
v___x_4794_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4795_ = l_mkPanicMessageWithDecl(v___x_4794_, v___x_4793_, v___x_4792_, v___x_4791_, v___x_4790_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* v_thmName_4796_, lean_object* v_levels_4797_, lean_object* v___x_4798_, lean_object* v_____r_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
lean_inc(v_thmName_4796_);
v___x_4805_ = l_Lean_mkConst(v_thmName_4796_, v_levels_4797_);
lean_inc(v___y_4803_);
lean_inc_ref(v___y_4802_);
lean_inc(v___y_4801_);
lean_inc_ref(v___y_4800_);
lean_inc_ref(v___x_4805_);
v___x_4806_ = lean_infer_type(v___x_4805_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4850_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4850_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4850_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4811_; lean_object* v_env_4812_; lean_object* v___x_4813_; lean_object* v_toEnvExtension_4814_; lean_object* v_asyncMode_4815_; uint8_t v___x_4816_; lean_object* v___x_4817_; 
v___x_4811_ = lean_st_ref_get(v___y_4803_);
v_env_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc_ref(v_env_4812_);
lean_dec(v___x_4811_);
v___x_4813_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4814_ = lean_ctor_get(v___x_4813_, 0);
v_asyncMode_4815_ = lean_ctor_get(v_toEnvExtension_4814_, 2);
v___x_4816_ = 0;
v___x_4817_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4798_, v___x_4813_, v_env_4812_, v_thmName_4796_, v_asyncMode_4815_, v___x_4816_);
if (lean_obj_tag(v___x_4817_) == 1)
{
lean_object* v_val_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4830_; 
v_val_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4830_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_val_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4830_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; lean_object* v___x_4824_; 
v___x_4822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4822_, 0, v_a_4807_);
lean_ctor_set(v___x_4822_, 1, v___x_4805_);
lean_ctor_set(v___x_4822_, 2, v_val_4818_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v___x_4822_);
v___x_4824_ = v___x_4820_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4822_);
v___x_4824_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; lean_object* v___x_4827_; 
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4825_);
v___x_4827_ = v___x_4809_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4825_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
lean_dec(v___x_4817_);
lean_del_object(v___x_4809_);
lean_dec(v_a_4807_);
lean_dec_ref(v___x_4805_);
v___x_4831_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1);
v___x_4832_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4831_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4841_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4841_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4841_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4837_, 0, v_a_4833_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4837_);
v___x_4839_ = v___x_4835_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v___x_4837_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
v_a_4842_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4832_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4832_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
}
}
else
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4858_; 
lean_dec_ref(v___x_4805_);
lean_dec_ref(v___x_4798_);
lean_dec(v_thmName_4796_);
v_a_4851_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4853_ = v___x_4806_;
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4806_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4854_ == 0)
{
v___x_4856_ = v___x_4853_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4851_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* v_thmName_4859_, lean_object* v_levels_4860_, lean_object* v___x_4861_, lean_object* v_____r_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4859_, v_levels_4860_, v___x_4861_, v_____r_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_);
lean_dec(v___y_4866_);
lean_dec_ref(v___y_4865_);
lean_dec(v___y_4864_);
lean_dec_ref(v___y_4863_);
return v_res_4868_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0(void){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Array_instInhabited___redArg();
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* v_declName_4870_, lean_object* v_levels_4871_, lean_object* v_numArgs_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_){
_start:
{
lean_object* v___y_4879_; uint8_t v___y_4880_; lean_object* v_a_4885_; lean_object* v___y_4889_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v_suffix_4903_; lean_object* v_thmName_4904_; lean_object* v___x_4905_; lean_object* v_env_4906_; uint8_t v___x_4907_; 
v___x_4900_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_4901_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4902_ = l_Nat_reprFast(v_numArgs_4872_);
v_suffix_4903_ = lean_string_append(v___x_4901_, v___x_4902_);
lean_dec_ref(v___x_4902_);
v_thmName_4904_ = l_Lean_Name_str___override(v_declName_4870_, v_suffix_4903_);
v___x_4905_ = lean_st_ref_get(v_a_4876_);
v_env_4906_ = lean_ctor_get(v___x_4905_, 0);
lean_inc_ref(v_env_4906_);
lean_dec(v___x_4905_);
v___x_4907_ = l_Lean_Environment_containsOnBranch(v_env_4906_, v_thmName_4904_);
lean_dec_ref(v_env_4906_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; 
lean_inc(v_thmName_4904_);
v___x_4908_ = l_Lean_executeReservedNameAction(v_thmName_4904_, v_a_4875_, v_a_4876_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
lean_dec_ref_known(v___x_4908_, 1);
v___x_4909_ = lean_box(0);
v___x_4910_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4904_, v_levels_4871_, v___x_4900_, v___x_4909_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_);
v___y_4889_ = v___x_4910_;
goto v___jp_4888_;
}
else
{
lean_object* v_a_4911_; 
lean_dec(v_thmName_4904_);
lean_dec(v_levels_4871_);
v_a_4911_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4908_, 1);
v_a_4885_ = v_a_4911_;
goto v___jp_4884_;
}
}
else
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = lean_box(0);
v___x_4913_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4904_, v_levels_4871_, v___x_4900_, v___x_4912_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_);
v___y_4889_ = v___x_4913_;
goto v___jp_4888_;
}
v___jp_4878_:
{
if (v___y_4880_ == 0)
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_dec_ref(v___y_4879_);
v___x_4881_ = lean_box(0);
v___x_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4881_);
return v___x_4882_;
}
else
{
lean_object* v___x_4883_; 
v___x_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4883_, 0, v___y_4879_);
return v___x_4883_;
}
}
v___jp_4884_:
{
uint8_t v___x_4886_; 
v___x_4886_ = l_Lean_Exception_isInterrupt(v_a_4885_);
if (v___x_4886_ == 0)
{
uint8_t v___x_4887_; 
lean_inc_ref(v_a_4885_);
v___x_4887_ = l_Lean_Exception_isRuntime(v_a_4885_);
v___y_4879_ = v_a_4885_;
v___y_4880_ = v___x_4887_;
goto v___jp_4878_;
}
else
{
v___y_4879_ = v_a_4885_;
v___y_4880_ = v___x_4886_;
goto v___jp_4878_;
}
}
v___jp_4888_:
{
if (lean_obj_tag(v___y_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4898_; 
v_a_4890_ = lean_ctor_get(v___y_4889_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___y_4889_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4892_ = v___y_4889_;
v_isShared_4893_ = v_isSharedCheck_4898_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___y_4889_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4898_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v_a_4894_; lean_object* v___x_4896_; 
v_a_4894_ = lean_ctor_get(v_a_4890_, 0);
lean_inc(v_a_4894_);
lean_dec(v_a_4890_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 0, v_a_4894_);
v___x_4896_ = v___x_4892_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4894_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
else
{
lean_object* v_a_4899_; 
v_a_4899_ = lean_ctor_get(v___y_4889_, 0);
lean_inc(v_a_4899_);
lean_dec_ref_known(v___y_4889_, 1);
v_a_4885_ = v_a_4899_;
goto v___jp_4884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object* v_declName_4914_, lean_object* v_levels_4915_, lean_object* v_numArgs_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_4914_, v_levels_4915_, v_numArgs_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* v_____r_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4931_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0));
v___x_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4931_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* v_____r_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
return v_res_4939_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4941_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4942_ = lean_unsigned_to_nat(8u);
v___x_4943_ = lean_unsigned_to_nat(478u);
v___x_4944_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0));
v___x_4945_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4946_ = l_mkPanicMessageWithDecl(v___x_4945_, v___x_4944_, v___x_4943_, v___x_4942_, v___x_4941_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object* v_thmName_4947_, lean_object* v_levels_4948_, lean_object* v___x_4949_, lean_object* v_____r_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
lean_inc(v_thmName_4947_);
v___x_4956_ = l_Lean_mkConst(v_thmName_4947_, v_levels_4948_);
lean_inc(v___y_4954_);
lean_inc_ref(v___y_4953_);
lean_inc(v___y_4952_);
lean_inc_ref(v___y_4951_);
lean_inc_ref(v___x_4956_);
v___x_4957_ = lean_infer_type(v___x_4956_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_5001_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4960_ = v___x_4957_;
v_isShared_4961_ = v_isSharedCheck_5001_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4957_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_5001_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4962_; lean_object* v_env_4963_; lean_object* v___x_4964_; lean_object* v_toEnvExtension_4965_; lean_object* v_asyncMode_4966_; uint8_t v___x_4967_; lean_object* v___x_4968_; 
v___x_4962_ = lean_st_ref_get(v___y_4954_);
v_env_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc_ref(v_env_4963_);
lean_dec(v___x_4962_);
v___x_4964_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4965_ = lean_ctor_get(v___x_4964_, 0);
v_asyncMode_4966_ = lean_ctor_get(v_toEnvExtension_4965_, 2);
v___x_4967_ = 0;
v___x_4968_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4949_, v___x_4964_, v_env_4963_, v_thmName_4947_, v_asyncMode_4966_, v___x_4967_);
if (lean_obj_tag(v___x_4968_) == 1)
{
lean_object* v_val_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4981_; 
v_val_4969_ = lean_ctor_get(v___x_4968_, 0);
v_isSharedCheck_4981_ = !lean_is_exclusive(v___x_4968_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4971_ = v___x_4968_;
v_isShared_4972_ = v_isSharedCheck_4981_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_val_4969_);
lean_dec(v___x_4968_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4981_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4973_; lean_object* v___x_4975_; 
v___x_4973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4973_, 0, v_a_4958_);
lean_ctor_set(v___x_4973_, 1, v___x_4956_);
lean_ctor_set(v___x_4973_, 2, v_val_4969_);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 0, v___x_4973_);
v___x_4975_ = v___x_4971_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4973_);
v___x_4975_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4978_; 
v___x_4976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 0, v___x_4976_);
v___x_4978_ = v___x_4960_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___x_4976_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4983_; 
lean_dec(v___x_4968_);
lean_del_object(v___x_4960_);
lean_dec(v_a_4958_);
lean_dec_ref(v___x_4956_);
v___x_4982_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1);
v___x_4983_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4982_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4992_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4986_ = v___x_4983_;
v_isShared_4987_ = v_isSharedCheck_4992_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4983_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4992_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4988_; lean_object* v___x_4990_; 
v___x_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4988_, 0, v_a_4984_);
if (v_isShared_4987_ == 0)
{
lean_ctor_set(v___x_4986_, 0, v___x_4988_);
v___x_4990_ = v___x_4986_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4988_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
else
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
v_a_4993_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4983_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4983_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
}
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec_ref(v___x_4956_);
lean_dec_ref(v___x_4949_);
lean_dec(v_thmName_4947_);
v_a_5002_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_4957_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_4957_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object* v_thmName_5010_, lean_object* v_levels_5011_, lean_object* v___x_5012_, lean_object* v_____r_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5010_, v_levels_5011_, v___x_5012_, v_____r_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
return v_res_5019_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1(void){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0));
v___x_5022_ = l_Lean_stringToMessageData(v___x_5021_);
return v___x_5022_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3(void){
_start:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5024_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2));
v___x_5025_ = l_Lean_stringToMessageData(v___x_5024_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* v_declName_5026_, lean_object* v_levels_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_){
_start:
{
lean_object* v_a_5034_; lean_object* v___y_5052_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v_thmName_5059_; lean_object* v___y_5061_; uint8_t v___y_5062_; lean_object* v_a_5090_; lean_object* v___y_5094_; lean_object* v___x_5097_; lean_object* v_env_5098_; uint8_t v___x_5099_; 
v___x_5057_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_5058_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v_thmName_5059_ = l_Lean_Name_str___override(v_declName_5026_, v___x_5058_);
v___x_5097_ = lean_st_ref_get(v_a_5031_);
v_env_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc_ref(v_env_5098_);
lean_dec(v___x_5097_);
v___x_5099_ = l_Lean_Environment_containsOnBranch(v_env_5098_, v_thmName_5059_);
lean_dec_ref(v_env_5098_);
if (v___x_5099_ == 0)
{
lean_object* v___x_5100_; 
lean_inc(v_thmName_5059_);
v___x_5100_ = l_Lean_executeReservedNameAction(v_thmName_5059_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
lean_dec_ref_known(v___x_5100_, 1);
v___x_5101_ = lean_box(0);
lean_inc(v_thmName_5059_);
v___x_5102_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5059_, v_levels_5027_, v___x_5057_, v___x_5101_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
v___y_5094_ = v___x_5102_;
goto v___jp_5093_;
}
else
{
lean_object* v_a_5103_; 
lean_dec(v_levels_5027_);
v_a_5103_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___x_5100_, 1);
v_a_5090_ = v_a_5103_;
goto v___jp_5089_;
}
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5104_ = lean_box(0);
lean_inc(v_thmName_5059_);
v___x_5105_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5059_, v_levels_5027_, v___x_5057_, v___x_5104_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
v___y_5094_ = v___x_5105_;
goto v___jp_5093_;
}
v___jp_5033_:
{
if (lean_obj_tag(v_a_5034_) == 0)
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5042_; 
v_a_5035_ = lean_ctor_get(v_a_5034_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v_a_5034_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5037_ = v_a_5034_;
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v_a_5034_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5040_; 
if (v_isShared_5038_ == 0)
{
v___x_5040_ = v___x_5037_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
else
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5050_; 
v_a_5043_ = lean_ctor_get(v_a_5034_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v_a_5034_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5045_ = v_a_5034_;
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v_a_5034_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5048_; 
if (v_isShared_5046_ == 0)
{
lean_ctor_set_tag(v___x_5045_, 0);
v___x_5048_ = v___x_5045_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5043_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
}
v___jp_5051_:
{
lean_object* v_a_5053_; 
v_a_5053_ = lean_ctor_get(v___y_5052_, 0);
lean_inc(v_a_5053_);
lean_dec_ref(v___y_5052_);
v_a_5034_ = v_a_5053_;
goto v___jp_5033_;
}
v___jp_5054_:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5055_ = lean_box(0);
v___x_5056_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v___x_5055_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
v___y_5052_ = v___x_5056_;
goto v___jp_5051_;
}
v___jp_5060_:
{
if (v___y_5062_ == 0)
{
lean_object* v_toCold_5063_; lean_object* v_options_5064_; uint8_t v_hasTrace_5065_; 
v_toCold_5063_ = lean_ctor_get(v_a_5030_, 0);
v_options_5064_ = lean_ctor_get(v_toCold_5063_, 2);
v_hasTrace_5065_ = lean_ctor_get_uint8(v_options_5064_, sizeof(void*)*1);
if (v_hasTrace_5065_ == 0)
{
lean_dec_ref(v___y_5061_);
lean_dec(v_thmName_5059_);
goto v___jp_5054_;
}
else
{
lean_object* v_inheritedTraceOptions_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; uint8_t v___x_5069_; 
v_inheritedTraceOptions_5066_ = lean_ctor_get(v_toCold_5063_, 11);
v___x_5067_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_5068_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_5069_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5066_, v_options_5064_, v___x_5068_);
if (v___x_5069_ == 0)
{
lean_dec_ref(v___y_5061_);
lean_dec(v_thmName_5059_);
goto v___jp_5054_;
}
else
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5070_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1);
v___x_5071_ = l_Lean_MessageData_ofName(v_thmName_5059_);
v___x_5072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5070_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3);
v___x_5074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5072_);
lean_ctor_set(v___x_5074_, 1, v___x_5073_);
v___x_5075_ = l_Lean_Exception_toMessageData(v___y_5061_);
v___x_5076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_5067_, v___x_5076_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5079_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref_known(v___x_5077_, 1);
v___x_5079_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_a_5078_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
v___y_5052_ = v___x_5079_;
goto v___jp_5051_;
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
v_a_5080_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_5077_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5077_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
}
}
else
{
lean_object* v___x_5088_; 
lean_dec(v_thmName_5059_);
v___x_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5088_, 0, v___y_5061_);
return v___x_5088_;
}
}
v___jp_5089_:
{
uint8_t v___x_5091_; 
v___x_5091_ = l_Lean_Exception_isInterrupt(v_a_5090_);
if (v___x_5091_ == 0)
{
uint8_t v___x_5092_; 
lean_inc_ref(v_a_5090_);
v___x_5092_ = l_Lean_Exception_isRuntime(v_a_5090_);
v___y_5061_ = v_a_5090_;
v___y_5062_ = v___x_5092_;
goto v___jp_5060_;
}
else
{
v___y_5061_ = v_a_5090_;
v___y_5062_ = v___x_5091_;
goto v___jp_5060_;
}
}
v___jp_5093_:
{
if (lean_obj_tag(v___y_5094_) == 0)
{
lean_object* v_a_5095_; 
lean_dec(v_thmName_5059_);
v_a_5095_ = lean_ctor_get(v___y_5094_, 0);
lean_inc(v_a_5095_);
lean_dec_ref_known(v___y_5094_, 1);
v_a_5034_ = v_a_5095_;
goto v___jp_5033_;
}
else
{
lean_object* v_a_5096_; 
v_a_5096_ = lean_ctor_get(v___y_5094_, 0);
lean_inc(v_a_5096_);
lean_dec_ref_known(v___y_5094_, 1);
v_a_5090_ = v_a_5096_;
goto v___jp_5089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object* v_declName_5106_, lean_object* v_levels_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_5106_, v_levels_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
return v_res_5113_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedCongrArgKind_default = _init_l_Lean_Meta_instInhabitedCongrArgKind_default();
l_Lean_Meta_instInhabitedCongrArgKind = _init_l_Lean_Meta_instInhabitedCongrArgKind();
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_congrKindsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_congrKindsExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CongrTheorems(builtin);
}
#ifdef __cplusplus
}
#endif
