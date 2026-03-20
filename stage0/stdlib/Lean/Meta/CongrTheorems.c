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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
uint8_t lean_is_class(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_before(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___boxed(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2;
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.CongrTheorems.0.Lean.Meta.mkCongrSimpCore\?.mk\?.go"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "e_"};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___closed__0;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "congrKindsExt"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 7, 195, 199, 246, 152, 65, 143)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declared `"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
uint8_t v_x_boxed_9_; lean_object* v_res_10_; 
v_x_boxed_9_ = lean_unbox(v_x_8_);
v_res_10_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_x_boxed_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_toCtorIdx(uint8_t v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_toCtorIdx___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_x_4__boxed_14_; lean_object* v_res_15_; 
v_x_4__boxed_14_ = lean_unbox(v_x_13_);
v_res_15_ = l_Lean_Meta_CongrArgKind_toCtorIdx(v_x_4__boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg(lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg___boxed(lean_object* v_k_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_CongrArgKind_ctorElim___redArg(v_k_17_);
lean_dec(v_k_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, uint8_t v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_inc(v_k_23_);
return v_k_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
uint8_t v_t_boxed_29_; lean_object* v_res_30_; 
v_t_boxed_29_ = lean_unbox(v_t_26_);
v_res_30_ = l_Lean_Meta_CongrArgKind_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_boxed_29_, v_h_27_, v_k_28_);
lean_dec(v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg(lean_object* v_fixed_31_){
_start:
{
lean_inc(v_fixed_31_);
return v_fixed_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg___boxed(lean_object* v_fixed_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Meta_CongrArgKind_fixed_elim___redArg(v_fixed_32_);
lean_dec(v_fixed_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim(lean_object* v_motive_34_, uint8_t v_t_35_, lean_object* v_h_36_, lean_object* v_fixed_37_){
_start:
{
lean_inc(v_fixed_37_);
return v_fixed_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___boxed(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_fixed_41_){
_start:
{
uint8_t v_t_boxed_42_; lean_object* v_res_43_; 
v_t_boxed_42_ = lean_unbox(v_t_39_);
v_res_43_ = l_Lean_Meta_CongrArgKind_fixed_elim(v_motive_38_, v_t_boxed_42_, v_h_40_, v_fixed_41_);
lean_dec(v_fixed_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(lean_object* v_fixedNoParam_44_){
_start:
{
lean_inc(v_fixedNoParam_44_);
return v_fixedNoParam_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg___boxed(lean_object* v_fixedNoParam_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(v_fixedNoParam_45_);
lean_dec(v_fixedNoParam_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim(lean_object* v_motive_47_, uint8_t v_t_48_, lean_object* v_h_49_, lean_object* v_fixedNoParam_50_){
_start:
{
lean_inc(v_fixedNoParam_50_);
return v_fixedNoParam_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___boxed(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_fixedNoParam_54_){
_start:
{
uint8_t v_t_boxed_55_; lean_object* v_res_56_; 
v_t_boxed_55_ = lean_unbox(v_t_52_);
v_res_56_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim(v_motive_51_, v_t_boxed_55_, v_h_53_, v_fixedNoParam_54_);
lean_dec(v_fixedNoParam_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg(lean_object* v_eq_57_){
_start:
{
lean_inc(v_eq_57_);
return v_eq_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg___boxed(lean_object* v_eq_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Meta_CongrArgKind_eq_elim___redArg(v_eq_58_);
lean_dec(v_eq_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim(lean_object* v_motive_60_, uint8_t v_t_61_, lean_object* v_h_62_, lean_object* v_eq_63_){
_start:
{
lean_inc(v_eq_63_);
return v_eq_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___boxed(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_eq_67_){
_start:
{
uint8_t v_t_boxed_68_; lean_object* v_res_69_; 
v_t_boxed_68_ = lean_unbox(v_t_65_);
v_res_69_ = l_Lean_Meta_CongrArgKind_eq_elim(v_motive_64_, v_t_boxed_68_, v_h_66_, v_eq_67_);
lean_dec(v_eq_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg(lean_object* v_cast_70_){
_start:
{
lean_inc(v_cast_70_);
return v_cast_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg___boxed(lean_object* v_cast_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_CongrArgKind_cast_elim___redArg(v_cast_71_);
lean_dec(v_cast_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim(lean_object* v_motive_73_, uint8_t v_t_74_, lean_object* v_h_75_, lean_object* v_cast_76_){
_start:
{
lean_inc(v_cast_76_);
return v_cast_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___boxed(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_cast_80_){
_start:
{
uint8_t v_t_boxed_81_; lean_object* v_res_82_; 
v_t_boxed_81_ = lean_unbox(v_t_78_);
v_res_82_ = l_Lean_Meta_CongrArgKind_cast_elim(v_motive_77_, v_t_boxed_81_, v_h_79_, v_cast_80_);
lean_dec(v_cast_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg(lean_object* v_heq_83_){
_start:
{
lean_inc(v_heq_83_);
return v_heq_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg___boxed(lean_object* v_heq_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Meta_CongrArgKind_heq_elim___redArg(v_heq_84_);
lean_dec(v_heq_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim(lean_object* v_motive_86_, uint8_t v_t_87_, lean_object* v_h_88_, lean_object* v_heq_89_){
_start:
{
lean_inc(v_heq_89_);
return v_heq_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___boxed(lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_heq_93_){
_start:
{
uint8_t v_t_boxed_94_; lean_object* v_res_95_; 
v_t_boxed_94_ = lean_unbox(v_t_91_);
v_res_95_ = l_Lean_Meta_CongrArgKind_heq_elim(v_motive_90_, v_t_boxed_94_, v_h_92_, v_heq_93_);
lean_dec(v_heq_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(lean_object* v_subsingletonInst_96_){
_start:
{
lean_inc(v_subsingletonInst_96_);
return v_subsingletonInst_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg___boxed(lean_object* v_subsingletonInst_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(v_subsingletonInst_97_);
lean_dec(v_subsingletonInst_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim(lean_object* v_motive_99_, uint8_t v_t_100_, lean_object* v_h_101_, lean_object* v_subsingletonInst_102_){
_start:
{
lean_inc(v_subsingletonInst_102_);
return v_subsingletonInst_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___boxed(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_subsingletonInst_106_){
_start:
{
uint8_t v_t_boxed_107_; lean_object* v_res_108_; 
v_t_boxed_107_ = lean_unbox(v_t_104_);
v_res_108_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim(v_motive_103_, v_t_boxed_107_, v_h_105_, v_subsingletonInst_106_);
lean_dec(v_subsingletonInst_106_);
return v_res_108_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind_default(void){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind(void){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(2u);
v___x_130_ = lean_nat_to_int(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_to_int(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr(uint8_t v_x_133_, lean_object* v_prec_134_){
_start:
{
lean_object* v___y_136_; lean_object* v___y_143_; lean_object* v___y_150_; lean_object* v___y_157_; lean_object* v___y_164_; lean_object* v___y_171_; 
switch(v_x_133_)
{
case 0:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(1024u);
v___x_178_ = lean_nat_dec_le(v___x_177_, v_prec_134_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_136_ = v___x_179_;
goto v___jp_135_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_136_ = v___x_180_;
goto v___jp_135_;
}
}
case 1:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(1024u);
v___x_182_ = lean_nat_dec_le(v___x_181_, v_prec_134_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_143_ = v___x_183_;
goto v___jp_142_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_143_ = v___x_184_;
goto v___jp_142_;
}
}
case 2:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(1024u);
v___x_186_ = lean_nat_dec_le(v___x_185_, v_prec_134_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_150_ = v___x_187_;
goto v___jp_149_;
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_150_ = v___x_188_;
goto v___jp_149_;
}
}
case 3:
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(1024u);
v___x_190_ = lean_nat_dec_le(v___x_189_, v_prec_134_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_157_ = v___x_191_;
goto v___jp_156_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_157_ = v___x_192_;
goto v___jp_156_;
}
}
case 4:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1024u);
v___x_194_ = lean_nat_dec_le(v___x_193_, v_prec_134_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_164_ = v___x_195_;
goto v___jp_163_;
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_164_ = v___x_196_;
goto v___jp_163_;
}
}
default: 
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(1024u);
v___x_198_ = lean_nat_dec_le(v___x_197_, v_prec_134_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_171_ = v___x_199_;
goto v___jp_170_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_171_ = v___x_200_;
goto v___jp_170_;
}
}
}
v___jp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_137_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__1));
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___y_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
v___x_141_ = l_Repr_addAppParen(v___x_140_, v_prec_134_);
return v___x_141_;
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_144_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__3));
v___x_145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_145_, 0, v___y_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = 0;
v___x_147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*1, v___x_146_);
v___x_148_ = l_Repr_addAppParen(v___x_147_, v_prec_134_);
return v___x_148_;
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__5));
v___x_152_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_152_, 0, v___y_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = 0;
v___x_154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_153_);
v___x_155_ = l_Repr_addAppParen(v___x_154_, v_prec_134_);
return v___x_155_;
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_158_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__7));
v___x_159_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_159_, 0, v___y_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = 0;
v___x_161_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*1, v___x_160_);
v___x_162_ = l_Repr_addAppParen(v___x_161_, v_prec_134_);
return v___x_162_;
}
v___jp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__9));
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___y_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = 0;
v___x_168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1, v___x_167_);
v___x_169_ = l_Repr_addAppParen(v___x_168_, v_prec_134_);
return v___x_169_;
}
v___jp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_172_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__11));
v___x_173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_173_, 0, v___y_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = 0;
v___x_175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_174_);
v___x_176_ = l_Repr_addAppParen(v___x_175_, v_prec_134_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr___boxed(lean_object* v_x_201_, lean_object* v_prec_202_){
_start:
{
uint8_t v_x_345__boxed_203_; lean_object* v_res_204_; 
v_x_345__boxed_203_ = lean_unbox(v_x_201_);
v_res_204_ = l_Lean_Meta_instReprCongrArgKind_repr(v_x_345__boxed_203_, v_prec_202_);
lean_dec(v_prec_202_);
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t v_x_207_, uint8_t v_y_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_x_207_);
v___x_210_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_y_208_);
v___x_211_ = lean_nat_dec_eq(v___x_209_, v___x_210_);
lean_dec(v___x_210_);
lean_dec(v___x_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqCongrArgKind_beq___boxed(lean_object* v_x_212_, lean_object* v_y_213_){
_start:
{
uint8_t v_x_17__boxed_214_; uint8_t v_y_18__boxed_215_; uint8_t v_res_216_; lean_object* v_r_217_; 
v_x_17__boxed_214_ = lean_unbox(v_x_212_);
v_y_18__boxed_215_ = lean_unbox(v_y_213_);
v_res_216_ = l_Lean_Meta_instBEqCongrArgKind_beq(v_x_17__boxed_214_, v_y_18__boxed_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(lean_object* v_as_221_, size_t v_sz_222_, size_t v_i_223_, lean_object* v_b_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = lean_usize_dec_lt(v_i_223_, v_sz_222_);
if (v___x_225_ == 0)
{
return v_b_224_;
}
else
{
lean_object* v_a_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; size_t v___x_233_; size_t v___x_234_; 
v_a_226_ = lean_array_uget_borrowed(v_as_221_, v_i_223_);
lean_inc_ref(v_b_224_);
v___x_227_ = l_Lean_LocalContext_getFVar_x21(v_b_224_, v_a_226_);
v___x_228_ = l_Lean_LocalDecl_fvarId(v___x_227_);
v___x_229_ = l_Lean_LocalDecl_userName(v___x_227_);
lean_dec_ref(v___x_227_);
v___x_230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0));
v___x_231_ = lean_name_append_after(v___x_229_, v___x_230_);
v___x_232_ = l_Lean_LocalContext_setUserName(v_b_224_, v___x_228_, v___x_231_);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_223_, v___x_233_);
v_i_223_ = v___x_234_;
v_b_224_ = v___x_232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(lean_object* v_as_236_, lean_object* v_sz_237_, lean_object* v_i_238_, lean_object* v_b_239_){
_start:
{
size_t v_sz_boxed_240_; size_t v_i_boxed_241_; lean_object* v_res_242_; 
v_sz_boxed_240_ = lean_unbox_usize(v_sz_237_);
lean_dec(v_sz_237_);
v_i_boxed_241_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_as_236_, v_sz_boxed_240_, v_i_boxed_241_, v_b_239_);
lean_dec_ref(v_as_236_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(lean_object* v_ys_243_, lean_object* v_lctx_244_){
_start:
{
size_t v_sz_245_; size_t v___x_246_; lean_object* v___x_247_; 
v_sz_245_ = lean_array_size(v_ys_243_);
v___x_246_ = ((size_t)0ULL);
v___x_247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_ys_243_, v_sz_245_, v___x_246_, v_lctx_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(lean_object* v_ys_248_, lean_object* v_lctx_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_248_, v_lctx_249_);
lean_dec_ref(v_ys_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(lean_object* v_as_251_, size_t v_sz_252_, size_t v_i_253_, lean_object* v_b_254_){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = lean_usize_dec_lt(v_i_253_, v_sz_252_);
if (v___x_255_ == 0)
{
return v_b_254_;
}
else
{
lean_object* v_a_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; size_t v___x_261_; size_t v___x_262_; 
v_a_256_ = lean_array_uget_borrowed(v_as_251_, v_i_253_);
lean_inc_ref(v_b_254_);
v___x_257_ = l_Lean_LocalContext_getFVar_x21(v_b_254_, v_a_256_);
v___x_258_ = l_Lean_LocalDecl_fvarId(v___x_257_);
lean_dec_ref(v___x_257_);
v___x_259_ = 0;
v___x_260_ = l_Lean_LocalContext_setBinderInfo(v_b_254_, v___x_258_, v___x_259_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_add(v_i_253_, v___x_261_);
v_i_253_ = v___x_262_;
v_b_254_ = v___x_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(lean_object* v_as_264_, lean_object* v_sz_265_, lean_object* v_i_266_, lean_object* v_b_267_){
_start:
{
size_t v_sz_boxed_268_; size_t v_i_boxed_269_; lean_object* v_res_270_; 
v_sz_boxed_268_ = lean_unbox_usize(v_sz_265_);
lean_dec(v_sz_265_);
v_i_boxed_269_ = lean_unbox_usize(v_i_266_);
lean_dec(v_i_266_);
v_res_270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_as_264_, v_sz_boxed_268_, v_i_boxed_269_, v_b_267_);
lean_dec_ref(v_as_264_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(lean_object* v_ys_271_, lean_object* v_lctx_272_){
_start:
{
size_t v_sz_273_; size_t v___x_274_; lean_object* v___x_275_; 
v_sz_273_ = lean_array_size(v_ys_271_);
v___x_274_ = ((size_t)0ULL);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_ys_271_, v_sz_273_, v___x_274_, v_lctx_272_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(lean_object* v_ys_276_, lean_object* v_lctx_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_276_, v_lctx_277_);
lean_dec_ref(v_ys_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_279_, lean_object* v_b_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_apply_6(v_k_279_, v_b_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, lean_box(0));
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_287_, lean_object* v_b_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_287_, v_b_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(lean_object* v_name_295_, uint8_t v_bi_296_, lean_object* v_type_297_, lean_object* v_k_298_, uint8_t v_kind_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___f_305_; lean_object* v___x_306_; 
v___f_305_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_305_, 0, v_k_298_);
v___x_306_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_295_, v_bi_296_, v_type_297_, v___f_305_, v_kind_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_315_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_306_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_306_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_323_, lean_object* v_bi_324_, lean_object* v_type_325_, lean_object* v_k_326_, lean_object* v_kind_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
uint8_t v_bi_boxed_333_; uint8_t v_kind_boxed_334_; lean_object* v_res_335_; 
v_bi_boxed_333_ = lean_unbox(v_bi_324_);
v_kind_boxed_334_ = lean_unbox(v_kind_327_);
v_res_335_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_323_, v_bi_boxed_333_, v_type_325_, v_k_326_, v_kind_boxed_334_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(lean_object* v_name_336_, lean_object* v_type_337_, lean_object* v_k_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_344_; uint8_t v___x_345_; lean_object* v___x_346_; 
v___x_344_ = 0;
v___x_345_ = 0;
v___x_346_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_336_, v___x_344_, v_type_337_, v_k_338_, v___x_345_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg___boxed(lean_object* v_name_347_, lean_object* v_type_348_, lean_object* v_k_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_347_, v_type_348_, v_k_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_eqs_359_, lean_object* v_kinds_360_, lean_object* v_xs_361_, lean_object* v_ys_362_, lean_object* v_k_363_, lean_object* v___x_364_, lean_object* v_h_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(v_eqs_359_, v_kinds_360_, v_xs_361_, v_ys_362_, v_k_363_, v___x_364_, v_h_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___x_364_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(lean_object* v_eqs_372_, lean_object* v_kinds_373_, lean_object* v_xs_374_, lean_object* v_ys_375_, lean_object* v_k_376_, lean_object* v___x_377_, lean_object* v_h_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_384_ = lean_array_push(v_eqs_372_, v_h_378_);
v___x_385_ = 2;
v___x_386_ = lean_box(v___x_385_);
v___x_387_ = lean_array_push(v_kinds_373_, v___x_386_);
v___x_388_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_374_, v_ys_375_, v_k_376_, v___x_377_, v___x_384_, v___x_387_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(lean_object* v_eqs_389_, lean_object* v_kinds_390_, lean_object* v_xs_391_, lean_object* v_ys_392_, lean_object* v_k_393_, lean_object* v___x_394_, lean_object* v_h_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(v_eqs_389_, v_kinds_390_, v_xs_391_, v_ys_392_, v_k_393_, v___x_394_, v_h_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___x_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(lean_object* v_xs_402_, lean_object* v_ys_403_, lean_object* v_k_404_, lean_object* v_i_405_, lean_object* v_eqs_406_, lean_object* v_kinds_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_array_get_size(v_xs_402_);
v___x_414_ = lean_nat_dec_lt(v_i_405_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec_ref(v_ys_403_);
lean_dec_ref(v_xs_402_);
v___x_415_ = lean_apply_7(v_k_404_, v_eqs_406_, v_kinds_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, lean_box(0));
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v_x_417_; lean_object* v___x_418_; 
v___x_416_ = l_Lean_instInhabitedExpr;
v_x_417_ = lean_array_get_borrowed(v___x_416_, v_xs_402_, v_i_405_);
lean_inc(v_a_411_);
lean_inc_ref(v_a_410_);
lean_inc(v_a_409_);
lean_inc_ref(v_a_408_);
lean_inc(v_x_417_);
v___x_418_ = lean_infer_type(v_x_417_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v_y_420_; lean_object* v___x_421_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
v_y_420_ = lean_array_get_borrowed(v___x_416_, v_ys_403_, v_i_405_);
lean_inc(v_a_411_);
lean_inc_ref(v_a_410_);
lean_inc(v_a_409_);
lean_inc_ref(v_a_408_);
lean_inc(v_y_420_);
v___x_421_ = lean_infer_type(v_y_420_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref(v___x_421_);
v___x_423_ = l_Lean_Expr_cleanupAnnotations(v_a_419_);
v___x_424_ = l_Lean_Expr_cleanupAnnotations(v_a_422_);
v___x_425_ = lean_expr_eqv(v___x_423_, v___x_424_);
lean_dec_ref(v___x_424_);
lean_dec_ref(v___x_423_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_inc(v_a_411_);
lean_inc_ref(v_a_410_);
lean_inc(v_a_409_);
lean_inc_ref(v_a_408_);
lean_inc(v_y_420_);
lean_inc(v_x_417_);
v___x_426_ = l_Lean_Meta_mkHEq(v_x_417_, v_y_420_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref(v___x_426_);
v___x_428_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1));
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_i_405_, v___x_429_);
lean_inc(v___x_430_);
v___f_431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_431_, 0, v_eqs_406_);
lean_closure_set(v___f_431_, 1, v_kinds_407_);
lean_closure_set(v___f_431_, 2, v_xs_402_);
lean_closure_set(v___f_431_, 3, v_ys_403_);
lean_closure_set(v___f_431_, 4, v_k_404_);
lean_closure_set(v___f_431_, 5, v___x_430_);
v___x_432_ = lean_name_append_index_after(v___x_428_, v___x_430_);
v___x_433_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_432_, v_a_427_, v___f_431_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
return v___x_433_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_kinds_407_);
lean_dec_ref(v_eqs_406_);
lean_dec_ref(v_k_404_);
lean_dec_ref(v_ys_403_);
lean_dec_ref(v_xs_402_);
v_a_434_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_426_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_426_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v___x_442_; 
lean_inc(v_a_411_);
lean_inc_ref(v_a_410_);
lean_inc(v_a_409_);
lean_inc_ref(v_a_408_);
lean_inc(v_y_420_);
lean_inc(v_x_417_);
v___x_442_ = l_Lean_Meta_mkEq(v_x_417_, v_y_420_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___f_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1));
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_i_405_, v___x_445_);
lean_inc(v___x_446_);
v___f_447_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_447_, 0, v_eqs_406_);
lean_closure_set(v___f_447_, 1, v_kinds_407_);
lean_closure_set(v___f_447_, 2, v_xs_402_);
lean_closure_set(v___f_447_, 3, v_ys_403_);
lean_closure_set(v___f_447_, 4, v_k_404_);
lean_closure_set(v___f_447_, 5, v___x_446_);
v___x_448_ = lean_name_append_index_after(v___x_444_, v___x_446_);
v___x_449_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_448_, v_a_443_, v___f_447_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
return v___x_449_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_kinds_407_);
lean_dec_ref(v_eqs_406_);
lean_dec_ref(v_k_404_);
lean_dec_ref(v_ys_403_);
lean_dec_ref(v_xs_402_);
v_a_450_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_442_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_442_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_a_419_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_kinds_407_);
lean_dec_ref(v_eqs_406_);
lean_dec_ref(v_k_404_);
lean_dec_ref(v_ys_403_);
lean_dec_ref(v_xs_402_);
v_a_458_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_421_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_421_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_kinds_407_);
lean_dec_ref(v_eqs_406_);
lean_dec_ref(v_k_404_);
lean_dec_ref(v_ys_403_);
lean_dec_ref(v_xs_402_);
v_a_466_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_418_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_418_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(lean_object* v_eqs_474_, lean_object* v_kinds_475_, lean_object* v_xs_476_, lean_object* v_ys_477_, lean_object* v_k_478_, lean_object* v___x_479_, lean_object* v_h_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_486_ = lean_array_push(v_eqs_474_, v_h_480_);
v___x_487_ = 4;
v___x_488_ = lean_box(v___x_487_);
v___x_489_ = lean_array_push(v_kinds_475_, v___x_488_);
v___x_490_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_476_, v_ys_477_, v_k_478_, v___x_479_, v___x_486_, v___x_489_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(lean_object* v_xs_491_, lean_object* v_ys_492_, lean_object* v_k_493_, lean_object* v_i_494_, lean_object* v_eqs_495_, lean_object* v_kinds_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_491_, v_ys_492_, v_k_493_, v_i_494_, v_eqs_495_, v_kinds_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_i_494_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_object* v_00_u03b1_503_, lean_object* v_xs_504_, lean_object* v_ys_505_, lean_object* v_k_506_, lean_object* v_i_507_, lean_object* v_eqs_508_, lean_object* v_kinds_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_504_, v_ys_505_, v_k_506_, v_i_507_, v_eqs_508_, v_kinds_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(lean_object* v_00_u03b1_516_, lean_object* v_xs_517_, lean_object* v_ys_518_, lean_object* v_k_519_, lean_object* v_i_520_, lean_object* v_eqs_521_, lean_object* v_kinds_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(v_00_u03b1_516_, v_xs_517_, v_ys_518_, v_k_519_, v_i_520_, v_eqs_521_, v_kinds_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_i_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(lean_object* v_00_u03b1_529_, lean_object* v_name_530_, uint8_t v_bi_531_, lean_object* v_type_532_, lean_object* v_k_533_, uint8_t v_kind_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_530_, v_bi_531_, v_type_532_, v_k_533_, v_kind_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_541_, lean_object* v_name_542_, lean_object* v_bi_543_, lean_object* v_type_544_, lean_object* v_k_545_, lean_object* v_kind_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
uint8_t v_bi_boxed_552_; uint8_t v_kind_boxed_553_; lean_object* v_res_554_; 
v_bi_boxed_552_ = lean_unbox(v_bi_543_);
v_kind_boxed_553_ = lean_unbox(v_kind_546_);
v_res_554_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_541_, v_name_542_, v_bi_boxed_552_, v_type_544_, v_k_545_, v_kind_boxed_553_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(lean_object* v_00_u03b1_555_, lean_object* v_name_556_, lean_object* v_type_557_, lean_object* v_k_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_556_, v_type_557_, v_k_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___boxed(lean_object* v_00_u03b1_565_, lean_object* v_name_566_, lean_object* v_type_567_, lean_object* v_k_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(v_00_u03b1_565_, v_name_566_, v_type_567_, v_k_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(lean_object* v_xs_577_, lean_object* v_ys_578_, lean_object* v_k_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_587_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_577_, v_ys_578_, v_k_579_, v___x_585_, v___x_586_, v___x_586_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___boxed(lean_object* v_xs_588_, lean_object* v_ys_589_, lean_object* v_k_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_588_, v_ys_589_, v_k_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(lean_object* v_00_u03b1_597_, lean_object* v_xs_598_, lean_object* v_ys_599_, lean_object* v_k_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_598_, v_ys_599_, v_k_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed(lean_object* v_00_u03b1_607_, lean_object* v_xs_608_, lean_object* v_ys_609_, lean_object* v_k_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(v_00_u03b1_607_, v_xs_608_, v_ys_609_, v_k_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(lean_object* v_k_617_, lean_object* v_b_618_, lean_object* v_c_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_apply_7(v_k_617_, v_b_618_, v_c_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, lean_box(0));
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed(lean_object* v_k_626_, lean_object* v_b_627_, lean_object* v_c_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(v_k_626_, v_b_627_, v_c_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(lean_object* v_type_635_, lean_object* v_maxFVars_x3f_636_, lean_object* v_k_637_, uint8_t v_cleanupAnnotations_638_, uint8_t v_whnfType_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___f_645_; lean_object* v___x_646_; 
v___f_645_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_645_, 0, v_k_637_);
v___x_646_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_635_, v_maxFVars_x3f_636_, v___f_645_, v_cleanupAnnotations_638_, v_whnfType_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
v_a_655_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_646_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_646_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___boxed(lean_object* v_type_663_, lean_object* v_maxFVars_x3f_664_, lean_object* v_k_665_, lean_object* v_cleanupAnnotations_666_, lean_object* v_whnfType_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_673_; uint8_t v_whnfType_boxed_674_; lean_object* v_res_675_; 
v_cleanupAnnotations_boxed_673_ = lean_unbox(v_cleanupAnnotations_666_);
v_whnfType_boxed_674_ = lean_unbox(v_whnfType_667_);
v_res_675_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_663_, v_maxFVars_x3f_664_, v_k_665_, v_cleanupAnnotations_boxed_673_, v_whnfType_boxed_674_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(lean_object* v_00_u03b1_676_, lean_object* v_type_677_, lean_object* v_maxFVars_x3f_678_, lean_object* v_k_679_, uint8_t v_cleanupAnnotations_680_, uint8_t v_whnfType_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_677_, v_maxFVars_x3f_678_, v_k_679_, v_cleanupAnnotations_680_, v_whnfType_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___boxed(lean_object* v_00_u03b1_688_, lean_object* v_type_689_, lean_object* v_maxFVars_x3f_690_, lean_object* v_k_691_, lean_object* v_cleanupAnnotations_692_, lean_object* v_whnfType_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_699_; uint8_t v_whnfType_boxed_700_; lean_object* v_res_701_; 
v_cleanupAnnotations_boxed_699_ = lean_unbox(v_cleanupAnnotations_692_);
v_whnfType_boxed_700_ = lean_unbox(v_whnfType_693_);
v_res_701_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(v_00_u03b1_688_, v_type_689_, v_maxFVars_x3f_690_, v_k_691_, v_cleanupAnnotations_boxed_699_, v_whnfType_boxed_700_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_a_715_, lean_object* v_type_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v___x_1936__boxed_722_; lean_object* v_res_723_; 
v___x_1936__boxed_722_ = lean_unbox(v___x_712_);
v_res_723_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(v___x_710_, v___x_711_, v___x_1936__boxed_722_, v___x_713_, v___x_714_, v_a_715_, v_type_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec_ref(v_a_715_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(lean_object* v_type_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_731_ = lean_unsigned_to_nat(3u);
v___x_732_ = l_Lean_Expr_isAppOfArity(v_type_724_, v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3));
v___x_734_ = lean_unsigned_to_nat(4u);
v___x_735_ = l_Lean_Expr_isAppOfArity(v_type_724_, v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___f_740_; uint8_t v___x_741_; lean_object* v___x_742_; 
v___x_736_ = l_Lean_instInhabitedExpr;
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_739_ = lean_box(v___x_735_);
v___f_740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed), 12, 5);
lean_closure_set(v___f_740_, 0, v___x_736_);
lean_closure_set(v___f_740_, 1, v___x_737_);
lean_closure_set(v___f_740_, 2, v___x_739_);
lean_closure_set(v___f_740_, 3, v___x_731_);
lean_closure_set(v___f_740_, 4, v___x_738_);
v___x_741_ = 1;
v___x_742_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_724_, v___x_738_, v___f_740_, v___x_741_, v___x_735_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = l_Lean_Expr_appFn_x21(v_type_724_);
lean_dec_ref(v_type_724_);
v___x_744_ = l_Lean_Expr_appFn_x21(v___x_743_);
lean_dec_ref(v___x_743_);
v___x_745_ = l_Lean_Expr_appArg_x21(v___x_744_);
lean_dec_ref(v___x_744_);
v___x_746_ = l_Lean_Meta_mkHEqRefl(v___x_745_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
return v___x_746_;
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = l_Lean_Expr_appFn_x21(v_type_724_);
lean_dec_ref(v_type_724_);
v___x_748_ = l_Lean_Expr_appArg_x21(v___x_747_);
lean_dec_ref(v___x_747_);
v___x_749_ = l_Lean_Meta_mkEqRefl(v___x_748_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(lean_object* v_type_750_, lean_object* v_motive_751_, lean_object* v___x_752_, lean_object* v_b_753_, uint8_t v___x_754_, lean_object* v___x_755_, lean_object* v_a_756_, lean_object* v_eqPr_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_type_763_; lean_object* v___x_764_; 
v_type_763_ = l_Lean_Expr_bindingBody_x21(v_type_750_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
v___x_764_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_763_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc_ref(v_eqPr_757_);
v___x_766_ = lean_infer_type(v_eqPr_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
v___x_768_ = lean_whnf(v_a_767_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v_motive_770_; lean_object* v_major_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; uint8_t v___x_790_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v_motive_770_ = l_Lean_Expr_bindingBody_x21(v_motive_751_);
v___x_790_ = l_Lean_Expr_isHEq(v_a_769_);
lean_dec(v_a_769_);
if (v___x_790_ == 0)
{
lean_inc_ref(v_eqPr_757_);
v_major_772_ = v_eqPr_757_;
v___y_773_ = v___y_758_;
v___y_774_ = v___y_759_;
v___y_775_ = v___y_760_;
v___y_776_ = v___y_761_;
goto v___jp_771_;
}
else
{
lean_object* v___x_791_; 
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc_ref(v_eqPr_757_);
v___x_791_ = l_Lean_Meta_mkEqOfHEq(v_eqPr_757_, v___x_790_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v___x_791_);
v_major_772_ = v_a_792_;
v___y_773_ = v___y_758_;
v___y_774_ = v___y_759_;
v___y_775_ = v___y_760_;
v___y_776_ = v___y_761_;
goto v___jp_771_;
}
else
{
lean_dec_ref(v_motive_770_);
lean_dec(v_a_765_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_791_;
}
}
v___jp_771_:
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; 
v___x_777_ = lean_mk_empty_array_with_capacity(v___x_752_);
lean_inc_ref(v_b_753_);
v___x_778_ = lean_array_push(v___x_777_, v_b_753_);
v___x_779_ = 1;
v___x_780_ = 1;
v___x_781_ = l_Lean_Meta_mkLambdaFVars(v___x_778_, v_motive_770_, v___x_754_, v___x_779_, v___x_754_, v___x_779_, v___x_780_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec_ref(v___x_778_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_781_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
v___x_783_ = l_Lean_Meta_mkEqNDRec(v_a_782_, v_a_765_, v_major_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_755_);
v___x_786_ = lean_array_push(v___x_785_, v_a_756_);
v___x_787_ = lean_array_push(v___x_786_, v_b_753_);
v___x_788_ = lean_array_push(v___x_787_, v_eqPr_757_);
v___x_789_ = l_Lean_Meta_mkLambdaFVars(v___x_788_, v_a_784_, v___x_754_, v___x_779_, v___x_754_, v___x_779_, v___x_780_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v___x_788_);
return v___x_789_;
}
else
{
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_783_;
}
}
else
{
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v_major_772_);
lean_dec(v_a_765_);
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_781_;
}
}
}
else
{
lean_dec(v_a_765_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_768_;
}
}
else
{
lean_dec(v_a_765_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_766_;
}
}
else
{
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(lean_object* v_type_793_, lean_object* v_motive_794_, lean_object* v___x_795_, lean_object* v_b_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_a_799_, lean_object* v_eqPr_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
uint8_t v___x_1996__boxed_806_; lean_object* v_res_807_; 
v___x_1996__boxed_806_ = lean_unbox(v___x_797_);
v_res_807_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(v_type_793_, v_motive_794_, v___x_795_, v_b_796_, v___x_1996__boxed_806_, v___x_798_, v_a_799_, v_eqPr_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___x_798_);
lean_dec(v___x_795_);
lean_dec_ref(v_motive_794_);
lean_dec_ref(v_type_793_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(lean_object* v___x_808_, lean_object* v___x_809_, lean_object* v_type_810_, lean_object* v_a_811_, lean_object* v___x_812_, uint8_t v___x_813_, lean_object* v___x_814_, lean_object* v_b_815_, lean_object* v_motive_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_b_822_; lean_object* v___x_823_; lean_object* v_type_824_; lean_object* v___x_825_; lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_b_822_ = lean_array_get_borrowed(v___x_808_, v_b_815_, v___x_809_);
v___x_823_ = l_Lean_Expr_bindingBody_x21(v_type_810_);
v_type_824_ = lean_expr_instantiate1(v___x_823_, v_a_811_);
lean_dec_ref(v___x_823_);
v___x_825_ = lean_box(v___x_813_);
lean_inc(v_b_822_);
lean_inc_ref(v_motive_816_);
v___f_826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed), 13, 7);
lean_closure_set(v___f_826_, 0, v_type_824_);
lean_closure_set(v___f_826_, 1, v_motive_816_);
lean_closure_set(v___f_826_, 2, v___x_812_);
lean_closure_set(v___f_826_, 3, v_b_822_);
lean_closure_set(v___f_826_, 4, v___x_825_);
lean_closure_set(v___f_826_, 5, v___x_814_);
lean_closure_set(v___f_826_, 6, v_a_811_);
v___x_827_ = l_Lean_Expr_bindingName_x21(v_motive_816_);
v___x_828_ = l_Lean_Expr_bindingDomain_x21(v_motive_816_);
lean_dec_ref(v_motive_816_);
v___x_829_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_827_, v___x_828_, v___f_826_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v_type_832_, lean_object* v_a_833_, lean_object* v___x_834_, lean_object* v___x_835_, lean_object* v___x_836_, lean_object* v_b_837_, lean_object* v_motive_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
uint8_t v___x_1951__boxed_844_; lean_object* v_res_845_; 
v___x_1951__boxed_844_ = lean_unbox(v___x_835_);
v_res_845_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(v___x_830_, v___x_831_, v_type_832_, v_a_833_, v___x_834_, v___x_1951__boxed_844_, v___x_836_, v_b_837_, v_motive_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec_ref(v_b_837_);
lean_dec_ref(v_type_832_);
lean_dec(v___x_831_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object* v___x_846_, lean_object* v___x_847_, uint8_t v___x_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v_a_851_, lean_object* v_type_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___f_861_; uint8_t v___x_862_; lean_object* v___x_863_; 
v___x_858_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_846_);
v_a_859_ = lean_array_get_borrowed(v___x_846_, v_a_851_, v___x_858_);
v___x_860_ = lean_box(v___x_848_);
lean_inc(v_a_859_);
lean_inc_ref(v_type_852_);
v___f_861_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed), 14, 7);
lean_closure_set(v___f_861_, 0, v___x_846_);
lean_closure_set(v___f_861_, 1, v___x_858_);
lean_closure_set(v___f_861_, 2, v_type_852_);
lean_closure_set(v___f_861_, 3, v_a_859_);
lean_closure_set(v___f_861_, 4, v___x_847_);
lean_closure_set(v___f_861_, 5, v___x_860_);
lean_closure_set(v___f_861_, 6, v___x_849_);
v___x_862_ = 1;
v___x_863_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_852_, v___x_850_, v___f_861_, v___x_862_, v___x_848_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___boxed(lean_object* v_type_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(lean_object* v_lctx_871_, lean_object* v_localInsts_872_, lean_object* v_x_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_871_, v_localInsts_872_, v_x_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_879_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_879_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(lean_object* v_lctx_896_, lean_object* v_localInsts_897_, lean_object* v_x_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_896_, v_localInsts_897_, v_x_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_object* v_00_u03b1_905_, lean_object* v_lctx_906_, lean_object* v_localInsts_907_, lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_906_, v_localInsts_907_, v_x_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(lean_object* v_00_u03b1_915_, lean_object* v_lctx_916_, lean_object* v_localInsts_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(v_00_u03b1_915_, v_lctx_916_, v_localInsts_917_, v_x_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(lean_object* v_as_925_, size_t v_sz_926_, size_t v_i_927_, lean_object* v_b_928_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_lt(v_i_927_, v_sz_926_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_b_928_);
return v___x_931_;
}
else
{
lean_object* v_snd_932_; lean_object* v_snd_933_; lean_object* v_fst_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_1004_; 
v_snd_932_ = lean_ctor_get(v_b_928_, 1);
lean_inc(v_snd_932_);
v_snd_933_ = lean_ctor_get(v_snd_932_, 1);
lean_inc(v_snd_933_);
v_fst_934_ = lean_ctor_get(v_b_928_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_b_928_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v_b_928_, 1);
lean_dec(v_unused_1005_);
v___x_936_ = v_b_928_;
v_isShared_937_ = v_isSharedCheck_1004_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_fst_934_);
lean_dec(v_b_928_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_1004_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_fst_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1002_; 
v_fst_938_ = lean_ctor_get(v_snd_932_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_snd_932_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v_snd_932_, 1);
lean_dec(v_unused_1003_);
v___x_940_ = v_snd_932_;
v_isShared_941_ = v_isSharedCheck_1002_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_fst_938_);
lean_dec(v_snd_932_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1002_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_array_942_; lean_object* v_start_943_; lean_object* v_stop_944_; uint8_t v___x_945_; 
v_array_942_ = lean_ctor_get(v_snd_933_, 0);
v_start_943_ = lean_ctor_get(v_snd_933_, 1);
v_stop_944_ = lean_ctor_get(v_snd_933_, 2);
v___x_945_ = lean_nat_dec_lt(v_start_943_, v_stop_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_947_; 
if (v_isShared_941_ == 0)
{
v___x_947_ = v___x_940_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_fst_938_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_snd_933_);
v___x_947_ = v_reuseFailAlloc_952_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_947_);
v___x_949_ = v___x_936_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_fst_934_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_947_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
}
else
{
lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_998_; 
lean_inc(v_stop_944_);
lean_inc(v_start_943_);
lean_inc_ref(v_array_942_);
v_isSharedCheck_998_ = !lean_is_exclusive(v_snd_933_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; lean_object* v_unused_1000_; lean_object* v_unused_1001_; 
v_unused_999_ = lean_ctor_get(v_snd_933_, 2);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_snd_933_, 1);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_snd_933_, 0);
lean_dec(v_unused_1001_);
v___x_954_ = v_snd_933_;
v_isShared_955_ = v_isSharedCheck_998_;
goto v_resetjp_953_;
}
else
{
lean_dec(v_snd_933_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_998_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_array_956_; lean_object* v_start_957_; lean_object* v_stop_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v_array_956_ = lean_ctor_get(v_fst_938_, 0);
v_start_957_ = lean_ctor_get(v_fst_938_, 1);
v_stop_958_ = lean_ctor_get(v_fst_938_, 2);
v___x_959_ = lean_array_fget(v_array_942_, v_start_943_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_start_943_, v___x_960_);
lean_dec(v_start_943_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_961_);
v___x_963_ = v___x_954_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_array_942_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_stop_944_);
v___x_963_ = v_reuseFailAlloc_997_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_lt(v_start_957_, v_stop_958_);
if (v___x_964_ == 0)
{
lean_object* v___x_966_; 
lean_dec(v___x_959_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_963_);
v___x_966_ = v___x_940_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_fst_938_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_963_);
v___x_966_ = v_reuseFailAlloc_971_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_966_);
v___x_968_ = v___x_936_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_fst_934_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_970_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
}
else
{
lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_993_; 
lean_inc(v_stop_958_);
lean_inc(v_start_957_);
lean_inc_ref(v_array_956_);
v_isSharedCheck_993_ = !lean_is_exclusive(v_fst_938_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; lean_object* v_unused_995_; lean_object* v_unused_996_; 
v_unused_994_ = lean_ctor_get(v_fst_938_, 2);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_fst_938_, 1);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_fst_938_, 0);
lean_dec(v_unused_996_);
v___x_973_ = v_fst_938_;
v_isShared_974_ = v_isSharedCheck_993_;
goto v_resetjp_972_;
}
else
{
lean_dec(v_fst_938_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_993_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_a_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v_a_975_ = lean_array_uget_borrowed(v_as_925_, v_i_927_);
v___x_976_ = lean_array_fget(v_array_956_, v_start_957_);
v___x_977_ = lean_nat_add(v_start_957_, v___x_960_);
lean_dec(v_start_957_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v___x_977_);
v___x_979_ = v___x_973_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_array_956_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_stop_958_);
v___x_979_ = v_reuseFailAlloc_992_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
lean_inc(v_a_975_);
v___x_980_ = lean_array_push(v_fst_934_, v_a_975_);
v___x_981_ = lean_array_push(v___x_980_, v___x_976_);
v___x_982_ = lean_array_push(v___x_981_, v___x_959_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_963_);
lean_ctor_set(v___x_940_, 0, v___x_979_);
v___x_984_ = v___x_940_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_963_);
v___x_984_ = v_reuseFailAlloc_991_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_984_);
lean_ctor_set(v___x_936_, 0, v___x_982_);
v___x_986_ = v___x_936_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
size_t v___x_987_; size_t v___x_988_; 
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_add(v_i_927_, v___x_987_);
v_i_927_ = v___x_988_;
v_b_928_ = v___x_986_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(lean_object* v_as_1006_, lean_object* v_sz_1007_, lean_object* v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_){
_start:
{
size_t v_sz_boxed_1011_; size_t v_i_boxed_1012_; lean_object* v_res_1013_; 
v_sz_boxed_1011_ = lean_unbox_usize(v_sz_1007_);
lean_dec(v_sz_1007_);
v_i_boxed_1012_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_1006_, v_sz_boxed_1011_, v_i_boxed_1012_, v_b_1009_);
lean_dec_ref(v_as_1006_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object* v_ys_1014_, lean_object* v_xs_1015_, lean_object* v_f_1016_, uint8_t v___x_1017_, uint8_t v___x_1018_, lean_object* v_eqs_1019_, lean_object* v_argKinds_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_1028_ = lean_array_get_size(v_ys_1014_);
lean_inc_ref(v_ys_1014_);
v___x_1029_ = l_Array_toSubarray___redArg(v_ys_1014_, v___x_1026_, v___x_1028_);
v___x_1030_ = lean_array_get_size(v_eqs_1019_);
v___x_1031_ = l_Array_toSubarray___redArg(v_eqs_1019_, v___x_1026_, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1029_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1027_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v_sz_1034_ = lean_array_size(v_xs_1015_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_xs_1015_, v_sz_1034_, v___x_1035_, v___x_1033_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v___x_1036_);
lean_inc_ref(v_f_1016_);
v___x_1038_ = l_Lean_mkAppN(v_f_1016_, v_xs_1015_);
v___x_1039_ = l_Lean_mkAppN(v_f_1016_, v_ys_1014_);
lean_dec_ref(v_ys_1014_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
v___x_1040_ = l_Lean_Meta_mkHEq(v___x_1038_, v___x_1039_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v_fst_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref(v___x_1040_);
v_fst_1042_ = lean_ctor_get(v_a_1037_, 0);
lean_inc(v_fst_1042_);
lean_dec(v_a_1037_);
v___x_1043_ = 1;
v___x_1044_ = l_Lean_Meta_mkForallFVars(v_fst_1042_, v_a_1041_, v___x_1017_, v___x_1018_, v___x_1018_, v___x_1043_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v_fst_1042_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v___x_1044_);
lean_inc(v_a_1045_);
v___x_1046_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_a_1045_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1051_, 0, v_a_1045_);
lean_ctor_set(v___x_1051_, 1, v_a_1047_);
lean_ctor_set(v___x_1051_, 2, v_argKinds_1020_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1051_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_a_1045_);
lean_dec_ref(v_argKinds_1020_);
v_a_1056_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1046_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1046_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v_argKinds_1020_);
v_a_1064_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1044_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1044_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v_a_1037_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v_argKinds_1020_);
v_a_1072_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1040_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1040_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v_argKinds_1020_);
lean_dec_ref(v_f_1016_);
lean_dec_ref(v_ys_1014_);
v_a_1080_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1036_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1036_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object* v_ys_1088_, lean_object* v_xs_1089_, lean_object* v_f_1090_, lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v_eqs_1093_, lean_object* v_argKinds_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
uint8_t v___x_5042__boxed_1100_; uint8_t v___x_5043__boxed_1101_; lean_object* v_res_1102_; 
v___x_5042__boxed_1100_ = lean_unbox(v___x_1091_);
v___x_5043__boxed_1101_ = lean_unbox(v___x_1092_);
v_res_1102_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1088_, v_xs_1089_, v_f_1090_, v___x_5042__boxed_1100_, v___x_5043__boxed_1101_, v_eqs_1093_, v_argKinds_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec_ref(v_xs_1089_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(lean_object* v_msgData_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v_env_1110_; lean_object* v___x_1111_; lean_object* v_mctx_1112_; lean_object* v_lctx_1113_; lean_object* v_options_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1109_ = lean_st_ref_get(v___y_1107_);
v_env_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_st_ref_get(v___y_1105_);
v_mctx_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_mctx_1112_);
lean_dec(v___x_1111_);
v_lctx_1113_ = lean_ctor_get(v___y_1104_, 2);
v_options_1114_ = lean_ctor_get(v___y_1106_, 2);
lean_inc_ref(v_options_1114_);
lean_inc_ref(v_lctx_1113_);
v___x_1115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1115_, 0, v_env_1110_);
lean_ctor_set(v___x_1115_, 1, v_mctx_1112_);
lean_ctor_set(v___x_1115_, 2, v_lctx_1113_);
lean_ctor_set(v___x_1115_, 3, v_options_1114_);
v___x_1116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_msgData_1103_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0___boxed(lean_object* v_msgData_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msgData_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_ref_1131_ = lean_ctor_get(v___y_1128_, 5);
v___x_1132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_inc(v_ref_1131_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_ref_1131_);
lean_ctor_set(v___x_1137_, 1, v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 1);
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object* v_msg_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1(lean_object* v_xs_1158_, lean_object* v_numArgs_1159_, lean_object* v_f_1160_, lean_object* v_ys_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_array_get_size(v_xs_1158_);
v___x_1169_ = lean_nat_dec_eq(v___x_1168_, v_numArgs_1159_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v_ys_1161_);
lean_dec_ref(v_xs_1158_);
v___x_1170_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1);
v___x_1171_ = l_Nat_reprFast(v_numArgs_1159_);
v___x_1172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
v___x_1173_ = l_Lean_MessageData_ofFormat(v___x_1172_);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1170_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Nat_reprFast(v___x_1168_);
v___x_1178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
v___x_1179_ = l_Lean_MessageData_ofFormat(v___x_1178_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1176_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_indentExpr(v_f_1160_);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v___x_1184_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; 
lean_dec(v_numArgs_1159_);
v___x_1186_ = l_Lean_Meta_getLocalInstances___redArg(v___y_1163_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_lctx_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v_lctx_1188_ = lean_ctor_get(v___y_1163_, 2);
v___x_1189_ = 0;
v___x_1190_ = lean_box(v___x_1189_);
v___x_1191_ = lean_box(v___x_1169_);
lean_inc_ref(v_xs_1158_);
lean_inc_ref(v_ys_1161_);
v___f_1192_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1192_, 0, v_ys_1161_);
lean_closure_set(v___f_1192_, 1, v_xs_1158_);
lean_closure_set(v___f_1192_, 2, v_f_1160_);
lean_closure_set(v___f_1192_, 3, v___x_1190_);
lean_closure_set(v___f_1192_, 4, v___x_1191_);
lean_inc_ref(v_lctx_1188_);
v___x_1193_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_1161_, v_lctx_1188_);
v___x_1194_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_1161_, v___x_1193_);
v___x_1195_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_xs_1158_, v___x_1194_);
v___x_1196_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed), 9, 4);
lean_closure_set(v___x_1196_, 0, lean_box(0));
lean_closure_set(v___x_1196_, 1, v_xs_1158_);
lean_closure_set(v___x_1196_, 2, v_ys_1161_);
lean_closure_set(v___x_1196_, 3, v___f_1192_);
v___x_1197_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v___x_1195_, v_a_1187_, v___x_1196_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1197_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec_ref(v_ys_1161_);
lean_dec_ref(v_f_1160_);
lean_dec_ref(v_xs_1158_);
v_a_1198_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1186_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1186_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object* v_xs_1206_, lean_object* v_numArgs_1207_, lean_object* v_f_1208_, lean_object* v_ys_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Meta_mkHCongrWithArity___lam__1(v_xs_1206_, v_numArgs_1207_, v_f_1208_, v_ys_1209_, v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec_ref(v_x_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object* v_numArgs_1217_, lean_object* v_f_1218_, lean_object* v_a_1219_, lean_object* v___x_1220_, lean_object* v_xs_1221_, lean_object* v_x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___f_1228_; uint8_t v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; 
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1228_, 0, v_xs_1221_);
lean_closure_set(v___f_1228_, 1, v_numArgs_1217_);
lean_closure_set(v___f_1228_, 2, v_f_1218_);
v___x_1229_ = 1;
v___x_1230_ = 0;
v___x_1231_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1219_, v___x_1220_, v___f_1228_, v___x_1229_, v___x_1230_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object* v_numArgs_1232_, lean_object* v_f_1233_, lean_object* v_a_1234_, lean_object* v___x_1235_, lean_object* v_xs_1236_, lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Meta_mkHCongrWithArity___lam__2(v_numArgs_1232_, v_f_1233_, v_a_1234_, v___x_1235_, v_xs_1236_, v_x_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec_ref(v_x_1237_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object* v_f_1244_, lean_object* v_numArgs_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1251_; 
lean_inc(v_a_1249_);
lean_inc_ref(v_a_1248_);
lean_inc(v_a_1247_);
lean_inc_ref(v_a_1246_);
lean_inc_ref(v_f_1244_);
v___x_1251_ = lean_infer_type(v_f_1244_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___f_1254_; uint8_t v___x_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
lean_inc(v_numArgs_1245_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_numArgs_1245_);
lean_inc_ref(v___x_1253_);
lean_inc(v_a_1252_);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1254_, 0, v_numArgs_1245_);
lean_closure_set(v___f_1254_, 1, v_f_1244_);
lean_closure_set(v___f_1254_, 2, v_a_1252_);
lean_closure_set(v___f_1254_, 3, v___x_1253_);
v___x_1255_ = 1;
v___x_1256_ = 0;
v___x_1257_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1252_, v___x_1253_, v___f_1254_, v___x_1255_, v___x_1256_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1257_;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_numArgs_1245_);
lean_dec_ref(v_f_1244_);
v_a_1258_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1251_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1251_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___boxed(lean_object* v_f_1266_, lean_object* v_numArgs_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_mkHCongrWithArity(v_f_1266_, v_numArgs_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object* v_00_u03b1_1274_, lean_object* v_msg_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(v_00_u03b1_1282_, v_msg_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object* v_as_1290_, size_t v_sz_1291_, size_t v_i_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_1290_, v_sz_1291_, v_i_1292_, v_b_1293_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object* v_as_1300_, lean_object* v_sz_1301_, lean_object* v_i_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
size_t v_sz_boxed_1309_; size_t v_i_boxed_1310_; lean_object* v_res_1311_; 
v_sz_boxed_1309_ = lean_unbox_usize(v_sz_1301_);
lean_dec(v_sz_1301_);
v_i_boxed_1310_ = lean_unbox_usize(v_i_1302_);
lean_dec(v_i_1302_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(v_as_1300_, v_sz_boxed_1309_, v_i_boxed_1310_, v_b_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_as_1300_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object* v_f_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_box(0);
lean_inc(v_a_1316_);
lean_inc_ref(v_a_1315_);
lean_inc(v_a_1314_);
lean_inc_ref(v_a_1313_);
lean_inc_ref(v_f_1312_);
v___x_1319_ = l_Lean_Meta_getFunInfo(v_f_1312_, v___x_1318_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = l_Lean_Meta_FunInfo_getArity(v_a_1320_);
lean_dec(v_a_1320_);
v___x_1322_ = l_Lean_Meta_mkHCongrWithArity(v_f_1312_, v___x_1321_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
return v___x_1322_;
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec_ref(v_f_1312_);
v_a_1323_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1319_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1319_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr___boxed(lean_object* v_f_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Meta_mkHCongr(v_f_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object* v_a_1338_, lean_object* v_as_1339_, size_t v_i_1340_, size_t v_stop_1341_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_eq(v_i_1340_, v_stop_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = lean_array_uget_borrowed(v_as_1339_, v_i_1340_);
v___x_1344_ = lean_nat_dec_eq(v_a_1338_, v___x_1343_);
if (v___x_1344_ == 0)
{
size_t v___x_1345_; size_t v___x_1346_; 
v___x_1345_ = ((size_t)1ULL);
v___x_1346_ = lean_usize_add(v_i_1340_, v___x_1345_);
v_i_1340_ = v___x_1346_;
goto _start;
}
else
{
return v___x_1344_;
}
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = 0;
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object* v_a_1349_, lean_object* v_as_1350_, lean_object* v_i_1351_, lean_object* v_stop_1352_){
_start:
{
size_t v_i_boxed_1353_; size_t v_stop_boxed_1354_; uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_i_boxed_1353_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_stop_boxed_1354_ = lean_unbox_usize(v_stop_1352_);
lean_dec(v_stop_1352_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1349_, v_as_1350_, v_i_boxed_1353_, v_stop_boxed_1354_);
lean_dec_ref(v_as_1350_);
lean_dec(v_a_1349_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object* v_as_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_array_get_size(v_as_1357_);
v___x_1361_ = lean_nat_dec_lt(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
return v___x_1361_;
}
else
{
if (v___x_1361_ == 0)
{
return v___x_1361_;
}
else
{
size_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = lean_usize_of_nat(v___x_1360_);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1358_, v_as_1357_, v___x_1362_, v___x_1363_);
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object* v_as_1365_, lean_object* v_a_1366_){
_start:
{
uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_res_1367_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_as_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_as_1365_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(lean_object* v_next_1369_, lean_object* v_upperBound_1370_, lean_object* v___x_1371_, lean_object* v_a_1372_, lean_object* v_b_1373_){
_start:
{
lean_object* v_a_1375_; uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_lt(v_a_1372_, v_upperBound_1370_);
if (v___x_1383_ == 0)
{
lean_dec(v_a_1372_);
return v_b_1373_;
}
else
{
lean_object* v___x_1384_; lean_object* v_backDeps_1385_; uint8_t v___x_1386_; 
v___x_1384_ = lean_array_fget_borrowed(v___x_1371_, v_a_1372_);
v_backDeps_1385_ = lean_ctor_get(v___x_1384_, 0);
v___x_1386_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_backDeps_1385_, v_next_1369_);
if (v___x_1386_ == 0)
{
v_a_1375_ = v_b_1373_;
goto v___jp_1374_;
}
else
{
uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1387_ = 0;
v___x_1388_ = lean_box(v___x_1387_);
v___x_1389_ = lean_array_get_borrowed(v___x_1388_, v_b_1373_, v_a_1372_);
v___x_1390_ = lean_unbox(v___x_1389_);
switch(v___x_1390_)
{
case 2:
{
lean_dec(v_a_1372_);
goto v___jp_1379_;
}
case 0:
{
lean_dec(v_a_1372_);
goto v___jp_1379_;
}
default: 
{
v_a_1375_ = v_b_1373_;
goto v___jp_1374_;
}
}
}
}
v___jp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v_a_1372_, v___x_1376_);
lean_dec(v_a_1372_);
v_a_1372_ = v___x_1377_;
v_b_1373_ = v_a_1375_;
goto _start;
}
v___jp_1379_:
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = 0;
v___x_1381_ = lean_box(v___x_1380_);
v___x_1382_ = lean_array_set(v_b_1373_, v_next_1369_, v___x_1381_);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(lean_object* v_next_1391_, lean_object* v_upperBound_1392_, lean_object* v___x_1393_, lean_object* v_a_1394_, lean_object* v_b_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1391_, v_upperBound_1392_, v___x_1393_, v_a_1394_, v_b_1395_);
lean_dec_ref(v___x_1393_);
lean_dec(v_upperBound_1392_);
lean_dec(v_next_1391_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object* v_upperBound_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, lean_object* v_a_1400_, lean_object* v_b_1401_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_lt(v_a_1400_, v_upperBound_1397_);
if (v___x_1402_ == 0)
{
lean_dec(v_a_1400_);
return v_b_1401_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_nat_add(v_a_1400_, v___x_1403_);
lean_inc(v___x_1404_);
v___x_1405_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_a_1400_, v___x_1398_, v___x_1399_, v___x_1404_, v_b_1401_);
lean_dec(v_a_1400_);
v_a_1400_ = v___x_1404_;
v_b_1401_ = v___x_1405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object* v_upperBound_1407_, lean_object* v___x_1408_, lean_object* v___x_1409_, lean_object* v_a_1410_, lean_object* v_b_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1407_, v___x_1408_, v___x_1409_, v_a_1410_, v_b_1411_);
lean_dec_ref(v___x_1409_);
lean_dec(v___x_1408_);
lean_dec(v_upperBound_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object* v_info_1413_, lean_object* v_kinds_1414_){
_start:
{
lean_object* v_paramInfo_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_paramInfo_1415_ = lean_ctor_get(v_info_1413_, 0);
v___x_1416_ = lean_array_get_size(v_paramInfo_1415_);
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v___x_1416_, v___x_1416_, v_paramInfo_1415_, v___x_1417_, v_kinds_1414_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object* v_info_1419_, lean_object* v_kinds_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_1419_, v_kinds_1420_);
lean_dec_ref(v_info_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(lean_object* v_next_1422_, lean_object* v_upperBound_1423_, lean_object* v___x_1424_, lean_object* v_inst_1425_, lean_object* v_R_1426_, lean_object* v_a_1427_, lean_object* v_b_1428_, lean_object* v_c_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1422_, v_upperBound_1423_, v___x_1424_, v_a_1427_, v_b_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(lean_object* v_next_1431_, lean_object* v_upperBound_1432_, lean_object* v___x_1433_, lean_object* v_inst_1434_, lean_object* v_R_1435_, lean_object* v_a_1436_, lean_object* v_b_1437_, lean_object* v_c_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(v_next_1431_, v_upperBound_1432_, v___x_1433_, v_inst_1434_, v_R_1435_, v_a_1436_, v_b_1437_, v_c_1438_);
lean_dec_ref(v___x_1433_);
lean_dec(v_upperBound_1432_);
lean_dec(v_next_1431_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object* v_upperBound_1440_, lean_object* v___x_1441_, lean_object* v___x_1442_, lean_object* v_inst_1443_, lean_object* v_R_1444_, lean_object* v_a_1445_, lean_object* v_b_1446_, lean_object* v_c_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1440_, v___x_1441_, v___x_1442_, v_a_1445_, v_b_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object* v_upperBound_1449_, lean_object* v___x_1450_, lean_object* v___x_1451_, lean_object* v_inst_1452_, lean_object* v_R_1453_, lean_object* v_a_1454_, lean_object* v_b_1455_, lean_object* v_c_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(v_upperBound_1449_, v___x_1450_, v___x_1451_, v_inst_1452_, v_R_1453_, v_a_1454_, v_b_1455_, v_c_1456_);
lean_dec_ref(v___x_1451_);
lean_dec(v___x_1450_);
lean_dec(v_upperBound_1449_);
return v_res_1457_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object* v_as_1458_, size_t v_i_1459_, size_t v_stop_1460_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_usize_dec_eq(v_i_1459_, v_stop_1460_);
if (v___x_1461_ == 0)
{
uint8_t v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1462_ = 1;
v___x_1463_ = lean_array_uget_borrowed(v_as_1458_, v_i_1459_);
v___x_1464_ = lean_unbox(v___x_1463_);
switch(v___x_1464_)
{
case 3:
{
return v___x_1462_;
}
case 5:
{
return v___x_1462_;
}
default: 
{
if (v___x_1461_ == 0)
{
size_t v___x_1465_; size_t v___x_1466_; 
v___x_1465_ = ((size_t)1ULL);
v___x_1466_ = lean_usize_add(v_i_1459_, v___x_1465_);
v_i_1459_ = v___x_1466_;
goto _start;
}
else
{
return v___x_1462_;
}
}
}
}
else
{
uint8_t v___x_1468_; 
v___x_1468_ = 0;
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object* v_as_1469_, lean_object* v_i_1470_, lean_object* v_stop_1471_){
_start:
{
size_t v_i_boxed_1472_; size_t v_stop_boxed_1473_; uint8_t v_res_1474_; lean_object* v_r_1475_; 
v_i_boxed_1472_ = lean_unbox_usize(v_i_1470_);
lean_dec(v_i_1470_);
v_stop_boxed_1473_ = lean_unbox_usize(v_stop_1471_);
lean_dec(v_stop_1471_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_as_1469_, v_i_boxed_1472_, v_stop_boxed_1473_);
lean_dec_ref(v_as_1469_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object* v_kinds_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_array_get_size(v_kinds_1476_);
v___x_1479_ = lean_nat_dec_lt(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
return v___x_1479_;
}
else
{
if (v___x_1479_ == 0)
{
return v___x_1479_;
}
else
{
size_t v___x_1480_; size_t v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = ((size_t)0ULL);
v___x_1481_ = lean_usize_of_nat(v___x_1478_);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_kinds_1476_, v___x_1480_, v___x_1481_);
return v___x_1482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object* v_kinds_1483_){
_start:
{
uint8_t v_res_1484_; lean_object* v_r_1485_; 
v_res_1484_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_1483_);
lean_dec_ref(v_kinds_1483_);
v_r_1485_ = lean_box(v_res_1484_);
return v_r_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object* v___x_1486_, lean_object* v_k_1487_, lean_object* v_xs_1488_, lean_object* v_type_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_array_get_borrowed(v___x_1486_, v_xs_1488_, v___x_1495_);
lean_inc(v___x_1496_);
v___x_1497_ = lean_apply_7(v_k_1487_, v___x_1496_, v_type_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, lean_box(0));
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object* v___x_1498_, lean_object* v_k_1499_, lean_object* v_xs_1500_, lean_object* v_type_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(v___x_1498_, v_k_1499_, v_xs_1500_, v_type_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec_ref(v_xs_1500_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object* v_type_1508_, lean_object* v_k_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___f_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; 
v___x_1515_ = l_Lean_instInhabitedExpr;
v___f_1516_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1516_, 0, v___x_1515_);
lean_closure_set(v___f_1516_, 1, v_k_1509_);
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_1518_ = 1;
v___x_1519_ = 0;
v___x_1520_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_1508_, v___x_1517_, v___f_1516_, v___x_1518_, v___x_1519_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(lean_object* v_type_1521_, lean_object* v_k_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1521_, v_k_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object* v_00_u03b1_1529_, lean_object* v_type_1530_, lean_object* v_k_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1530_, v_k_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(lean_object* v_00_u03b1_1538_, lean_object* v_type_1539_, lean_object* v_k_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(v_00_u03b1_1538_, v_type_1539_, v_k_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object* v_kinds_1550_, uint8_t v___x_1551_, lean_object* v_as_1552_, size_t v_sz_1553_, size_t v_i_1554_, lean_object* v_b_1555_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = lean_usize_dec_lt(v_i_1554_, v_sz_1553_);
if (v___x_1556_ == 0)
{
return v_b_1555_;
}
else
{
lean_object* v___x_1557_; lean_object* v_a_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
lean_dec_ref(v_b_1555_);
v___x_1557_ = lean_box(0);
v_a_1558_ = lean_array_uget_borrowed(v_as_1552_, v_i_1554_);
v___x_1559_ = 0;
v___x_1560_ = lean_box(v___x_1559_);
v___x_1561_ = lean_array_get_borrowed(v___x_1560_, v_kinds_1550_, v_a_1558_);
v___x_1562_ = lean_unbox(v___x_1561_);
if (v___x_1562_ == 2)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_box(v___x_1551_);
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1557_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; size_t v___x_1567_; size_t v___x_1568_; 
v___x_1566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_add(v_i_1554_, v___x_1567_);
v_i_1554_ = v___x_1568_;
v_b_1555_ = v___x_1566_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object* v_kinds_1570_, lean_object* v___x_1571_, lean_object* v_as_1572_, lean_object* v_sz_1573_, lean_object* v_i_1574_, lean_object* v_b_1575_){
_start:
{
uint8_t v___x_661__boxed_1576_; size_t v_sz_boxed_1577_; size_t v_i_boxed_1578_; lean_object* v_res_1579_; 
v___x_661__boxed_1576_ = lean_unbox(v___x_1571_);
v_sz_boxed_1577_ = lean_unbox_usize(v_sz_1573_);
lean_dec(v_sz_1573_);
v_i_boxed_1578_ = lean_unbox_usize(v_i_1574_);
lean_dec(v_i_1574_);
v_res_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1570_, v___x_661__boxed_1576_, v_as_1572_, v_sz_boxed_1577_, v_i_boxed_1578_, v_b_1575_);
lean_dec_ref(v_as_1572_);
lean_dec_ref(v_kinds_1570_);
return v_res_1579_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object* v_info_1580_, lean_object* v_kinds_1581_, lean_object* v_i_1582_){
_start:
{
lean_object* v_paramInfo_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v_isDecInst_1586_; 
v_paramInfo_1583_ = lean_ctor_get(v_info_1580_, 0);
v___x_1584_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_1585_ = lean_array_get_borrowed(v___x_1584_, v_paramInfo_1583_, v_i_1582_);
v_isDecInst_1586_ = lean_ctor_get_uint8(v___x_1585_, sizeof(void*)*1 + 3);
if (v_isDecInst_1586_ == 0)
{
return v_isDecInst_1586_;
}
else
{
lean_object* v_backDeps_1587_; lean_object* v___x_1588_; size_t v_sz_1589_; size_t v___x_1590_; lean_object* v___x_1591_; lean_object* v_fst_1592_; 
v_backDeps_1587_ = lean_ctor_get(v___x_1585_, 0);
v___x_1588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v_sz_1589_ = lean_array_size(v_backDeps_1587_);
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1581_, v_isDecInst_1586_, v_backDeps_1587_, v_sz_1589_, v___x_1590_, v___x_1588_);
v_fst_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_fst_1592_);
lean_dec_ref(v___x_1591_);
if (lean_obj_tag(v_fst_1592_) == 0)
{
uint8_t v___x_1593_; 
v___x_1593_ = 0;
return v___x_1593_;
}
else
{
lean_object* v_val_1594_; uint8_t v___x_1595_; 
v_val_1594_ = lean_ctor_get(v_fst_1592_, 0);
lean_inc(v_val_1594_);
lean_dec_ref(v_fst_1592_);
v___x_1595_ = lean_unbox(v_val_1594_);
lean_dec(v_val_1594_);
return v___x_1595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object* v_info_1596_, lean_object* v_kinds_1597_, lean_object* v_i_1598_){
_start:
{
uint8_t v_res_1599_; lean_object* v_r_1600_; 
v_res_1599_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_1596_, v_kinds_1597_, v_i_1598_);
lean_dec(v_i_1598_);
lean_dec_ref(v_kinds_1597_);
lean_dec_ref(v_info_1596_);
v_r_1600_ = lean_box(v_res_1599_);
return v_r_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(lean_object* v_type_1601_, lean_object* v_k_1602_, uint8_t v_cleanupAnnotations_1603_, uint8_t v_whnfType_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___f_1610_; lean_object* v___x_1611_; 
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1610_, 0, v_k_1602_);
v___x_1611_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1601_, v___f_1610_, v_cleanupAnnotations_1603_, v_whnfType_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1620_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1611_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1611_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(lean_object* v_type_1628_, lean_object* v_k_1629_, lean_object* v_cleanupAnnotations_1630_, lean_object* v_whnfType_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1637_; uint8_t v_whnfType_boxed_1638_; lean_object* v_res_1639_; 
v_cleanupAnnotations_boxed_1637_ = lean_unbox(v_cleanupAnnotations_1630_);
v_whnfType_boxed_1638_ = lean_unbox(v_whnfType_1631_);
v_res_1639_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1628_, v_k_1629_, v_cleanupAnnotations_boxed_1637_, v_whnfType_boxed_1638_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_object* v_00_u03b1_1640_, lean_object* v_type_1641_, lean_object* v_k_1642_, uint8_t v_cleanupAnnotations_1643_, uint8_t v_whnfType_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1641_, v_k_1642_, v_cleanupAnnotations_1643_, v_whnfType_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_type_1652_, lean_object* v_k_1653_, lean_object* v_cleanupAnnotations_1654_, lean_object* v_whnfType_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1661_; uint8_t v_whnfType_boxed_1662_; lean_object* v_res_1663_; 
v_cleanupAnnotations_boxed_1661_ = lean_unbox(v_cleanupAnnotations_1654_);
v_whnfType_boxed_1662_ = lean_unbox(v_whnfType_1655_);
v_res_1663_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(v_00_u03b1_1651_, v_type_1652_, v_k_1653_, v_cleanupAnnotations_boxed_1661_, v_whnfType_boxed_1662_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(lean_object* v_upperBound_1664_, lean_object* v_val_1665_, lean_object* v_xs_1666_, lean_object* v___x_1667_, lean_object* v___x_1668_, uint8_t v___x_1669_, lean_object* v_a_1670_, lean_object* v_b_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_a_1677_; uint8_t v___x_1681_; 
v___x_1681_ = lean_nat_dec_lt(v_a_1670_, v_upperBound_1664_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref(v___y_1672_);
lean_dec(v_a_1670_);
lean_dec(v___x_1668_);
lean_dec_ref(v___x_1667_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_b_1671_);
return v___x_1682_;
}
else
{
lean_object* v_numParams_1683_; uint8_t v___x_1684_; 
v_numParams_1683_ = lean_ctor_get(v_val_1665_, 3);
v___x_1684_ = lean_nat_dec_lt(v_a_1670_, v_numParams_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_array_fget_borrowed(v_xs_1666_, v_a_1670_);
v___x_1686_ = l_Lean_Expr_fvarId_x21(v___x_1685_);
lean_inc_ref(v___y_1672_);
v___x_1687_ = l_Lean_FVarId_getDecl___redArg(v___x_1686_, v___y_1672_, v___y_1673_, v___y_1674_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; uint8_t v___y_1690_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1687_);
v___x_1693_ = l_Lean_LocalDecl_userName(v_a_1688_);
lean_dec(v_a_1688_);
lean_inc(v___x_1668_);
lean_inc_ref(v___x_1667_);
v___x_1694_ = l_Lean_isSubobjectField_x3f(v___x_1667_, v___x_1668_, v___x_1693_);
if (lean_obj_tag(v___x_1694_) == 0)
{
v___y_1690_ = v___x_1684_;
goto v___jp_1689_;
}
else
{
lean_dec_ref(v___x_1694_);
v___y_1690_ = v___x_1669_;
goto v___jp_1689_;
}
v___jp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_box(v___y_1690_);
v___x_1692_ = lean_array_push(v_b_1671_, v___x_1691_);
v_a_1677_ = v___x_1692_;
goto v___jp_1676_;
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v___y_1672_);
lean_dec_ref(v_b_1671_);
lean_dec(v_a_1670_);
lean_dec(v___x_1668_);
lean_dec_ref(v___x_1667_);
v_a_1695_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1687_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1687_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = 0;
v___x_1704_ = lean_box(v___x_1703_);
v___x_1705_ = lean_array_push(v_b_1671_, v___x_1704_);
v_a_1677_ = v___x_1705_;
goto v___jp_1676_;
}
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_unsigned_to_nat(1u);
v___x_1679_ = lean_nat_add(v_a_1670_, v___x_1678_);
lean_dec(v_a_1670_);
v_a_1670_ = v___x_1679_;
v_b_1671_ = v_a_1677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_1706_, lean_object* v_val_1707_, lean_object* v_xs_1708_, lean_object* v___x_1709_, lean_object* v___x_1710_, lean_object* v___x_1711_, lean_object* v_a_1712_, lean_object* v_b_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v___x_5875__boxed_1718_; lean_object* v_res_1719_; 
v___x_5875__boxed_1718_ = lean_unbox(v___x_1711_);
v_res_1719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1706_, v_val_1707_, v_xs_1708_, v___x_1709_, v___x_1710_, v___x_5875__boxed_1718_, v_a_1712_, v_b_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec_ref(v_xs_1708_);
lean_dec_ref(v_val_1707_);
lean_dec(v_upperBound_1706_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object* v_val_1722_, lean_object* v_induct_1723_, uint8_t v___x_1724_, lean_object* v_xs_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; lean_object* v_env_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1732_ = lean_st_ref_get(v___y_1730_);
v_env_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc_ref(v_env_1733_);
lean_dec(v___x_1732_);
v___x_1734_ = lean_array_get_size(v_xs_1725_);
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0));
v___x_1737_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v___x_1734_, v_val_1722_, v_xs_1725_, v_env_1733_, v_induct_1723_, v___x_1724_, v___x_1735_, v___x_1736_, v___y_1727_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1746_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_a_1738_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1742_);
v___x_1744_ = v___x_1740_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1737_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1737_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object* v_val_1755_, lean_object* v_induct_1756_, lean_object* v___x_1757_, lean_object* v_xs_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
uint8_t v___x_5962__boxed_1765_; lean_object* v_res_1766_; 
v___x_5962__boxed_1765_ = lean_unbox(v___x_1757_);
v_res_1766_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1755_, v_induct_1756_, v___x_5962__boxed_1765_, v_xs_1758_, v_x_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v_x_1759_);
lean_dec_ref(v_xs_1758_);
lean_dec_ref(v_val_1755_);
return v_res_1766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
lean_ctor_set(v___x_1772_, 2, v___x_1771_);
lean_ctor_set(v___x_1772_, 3, v___x_1770_);
lean_ctor_set(v___x_1772_, 4, v___x_1770_);
lean_ctor_set(v___x_1772_, 5, v___x_1770_);
lean_ctor_set(v___x_1772_, 6, v___x_1770_);
lean_ctor_set(v___x_1772_, 7, v___x_1770_);
lean_ctor_set(v___x_1772_, 8, v___x_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_unsigned_to_nat(32u);
v___x_1774_ = lean_mk_empty_array_with_capacity(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1776_ = ((size_t)5ULL);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = lean_unsigned_to_nat(32u);
v___x_1779_ = lean_mk_empty_array_with_capacity(v___x_1778_);
v___x_1780_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1781_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___x_1779_);
lean_ctor_set(v___x_1781_, 2, v___x_1777_);
lean_ctor_set(v___x_1781_, 3, v___x_1777_);
lean_ctor_set_usize(v___x_1781_, 4, v___x_1776_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1782_ = lean_box(1);
v___x_1783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1784_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1783_);
lean_ctor_set(v___x_1785_, 2, v___x_1782_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1806_ = l_Lean_stringToMessageData(v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1807_, lean_object* v_declHint_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v_env_1812_; uint8_t v___x_1813_; 
v___x_1811_ = lean_st_ref_get(v___y_1809_);
v_env_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc_ref(v_env_1812_);
lean_dec(v___x_1811_);
v___x_1813_ = l_Lean_Name_isAnonymous(v_declHint_1808_);
if (v___x_1813_ == 0)
{
uint8_t v_isExporting_1814_; 
v_isExporting_1814_ = lean_ctor_get_uint8(v_env_1812_, sizeof(void*)*8);
if (v_isExporting_1814_ == 0)
{
lean_object* v___x_1815_; 
lean_dec_ref(v_env_1812_);
lean_dec(v_declHint_1808_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_msg_1807_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
lean_inc_ref(v_env_1812_);
v___x_1816_ = l_Lean_Environment_setExporting(v_env_1812_, v___x_1813_);
lean_inc(v_declHint_1808_);
lean_inc_ref(v___x_1816_);
v___x_1817_ = l_Lean_Environment_contains(v___x_1816_, v_declHint_1808_, v_isExporting_1814_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec_ref(v___x_1816_);
lean_dec_ref(v_env_1812_);
lean_dec(v_declHint_1808_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_msg_1807_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_c_1824_; lean_object* v___x_1825_; 
v___x_1819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1820_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1821_ = l_Lean_Options_empty;
v___x_1822_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1816_);
lean_ctor_set(v___x_1822_, 1, v___x_1819_);
lean_ctor_set(v___x_1822_, 2, v___x_1820_);
lean_ctor_set(v___x_1822_, 3, v___x_1821_);
lean_inc(v_declHint_1808_);
v___x_1823_ = l_Lean_MessageData_ofConstName(v_declHint_1808_, v___x_1813_);
v_c_1824_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1824_, 0, v___x_1822_);
lean_ctor_set(v_c_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1812_, v_declHint_1808_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v_env_1812_);
lean_dec(v_declHint_1808_);
v___x_1826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v_c_1824_);
v___x_1828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = l_Lean_MessageData_note(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v_msg_1807_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
else
{
lean_object* v_val_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1868_; 
v_val_1833_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1835_ = v___x_1825_;
v_isShared_1836_ = v_isSharedCheck_1868_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_val_1833_);
lean_dec(v___x_1825_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1868_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v_mod_1840_; uint8_t v___x_1841_; 
v___x_1837_ = lean_box(0);
v___x_1838_ = l_Lean_Environment_header(v_env_1812_);
lean_dec_ref(v_env_1812_);
v___x_1839_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1838_);
v_mod_1840_ = lean_array_get(v___x_1837_, v___x_1839_, v_val_1833_);
lean_dec(v_val_1833_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = l_Lean_isPrivateName(v_declHint_1808_);
lean_dec(v_declHint_1808_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v_c_1824_);
v___x_1844_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = l_Lean_MessageData_ofName(v_mod_1840_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_MessageData_note(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v_msg_1807_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1851_);
v___x_1853_ = v___x_1835_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v_c_1824_);
v___x_1857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_MessageData_ofName(v_mod_1840_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_MessageData_note(v___x_1862_);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_msg_1807_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1864_);
v___x_1866_ = v___x_1835_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1869_; 
lean_dec_ref(v_env_1812_);
lean_dec(v_declHint_1808_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_msg_1807_);
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1870_, lean_object* v_declHint_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1870_, v_declHint_1871_, v___y_1872_);
lean_dec(v___y_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msg_1875_, lean_object* v_declHint_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1892_; 
v___x_1882_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1875_, v_declHint_1876_, v___y_1880_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = l_Lean_unknownIdentifierMessageTag;
v___x_1888_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_a_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1893_, lean_object* v_declHint_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1893_, v_declHint_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1901_, lean_object* v_msg_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_fileName_1908_; lean_object* v_fileMap_1909_; lean_object* v_options_1910_; lean_object* v_currRecDepth_1911_; lean_object* v_maxRecDepth_1912_; lean_object* v_ref_1913_; lean_object* v_currNamespace_1914_; lean_object* v_openDecls_1915_; lean_object* v_initHeartbeats_1916_; lean_object* v_maxHeartbeats_1917_; lean_object* v_quotContext_1918_; lean_object* v_currMacroScope_1919_; uint8_t v_diag_1920_; lean_object* v_cancelTk_x3f_1921_; uint8_t v_suppressElabErrors_1922_; lean_object* v_inheritedTraceOptions_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1932_; 
v_fileName_1908_ = lean_ctor_get(v___y_1905_, 0);
v_fileMap_1909_ = lean_ctor_get(v___y_1905_, 1);
v_options_1910_ = lean_ctor_get(v___y_1905_, 2);
v_currRecDepth_1911_ = lean_ctor_get(v___y_1905_, 3);
v_maxRecDepth_1912_ = lean_ctor_get(v___y_1905_, 4);
v_ref_1913_ = lean_ctor_get(v___y_1905_, 5);
v_currNamespace_1914_ = lean_ctor_get(v___y_1905_, 6);
v_openDecls_1915_ = lean_ctor_get(v___y_1905_, 7);
v_initHeartbeats_1916_ = lean_ctor_get(v___y_1905_, 8);
v_maxHeartbeats_1917_ = lean_ctor_get(v___y_1905_, 9);
v_quotContext_1918_ = lean_ctor_get(v___y_1905_, 10);
v_currMacroScope_1919_ = lean_ctor_get(v___y_1905_, 11);
v_diag_1920_ = lean_ctor_get_uint8(v___y_1905_, sizeof(void*)*14);
v_cancelTk_x3f_1921_ = lean_ctor_get(v___y_1905_, 12);
v_suppressElabErrors_1922_ = lean_ctor_get_uint8(v___y_1905_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1923_ = lean_ctor_get(v___y_1905_, 13);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___y_1905_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1925_ = v___y_1905_;
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_inheritedTraceOptions_1923_);
lean_inc(v_cancelTk_x3f_1921_);
lean_inc(v_currMacroScope_1919_);
lean_inc(v_quotContext_1918_);
lean_inc(v_maxHeartbeats_1917_);
lean_inc(v_initHeartbeats_1916_);
lean_inc(v_openDecls_1915_);
lean_inc(v_currNamespace_1914_);
lean_inc(v_ref_1913_);
lean_inc(v_maxRecDepth_1912_);
lean_inc(v_currRecDepth_1911_);
lean_inc(v_options_1910_);
lean_inc(v_fileMap_1909_);
lean_inc(v_fileName_1908_);
lean_dec(v___y_1905_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v_ref_1927_; lean_object* v___x_1929_; 
v_ref_1927_ = l_Lean_replaceRef(v_ref_1901_, v_ref_1913_);
lean_dec(v_ref_1913_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 5, v_ref_1927_);
v___x_1929_ = v___x_1925_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_fileName_1908_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_fileMap_1909_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_options_1910_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_currRecDepth_1911_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_maxRecDepth_1912_);
lean_ctor_set(v_reuseFailAlloc_1931_, 5, v_ref_1927_);
lean_ctor_set(v_reuseFailAlloc_1931_, 6, v_currNamespace_1914_);
lean_ctor_set(v_reuseFailAlloc_1931_, 7, v_openDecls_1915_);
lean_ctor_set(v_reuseFailAlloc_1931_, 8, v_initHeartbeats_1916_);
lean_ctor_set(v_reuseFailAlloc_1931_, 9, v_maxHeartbeats_1917_);
lean_ctor_set(v_reuseFailAlloc_1931_, 10, v_quotContext_1918_);
lean_ctor_set(v_reuseFailAlloc_1931_, 11, v_currMacroScope_1919_);
lean_ctor_set(v_reuseFailAlloc_1931_, 12, v_cancelTk_x3f_1921_);
lean_ctor_set(v_reuseFailAlloc_1931_, 13, v_inheritedTraceOptions_1923_);
lean_ctor_set_uint8(v_reuseFailAlloc_1931_, sizeof(void*)*14, v_diag_1920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1931_, sizeof(void*)*14 + 1, v_suppressElabErrors_1922_);
v___x_1929_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1902_, v___y_1903_, v___y_1904_, v___x_1929_, v___y_1906_);
lean_dec_ref(v___x_1929_);
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1933_, lean_object* v_msg_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1933_, v_msg_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v_ref_1933_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1941_, lean_object* v_msg_1942_, lean_object* v_declHint_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1951_; 
v___x_1949_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1942_, v_declHint_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1941_, v_a_1950_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1952_, lean_object* v_msg_1953_, lean_object* v_declHint_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1952_, v_msg_1953_, v_declHint_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v_ref_1952_);
return v_res_1960_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1963_ = l_Lean_stringToMessageData(v___x_1962_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1967_, lean_object* v_constName_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1974_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1975_ = 0;
lean_inc(v_constName_1968_);
v___x_1976_ = l_Lean_MessageData_ofConstName(v_constName_1968_, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1974_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1967_, v___x_1979_, v_constName_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1981_, lean_object* v_constName_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1981_, v_constName_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v_ref_1981_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_ref_1995_; lean_object* v___x_1996_; 
v_ref_1995_ = lean_ctor_get(v___y_1992_, 5);
lean_inc(v_ref_1995_);
v___x_1996_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1995_, v_constName_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v_ref_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; lean_object* v_env_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; 
v___x_2010_ = lean_st_ref_get(v___y_2008_);
v_env_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc_ref(v_env_2011_);
lean_dec(v___x_2010_);
v___x_2012_ = 0;
lean_inc(v_constName_2004_);
v___x_2013_ = l_Lean_Environment_find_x3f(v_env_2011_, v_constName_2004_, v___x_2012_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2014_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v___y_2007_);
lean_dec(v_constName_2004_);
v_val_2015_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2013_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v___x_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 0);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_val_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
if (lean_obj_tag(v_f_2030_) == 4)
{
lean_object* v_declName_2036_; lean_object* v___x_2037_; 
v_declName_2036_ = lean_ctor_get(v_f_2030_, 0);
lean_inc(v_declName_2036_);
lean_dec_ref(v_f_2030_);
lean_inc_ref(v_a_2033_);
v___x_2037_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2036_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2061_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2061_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2061_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
if (lean_obj_tag(v_a_2038_) == 6)
{
lean_object* v_val_2042_; lean_object* v___x_2043_; lean_object* v_env_2044_; lean_object* v_toConstantVal_2045_; lean_object* v_induct_2046_; uint8_t v___x_2047_; 
v_val_2042_ = lean_ctor_get(v_a_2038_, 0);
lean_inc_ref(v_val_2042_);
lean_dec_ref(v_a_2038_);
v___x_2043_ = lean_st_ref_get(v_a_2034_);
v_env_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_ref(v_env_2044_);
lean_dec(v___x_2043_);
v_toConstantVal_2045_ = lean_ctor_get(v_val_2042_, 0);
v_induct_2046_ = lean_ctor_get(v_val_2042_, 1);
lean_inc(v_induct_2046_);
lean_inc(v_induct_2046_);
v___x_2047_ = lean_is_class(v_env_2044_, v_induct_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
lean_dec(v_induct_2046_);
lean_dec_ref(v_val_2042_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
v___x_2048_ = lean_box(0);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2048_);
v___x_2050_ = v___x_2040_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
else
{
lean_object* v_type_2052_; lean_object* v___x_2053_; lean_object* v___f_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; 
lean_del_object(v___x_2040_);
v_type_2052_ = lean_ctor_get(v_toConstantVal_2045_, 2);
lean_inc_ref(v_type_2052_);
v___x_2053_ = lean_box(v___x_2047_);
v___f_2054_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2054_, 0, v_val_2042_);
lean_closure_set(v___f_2054_, 1, v_induct_2046_);
lean_closure_set(v___f_2054_, 2, v___x_2053_);
v___x_2055_ = 0;
v___x_2056_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2052_, v___f_2054_, v___x_2047_, v___x_2055_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
return v___x_2056_;
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_dec(v_a_2038_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
v___x_2057_ = lean_box(0);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2057_);
v___x_2059_ = v___x_2040_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
v_a_2062_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2037_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2037_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
lean_dec_ref(v_f_2030_);
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2079_, lean_object* v_val_2080_, lean_object* v_xs_2081_, lean_object* v___x_2082_, lean_object* v___x_2083_, uint8_t v___x_2084_, lean_object* v_inst_2085_, lean_object* v_R_2086_, lean_object* v_a_2087_, lean_object* v_b_2088_, lean_object* v_c_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2079_, v_val_2080_, v_xs_2081_, v___x_2082_, v___x_2083_, v___x_2084_, v_a_2087_, v_b_2088_, v___y_2090_, v___y_2092_, v___y_2093_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2096_, lean_object* v_val_2097_, lean_object* v_xs_2098_, lean_object* v___x_2099_, lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v_inst_2102_, lean_object* v_R_2103_, lean_object* v_a_2104_, lean_object* v_b_2105_, lean_object* v_c_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
uint8_t v___x_6564__boxed_2112_; lean_object* v_res_2113_; 
v___x_6564__boxed_2112_ = lean_unbox(v___x_2101_);
v_res_2113_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2096_, v_val_2097_, v_xs_2098_, v___x_2099_, v___x_2100_, v___x_6564__boxed_2112_, v_inst_2102_, v_R_2103_, v_a_2104_, v_b_2105_, v_c_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v_xs_2098_);
lean_dec_ref(v_val_2097_);
lean_dec(v_upperBound_2096_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2114_, lean_object* v_constName_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2122_, lean_object* v_constName_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2122_, v_constName_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2130_, lean_object* v_ref_2131_, lean_object* v_constName_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2131_, v_constName_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_ref_2140_, lean_object* v_constName_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2139_, v_ref_2140_, v_constName_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v_ref_2140_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2148_, lean_object* v_ref_2149_, lean_object* v_msg_2150_, lean_object* v_declHint_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2149_, v_msg_2150_, v_declHint_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2158_, lean_object* v_ref_2159_, lean_object* v_msg_2160_, lean_object* v_declHint_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2158_, v_ref_2159_, v_msg_2160_, v_declHint_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v_ref_2159_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2168_, lean_object* v_declHint_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2168_, v_declHint_2169_, v___y_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2176_, lean_object* v_declHint_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2176_, v_declHint_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2184_, lean_object* v_ref_2185_, lean_object* v_msg_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2185_, v_msg_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2193_, lean_object* v_ref_2194_, lean_object* v_msg_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2193_, v_ref_2194_, v_msg_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v_ref_2194_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2202_, lean_object* v_a_2203_, lean_object* v_____r_2204_, lean_object* v_result_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
uint8_t v___x_2211_; 
v___x_2211_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2202_, v_result_2205_, v_a_2203_);
if (v___x_2211_ == 0)
{
uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2212_ = 0;
v___x_2213_ = lean_box(v___x_2212_);
v___x_2214_ = lean_array_push(v_result_2205_, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
else
{
uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2217_ = 5;
v___x_2218_ = lean_box(v___x_2217_);
v___x_2219_ = lean_array_push(v_result_2205_, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2222_, lean_object* v_a_2223_, lean_object* v_____r_2224_, lean_object* v_result_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2222_, v_a_2223_, v_____r_2224_, v_result_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v_a_2223_);
lean_dec_ref(v_info_2222_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2232_, lean_object* v_upperBound_2233_, lean_object* v___x_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_a_2244_; lean_object* v___y_2249_; uint8_t v___x_2268_; 
v___x_2268_ = lean_nat_dec_lt(v_a_2236_, v_upperBound_2233_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_dec(v_a_2236_);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_b_2237_);
return v___x_2269_;
}
else
{
lean_object* v_resultDeps_2270_; uint8_t v___x_2271_; 
v_resultDeps_2270_ = lean_ctor_get(v_info_2232_, 1);
v___x_2271_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2270_, v_a_2236_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; uint8_t v_isProp_2273_; 
v___x_2272_ = lean_array_fget_borrowed(v___x_2234_, v_a_2236_);
v_isProp_2273_ = lean_ctor_get_uint8(v___x_2272_, sizeof(void*)*1 + 2);
if (v_isProp_2273_ == 0)
{
uint8_t v_isInstance_2274_; 
v_isInstance_2274_ = lean_ctor_get_uint8(v___x_2272_, sizeof(void*)*1 + 4);
if (v_isInstance_2274_ == 0)
{
uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = 2;
v___x_2276_ = lean_box(v___x_2275_);
v___x_2277_ = lean_array_push(v_b_2237_, v___x_2276_);
v_a_2244_ = v___x_2277_;
goto v___jp_2243_;
}
else
{
if (lean_obj_tag(v_a_2235_) == 1)
{
lean_object* v_val_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_val_2278_ = lean_ctor_get(v_a_2235_, 0);
v___x_2279_ = lean_array_get_size(v_val_2278_);
v___x_2280_ = lean_nat_dec_lt(v_a_2236_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_box(0);
v___x_2282_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2232_, v_a_2236_, v___x_2281_, v_b_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
v___y_2249_ = v___x_2282_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = lean_array_fget_borrowed(v_val_2278_, v_a_2236_);
v___x_2284_ = lean_unbox(v___x_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_box(0);
v___x_2286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2232_, v_a_2236_, v___x_2285_, v_b_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
v___y_2249_ = v___x_2286_;
goto v___jp_2248_;
}
else
{
uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = 2;
v___x_2288_ = lean_box(v___x_2287_);
v___x_2289_ = lean_array_push(v_b_2237_, v___x_2288_);
v_a_2244_ = v___x_2289_;
goto v___jp_2243_;
}
}
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_box(0);
v___x_2291_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2232_, v_a_2236_, v___x_2290_, v_b_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
v___y_2249_ = v___x_2291_;
goto v___jp_2248_;
}
}
}
else
{
uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = 3;
v___x_2293_ = lean_box(v___x_2292_);
v___x_2294_ = lean_array_push(v_b_2237_, v___x_2293_);
v_a_2244_ = v___x_2294_;
goto v___jp_2243_;
}
}
else
{
uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = 0;
v___x_2296_ = lean_box(v___x_2295_);
v___x_2297_ = lean_array_push(v_b_2237_, v___x_2296_);
v_a_2244_ = v___x_2297_;
goto v___jp_2243_;
}
}
v___jp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_a_2236_, v___x_2245_);
lean_dec(v_a_2236_);
v_a_2236_ = v___x_2246_;
v_b_2237_ = v_a_2244_;
goto _start;
}
v___jp_2248_:
{
if (lean_obj_tag(v___y_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2259_; 
v_a_2250_ = lean_ctor_get(v___y_2249_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___y_2249_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2252_ = v___y_2249_;
v_isShared_2253_ = v_isSharedCheck_2259_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___y_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2259_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
if (lean_obj_tag(v_a_2250_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; 
lean_dec(v_a_2236_);
v_a_2254_ = lean_ctor_get(v_a_2250_, 0);
lean_inc(v_a_2254_);
lean_dec_ref(v_a_2250_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_a_2254_);
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
else
{
lean_object* v_a_2258_; 
lean_del_object(v___x_2252_);
v_a_2258_ = lean_ctor_get(v_a_2250_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v_a_2250_);
v_a_2244_ = v_a_2258_;
goto v___jp_2243_;
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_a_2236_);
v_a_2260_ = lean_ctor_get(v___y_2249_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___y_2249_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___y_2249_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___y_2249_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2298_, lean_object* v_upperBound_2299_, lean_object* v___x_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_b_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2298_, v_upperBound_2299_, v___x_2300_, v_a_2301_, v_a_2302_, v_b_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v_a_2301_);
lean_dec_ref(v___x_2300_);
lean_dec(v_upperBound_2299_);
lean_dec_ref(v_info_2298_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2312_, lean_object* v_info_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2319_; 
lean_inc(v_a_2317_);
lean_inc_ref(v_a_2316_);
lean_inc(v_a_2315_);
lean_inc_ref(v_a_2314_);
v___x_2319_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2312_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v_paramInfo_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_result_2324_; lean_object* v___x_2325_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2319_);
v_paramInfo_2321_ = lean_ctor_get(v_info_2313_, 0);
v___x_2322_ = lean_array_get_size(v_paramInfo_2321_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v_result_2324_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2313_, v___x_2322_, v_paramInfo_2321_, v_a_2320_, v___x_2323_, v_result_2324_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2320_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2313_, v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
else
{
return v___x_2325_;
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
v_a_2335_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2319_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2319_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2343_, lean_object* v_info_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Meta_getCongrSimpKinds(v_f_2343_, v_info_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
lean_dec_ref(v_info_2344_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2351_, lean_object* v_upperBound_2352_, lean_object* v___x_2353_, lean_object* v_a_2354_, lean_object* v_inst_2355_, lean_object* v_R_2356_, lean_object* v_a_2357_, lean_object* v_b_2358_, lean_object* v_c_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2351_, v_upperBound_2352_, v___x_2353_, v_a_2354_, v_a_2357_, v_b_2358_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2366_, lean_object* v_upperBound_2367_, lean_object* v___x_2368_, lean_object* v_a_2369_, lean_object* v_inst_2370_, lean_object* v_R_2371_, lean_object* v_a_2372_, lean_object* v_b_2373_, lean_object* v_c_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2366_, v_upperBound_2367_, v___x_2368_, v_a_2369_, v_inst_2370_, v_R_2371_, v_a_2372_, v_b_2373_, v_c_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v_a_2369_);
lean_dec_ref(v___x_2368_);
lean_dec(v_upperBound_2367_);
lean_dec_ref(v_info_2366_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2381_, lean_object* v_info_2382_, lean_object* v___x_2383_, lean_object* v_a_2384_, lean_object* v_b_2385_){
_start:
{
lean_object* v_a_2388_; uint8_t v___x_2392_; 
v___x_2392_ = lean_nat_dec_lt(v_a_2384_, v_upperBound_2381_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec(v_a_2384_);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_b_2385_);
return v___x_2393_;
}
else
{
lean_object* v_resultDeps_2394_; uint8_t v___x_2395_; 
v_resultDeps_2394_ = lean_ctor_get(v_info_2382_, 1);
v___x_2395_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2394_, v_a_2384_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = lean_nat_dec_eq(v_a_2384_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; uint8_t v_isProp_2399_; 
v___x_2398_ = lean_array_fget_borrowed(v___x_2383_, v_a_2384_);
v_isProp_2399_ = lean_ctor_get_uint8(v___x_2398_, sizeof(void*)*1 + 2);
if (v_isProp_2399_ == 0)
{
uint8_t v_isInstance_2400_; 
v_isInstance_2400_ = lean_ctor_get_uint8(v___x_2398_, sizeof(void*)*1 + 4);
if (v_isInstance_2400_ == 0)
{
uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = 0;
v___x_2402_ = lean_box(v___x_2401_);
v___x_2403_ = lean_array_push(v_b_2385_, v___x_2402_);
v_a_2388_ = v___x_2403_;
goto v___jp_2387_;
}
else
{
uint8_t v___x_2404_; 
v___x_2404_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2382_, v_b_2385_, v_a_2384_);
if (v___x_2404_ == 0)
{
uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = 0;
v___x_2406_ = lean_box(v___x_2405_);
v___x_2407_ = lean_array_push(v_b_2385_, v___x_2406_);
v_a_2388_ = v___x_2407_;
goto v___jp_2387_;
}
else
{
uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = 5;
v___x_2409_ = lean_box(v___x_2408_);
v___x_2410_ = lean_array_push(v_b_2385_, v___x_2409_);
v_a_2388_ = v___x_2410_;
goto v___jp_2387_;
}
}
}
else
{
uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = 3;
v___x_2412_ = lean_box(v___x_2411_);
v___x_2413_ = lean_array_push(v_b_2385_, v___x_2412_);
v_a_2388_ = v___x_2413_;
goto v___jp_2387_;
}
}
else
{
uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = 2;
v___x_2415_ = lean_box(v___x_2414_);
v___x_2416_ = lean_array_push(v_b_2385_, v___x_2415_);
v_a_2388_ = v___x_2416_;
goto v___jp_2387_;
}
}
else
{
uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = 0;
v___x_2418_ = lean_box(v___x_2417_);
v___x_2419_ = lean_array_push(v_b_2385_, v___x_2418_);
v_a_2388_ = v___x_2419_;
goto v___jp_2387_;
}
}
v___jp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = lean_nat_add(v_a_2384_, v___x_2389_);
lean_dec(v_a_2384_);
v_a_2384_ = v___x_2390_;
v_b_2385_ = v_a_2388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2420_, lean_object* v_info_2421_, lean_object* v___x_2422_, lean_object* v_a_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2420_, v_info_2421_, v___x_2422_, v_a_2423_, v_b_2424_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v_info_2421_);
lean_dec(v_upperBound_2420_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_paramInfo_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_result_2436_; lean_object* v___x_2437_; 
v_paramInfo_2433_ = lean_ctor_get(v_info_2427_, 0);
v___x_2434_ = lean_array_get_size(v_paramInfo_2433_);
v___x_2435_ = lean_unsigned_to_nat(0u);
v_result_2436_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2434_, v_info_2427_, v_paramInfo_2433_, v___x_2435_, v_result_2436_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2446_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2446_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2446_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2442_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2427_, v_a_2438_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2442_);
v___x_2444_ = v___x_2440_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec_ref(v_info_2447_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2454_, lean_object* v_info_2455_, lean_object* v___x_2456_, lean_object* v_inst_2457_, lean_object* v_R_2458_, lean_object* v_a_2459_, lean_object* v_b_2460_, lean_object* v_c_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2454_, v_info_2455_, v___x_2456_, v_a_2459_, v_b_2460_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2468_, lean_object* v_info_2469_, lean_object* v___x_2470_, lean_object* v_inst_2471_, lean_object* v_R_2472_, lean_object* v_a_2473_, lean_object* v_b_2474_, lean_object* v_c_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2468_, v_info_2469_, v___x_2470_, v_inst_2471_, v_R_2472_, v_a_2473_, v_b_2474_, v_c_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___x_2470_);
lean_dec_ref(v_info_2469_);
lean_dec(v_upperBound_2468_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(lean_object* v_x_2482_){
_start:
{
if (lean_obj_tag(v_x_2482_) == 0)
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_unsigned_to_nat(0u);
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_unsigned_to_nat(1u);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___boxed(lean_object* v_x_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(v_x_2485_);
lean_dec_ref(v_x_2485_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2487_, lean_object* v_k_2488_){
_start:
{
if (lean_obj_tag(v_t_2487_) == 0)
{
lean_object* v_fvarId_2489_; lean_object* v___x_2490_; 
v_fvarId_2489_ = lean_ctor_get(v_t_2487_, 0);
lean_inc(v_fvarId_2489_);
lean_dec_ref(v_t_2487_);
v___x_2490_ = lean_apply_1(v_k_2488_, v_fvarId_2489_);
return v___x_2490_;
}
else
{
lean_object* v_lhs_2491_; lean_object* v_rhs_2492_; lean_object* v___x_2493_; 
v_lhs_2491_ = lean_ctor_get(v_t_2487_, 0);
lean_inc(v_lhs_2491_);
v_rhs_2492_ = lean_ctor_get(v_t_2487_, 1);
lean_inc(v_rhs_2492_);
lean_dec_ref(v_t_2487_);
v___x_2493_ = lean_apply_2(v_k_2488_, v_lhs_2491_, v_rhs_2492_);
return v___x_2493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2494_, lean_object* v_ctorIdx_2495_, lean_object* v_t_2496_, lean_object* v_h_2497_, lean_object* v_k_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2496_, v_k_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2500_, lean_object* v_ctorIdx_2501_, lean_object* v_t_2502_, lean_object* v_h_2503_, lean_object* v_k_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2500_, v_ctorIdx_2501_, v_t_2502_, v_h_2503_, v_k_2504_);
lean_dec(v_ctorIdx_2501_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2506_, lean_object* v_hyp_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2506_, v_hyp_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2509_, lean_object* v_t_2510_, lean_object* v_h_2511_, lean_object* v_hyp_2512_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2510_, v_hyp_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2514_, lean_object* v_decSubsingleton_2515_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2514_, v_decSubsingleton_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2517_, lean_object* v_t_2518_, lean_object* v_h_2519_, lean_object* v_decSubsingleton_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2518_, v_decSubsingleton_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2522_, lean_object* v_fvarId_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2522_, v_fvarId_2523_);
if (lean_obj_tag(v___x_2524_) == 1)
{
lean_object* v_val_2525_; lean_object* v___x_2526_; 
v_val_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_val_2525_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = l_Lean_Expr_fvarId_x21(v_val_2525_);
lean_dec(v_val_2525_);
return v___x_2526_;
}
else
{
lean_dec(v___x_2524_);
lean_inc(v_fvarId_2523_);
return v_fvarId_2523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2527_, lean_object* v_fvarId_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2527_, v_fvarId_2528_);
lean_dec(v_fvarId_2528_);
lean_dec(v_s_2527_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2530_, v_x_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_a_2546_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2537_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2537_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2554_, v_x_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2562_, lean_object* v_mvarId_2563_, lean_object* v_x_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2563_, v_x_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2571_, lean_object* v_mvarId_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2571_, v_mvarId_2572_, v_x_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2580_, lean_object* v___y_2581_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = l_Lean_Expr_hasMVar(v_e_2580_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_e_2580_);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; lean_object* v_mctx_2586_; lean_object* v___x_2587_; lean_object* v_fst_2588_; lean_object* v_snd_2589_; lean_object* v___x_2590_; lean_object* v_cache_2591_; lean_object* v_zetaDeltaFVarIds_2592_; lean_object* v_postponed_2593_; lean_object* v_diag_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2603_; 
v___x_2585_ = lean_st_ref_get(v___y_2581_);
v_mctx_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc_ref(v_mctx_2586_);
lean_dec(v___x_2585_);
v___x_2587_ = l_Lean_instantiateMVarsCore(v_mctx_2586_, v_e_2580_);
v_fst_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_fst_2588_);
v_snd_2589_ = lean_ctor_get(v___x_2587_, 1);
lean_inc(v_snd_2589_);
lean_dec_ref(v___x_2587_);
v___x_2590_ = lean_st_ref_take(v___y_2581_);
v_cache_2591_ = lean_ctor_get(v___x_2590_, 1);
v_zetaDeltaFVarIds_2592_ = lean_ctor_get(v___x_2590_, 2);
v_postponed_2593_ = lean_ctor_get(v___x_2590_, 3);
v_diag_2594_ = lean_ctor_get(v___x_2590_, 4);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v___x_2590_, 0);
lean_dec(v_unused_2604_);
v___x_2596_ = v___x_2590_;
v_isShared_2597_ = v_isSharedCheck_2603_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_diag_2594_);
lean_inc(v_postponed_2593_);
lean_inc(v_zetaDeltaFVarIds_2592_);
lean_inc(v_cache_2591_);
lean_dec(v___x_2590_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2603_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v_snd_2589_);
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_snd_2589_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_cache_2591_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_zetaDeltaFVarIds_2592_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_postponed_2593_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_diag_2594_);
v___x_2599_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_st_ref_set(v___y_2581_, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_fst_2588_);
return v___x_2601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2605_, v___y_2606_);
lean_dec(v___y_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2609_, v___y_2611_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_){
_start:
{
lean_object* v_ks_2627_; lean_object* v_vs_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2652_; 
v_ks_2627_ = lean_ctor_get(v_x_2623_, 0);
v_vs_2628_ = lean_ctor_get(v_x_2623_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_x_2623_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2630_ = v_x_2623_;
v_isShared_2631_ = v_isSharedCheck_2652_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_vs_2628_);
lean_inc(v_ks_2627_);
lean_dec(v_x_2623_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2652_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = lean_array_get_size(v_ks_2627_);
v___x_2633_ = lean_nat_dec_lt(v_x_2624_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
lean_dec(v_x_2624_);
v___x_2634_ = lean_array_push(v_ks_2627_, v_x_2625_);
v___x_2635_ = lean_array_push(v_vs_2628_, v_x_2626_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 1, v___x_2635_);
lean_ctor_set(v___x_2630_, 0, v___x_2634_);
v___x_2637_ = v___x_2630_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
else
{
lean_object* v_k_x27_2639_; uint8_t v___x_2640_; 
v_k_x27_2639_ = lean_array_fget_borrowed(v_ks_2627_, v_x_2624_);
v___x_2640_ = l_Lean_instBEqMVarId_beq(v_x_2625_, v_k_x27_2639_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2642_; 
if (v_isShared_2631_ == 0)
{
v___x_2642_ = v___x_2630_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_ks_2627_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_vs_2628_);
v___x_2642_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_unsigned_to_nat(1u);
v___x_2644_ = lean_nat_add(v_x_2624_, v___x_2643_);
lean_dec(v_x_2624_);
v_x_2623_ = v___x_2642_;
v_x_2624_ = v___x_2644_;
goto _start;
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2647_ = lean_array_fset(v_ks_2627_, v_x_2624_, v_x_2625_);
v___x_2648_ = lean_array_fset(v_vs_2628_, v_x_2624_, v_x_2626_);
lean_dec(v_x_2624_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 1, v___x_2648_);
lean_ctor_set(v___x_2630_, 0, v___x_2647_);
v___x_2650_ = v___x_2630_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2653_, lean_object* v_k_2654_, lean_object* v_v_2655_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2653_, v___x_2656_, v_k_2654_, v_v_2655_);
return v___x_2657_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_2658_; size_t v___x_2659_; size_t v___x_2660_; 
v___x_2658_ = ((size_t)5ULL);
v___x_2659_ = ((size_t)1ULL);
v___x_2660_ = lean_usize_shift_left(v___x_2659_, v___x_2658_);
return v___x_2660_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_2661_; size_t v___x_2662_; size_t v___x_2663_; 
v___x_2661_ = ((size_t)1ULL);
v___x_2662_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2663_ = lean_usize_sub(v___x_2662_, v___x_2661_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2665_, size_t v_x_2666_, size_t v_x_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
if (lean_obj_tag(v_x_2665_) == 0)
{
lean_object* v_es_2670_; size_t v___x_2671_; size_t v___x_2672_; size_t v___x_2673_; size_t v___x_2674_; lean_object* v_j_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v_es_2670_ = lean_ctor_get(v_x_2665_, 0);
v___x_2671_ = ((size_t)5ULL);
v___x_2672_ = ((size_t)1ULL);
v___x_2673_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1);
v___x_2674_ = lean_usize_land(v_x_2666_, v___x_2673_);
v_j_2675_ = lean_usize_to_nat(v___x_2674_);
v___x_2676_ = lean_array_get_size(v_es_2670_);
v___x_2677_ = lean_nat_dec_lt(v_j_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_dec(v_j_2675_);
lean_dec(v_x_2669_);
lean_dec(v_x_2668_);
return v_x_2665_;
}
else
{
lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2714_; 
lean_inc_ref(v_es_2670_);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_x_2665_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; 
v_unused_2715_ = lean_ctor_get(v_x_2665_, 0);
lean_dec(v_unused_2715_);
v___x_2679_ = v_x_2665_;
v_isShared_2680_ = v_isSharedCheck_2714_;
goto v_resetjp_2678_;
}
else
{
lean_dec(v_x_2665_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2714_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v_v_2681_; lean_object* v___x_2682_; lean_object* v_xs_x27_2683_; lean_object* v___y_2685_; 
v_v_2681_ = lean_array_fget(v_es_2670_, v_j_2675_);
v___x_2682_ = lean_box(0);
v_xs_x27_2683_ = lean_array_fset(v_es_2670_, v_j_2675_, v___x_2682_);
switch(lean_obj_tag(v_v_2681_))
{
case 0:
{
lean_object* v_key_2690_; lean_object* v_val_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2701_; 
v_key_2690_ = lean_ctor_get(v_v_2681_, 0);
v_val_2691_ = lean_ctor_get(v_v_2681_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_v_2681_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2693_ = v_v_2681_;
v_isShared_2694_ = v_isSharedCheck_2701_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_val_2691_);
lean_inc(v_key_2690_);
lean_dec(v_v_2681_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2701_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
uint8_t v___x_2695_; 
v___x_2695_ = l_Lean_instBEqMVarId_beq(v_x_2668_, v_key_2690_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_del_object(v___x_2693_);
v___x_2696_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2690_, v_val_2691_, v_x_2668_, v_x_2669_);
v___x_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
v___y_2685_ = v___x_2697_;
goto v___jp_2684_;
}
else
{
lean_object* v___x_2699_; 
lean_dec(v_val_2691_);
lean_dec(v_key_2690_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v_x_2669_);
lean_ctor_set(v___x_2693_, 0, v_x_2668_);
v___x_2699_ = v___x_2693_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_x_2668_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_x_2669_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
v___y_2685_ = v___x_2699_;
goto v___jp_2684_;
}
}
}
}
case 1:
{
lean_object* v_node_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2712_; 
v_node_2702_ = lean_ctor_get(v_v_2681_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_v_2681_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2704_ = v_v_2681_;
v_isShared_2705_ = v_isSharedCheck_2712_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_node_2702_);
lean_dec(v_v_2681_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2712_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2706_ = lean_usize_shift_right(v_x_2666_, v___x_2671_);
v___x_2707_ = lean_usize_add(v_x_2667_, v___x_2672_);
v___x_2708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2702_, v___x_2706_, v___x_2707_, v_x_2668_, v_x_2669_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v___x_2708_);
v___x_2710_ = v___x_2704_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
v___y_2685_ = v___x_2710_;
goto v___jp_2684_;
}
}
}
default: 
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_x_2668_);
lean_ctor_set(v___x_2713_, 1, v_x_2669_);
v___y_2685_ = v___x_2713_;
goto v___jp_2684_;
}
}
v___jp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2686_ = lean_array_fset(v_xs_x27_2683_, v_j_2675_, v___y_2685_);
lean_dec(v_j_2675_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v___x_2686_);
v___x_2688_ = v___x_2679_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
else
{
lean_object* v_ks_2716_; lean_object* v_vs_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2737_; 
v_ks_2716_ = lean_ctor_get(v_x_2665_, 0);
v_vs_2717_ = lean_ctor_get(v_x_2665_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_x_2665_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2719_ = v_x_2665_;
v_isShared_2720_ = v_isSharedCheck_2737_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_vs_2717_);
lean_inc(v_ks_2716_);
lean_dec(v_x_2665_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2737_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_ks_2716_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_vs_2717_);
v___x_2722_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v_newNode_2723_; uint8_t v___y_2725_; size_t v___x_2731_; uint8_t v___x_2732_; 
v_newNode_2723_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2722_, v_x_2668_, v_x_2669_);
v___x_2731_ = ((size_t)7ULL);
v___x_2732_ = lean_usize_dec_le(v___x_2731_, v_x_2667_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2733_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2723_);
v___x_2734_ = lean_unsigned_to_nat(4u);
v___x_2735_ = lean_nat_dec_lt(v___x_2733_, v___x_2734_);
lean_dec(v___x_2733_);
v___y_2725_ = v___x_2735_;
goto v___jp_2724_;
}
else
{
v___y_2725_ = v___x_2732_;
goto v___jp_2724_;
}
v___jp_2724_:
{
if (v___y_2725_ == 0)
{
lean_object* v_ks_2726_; lean_object* v_vs_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_ks_2726_ = lean_ctor_get(v_newNode_2723_, 0);
lean_inc_ref(v_ks_2726_);
v_vs_2727_ = lean_ctor_get(v_newNode_2723_, 1);
lean_inc_ref(v_vs_2727_);
lean_dec_ref(v_newNode_2723_);
v___x_2728_ = lean_unsigned_to_nat(0u);
v___x_2729_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2);
v___x_2730_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2667_, v_ks_2726_, v_vs_2727_, v___x_2728_, v___x_2729_);
lean_dec_ref(v_vs_2727_);
lean_dec_ref(v_ks_2726_);
return v___x_2730_;
}
else
{
return v_newNode_2723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_2738_, lean_object* v_keys_2739_, lean_object* v_vals_2740_, lean_object* v_i_2741_, lean_object* v_entries_2742_){
_start:
{
lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2743_ = lean_array_get_size(v_keys_2739_);
v___x_2744_ = lean_nat_dec_lt(v_i_2741_, v___x_2743_);
if (v___x_2744_ == 0)
{
lean_dec(v_i_2741_);
return v_entries_2742_;
}
else
{
lean_object* v_k_2745_; lean_object* v_v_2746_; uint64_t v___x_2747_; size_t v_h_2748_; size_t v___x_2749_; lean_object* v___x_2750_; size_t v___x_2751_; size_t v___x_2752_; size_t v___x_2753_; size_t v_h_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_k_2745_ = lean_array_fget_borrowed(v_keys_2739_, v_i_2741_);
v_v_2746_ = lean_array_fget_borrowed(v_vals_2740_, v_i_2741_);
v___x_2747_ = l_Lean_instHashableMVarId_hash(v_k_2745_);
v_h_2748_ = lean_uint64_to_usize(v___x_2747_);
v___x_2749_ = ((size_t)5ULL);
v___x_2750_ = lean_unsigned_to_nat(1u);
v___x_2751_ = ((size_t)1ULL);
v___x_2752_ = lean_usize_sub(v_depth_2738_, v___x_2751_);
v___x_2753_ = lean_usize_mul(v___x_2749_, v___x_2752_);
v_h_2754_ = lean_usize_shift_right(v_h_2748_, v___x_2753_);
v___x_2755_ = lean_nat_add(v_i_2741_, v___x_2750_);
lean_dec(v_i_2741_);
lean_inc(v_v_2746_);
lean_inc(v_k_2745_);
v___x_2756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_2742_, v_h_2754_, v_depth_2738_, v_k_2745_, v_v_2746_);
v_i_2741_ = v___x_2755_;
v_entries_2742_ = v___x_2756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2758_, lean_object* v_keys_2759_, lean_object* v_vals_2760_, lean_object* v_i_2761_, lean_object* v_entries_2762_){
_start:
{
size_t v_depth_boxed_2763_; lean_object* v_res_2764_; 
v_depth_boxed_2763_ = lean_unbox_usize(v_depth_2758_);
lean_dec(v_depth_2758_);
v_res_2764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_2763_, v_keys_2759_, v_vals_2760_, v_i_2761_, v_entries_2762_);
lean_dec_ref(v_vals_2760_);
lean_dec_ref(v_keys_2759_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_2765_, lean_object* v_x_2766_, lean_object* v_x_2767_, lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
size_t v_x_4290__boxed_2770_; size_t v_x_4291__boxed_2771_; lean_object* v_res_2772_; 
v_x_4290__boxed_2770_ = lean_unbox_usize(v_x_2766_);
lean_dec(v_x_2766_);
v_x_4291__boxed_2771_ = lean_unbox_usize(v_x_2767_);
lean_dec(v_x_2767_);
v_res_2772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2765_, v_x_4290__boxed_2770_, v_x_4291__boxed_2771_, v_x_2768_, v_x_2769_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object* v_x_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_){
_start:
{
uint64_t v___x_2776_; size_t v___x_2777_; size_t v___x_2778_; lean_object* v___x_2779_; 
v___x_2776_ = l_Lean_instHashableMVarId_hash(v_x_2774_);
v___x_2777_ = lean_uint64_to_usize(v___x_2776_);
v___x_2778_ = ((size_t)1ULL);
v___x_2779_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2773_, v___x_2777_, v___x_2778_, v_x_2774_, v_x_2775_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object* v_mvarId_2780_, lean_object* v_val_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; lean_object* v_mctx_2785_; lean_object* v_cache_2786_; lean_object* v_zetaDeltaFVarIds_2787_; lean_object* v_postponed_2788_; lean_object* v_diag_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2816_; 
v___x_2784_ = lean_st_ref_take(v___y_2782_);
v_mctx_2785_ = lean_ctor_get(v___x_2784_, 0);
v_cache_2786_ = lean_ctor_get(v___x_2784_, 1);
v_zetaDeltaFVarIds_2787_ = lean_ctor_get(v___x_2784_, 2);
v_postponed_2788_ = lean_ctor_get(v___x_2784_, 3);
v_diag_2789_ = lean_ctor_get(v___x_2784_, 4);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2791_ = v___x_2784_;
v_isShared_2792_ = v_isSharedCheck_2816_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_diag_2789_);
lean_inc(v_postponed_2788_);
lean_inc(v_zetaDeltaFVarIds_2787_);
lean_inc(v_cache_2786_);
lean_inc(v_mctx_2785_);
lean_dec(v___x_2784_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2816_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v_depth_2793_; lean_object* v_levelAssignDepth_2794_; lean_object* v_mvarCounter_2795_; lean_object* v_lDepth_2796_; lean_object* v_decls_2797_; lean_object* v_userNames_2798_; lean_object* v_lAssignment_2799_; lean_object* v_eAssignment_2800_; lean_object* v_dAssignment_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2815_; 
v_depth_2793_ = lean_ctor_get(v_mctx_2785_, 0);
v_levelAssignDepth_2794_ = lean_ctor_get(v_mctx_2785_, 1);
v_mvarCounter_2795_ = lean_ctor_get(v_mctx_2785_, 2);
v_lDepth_2796_ = lean_ctor_get(v_mctx_2785_, 3);
v_decls_2797_ = lean_ctor_get(v_mctx_2785_, 4);
v_userNames_2798_ = lean_ctor_get(v_mctx_2785_, 5);
v_lAssignment_2799_ = lean_ctor_get(v_mctx_2785_, 6);
v_eAssignment_2800_ = lean_ctor_get(v_mctx_2785_, 7);
v_dAssignment_2801_ = lean_ctor_get(v_mctx_2785_, 8);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_mctx_2785_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2803_ = v_mctx_2785_;
v_isShared_2804_ = v_isSharedCheck_2815_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_dAssignment_2801_);
lean_inc(v_eAssignment_2800_);
lean_inc(v_lAssignment_2799_);
lean_inc(v_userNames_2798_);
lean_inc(v_decls_2797_);
lean_inc(v_lDepth_2796_);
lean_inc(v_mvarCounter_2795_);
lean_inc(v_levelAssignDepth_2794_);
lean_inc(v_depth_2793_);
lean_dec(v_mctx_2785_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2815_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2805_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2800_, v_mvarId_2780_, v_val_2781_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 7, v___x_2805_);
v___x_2807_ = v___x_2803_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_depth_2793_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_levelAssignDepth_2794_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_mvarCounter_2795_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v_lDepth_2796_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_decls_2797_);
lean_ctor_set(v_reuseFailAlloc_2814_, 5, v_userNames_2798_);
lean_ctor_set(v_reuseFailAlloc_2814_, 6, v_lAssignment_2799_);
lean_ctor_set(v_reuseFailAlloc_2814_, 7, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2814_, 8, v_dAssignment_2801_);
v___x_2807_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2809_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2807_);
v___x_2809_ = v___x_2791_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_cache_2786_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_zetaDeltaFVarIds_2787_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_postponed_2788_);
lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_diag_2789_);
v___x_2809_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = lean_st_ref_set(v___y_2782_, v___x_2809_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2817_, lean_object* v_val_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2817_, v_val_2818_, v___y_2819_);
lean_dec(v___y_2819_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2830_, lean_object* v_as_2831_, size_t v_sz_2832_, size_t v_i_2833_, lean_object* v_b_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_a_2841_; uint8_t v___x_2845_; 
v___x_2845_ = lean_usize_dec_lt(v_i_2833_, v_sz_2832_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; 
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v_b_2834_);
return v___x_2846_;
}
else
{
lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v_a_2851_; 
v_fst_2847_ = lean_ctor_get(v_b_2834_, 0);
lean_inc(v_fst_2847_);
v_snd_2848_ = lean_ctor_get(v_b_2834_, 1);
lean_inc(v_snd_2848_);
lean_dec_ref(v_b_2834_);
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_nat_dec_eq(v___x_2830_, v___x_2849_);
v_a_2851_ = lean_array_uget_borrowed(v_as_2831_, v_i_2833_);
if (lean_obj_tag(v_a_2851_) == 0)
{
lean_object* v_fvarId_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_fvarId_2852_ = lean_ctor_get(v_a_2851_, 0);
v___x_2853_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2848_, v_fvarId_2852_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
v___x_2854_ = l_Lean_Meta_substCore(v_fst_2847_, v___x_2853_, v___x_2845_, v_snd_2848_, v___x_2845_, v___x_2850_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v_fst_2856_; lean_object* v_snd_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref(v___x_2854_);
v_fst_2856_ = lean_ctor_get(v_a_2855_, 0);
v_snd_2857_ = lean_ctor_get(v_a_2855_, 1);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_a_2855_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v_a_2855_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_snd_2857_);
lean_inc(v_fst_2856_);
lean_dec(v_a_2855_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v_fst_2856_);
lean_ctor_set(v___x_2859_, 0, v_snd_2857_);
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_snd_2857_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_fst_2856_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
v_a_2841_ = v___x_2862_;
goto v___jp_2840_;
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
v_a_2865_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2854_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2854_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_lhs_2873_; lean_object* v_rhs_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_lhs_2873_ = lean_ctor_get(v_a_2851_, 0);
v_rhs_2874_ = lean_ctor_get(v_a_2851_, 1);
v___x_2875_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2848_, v_lhs_2873_);
v___x_2876_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2848_, v_rhs_2874_);
v___x_2877_ = l_Lean_mkFVar(v___x_2875_);
v___x_2878_ = l_Lean_mkFVar(v___x_2876_);
lean_inc_ref(v___x_2878_);
lean_inc_ref(v___x_2877_);
v___x_2879_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2879_, 0, v___x_2877_);
lean_closure_set(v___x_2879_, 1, v___x_2878_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc(v_fst_2847_);
v___x_2880_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2847_, v___x_2879_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
v___x_2882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2883_ = lean_unsigned_to_nat(2u);
v___x_2884_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2885_ = lean_array_push(v___x_2884_, v___x_2877_);
v___x_2886_ = lean_array_push(v___x_2885_, v___x_2878_);
v___x_2887_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2887_, 0, v___x_2882_);
lean_closure_set(v___x_2887_, 1, v___x_2886_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc(v_fst_2847_);
v___x_2888_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2847_, v___x_2887_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref(v___x_2888_);
v___x_2890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
v___x_2891_ = l_Lean_MVarId_assert(v_fst_2847_, v___x_2890_, v_a_2881_, v_a_2889_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
v___x_2893_ = l_Lean_Meta_intro1Core(v_a_2892_, v___x_2850_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v_fst_2895_; lean_object* v_snd_2896_; lean_object* v___x_2897_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2893_);
v_fst_2895_ = lean_ctor_get(v_a_2894_, 0);
lean_inc(v_fst_2895_);
v_snd_2896_ = lean_ctor_get(v_a_2894_, 1);
lean_inc(v_snd_2896_);
lean_dec(v_a_2894_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
v___x_2897_ = l_Lean_Meta_substCore(v_snd_2896_, v_fst_2895_, v___x_2845_, v_snd_2848_, v___x_2845_, v___x_2850_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v_fst_2899_; lean_object* v_snd_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v_fst_2899_ = lean_ctor_get(v_a_2898_, 0);
v_snd_2900_ = lean_ctor_get(v_a_2898_, 1);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_a_2898_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v_a_2898_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_snd_2900_);
lean_inc(v_fst_2899_);
lean_dec(v_a_2898_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 1, v_fst_2899_);
lean_ctor_set(v___x_2902_, 0, v_snd_2900_);
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_snd_2900_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_fst_2899_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
v_a_2841_ = v___x_2905_;
goto v___jp_2840_;
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
v_a_2908_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2897_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2897_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_snd_2848_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
v_a_2916_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2893_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2893_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v_snd_2848_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
v_a_2924_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2891_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2891_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v_a_2881_);
lean_dec(v_snd_2848_);
lean_dec(v_fst_2847_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
v_a_2932_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2888_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2888_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec_ref(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec(v_snd_2848_);
lean_dec(v_fst_2847_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
v_a_2940_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2880_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2880_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
v___jp_2840_:
{
size_t v___x_2842_; size_t v___x_2843_; 
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_add(v_i_2833_, v___x_2842_);
v_i_2833_ = v___x_2843_;
v_b_2834_ = v_a_2841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_2948_, lean_object* v_as_2949_, lean_object* v_sz_2950_, lean_object* v_i_2951_, lean_object* v_b_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
size_t v_sz_boxed_2958_; size_t v_i_boxed_2959_; lean_object* v_res_2960_; 
v_sz_boxed_2958_ = lean_unbox_usize(v_sz_2950_);
lean_dec(v_sz_2950_);
v_i_boxed_2959_ = lean_unbox_usize(v_i_2951_);
lean_dec(v_i_2951_);
v_res_2960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2948_, v_as_2949_, v_sz_boxed_2958_, v_i_boxed_2959_, v_b_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec_ref(v_as_2949_);
lean_dec(v___x_2948_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_2961_, lean_object* v_as_2962_, size_t v_i_2963_, size_t v_stop_2964_, lean_object* v_b_2965_){
_start:
{
lean_object* v___y_2967_; uint8_t v___x_2971_; 
v___x_2971_ = lean_usize_dec_eq(v_i_2963_, v_stop_2964_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = lean_box(0);
v___x_2973_ = lean_array_uget_borrowed(v_as_2962_, v_i_2963_);
v___x_2974_ = lean_array_get_borrowed(v___x_2972_, v_eqs_2961_, v___x_2973_);
if (lean_obj_tag(v___x_2974_) == 0)
{
v___y_2967_ = v_b_2965_;
goto v___jp_2966_;
}
else
{
lean_object* v_val_2975_; lean_object* v___x_2976_; 
v_val_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_val_2975_);
v___x_2976_ = lean_array_push(v_b_2965_, v_val_2975_);
v___y_2967_ = v___x_2976_;
goto v___jp_2966_;
}
}
else
{
return v_b_2965_;
}
v___jp_2966_:
{
size_t v___x_2968_; size_t v___x_2969_; 
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_add(v_i_2963_, v___x_2968_);
v_i_2963_ = v___x_2969_;
v_b_2965_ = v___y_2967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_2977_, lean_object* v_as_2978_, lean_object* v_i_2979_, lean_object* v_stop_2980_, lean_object* v_b_2981_){
_start:
{
size_t v_i_boxed_2982_; size_t v_stop_boxed_2983_; lean_object* v_res_2984_; 
v_i_boxed_2982_ = lean_unbox_usize(v_i_2979_);
lean_dec(v_i_2979_);
v_stop_boxed_2983_ = lean_unbox_usize(v_stop_2980_);
lean_dec(v_stop_2980_);
v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2977_, v_as_2978_, v_i_boxed_2982_, v_stop_boxed_2983_, v_b_2981_);
lean_dec_ref(v_as_2978_);
lean_dec_ref(v_eqs_2977_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_2987_, lean_object* v_as_2988_, lean_object* v_start_2989_, lean_object* v_stop_2990_){
_start:
{
lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2991_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_2992_ = lean_nat_dec_lt(v_start_2989_, v_stop_2990_);
if (v___x_2992_ == 0)
{
return v___x_2991_;
}
else
{
lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2993_ = lean_array_get_size(v_as_2988_);
v___x_2994_ = lean_nat_dec_le(v_stop_2990_, v___x_2993_);
if (v___x_2994_ == 0)
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_nat_dec_lt(v_start_2989_, v___x_2993_);
if (v___x_2995_ == 0)
{
return v___x_2991_;
}
else
{
size_t v___x_2996_; size_t v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_usize_of_nat(v_start_2989_);
v___x_2997_ = lean_usize_of_nat(v___x_2993_);
v___x_2998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2987_, v_as_2988_, v___x_2996_, v___x_2997_, v___x_2991_);
return v___x_2998_;
}
}
else
{
size_t v___x_2999_; size_t v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = lean_usize_of_nat(v_start_2989_);
v___x_3000_ = lean_usize_of_nat(v_stop_2990_);
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2987_, v_as_2988_, v___x_2999_, v___x_3000_, v___x_2991_);
return v___x_3001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_3002_, lean_object* v_as_3003_, lean_object* v_start_3004_, lean_object* v_stop_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_3002_, v_as_3003_, v_start_3004_, v_stop_3005_);
lean_dec(v_stop_3005_);
lean_dec(v_start_3004_);
lean_dec_ref(v_as_3003_);
lean_dec_ref(v_eqs_3002_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_3007_, lean_object* v_type_3008_, lean_object* v_deps_3009_, lean_object* v_eqs_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v_eqs_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_array_get_size(v_deps_3009_);
v_eqs_3018_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_3010_, v_deps_3009_, v___x_3016_, v___x_3017_);
v___x_3019_ = lean_array_get_size(v_eqs_3018_);
v___x_3020_ = lean_nat_dec_eq(v___x_3019_, v___x_3016_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_type_3008_);
v___x_3022_ = 0;
v___x_3023_ = lean_box(0);
lean_inc_ref(v_a_3011_);
v___x_3024_ = l_Lean_Meta_mkFreshExprMVar(v___x_3021_, v___x_3022_, v___x_3023_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; size_t v_sz_3029_; size_t v___x_3030_; lean_object* v___x_3031_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = l_Lean_Expr_mvarId_x21(v_a_3025_);
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v_sz_3029_ = lean_array_size(v_eqs_3018_);
v___x_3030_ = ((size_t)0ULL);
lean_inc(v_a_3012_);
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_3019_, v_eqs_3018_, v_sz_3029_, v___x_3030_, v___x_3028_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
lean_dec_ref(v_eqs_3018_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v_fst_3033_; lean_object* v_snd_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3031_);
v_fst_3033_ = lean_ctor_get(v_a_3032_, 0);
lean_inc(v_fst_3033_);
v_snd_3034_ = lean_ctor_get(v_a_3032_, 1);
lean_inc(v_snd_3034_);
lean_dec(v_a_3032_);
v___x_3035_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_3034_, v_fvarId_3007_);
lean_dec(v_fvarId_3007_);
lean_dec(v_snd_3034_);
v___x_3036_ = l_Lean_mkFVar(v___x_3035_);
v___x_3037_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_3033_, v___x_3036_, v_a_3012_);
lean_dec_ref(v___x_3037_);
v___x_3038_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_3025_, v_a_3012_);
lean_dec(v_a_3012_);
return v___x_3038_;
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec(v_a_3025_);
lean_dec(v_a_3012_);
lean_dec(v_fvarId_3007_);
v_a_3039_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3031_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3031_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_dec_ref(v_eqs_3018_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_fvarId_3007_);
return v___x_3024_;
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec_ref(v_eqs_3018_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec_ref(v_type_3008_);
v___x_3047_ = l_Lean_mkFVar(v_fvarId_3007_);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3049_, lean_object* v_type_3050_, lean_object* v_deps_3051_, lean_object* v_eqs_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3049_, v_type_3050_, v_deps_3051_, v_eqs_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
lean_dec_ref(v_eqs_3052_);
lean_dec_ref(v_deps_3051_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3059_, lean_object* v_val_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3059_, v_val_3060_, v___y_3062_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3067_, lean_object* v_val_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3067_, v_val_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3075_, lean_object* v_x_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3076_, v_x_3077_, v_x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3080_, lean_object* v_x_3081_, size_t v_x_3082_, size_t v_x_3083_, lean_object* v_x_3084_, lean_object* v_x_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3081_, v_x_3082_, v_x_3083_, v_x_3084_, v_x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3087_, lean_object* v_x_3088_, lean_object* v_x_3089_, lean_object* v_x_3090_, lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
size_t v_x_4913__boxed_3093_; size_t v_x_4914__boxed_3094_; lean_object* v_res_3095_; 
v_x_4913__boxed_3093_ = lean_unbox_usize(v_x_3089_);
lean_dec(v_x_3089_);
v_x_4914__boxed_3094_ = lean_unbox_usize(v_x_3090_);
lean_dec(v_x_3090_);
v_res_3095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3087_, v_x_3088_, v_x_4913__boxed_3093_, v_x_4914__boxed_3094_, v_x_3091_, v_x_3092_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3096_, lean_object* v_n_3097_, lean_object* v_k_3098_, lean_object* v_v_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3097_, v_k_3098_, v_v_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3101_, size_t v_depth_3102_, lean_object* v_keys_3103_, lean_object* v_vals_3104_, lean_object* v_heq_3105_, lean_object* v_i_3106_, lean_object* v_entries_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3102_, v_keys_3103_, v_vals_3104_, v_i_3106_, v_entries_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3109_, lean_object* v_depth_3110_, lean_object* v_keys_3111_, lean_object* v_vals_3112_, lean_object* v_heq_3113_, lean_object* v_i_3114_, lean_object* v_entries_3115_){
_start:
{
size_t v_depth_boxed_3116_; lean_object* v_res_3117_; 
v_depth_boxed_3116_ = lean_unbox_usize(v_depth_3110_);
lean_dec(v_depth_3110_);
v_res_3117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3109_, v_depth_boxed_3116_, v_keys_3111_, v_vals_3112_, v_heq_3113_, v_i_3114_, v_entries_3115_);
lean_dec_ref(v_vals_3112_);
lean_dec_ref(v_keys_3111_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3118_, lean_object* v_x_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_, lean_object* v_x_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3119_, v_x_3120_, v_x_3121_, v_x_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___f_3131_; lean_object* v___x_1807__overap_3132_; lean_object* v___x_3133_; 
v___f_3131_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1807__overap_3132_ = lean_panic_fn(v___f_3131_, v_msg_3125_);
v___x_3133_ = lean_apply_5(v___x_1807__overap_3132_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, lean_box(0));
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v_res_3140_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3144_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3145_ = lean_unsigned_to_nat(34u);
v___x_3146_ = lean_unsigned_to_nat(360u);
v___x_3147_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3148_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3149_ = l_mkPanicMessageWithDecl(v___x_3148_, v___x_3147_, v___x_3146_, v___x_3145_, v___x_3144_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3150_, lean_object* v___x_3151_, lean_object* v___x_3152_, lean_object* v_i_3153_, lean_object* v_kinds_3154_, lean_object* v___x_3155_, lean_object* v_lhs_3156_, lean_object* v_rhs_3157_, lean_object* v_type_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v___x_1994__boxed_3164_; uint8_t v___x_1995__boxed_3165_; lean_object* v_res_3166_; 
v___x_1994__boxed_3164_ = lean_unbox(v___x_3151_);
v___x_1995__boxed_3165_ = lean_unbox(v___x_3152_);
v_res_3166_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3150_, v___x_1994__boxed_3164_, v___x_1995__boxed_3165_, v_i_3153_, v_kinds_3154_, v___x_3155_, v_lhs_3156_, v_rhs_3157_, v_type_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3167_, uint8_t v___x_3168_, uint8_t v___x_3169_, lean_object* v_i_3170_, lean_object* v___x_3171_, lean_object* v_kinds_3172_, lean_object* v_typeSub_3173_, lean_object* v_lhs_3174_, lean_object* v_rhs_3175_, lean_object* v_type_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; uint8_t v___x_3183_; lean_object* v___x_3184_; 
lean_inc_ref(v_rhs_3175_);
v___x_3182_ = lean_array_push(v___x_3167_, v_rhs_3175_);
v___x_3183_ = 1;
v___x_3184_ = l_Lean_Meta_mkLambdaFVars(v___x_3182_, v_type_3176_, v___x_3168_, v___x_3169_, v___x_3168_, v___x_3169_, v___x_3183_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec_ref(v___x_3182_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref(v___x_3184_);
v___x_3186_ = lean_nat_add(v_i_3170_, v___x_3171_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
v___x_3187_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3172_, v___x_3186_, v_typeSub_3173_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3190_ = lean_unsigned_to_nat(2u);
v___x_3191_ = lean_mk_empty_array_with_capacity(v___x_3190_);
v___x_3192_ = lean_array_push(v___x_3191_, v_lhs_3174_);
v___x_3193_ = lean_array_push(v___x_3192_, v_rhs_3175_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc_ref(v___x_3193_);
v___x_3194_ = l_Lean_Meta_mkAppM(v___x_3189_, v___x_3193_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref(v___x_3194_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
v___x_3196_ = l_Lean_Meta_mkEqNDRec(v_a_3185_, v_a_3188_, v_a_3195_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref(v___x_3196_);
v___x_3198_ = l_Lean_Meta_mkLambdaFVars(v___x_3193_, v_a_3197_, v___x_3168_, v___x_3169_, v___x_3168_, v___x_3169_, v___x_3183_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v___x_3193_);
return v___x_3198_;
}
else
{
lean_dec_ref(v___x_3193_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
return v___x_3196_;
}
}
else
{
lean_dec_ref(v___x_3193_);
lean_dec(v_a_3188_);
lean_dec(v_a_3185_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
return v___x_3194_;
}
}
else
{
lean_dec(v_a_3185_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v_rhs_3175_);
lean_dec_ref(v_lhs_3174_);
return v___x_3187_;
}
}
else
{
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v_rhs_3175_);
lean_dec_ref(v_lhs_3174_);
lean_dec_ref(v_typeSub_3173_);
lean_dec_ref(v_kinds_3172_);
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3199_, lean_object* v___x_3200_, lean_object* v___x_3201_, lean_object* v_i_3202_, lean_object* v___x_3203_, lean_object* v_kinds_3204_, lean_object* v_typeSub_3205_, lean_object* v_lhs_3206_, lean_object* v_rhs_3207_, lean_object* v_type_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
uint8_t v___x_2061__boxed_3214_; uint8_t v___x_2062__boxed_3215_; lean_object* v_res_3216_; 
v___x_2061__boxed_3214_ = lean_unbox(v___x_3200_);
v___x_2062__boxed_3215_ = lean_unbox(v___x_3201_);
v_res_3216_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3199_, v___x_2061__boxed_3214_, v___x_2062__boxed_3215_, v_i_3202_, v___x_3203_, v_kinds_3204_, v_typeSub_3205_, v_lhs_3206_, v_rhs_3207_, v_type_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___x_3203_);
lean_dec(v_i_3202_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(lean_object* v_kinds_3217_, lean_object* v_i_3218_, uint8_t v___x_3219_, uint8_t v___x_3220_, lean_object* v_lhs_3221_, lean_object* v_type_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
uint8_t v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3231_ = 0;
v___x_3232_ = lean_box(v___x_3231_);
v___x_3233_ = lean_array_get_borrowed(v___x_3232_, v_kinds_3217_, v_i_3218_);
v___x_3234_ = lean_unbox(v___x_3233_);
switch(v___x_3234_)
{
case 1:
{
lean_dec_ref(v_type_3222_);
lean_dec_ref(v_lhs_3221_);
lean_dec(v_i_3218_);
lean_dec_ref(v_kinds_3217_);
goto v___jp_3228_;
}
case 2:
{
lean_object* v___x_3235_; 
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
lean_inc_ref(v_lhs_3221_);
v___x_3235_ = l_Lean_Meta_mkEqRefl(v_lhs_3221_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___f_3246_; lean_object* v___x_3247_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref(v___x_3235_);
v___x_3237_ = l_Lean_Expr_bindingBody_x21(v_type_3222_);
v___x_3238_ = l_Lean_Expr_bindingBody_x21(v___x_3237_);
lean_dec_ref(v___x_3237_);
v___x_3239_ = lean_unsigned_to_nat(2u);
v___x_3240_ = lean_mk_empty_array_with_capacity(v___x_3239_);
lean_inc_ref(v___x_3240_);
v___x_3241_ = lean_array_push(v___x_3240_, v_a_3236_);
lean_inc_ref(v_lhs_3221_);
v___x_3242_ = lean_array_push(v___x_3241_, v_lhs_3221_);
v___x_3243_ = lean_expr_instantiate(v___x_3238_, v___x_3242_);
lean_dec_ref(v___x_3242_);
lean_dec_ref(v___x_3238_);
v___x_3244_ = lean_box(v___x_3219_);
v___x_3245_ = lean_box(v___x_3220_);
v___f_3246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3246_, 0, v___x_3240_);
lean_closure_set(v___f_3246_, 1, v___x_3244_);
lean_closure_set(v___f_3246_, 2, v___x_3245_);
lean_closure_set(v___f_3246_, 3, v_i_3218_);
lean_closure_set(v___f_3246_, 4, v_kinds_3217_);
lean_closure_set(v___f_3246_, 5, v___x_3243_);
lean_closure_set(v___f_3246_, 6, v_lhs_3221_);
v___x_3247_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3222_, v___f_3246_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
return v___x_3247_;
}
else
{
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec_ref(v_type_3222_);
lean_dec_ref(v_lhs_3221_);
lean_dec(v_i_3218_);
lean_dec_ref(v_kinds_3217_);
return v___x_3235_;
}
}
case 4:
{
lean_dec_ref(v_type_3222_);
lean_dec_ref(v_lhs_3221_);
lean_dec(v_i_3218_);
lean_dec_ref(v_kinds_3217_);
goto v___jp_3228_;
}
case 5:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v_typeSub_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___f_3255_; lean_object* v___x_3256_; 
v___x_3248_ = l_Lean_Expr_bindingBody_x21(v_type_3222_);
v___x_3249_ = lean_unsigned_to_nat(1u);
v___x_3250_ = lean_mk_empty_array_with_capacity(v___x_3249_);
lean_inc_ref(v_lhs_3221_);
lean_inc_ref(v___x_3250_);
v___x_3251_ = lean_array_push(v___x_3250_, v_lhs_3221_);
v_typeSub_3252_ = lean_expr_instantiate(v___x_3248_, v___x_3251_);
lean_dec_ref(v___x_3251_);
lean_dec_ref(v___x_3248_);
v___x_3253_ = lean_box(v___x_3219_);
v___x_3254_ = lean_box(v___x_3220_);
v___f_3255_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3255_, 0, v___x_3250_);
lean_closure_set(v___f_3255_, 1, v___x_3253_);
lean_closure_set(v___f_3255_, 2, v___x_3254_);
lean_closure_set(v___f_3255_, 3, v_i_3218_);
lean_closure_set(v___f_3255_, 4, v___x_3249_);
lean_closure_set(v___f_3255_, 5, v_kinds_3217_);
lean_closure_set(v___f_3255_, 6, v_typeSub_3252_);
lean_closure_set(v___f_3255_, 7, v_lhs_3221_);
v___x_3256_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3222_, v___f_3255_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
return v___x_3256_;
}
default: 
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_unsigned_to_nat(1u);
v___x_3258_ = lean_nat_add(v_i_3218_, v___x_3257_);
lean_dec(v_i_3218_);
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
v___x_3259_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3217_, v___x_3258_, v_type_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; lean_object* v___x_3264_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref(v___x_3259_);
v___x_3261_ = lean_mk_empty_array_with_capacity(v___x_3257_);
v___x_3262_ = lean_array_push(v___x_3261_, v_lhs_3221_);
v___x_3263_ = 1;
v___x_3264_ = l_Lean_Meta_mkLambdaFVars(v___x_3262_, v_a_3260_, v___x_3219_, v___x_3220_, v___x_3219_, v___x_3220_, v___x_3263_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec_ref(v___x_3262_);
return v___x_3264_;
}
else
{
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec_ref(v_lhs_3221_);
return v___x_3259_;
}
}
}
v___jp_3228_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3230_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3229_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
return v___x_3230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v_kinds_3265_, lean_object* v_i_3266_, lean_object* v___x_3267_, lean_object* v___x_3268_, lean_object* v_lhs_3269_, lean_object* v_type_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v___x_2098__boxed_3276_; uint8_t v___x_2099__boxed_3277_; lean_object* v_res_3278_; 
v___x_2098__boxed_3276_ = lean_unbox(v___x_3267_);
v___x_2099__boxed_3277_ = lean_unbox(v___x_3268_);
v_res_3278_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v_kinds_3265_, v_i_3266_, v___x_2098__boxed_3276_, v___x_2099__boxed_3277_, v_lhs_3269_, v_type_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
return v_res_3278_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3279_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3280_ = lean_unsigned_to_nat(43u);
v___x_3281_ = lean_unsigned_to_nat(355u);
v___x_3282_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3283_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3284_ = l_mkPanicMessageWithDecl(v___x_3283_, v___x_3282_, v___x_3281_, v___x_3280_, v___x_3279_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3285_, lean_object* v_i_3286_, lean_object* v_type_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v___x_3293_; uint8_t v___x_3294_; 
v___x_3293_ = lean_array_get_size(v_kinds_3285_);
v___x_3294_ = lean_nat_dec_eq(v_i_3286_, v___x_3293_);
if (v___x_3294_ == 0)
{
uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; 
v___x_3295_ = 1;
v___x_3296_ = lean_box(v___x_3294_);
v___x_3297_ = lean_box(v___x_3295_);
v___f_3298_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3298_, 0, v_kinds_3285_);
lean_closure_set(v___f_3298_, 1, v_i_3286_);
lean_closure_set(v___f_3298_, 2, v___x_3296_);
lean_closure_set(v___f_3298_, 3, v___x_3297_);
v___x_3299_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3287_, v___f_3298_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
lean_dec(v_i_3286_);
lean_dec_ref(v_kinds_3285_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3301_ = lean_unsigned_to_nat(3u);
v___x_3302_ = l_Lean_Expr_isAppOfArity(v_type_3287_, v___x_3300_, v___x_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec_ref(v_type_3287_);
v___x_3303_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3304_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3303_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
return v___x_3304_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = l_Lean_Expr_appFn_x21(v_type_3287_);
lean_dec_ref(v_type_3287_);
v___x_3306_ = l_Lean_Expr_appArg_x21(v___x_3305_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = l_Lean_Meta_mkEqRefl(v___x_3306_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
return v___x_3307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* v___x_3308_, lean_object* v_rhs_3309_, uint8_t v___x_3310_, uint8_t v___x_3311_, lean_object* v_i_3312_, lean_object* v_kinds_3313_, lean_object* v___x_3314_, lean_object* v_lhs_3315_, lean_object* v_heq_3316_, lean_object* v_type_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; lean_object* v___x_3326_; 
lean_inc_ref(v_rhs_3309_);
v___x_3323_ = lean_array_push(v___x_3308_, v_rhs_3309_);
lean_inc_ref(v_heq_3316_);
v___x_3324_ = lean_array_push(v___x_3323_, v_heq_3316_);
v___x_3325_ = 1;
v___x_3326_ = l_Lean_Meta_mkLambdaFVars(v___x_3324_, v_type_3317_, v___x_3310_, v___x_3311_, v___x_3310_, v___x_3311_, v___x_3325_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec_ref(v___x_3324_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(1u);
v___x_3329_ = lean_nat_add(v_i_3312_, v___x_3328_);
lean_inc(v___y_3321_);
lean_inc_ref(v___y_3320_);
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3318_);
v___x_3330_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3313_, v___x_3329_, v___x_3314_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref(v___x_3330_);
lean_inc(v___y_3321_);
lean_inc_ref(v___y_3320_);
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3318_);
lean_inc_ref(v_heq_3316_);
v___x_3332_ = l_Lean_Meta_mkEqRec(v_a_3327_, v_a_3331_, v_heq_3316_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = lean_unsigned_to_nat(3u);
v___x_3335_ = lean_mk_empty_array_with_capacity(v___x_3334_);
v___x_3336_ = lean_array_push(v___x_3335_, v_lhs_3315_);
v___x_3337_ = lean_array_push(v___x_3336_, v_rhs_3309_);
v___x_3338_ = lean_array_push(v___x_3337_, v_heq_3316_);
v___x_3339_ = l_Lean_Meta_mkLambdaFVars(v___x_3338_, v_a_3333_, v___x_3310_, v___x_3311_, v___x_3310_, v___x_3311_, v___x_3325_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec_ref(v___x_3338_);
return v___x_3339_;
}
else
{
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec_ref(v_heq_3316_);
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v_rhs_3309_);
return v___x_3332_;
}
}
else
{
lean_dec(v_a_3327_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec_ref(v_heq_3316_);
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v_rhs_3309_);
return v___x_3330_;
}
}
else
{
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec_ref(v_heq_3316_);
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v___x_3314_);
lean_dec_ref(v_kinds_3313_);
lean_dec_ref(v_rhs_3309_);
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* v___x_3340_, lean_object* v_rhs_3341_, lean_object* v___x_3342_, lean_object* v___x_3343_, lean_object* v_i_3344_, lean_object* v_kinds_3345_, lean_object* v___x_3346_, lean_object* v_lhs_3347_, lean_object* v_heq_3348_, lean_object* v_type_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
uint8_t v___x_2005__boxed_3355_; uint8_t v___x_2006__boxed_3356_; lean_object* v_res_3357_; 
v___x_2005__boxed_3355_ = lean_unbox(v___x_3342_);
v___x_2006__boxed_3356_ = lean_unbox(v___x_3343_);
v_res_3357_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3340_, v_rhs_3341_, v___x_2005__boxed_3355_, v___x_2006__boxed_3356_, v_i_3344_, v_kinds_3345_, v___x_3346_, v_lhs_3347_, v_heq_3348_, v_type_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec(v_i_3344_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* v___x_3358_, uint8_t v___x_3359_, uint8_t v___x_3360_, lean_object* v_i_3361_, lean_object* v_kinds_3362_, lean_object* v___x_3363_, lean_object* v_lhs_3364_, lean_object* v_rhs_3365_, lean_object* v_type_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___f_3374_; lean_object* v___x_3375_; 
v___x_3372_ = lean_box(v___x_3359_);
v___x_3373_ = lean_box(v___x_3360_);
v___f_3374_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3374_, 0, v___x_3358_);
lean_closure_set(v___f_3374_, 1, v_rhs_3365_);
lean_closure_set(v___f_3374_, 2, v___x_3372_);
lean_closure_set(v___f_3374_, 3, v___x_3373_);
lean_closure_set(v___f_3374_, 4, v_i_3361_);
lean_closure_set(v___f_3374_, 5, v_kinds_3362_);
lean_closure_set(v___f_3374_, 6, v___x_3363_);
lean_closure_set(v___f_3374_, 7, v_lhs_3364_);
v___x_3375_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3366_, v___f_3374_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object* v_kinds_3376_, lean_object* v_i_3377_, lean_object* v_type_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3376_, v_i_3377_, v_type_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* v_type_3385_, lean_object* v_kinds_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = lean_unsigned_to_nat(0u);
v___x_3393_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3386_, v___x_3392_, v_type_3385_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object* v_type_3394_, lean_object* v_kinds_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3394_, v_kinds_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_msg_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___f_3408_; lean_object* v___x_2116__overap_3409_; lean_object* v___x_3410_; 
v___f_3408_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_2116__overap_3409_ = lean_panic_fn(v___f_3408_, v_msg_3402_);
v___x_3410_ = lean_apply_5(v___x_2116__overap_3409_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, lean_box(0));
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_msg_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_msg_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(lean_object* v_bs_3418_, lean_object* v_k_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3418_, v_k_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3425_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3425_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3425_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg___boxed(lean_object* v_bs_3442_, lean_object* v_k_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3442_, v_k_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec_ref(v_bs_3442_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(lean_object* v_00_u03b1_3450_, lean_object* v_bs_3451_, lean_object* v_k_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3451_, v_k_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3459_, lean_object* v_bs_3460_, lean_object* v_k_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(v_00_u03b1_3459_, v_bs_3460_, v_k_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec_ref(v_bs_3460_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(size_t v_sz_3468_, size_t v_i_3469_, lean_object* v_bs_3470_){
_start:
{
uint8_t v___x_3471_; 
v___x_3471_ = lean_usize_dec_lt(v_i_3469_, v_sz_3468_);
if (v___x_3471_ == 0)
{
return v_bs_3470_;
}
else
{
lean_object* v_v_3472_; lean_object* v___x_3473_; lean_object* v_bs_x27_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; size_t v___x_3479_; size_t v___x_3480_; lean_object* v___x_3481_; 
v_v_3472_ = lean_array_uget(v_bs_3470_, v_i_3469_);
v___x_3473_ = lean_unsigned_to_nat(0u);
v_bs_x27_3474_ = lean_array_uset(v_bs_3470_, v_i_3469_, v___x_3473_);
v___x_3475_ = l_Lean_Expr_fvarId_x21(v_v_3472_);
lean_dec(v_v_3472_);
v___x_3476_ = 1;
v___x_3477_ = lean_box(v___x_3476_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3475_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_add(v_i_3469_, v___x_3479_);
v___x_3481_ = lean_array_uset(v_bs_x27_3474_, v_i_3469_, v___x_3478_);
v_i_3469_ = v___x_3480_;
v_bs_3470_ = v___x_3481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0___boxed(lean_object* v_sz_3483_, lean_object* v_i_3484_, lean_object* v_bs_3485_){
_start:
{
size_t v_sz_boxed_3486_; size_t v_i_boxed_3487_; lean_object* v_res_3488_; 
v_sz_boxed_3486_ = lean_unbox_usize(v_sz_3483_);
lean_dec(v_sz_3483_);
v_i_boxed_3487_ = lean_unbox_usize(v_i_3484_);
lean_dec(v_i_3484_);
v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_boxed_3486_, v_i_boxed_3487_, v_bs_3485_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(lean_object* v_bs_3489_, lean_object* v_k_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
size_t v_sz_3496_; size_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_sz_3496_ = lean_array_size(v_bs_3489_);
v___x_3497_ = ((size_t)0ULL);
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_3496_, v___x_3497_, v_bs_3489_);
v___x_3499_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v___x_3498_, v_k_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec_ref(v___x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg___boxed(lean_object* v_bs_3500_, lean_object* v_k_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3500_, v_k_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_00_u03b1_3508_, lean_object* v_bs_3509_, lean_object* v_k_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3509_, v_k_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3517_, lean_object* v_bs_3518_, lean_object* v_k_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_00_u03b1_3517_, v_bs_3518_, v_k_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3526_, lean_object* v_rhss_3527_, lean_object* v_lhs_3528_, lean_object* v_eqs_3529_, lean_object* v_hyps_3530_, uint8_t v_subsingletonInstImplicitRhs_3531_, lean_object* v_f_3532_, lean_object* v_info_3533_, lean_object* v_kinds_3534_, lean_object* v_lhss_3535_, lean_object* v_b_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3542_ = lean_unsigned_to_nat(1u);
v___x_3543_ = lean_nat_add(v_i_3526_, v___x_3542_);
lean_inc_ref(v_b_3536_);
v___x_3544_ = lean_array_push(v_rhss_3527_, v_b_3536_);
v___x_3545_ = l_Lean_Expr_fvarId_x21(v_lhs_3528_);
v___x_3546_ = l_Lean_Expr_fvarId_x21(v_b_3536_);
v___x_3547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
v___x_3549_ = lean_array_push(v_eqs_3529_, v___x_3548_);
v___x_3550_ = lean_array_push(v_hyps_3530_, v_b_3536_);
v___x_3551_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3531_, v_f_3532_, v_info_3533_, v_kinds_3534_, v_lhss_3535_, v___x_3543_, v___x_3544_, v___x_3549_, v___x_3550_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3552_, lean_object* v_rhss_3553_, lean_object* v_lhs_3554_, lean_object* v_eqs_3555_, lean_object* v_hyps_3556_, lean_object* v_subsingletonInstImplicitRhs_3557_, lean_object* v_f_3558_, lean_object* v_info_3559_, lean_object* v_kinds_3560_, lean_object* v_lhss_3561_, lean_object* v_b_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3568_; lean_object* v_res_3569_; 
v_subsingletonInstImplicitRhs_boxed_3568_ = lean_unbox(v_subsingletonInstImplicitRhs_3557_);
v_res_3569_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3552_, v_rhss_3553_, v_lhs_3554_, v_eqs_3555_, v_hyps_3556_, v_subsingletonInstImplicitRhs_boxed_3568_, v_f_3558_, v_info_3559_, v_kinds_3560_, v_lhss_3561_, v_b_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
lean_dec_ref(v_lhs_3554_);
lean_dec(v_i_3552_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3570_, lean_object* v_rhss_3571_, lean_object* v_lhs_3572_, lean_object* v_eqs_3573_, lean_object* v_hyps_3574_, uint8_t v_subsingletonInstImplicitRhs_3575_, lean_object* v_f_3576_, lean_object* v_info_3577_, lean_object* v_kinds_3578_, lean_object* v_lhss_3579_, lean_object* v_name_3580_, uint8_t v_bi_3581_, lean_object* v_type_3582_, uint8_t v_kind_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; lean_object* v___f_3590_; lean_object* v___x_3591_; 
v___x_3589_ = lean_box(v_subsingletonInstImplicitRhs_3575_);
v___f_3590_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3590_, 0, v_i_3570_);
lean_closure_set(v___f_3590_, 1, v_rhss_3571_);
lean_closure_set(v___f_3590_, 2, v_lhs_3572_);
lean_closure_set(v___f_3590_, 3, v_eqs_3573_);
lean_closure_set(v___f_3590_, 4, v_hyps_3574_);
lean_closure_set(v___f_3590_, 5, v___x_3589_);
lean_closure_set(v___f_3590_, 6, v_f_3576_);
lean_closure_set(v___f_3590_, 7, v_info_3577_);
lean_closure_set(v___f_3590_, 8, v_kinds_3578_);
lean_closure_set(v___f_3590_, 9, v_lhss_3579_);
v___x_3591_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3580_, v_bi_3581_, v_type_3582_, v___f_3590_, v_kind_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3591_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3591_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
v_a_3600_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3591_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3591_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3608_, lean_object* v_rhss_3609_, lean_object* v_lhss_3610_, lean_object* v_i_3611_, lean_object* v_eqs_3612_, lean_object* v_hyps_3613_, uint8_t v_subsingletonInstImplicitRhs_3614_, lean_object* v_f_3615_, lean_object* v_info_3616_, lean_object* v_kinds_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v___x_3623_; 
lean_inc(v___y_3621_);
lean_inc_ref(v___y_3620_);
lean_inc(v___y_3619_);
lean_inc_ref(v___y_3618_);
lean_inc_ref(v_lhs_3608_);
v___x_3623_ = lean_infer_type(v_lhs_3608_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___y_3631_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref(v___x_3623_);
v___x_3625_ = lean_array_get_size(v_rhss_3609_);
v___x_3626_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3610_);
v___x_3627_ = l_Array_toSubarray___redArg(v_lhss_3610_, v___x_3626_, v___x_3625_);
v___x_3628_ = l_Subarray_copy___redArg(v___x_3627_);
v___x_3629_ = l_Lean_Expr_replaceFVars(v_a_3624_, v___x_3628_, v_rhss_3609_);
lean_dec_ref(v___x_3628_);
lean_dec(v_a_3624_);
if (v_subsingletonInstImplicitRhs_3614_ == 0)
{
uint8_t v___x_3646_; 
v___x_3646_ = 1;
v___y_3631_ = v___x_3646_;
goto v___jp_3630_;
}
else
{
uint8_t v___x_3647_; 
v___x_3647_ = 3;
v___y_3631_ = v___x_3647_;
goto v___jp_3630_;
}
v___jp_3630_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = l_Lean_Expr_fvarId_x21(v_lhs_3608_);
lean_inc_ref(v___y_3618_);
v___x_3633_ = l_Lean_FVarId_getDecl___redArg(v___x_3632_, v___y_3618_, v___y_3620_, v___y_3621_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; lean_object* v___x_3637_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref(v___x_3633_);
v___x_3635_ = l_Lean_LocalDecl_userName(v_a_3634_);
lean_dec(v_a_3634_);
v___x_3636_ = 0;
v___x_3637_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3611_, v_rhss_3609_, v_lhs_3608_, v_eqs_3612_, v_hyps_3613_, v_subsingletonInstImplicitRhs_3614_, v_f_3615_, v_info_3616_, v_kinds_3617_, v_lhss_3610_, v___x_3635_, v___y_3631_, v___x_3629_, v___x_3636_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
return v___x_3637_;
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec_ref(v___x_3629_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v_kinds_3617_);
lean_dec_ref(v_info_3616_);
lean_dec_ref(v_f_3615_);
lean_dec_ref(v_hyps_3613_);
lean_dec_ref(v_eqs_3612_);
lean_dec(v_i_3611_);
lean_dec_ref(v_lhss_3610_);
lean_dec_ref(v_rhss_3609_);
lean_dec_ref(v_lhs_3608_);
v_a_3638_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3633_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3633_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v_kinds_3617_);
lean_dec_ref(v_info_3616_);
lean_dec_ref(v_f_3615_);
lean_dec_ref(v_hyps_3613_);
lean_dec_ref(v_eqs_3612_);
lean_dec(v_i_3611_);
lean_dec_ref(v_lhss_3610_);
lean_dec_ref(v_rhss_3609_);
lean_dec_ref(v_lhs_3608_);
v_a_3648_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3623_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3623_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3656_, lean_object* v_rhss_3657_, lean_object* v_lhss_3658_, lean_object* v_i_3659_, lean_object* v_eqs_3660_, lean_object* v_hyps_3661_, lean_object* v_subsingletonInstImplicitRhs_3662_, lean_object* v_f_3663_, lean_object* v_info_3664_, lean_object* v_kinds_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3671_; lean_object* v_res_3672_; 
v_subsingletonInstImplicitRhs_boxed_3671_ = lean_unbox(v_subsingletonInstImplicitRhs_3662_);
v_res_3672_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3656_, v_rhss_3657_, v_lhss_3658_, v_i_3659_, v_eqs_3660_, v_hyps_3661_, v_subsingletonInstImplicitRhs_boxed_3671_, v_f_3663_, v_info_3664_, v_kinds_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
return v_res_3672_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3674_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3675_ = lean_unsigned_to_nat(38u);
v___x_3676_ = lean_unsigned_to_nat(328u);
v___x_3677_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3678_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3679_ = l_mkPanicMessageWithDecl(v___x_3678_, v___x_3677_, v___x_3676_, v___x_3675_, v___x_3674_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3680_, lean_object* v_f_3681_, lean_object* v_info_3682_, lean_object* v_kinds_3683_, lean_object* v_lhss_3684_, lean_object* v_i_3685_, lean_object* v_rhss_3686_, lean_object* v_eqs_3687_, lean_object* v_hyps_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_){
_start:
{
lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3694_ = lean_array_get_size(v_kinds_3683_);
v___x_3695_ = lean_nat_dec_eq(v_i_3685_, v___x_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v_lhs_3697_; lean_object* v_hyps_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3696_ = l_Lean_instInhabitedExpr;
v_lhs_3697_ = lean_array_get_borrowed(v___x_3696_, v_lhss_3684_, v_i_3685_);
lean_inc(v_lhs_3697_);
v_hyps_3698_ = lean_array_push(v_hyps_3688_, v_lhs_3697_);
v___x_3699_ = 0;
v___x_3700_ = lean_box(v___x_3699_);
v___x_3701_ = lean_array_get_borrowed(v___x_3700_, v_kinds_3683_, v_i_3685_);
v___x_3702_ = lean_unbox(v___x_3701_);
switch(v___x_3702_)
{
case 0:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3703_ = lean_unsigned_to_nat(1u);
v___x_3704_ = lean_nat_add(v_i_3685_, v___x_3703_);
lean_dec(v_i_3685_);
lean_inc(v_lhs_3697_);
v___x_3705_ = lean_array_push(v_rhss_3686_, v_lhs_3697_);
v___x_3706_ = lean_box(0);
v___x_3707_ = lean_array_push(v_eqs_3687_, v___x_3706_);
v_i_3685_ = v___x_3704_;
v_rhss_3686_ = v___x_3705_;
v_eqs_3687_ = v___x_3707_;
v_hyps_3688_ = v_hyps_3698_;
goto _start;
}
case 2:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_inc(v_lhs_3697_);
v___x_3709_ = l_Lean_Expr_fvarId_x21(v_lhs_3697_);
lean_inc_ref(v_a_3689_);
v___x_3710_ = l_Lean_FVarId_getDecl___redArg(v___x_3709_, v_a_3689_, v_a_3691_, v_a_3692_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; lean_object* v___x_3716_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref(v___x_3710_);
v___x_3712_ = l_Lean_LocalDecl_userName(v_a_3711_);
v___x_3713_ = l_Lean_LocalDecl_binderInfo(v_a_3711_);
v___x_3714_ = l_Lean_LocalDecl_type(v_a_3711_);
lean_dec(v_a_3711_);
v___x_3715_ = 0;
lean_inc(v___x_3712_);
v___x_3716_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3685_, v_rhss_3686_, v_eqs_3687_, v_hyps_3698_, v_subsingletonInstImplicitRhs_3680_, v_f_3681_, v_info_3682_, v_kinds_3683_, v_lhss_3684_, v_lhs_3697_, v___x_3712_, v___x_3712_, v___x_3713_, v___x_3714_, v___x_3715_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
return v___x_3716_;
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v_hyps_3698_);
lean_dec(v_lhs_3697_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec_ref(v_eqs_3687_);
lean_dec_ref(v_rhss_3686_);
lean_dec(v_i_3685_);
lean_dec_ref(v_lhss_3684_);
lean_dec_ref(v_kinds_3683_);
lean_dec_ref(v_info_3682_);
lean_dec_ref(v_f_3681_);
v_a_3717_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3710_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3710_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
case 3:
{
lean_object* v___x_3725_; 
lean_inc(v_a_3692_);
lean_inc_ref(v_a_3691_);
lean_inc(v_a_3690_);
lean_inc_ref(v_a_3689_);
lean_inc(v_lhs_3697_);
v___x_3725_ = lean_infer_type(v_lhs_3697_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v_paramInfo_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v_backDeps_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref(v___x_3725_);
v_paramInfo_3727_ = lean_ctor_get(v_info_3682_, 0);
v___x_3728_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_3729_ = lean_array_get_borrowed(v___x_3728_, v_paramInfo_3727_, v_i_3685_);
v_backDeps_3730_ = lean_ctor_get(v___x_3729_, 0);
v___x_3731_ = lean_array_get_size(v_rhss_3686_);
v___x_3732_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3684_);
v___x_3733_ = l_Array_toSubarray___redArg(v_lhss_3684_, v___x_3732_, v___x_3731_);
v___x_3734_ = l_Subarray_copy___redArg(v___x_3733_);
v___x_3735_ = l_Lean_Expr_replaceFVars(v_a_3726_, v___x_3734_, v_rhss_3686_);
lean_dec_ref(v___x_3734_);
lean_dec(v_a_3726_);
v___x_3736_ = l_Lean_Expr_fvarId_x21(v_lhs_3697_);
lean_inc(v_a_3692_);
lean_inc_ref(v_a_3691_);
lean_inc(v_a_3690_);
lean_inc_ref(v_a_3689_);
v___x_3737_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3736_, v___x_3735_, v_backDeps_3730_, v_eqs_3687_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___x_3737_);
v___x_3739_ = lean_unsigned_to_nat(1u);
v___x_3740_ = lean_nat_add(v_i_3685_, v___x_3739_);
lean_dec(v_i_3685_);
v___x_3741_ = lean_array_push(v_rhss_3686_, v_a_3738_);
v___x_3742_ = lean_box(0);
v___x_3743_ = lean_array_push(v_eqs_3687_, v___x_3742_);
v_i_3685_ = v___x_3740_;
v_rhss_3686_ = v___x_3741_;
v_eqs_3687_ = v___x_3743_;
v_hyps_3688_ = v_hyps_3698_;
goto _start;
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec_ref(v_hyps_3698_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec_ref(v_eqs_3687_);
lean_dec_ref(v_rhss_3686_);
lean_dec(v_i_3685_);
lean_dec_ref(v_lhss_3684_);
lean_dec_ref(v_kinds_3683_);
lean_dec_ref(v_info_3682_);
lean_dec_ref(v_f_3681_);
v_a_3745_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3737_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3737_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec_ref(v_hyps_3698_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec_ref(v_eqs_3687_);
lean_dec_ref(v_rhss_3686_);
lean_dec(v_i_3685_);
lean_dec_ref(v_lhss_3684_);
lean_dec_ref(v_kinds_3683_);
lean_dec_ref(v_info_3682_);
lean_dec_ref(v_f_3681_);
v_a_3753_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3725_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3725_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
case 5:
{
lean_object* v___x_3761_; lean_object* v___f_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_inc(v_lhs_3697_);
v___x_3761_ = lean_box(v_subsingletonInstImplicitRhs_3680_);
lean_inc(v_lhs_3697_);
v___f_3762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3762_, 0, v_lhs_3697_);
lean_closure_set(v___f_3762_, 1, v_rhss_3686_);
lean_closure_set(v___f_3762_, 2, v_lhss_3684_);
lean_closure_set(v___f_3762_, 3, v_i_3685_);
lean_closure_set(v___f_3762_, 4, v_eqs_3687_);
lean_closure_set(v___f_3762_, 5, v_hyps_3698_);
lean_closure_set(v___f_3762_, 6, v___x_3761_);
lean_closure_set(v___f_3762_, 7, v_f_3681_);
lean_closure_set(v___f_3762_, 8, v_info_3682_);
lean_closure_set(v___f_3762_, 9, v_kinds_3683_);
v___x_3763_ = lean_unsigned_to_nat(1u);
v___x_3764_ = lean_mk_empty_array_with_capacity(v___x_3763_);
v___x_3765_ = lean_array_push(v___x_3764_, v_lhs_3697_);
v___x_3766_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v___x_3765_, v___f_3762_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
return v___x_3766_;
}
default: 
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_dec_ref(v_hyps_3698_);
lean_dec_ref(v_eqs_3687_);
lean_dec_ref(v_rhss_3686_);
lean_dec(v_i_3685_);
lean_dec_ref(v_lhss_3684_);
lean_dec_ref(v_kinds_3683_);
lean_dec_ref(v_info_3682_);
lean_dec_ref(v_f_3681_);
v___x_3767_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3768_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v___x_3767_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
return v___x_3768_;
}
}
}
else
{
lean_object* v_lhs_3769_; lean_object* v_rhs_3770_; lean_object* v___x_3771_; 
lean_dec_ref(v_eqs_3687_);
lean_dec(v_i_3685_);
lean_dec_ref(v_info_3682_);
lean_inc_ref(v_f_3681_);
v_lhs_3769_ = l_Lean_mkAppN(v_f_3681_, v_lhss_3684_);
lean_dec_ref(v_lhss_3684_);
v_rhs_3770_ = l_Lean_mkAppN(v_f_3681_, v_rhss_3686_);
lean_dec_ref(v_rhss_3686_);
lean_inc(v_a_3692_);
lean_inc_ref(v_a_3691_);
lean_inc(v_a_3690_);
lean_inc_ref(v_a_3689_);
v___x_3771_ = l_Lean_Meta_mkEq(v_lhs_3769_, v_rhs_3770_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; uint8_t v___x_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref(v___x_3771_);
v___x_3773_ = 0;
v___x_3774_ = 1;
v___x_3775_ = l_Lean_Meta_mkForallFVars(v_hyps_3688_, v_a_3772_, v___x_3773_, v___x_3695_, v___x_3695_, v___x_3774_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
lean_dec_ref(v_hyps_3688_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3777_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3775_);
lean_inc_ref(v_kinds_3683_);
lean_inc(v_a_3776_);
v___x_3777_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3776_, v_kinds_3683_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3786_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3786_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3786_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3784_; 
v___x_3782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3782_, 0, v_a_3776_);
lean_ctor_set(v___x_3782_, 1, v_a_3778_);
lean_ctor_set(v___x_3782_, 2, v_kinds_3683_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3782_);
v___x_3784_ = v___x_3780_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec(v_a_3776_);
lean_dec_ref(v_kinds_3683_);
v_a_3787_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3777_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3777_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec_ref(v_kinds_3683_);
v_a_3795_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3775_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3775_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec_ref(v_hyps_3688_);
lean_dec_ref(v_kinds_3683_);
v_a_3803_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3771_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3771_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3811_, lean_object* v_rhss_3812_, lean_object* v_b_3813_, lean_object* v_eqs_3814_, lean_object* v_hyps_3815_, uint8_t v_subsingletonInstImplicitRhs_3816_, lean_object* v_f_3817_, lean_object* v_info_3818_, lean_object* v_kinds_3819_, lean_object* v_lhss_3820_, lean_object* v_eq_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3827_ = lean_unsigned_to_nat(1u);
v___x_3828_ = lean_nat_add(v_i_3811_, v___x_3827_);
lean_inc_ref(v_b_3813_);
v___x_3829_ = lean_array_push(v_rhss_3812_, v_b_3813_);
v___x_3830_ = l_Lean_Expr_fvarId_x21(v_eq_3821_);
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
v___x_3833_ = lean_array_push(v_eqs_3814_, v___x_3832_);
v___x_3834_ = lean_array_push(v_hyps_3815_, v_b_3813_);
v___x_3835_ = lean_array_push(v___x_3834_, v_eq_3821_);
v___x_3836_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3816_, v_f_3817_, v_info_3818_, v_kinds_3819_, v_lhss_3820_, v___x_3828_, v___x_3829_, v___x_3833_, v___x_3835_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_3837_, lean_object* v_rhss_3838_, lean_object* v_b_3839_, lean_object* v_eqs_3840_, lean_object* v_hyps_3841_, lean_object* v_subsingletonInstImplicitRhs_3842_, lean_object* v_f_3843_, lean_object* v_info_3844_, lean_object* v_kinds_3845_, lean_object* v_lhss_3846_, lean_object* v_eq_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3853_; lean_object* v_res_3854_; 
v_subsingletonInstImplicitRhs_boxed_3853_ = lean_unbox(v_subsingletonInstImplicitRhs_3842_);
v_res_3854_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3837_, v_rhss_3838_, v_b_3839_, v_eqs_3840_, v_hyps_3841_, v_subsingletonInstImplicitRhs_boxed_3853_, v_f_3843_, v_info_3844_, v_kinds_3845_, v_lhss_3846_, v_eq_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v_i_3837_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(lean_object* v_lhs_3856_, lean_object* v_i_3857_, lean_object* v_rhss_3858_, lean_object* v_eqs_3859_, lean_object* v_hyps_3860_, uint8_t v_subsingletonInstImplicitRhs_3861_, lean_object* v_f_3862_, lean_object* v_info_3863_, lean_object* v_kinds_3864_, lean_object* v_lhss_3865_, lean_object* v___x_3866_, lean_object* v_b_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; 
lean_inc(v___y_3871_);
lean_inc_ref(v___y_3870_);
lean_inc(v___y_3869_);
lean_inc_ref(v___y_3868_);
lean_inc_ref(v_b_3867_);
v___x_3873_ = l_Lean_Meta_mkEq(v_lhs_3856_, v_b_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; lean_object* v___f_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref(v___x_3873_);
v___x_3875_ = lean_box(v_subsingletonInstImplicitRhs_3861_);
v___f_3876_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3876_, 0, v_i_3857_);
lean_closure_set(v___f_3876_, 1, v_rhss_3858_);
lean_closure_set(v___f_3876_, 2, v_b_3867_);
lean_closure_set(v___f_3876_, 3, v_eqs_3859_);
lean_closure_set(v___f_3876_, 4, v_hyps_3860_);
lean_closure_set(v___f_3876_, 5, v___x_3875_);
lean_closure_set(v___f_3876_, 6, v_f_3862_);
lean_closure_set(v___f_3876_, 7, v_info_3863_);
lean_closure_set(v___f_3876_, 8, v_kinds_3864_);
lean_closure_set(v___f_3876_, 9, v_lhss_3865_);
v___x_3877_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0));
v___x_3878_ = lean_name_append_before(v___x_3866_, v___x_3877_);
v___x_3879_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3878_, v_a_3874_, v___f_3876_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3879_;
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v_b_3867_);
lean_dec(v___x_3866_);
lean_dec_ref(v_lhss_3865_);
lean_dec_ref(v_kinds_3864_);
lean_dec_ref(v_info_3863_);
lean_dec_ref(v_f_3862_);
lean_dec_ref(v_hyps_3860_);
lean_dec_ref(v_eqs_3859_);
lean_dec_ref(v_rhss_3858_);
lean_dec(v_i_3857_);
v_a_3880_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3873_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3873_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v_lhs_3888_ = _args[0];
lean_object* v_i_3889_ = _args[1];
lean_object* v_rhss_3890_ = _args[2];
lean_object* v_eqs_3891_ = _args[3];
lean_object* v_hyps_3892_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3893_ = _args[5];
lean_object* v_f_3894_ = _args[6];
lean_object* v_info_3895_ = _args[7];
lean_object* v_kinds_3896_ = _args[8];
lean_object* v_lhss_3897_ = _args[9];
lean_object* v___x_3898_ = _args[10];
lean_object* v_b_3899_ = _args[11];
lean_object* v___y_3900_ = _args[12];
lean_object* v___y_3901_ = _args[13];
lean_object* v___y_3902_ = _args[14];
lean_object* v___y_3903_ = _args[15];
lean_object* v___y_3904_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3905_; lean_object* v_res_3906_; 
v_subsingletonInstImplicitRhs_boxed_3905_ = lean_unbox(v_subsingletonInstImplicitRhs_3893_);
v_res_3906_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(v_lhs_3888_, v_i_3889_, v_rhss_3890_, v_eqs_3891_, v_hyps_3892_, v_subsingletonInstImplicitRhs_boxed_3905_, v_f_3894_, v_info_3895_, v_kinds_3896_, v_lhss_3897_, v___x_3898_, v_b_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_3907_, lean_object* v_rhss_3908_, lean_object* v_eqs_3909_, lean_object* v_hyps_3910_, uint8_t v_subsingletonInstImplicitRhs_3911_, lean_object* v_f_3912_, lean_object* v_info_3913_, lean_object* v_kinds_3914_, lean_object* v_lhss_3915_, lean_object* v_lhs_3916_, lean_object* v___x_3917_, lean_object* v_name_3918_, uint8_t v_bi_3919_, lean_object* v_type_3920_, uint8_t v_kind_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; lean_object* v___f_3928_; lean_object* v___x_3929_; 
v___x_3927_ = lean_box(v_subsingletonInstImplicitRhs_3911_);
v___f_3928_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3928_, 0, v_lhs_3916_);
lean_closure_set(v___f_3928_, 1, v_i_3907_);
lean_closure_set(v___f_3928_, 2, v_rhss_3908_);
lean_closure_set(v___f_3928_, 3, v_eqs_3909_);
lean_closure_set(v___f_3928_, 4, v_hyps_3910_);
lean_closure_set(v___f_3928_, 5, v___x_3927_);
lean_closure_set(v___f_3928_, 6, v_f_3912_);
lean_closure_set(v___f_3928_, 7, v_info_3913_);
lean_closure_set(v___f_3928_, 8, v_kinds_3914_);
lean_closure_set(v___f_3928_, 9, v_lhss_3915_);
lean_closure_set(v___f_3928_, 10, v___x_3917_);
v___x_3929_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3918_, v_bi_3919_, v_type_3920_, v___f_3928_, v_kind_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
v_a_3938_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3929_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3929_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object** _args){
lean_object* v_i_3946_ = _args[0];
lean_object* v_rhss_3947_ = _args[1];
lean_object* v_eqs_3948_ = _args[2];
lean_object* v_hyps_3949_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3950_ = _args[4];
lean_object* v_f_3951_ = _args[5];
lean_object* v_info_3952_ = _args[6];
lean_object* v_kinds_3953_ = _args[7];
lean_object* v_lhss_3954_ = _args[8];
lean_object* v_lhs_3955_ = _args[9];
lean_object* v___x_3956_ = _args[10];
lean_object* v_name_3957_ = _args[11];
lean_object* v_bi_3958_ = _args[12];
lean_object* v_type_3959_ = _args[13];
lean_object* v_kind_3960_ = _args[14];
lean_object* v___y_3961_ = _args[15];
lean_object* v___y_3962_ = _args[16];
lean_object* v___y_3963_ = _args[17];
lean_object* v___y_3964_ = _args[18];
lean_object* v___y_3965_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3966_; uint8_t v_bi_boxed_3967_; uint8_t v_kind_boxed_3968_; lean_object* v_res_3969_; 
v_subsingletonInstImplicitRhs_boxed_3966_ = lean_unbox(v_subsingletonInstImplicitRhs_3950_);
v_bi_boxed_3967_ = lean_unbox(v_bi_3958_);
v_kind_boxed_3968_ = lean_unbox(v_kind_3960_);
v_res_3969_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3946_, v_rhss_3947_, v_eqs_3948_, v_hyps_3949_, v_subsingletonInstImplicitRhs_boxed_3966_, v_f_3951_, v_info_3952_, v_kinds_3953_, v_lhss_3954_, v_lhs_3955_, v___x_3956_, v_name_3957_, v_bi_boxed_3967_, v_type_3959_, v_kind_boxed_3968_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_3970_ = _args[0];
lean_object* v_rhss_3971_ = _args[1];
lean_object* v_lhs_3972_ = _args[2];
lean_object* v_eqs_3973_ = _args[3];
lean_object* v_hyps_3974_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3975_ = _args[5];
lean_object* v_f_3976_ = _args[6];
lean_object* v_info_3977_ = _args[7];
lean_object* v_kinds_3978_ = _args[8];
lean_object* v_lhss_3979_ = _args[9];
lean_object* v_name_3980_ = _args[10];
lean_object* v_bi_3981_ = _args[11];
lean_object* v_type_3982_ = _args[12];
lean_object* v_kind_3983_ = _args[13];
lean_object* v___y_3984_ = _args[14];
lean_object* v___y_3985_ = _args[15];
lean_object* v___y_3986_ = _args[16];
lean_object* v___y_3987_ = _args[17];
lean_object* v___y_3988_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3989_; uint8_t v_bi_boxed_3990_; uint8_t v_kind_boxed_3991_; lean_object* v_res_3992_; 
v_subsingletonInstImplicitRhs_boxed_3989_ = lean_unbox(v_subsingletonInstImplicitRhs_3975_);
v_bi_boxed_3990_ = lean_unbox(v_bi_3981_);
v_kind_boxed_3991_ = lean_unbox(v_kind_3983_);
v_res_3992_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3970_, v_rhss_3971_, v_lhs_3972_, v_eqs_3973_, v_hyps_3974_, v_subsingletonInstImplicitRhs_boxed_3989_, v_f_3976_, v_info_3977_, v_kinds_3978_, v_lhss_3979_, v_name_3980_, v_bi_boxed_3990_, v_type_3982_, v_kind_boxed_3991_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* v_subsingletonInstImplicitRhs_3993_, lean_object* v_f_3994_, lean_object* v_info_3995_, lean_object* v_kinds_3996_, lean_object* v_lhss_3997_, lean_object* v_i_3998_, lean_object* v_rhss_3999_, lean_object* v_eqs_4000_, lean_object* v_hyps_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4007_; lean_object* v_res_4008_; 
v_subsingletonInstImplicitRhs_boxed_4007_ = lean_unbox(v_subsingletonInstImplicitRhs_3993_);
v_res_4008_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_boxed_4007_, v_f_3994_, v_info_3995_, v_kinds_3996_, v_lhss_3997_, v_i_3998_, v_rhss_3999_, v_eqs_4000_, v_hyps_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* v___x_4009_, uint8_t v_subsingletonInstImplicitRhs_4010_, lean_object* v_f_4011_, lean_object* v_info_4012_, lean_object* v_kinds_4013_, lean_object* v_lhss_4014_, lean_object* v_x_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; uint8_t v___x_4022_; 
v___x_4021_ = lean_array_get_size(v_lhss_4014_);
v___x_4022_ = lean_nat_dec_eq(v___x_4021_, v___x_4009_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec_ref(v_lhss_4014_);
lean_dec_ref(v_kinds_4013_);
lean_dec_ref(v_info_4012_);
lean_dec_ref(v_f_4011_);
v___x_4023_ = lean_box(0);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4025_ = lean_unsigned_to_nat(0u);
v___x_4026_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_4027_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_4010_, v_f_4011_, v_info_4012_, v_kinds_4013_, v_lhss_4014_, v___x_4025_, v___x_4026_, v___x_4026_, v___x_4026_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4036_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4036_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4036_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v_a_4028_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 0, v___x_4032_);
v___x_4034_ = v___x_4030_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
v_a_4037_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4027_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4027_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* v___x_4045_, lean_object* v_subsingletonInstImplicitRhs_4046_, lean_object* v_f_4047_, lean_object* v_info_4048_, lean_object* v_kinds_4049_, lean_object* v_lhss_4050_, lean_object* v_x_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4057_; lean_object* v_res_4058_; 
v_subsingletonInstImplicitRhs_boxed_4057_ = lean_unbox(v_subsingletonInstImplicitRhs_4046_);
v_res_4058_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4045_, v_subsingletonInstImplicitRhs_boxed_4057_, v_f_4047_, v_info_4048_, v_kinds_4049_, v_lhss_4050_, v_x_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec_ref(v_x_4051_);
lean_dec(v___x_4045_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t v_subsingletonInstImplicitRhs_4059_, lean_object* v_f_4060_, lean_object* v_info_4061_, lean_object* v_kinds_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v___y_4069_; uint8_t v___y_4070_; lean_object* v_a_4075_; lean_object* v___x_4078_; 
lean_inc(v_a_4066_);
lean_inc_ref(v_a_4065_);
lean_inc(v_a_4064_);
lean_inc_ref(v_a_4063_);
lean_inc_ref(v_f_4060_);
v___x_4078_ = lean_infer_type(v_f_4060_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4093_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4093_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4093_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___f_4085_; lean_object* v___x_4087_; 
v___x_4083_ = lean_array_get_size(v_kinds_4062_);
v___x_4084_ = lean_box(v_subsingletonInstImplicitRhs_4059_);
v___f_4085_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4085_, 0, v___x_4083_);
lean_closure_set(v___f_4085_, 1, v___x_4084_);
lean_closure_set(v___f_4085_, 2, v_f_4060_);
lean_closure_set(v___f_4085_, 3, v_info_4061_);
lean_closure_set(v___f_4085_, 4, v_kinds_4062_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set_tag(v___x_4081_, 1);
lean_ctor_set(v___x_4081_, 0, v___x_4083_);
v___x_4087_ = v___x_4081_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4083_);
v___x_4087_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
uint8_t v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = 1;
v___x_4089_ = 0;
v___x_4090_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_4079_, v___x_4087_, v___f_4085_, v___x_4088_, v___x_4089_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
if (lean_obj_tag(v___x_4090_) == 0)
{
return v___x_4090_;
}
else
{
lean_object* v_a_4091_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref(v___x_4090_);
v_a_4075_ = v_a_4091_;
goto v___jp_4074_;
}
}
}
}
else
{
lean_object* v_a_4094_; 
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec_ref(v_kinds_4062_);
lean_dec_ref(v_info_4061_);
lean_dec_ref(v_f_4060_);
v_a_4094_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4094_);
lean_dec_ref(v___x_4078_);
v_a_4075_ = v_a_4094_;
goto v___jp_4074_;
}
v___jp_4068_:
{
if (v___y_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_dec_ref(v___y_4069_);
v___x_4071_ = lean_box(0);
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
else
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___y_4069_);
return v___x_4073_;
}
}
v___jp_4074_:
{
uint8_t v___x_4076_; 
v___x_4076_ = l_Lean_Exception_isInterrupt(v_a_4075_);
if (v___x_4076_ == 0)
{
uint8_t v___x_4077_; 
lean_inc_ref(v_a_4075_);
v___x_4077_ = l_Lean_Exception_isRuntime(v_a_4075_);
v___y_4069_ = v_a_4075_;
v___y_4070_ = v___x_4077_;
goto v___jp_4068_;
}
else
{
v___y_4069_ = v_a_4075_;
v___y_4070_ = v___x_4076_;
goto v___jp_4068_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* v_subsingletonInstImplicitRhs_4095_, lean_object* v_f_4096_, lean_object* v_info_4097_, lean_object* v_kinds_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4104_; lean_object* v_res_4105_; 
v_subsingletonInstImplicitRhs_boxed_4104_ = lean_unbox(v_subsingletonInstImplicitRhs_4095_);
v_res_4105_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_boxed_4104_, v_f_4096_, v_info_4097_, v_kinds_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t v_sz_4106_, size_t v_i_4107_, lean_object* v_bs_4108_){
_start:
{
uint8_t v___x_4109_; 
v___x_4109_ = lean_usize_dec_lt(v_i_4107_, v_sz_4106_);
if (v___x_4109_ == 0)
{
return v_bs_4108_;
}
else
{
lean_object* v_v_4110_; lean_object* v___x_4111_; lean_object* v_bs_x27_4112_; uint8_t v___y_4114_; uint8_t v___x_4120_; 
v_v_4110_ = lean_array_uget(v_bs_4108_, v_i_4107_);
v___x_4111_ = lean_unsigned_to_nat(0u);
v_bs_x27_4112_ = lean_array_uset(v_bs_4108_, v_i_4107_, v___x_4111_);
v___x_4120_ = lean_unbox(v_v_4110_);
switch(v___x_4120_)
{
case 3:
{
uint8_t v___x_4121_; 
lean_dec(v_v_4110_);
v___x_4121_ = 0;
v___y_4114_ = v___x_4121_;
goto v___jp_4113_;
}
case 5:
{
uint8_t v___x_4122_; 
lean_dec(v_v_4110_);
v___x_4122_ = 0;
v___y_4114_ = v___x_4122_;
goto v___jp_4113_;
}
default: 
{
uint8_t v___x_4123_; 
v___x_4123_ = lean_unbox(v_v_4110_);
lean_dec(v_v_4110_);
v___y_4114_ = v___x_4123_;
goto v___jp_4113_;
}
}
v___jp_4113_:
{
size_t v___x_4115_; size_t v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4115_ = ((size_t)1ULL);
v___x_4116_ = lean_usize_add(v_i_4107_, v___x_4115_);
v___x_4117_ = lean_box(v___y_4114_);
v___x_4118_ = lean_array_uset(v_bs_x27_4112_, v_i_4107_, v___x_4117_);
v_i_4107_ = v___x_4116_;
v_bs_4108_ = v___x_4118_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* v_sz_4124_, lean_object* v_i_4125_, lean_object* v_bs_4126_){
_start:
{
size_t v_sz_boxed_4127_; size_t v_i_boxed_4128_; lean_object* v_res_4129_; 
v_sz_boxed_4127_ = lean_unbox_usize(v_sz_4124_);
lean_dec(v_sz_4124_);
v_i_boxed_4128_ = lean_unbox_usize(v_i_4125_);
lean_dec(v_i_4125_);
v_res_4129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_4127_, v_i_boxed_4128_, v_bs_4126_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* v_f_4130_, lean_object* v_info_4131_, lean_object* v_kinds_4132_, uint8_t v_subsingletonInstImplicitRhs_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v___x_4139_; 
lean_inc(v_a_4137_);
lean_inc_ref(v_a_4136_);
lean_inc(v_a_4135_);
lean_inc_ref(v_a_4134_);
lean_inc_ref(v_kinds_4132_);
lean_inc_ref(v_info_4131_);
lean_inc_ref(v_f_4130_);
v___x_4139_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4133_, v_f_4130_, v_info_4131_, v_kinds_4132_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
if (lean_obj_tag(v_a_4140_) == 1)
{
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec_ref(v_kinds_4132_);
lean_dec_ref(v_info_4131_);
lean_dec_ref(v_f_4130_);
return v___x_4139_;
}
else
{
lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4153_; 
lean_dec(v_a_4140_);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4153_ == 0)
{
lean_object* v_unused_4154_; 
v_unused_4154_ = lean_ctor_get(v___x_4139_, 0);
lean_dec(v_unused_4154_);
v___x_4142_ = v___x_4139_;
v_isShared_4143_ = v_isSharedCheck_4153_;
goto v_resetjp_4141_;
}
else
{
lean_dec(v___x_4139_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4153_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
uint8_t v___x_4144_; 
v___x_4144_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_4132_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec_ref(v_kinds_4132_);
lean_dec_ref(v_info_4131_);
lean_dec_ref(v_f_4130_);
v___x_4145_ = lean_box(0);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 0, v___x_4145_);
v___x_4147_ = v___x_4142_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
else
{
size_t v_sz_4149_; size_t v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_del_object(v___x_4142_);
v_sz_4149_ = lean_array_size(v_kinds_4132_);
v___x_4150_ = ((size_t)0ULL);
v___x_4151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4149_, v___x_4150_, v_kinds_4132_);
v___x_4152_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4133_, v_f_4130_, v_info_4131_, v___x_4151_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
return v___x_4152_;
}
}
}
}
else
{
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec_ref(v_kinds_4132_);
lean_dec_ref(v_info_4131_);
lean_dec_ref(v_f_4130_);
return v___x_4139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* v_f_4155_, lean_object* v_info_4156_, lean_object* v_kinds_4157_, lean_object* v_subsingletonInstImplicitRhs_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4164_; lean_object* v_res_4165_; 
v_subsingletonInstImplicitRhs_boxed_4164_ = lean_unbox(v_subsingletonInstImplicitRhs_4158_);
v_res_4165_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4155_, v_info_4156_, v_kinds_4157_, v_subsingletonInstImplicitRhs_boxed_4164_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* v_f_4166_, uint8_t v_subsingletonInstImplicitRhs_4167_, lean_object* v_maxArgs_x3f_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v___x_4174_; lean_object* v_a_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4174_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_4166_, v_a_4170_);
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref(v___x_4174_);
v___x_4176_ = l_Lean_Expr_cleanupAnnotations(v_a_4175_);
lean_inc(v_a_4172_);
lean_inc_ref(v_a_4171_);
lean_inc(v_a_4170_);
lean_inc_ref(v_a_4169_);
lean_inc_ref(v___x_4176_);
v___x_4177_ = l_Lean_Meta_getFunInfo(v___x_4176_, v_maxArgs_x3f_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4179_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref(v___x_4177_);
lean_inc(v_a_4172_);
lean_inc_ref(v_a_4171_);
lean_inc(v_a_4170_);
lean_inc_ref(v_a_4169_);
lean_inc_ref(v___x_4176_);
v___x_4179_ = l_Lean_Meta_getCongrSimpKinds(v___x_4176_, v_a_4178_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4181_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref(v___x_4179_);
v___x_4181_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4176_, v_a_4178_, v_a_4180_, v_subsingletonInstImplicitRhs_4167_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
return v___x_4181_;
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
lean_dec(v_a_4178_);
lean_dec_ref(v___x_4176_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
v_a_4182_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4179_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4179_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec_ref(v___x_4176_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
v_a_4190_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4177_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4177_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* v_f_4198_, lean_object* v_subsingletonInstImplicitRhs_4199_, lean_object* v_maxArgs_x3f_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4206_; lean_object* v_res_4207_; 
v_subsingletonInstImplicitRhs_boxed_4206_ = lean_unbox(v_subsingletonInstImplicitRhs_4199_);
v_res_4207_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4198_, v_subsingletonInstImplicitRhs_boxed_4206_, v_maxArgs_x3f_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
return v_res_4207_;
}
}
static lean_object* _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4212_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4213_ = lean_string_utf8_byte_size(v___x_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4214_){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4215_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4216_ = lean_string_utf8_byte_size(v_s_4214_);
v___x_4217_ = lean_obj_once(&l_Lean_Meta_isHCongrReservedNameSuffix___closed__0, &l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0);
v___x_4218_ = lean_nat_dec_le(v___x_4217_, v___x_4216_);
if (v___x_4218_ == 0)
{
lean_dec_ref(v_s_4214_);
return v___x_4218_;
}
else
{
lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4219_ = lean_unsigned_to_nat(0u);
v___x_4220_ = lean_string_memcmp(v_s_4214_, v___x_4215_, v___x_4219_, v___x_4219_, v___x_4217_);
if (v___x_4220_ == 0)
{
lean_dec_ref(v_s_4214_);
return v___x_4220_;
}
else
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4221_ = lean_unsigned_to_nat(7u);
lean_inc_ref(v_s_4214_);
v___x_4222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4222_, 0, v_s_4214_);
lean_ctor_set(v___x_4222_, 1, v___x_4219_);
lean_ctor_set(v___x_4222_, 2, v___x_4216_);
v___x_4223_ = l_String_Slice_Pos_nextn(v___x_4222_, v___x_4219_, v___x_4221_);
lean_dec_ref(v___x_4222_);
v___x_4224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4224_, 0, v_s_4214_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
lean_ctor_set(v___x_4224_, 2, v___x_4216_);
v___x_4225_ = l_String_Slice_isNat(v___x_4224_);
lean_dec_ref(v___x_4224_);
return v___x_4225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* v_s_4226_){
_start:
{
uint8_t v_res_4227_; lean_object* v_r_4228_; 
v_res_4227_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4226_);
v_r_4228_ = lean_box(v_res_4227_);
return v_r_4228_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = lean_unsigned_to_nat(3482611248u);
v___x_4279_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4280_ = l_Lean_Name_num___override(v___x_4279_, v___x_4278_);
return v___x_4280_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4283_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4284_ = l_Lean_Name_str___override(v___x_4283_, v___x_4282_);
return v___x_4284_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4286_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4287_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4288_ = l_Lean_Name_str___override(v___x_4287_, v___x_4286_);
return v___x_4288_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4289_ = lean_unsigned_to_nat(2u);
v___x_4290_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4291_ = l_Lean_Name_num___override(v___x_4290_, v___x_4289_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4293_; uint8_t v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4293_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4294_ = 0;
v___x_4295_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4296_ = l_Lean_registerTraceClass(v___x_4293_, v___x_4294_, v___x_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4299_, lean_object* v_as_4300_, size_t v_i_4301_, size_t v_stop_4302_, lean_object* v_b_4303_){
_start:
{
lean_object* v___y_4305_; uint8_t v___x_4309_; 
v___x_4309_ = lean_usize_dec_eq(v_i_4301_, v_stop_4302_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4310_; lean_object* v_fst_4311_; uint8_t v___x_4312_; 
v___x_4310_ = lean_array_uget_borrowed(v_as_4300_, v_i_4301_);
v_fst_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_fst_4311_);
lean_inc_ref(v_env_4299_);
v___x_4312_ = l_Lean_Environment_contains(v_env_4299_, v_fst_4311_, v___x_4309_);
if (v___x_4312_ == 0)
{
v___y_4305_ = v_b_4303_;
goto v___jp_4304_;
}
else
{
lean_object* v___x_4313_; 
lean_inc(v___x_4310_);
v___x_4313_ = lean_array_push(v_b_4303_, v___x_4310_);
v___y_4305_ = v___x_4313_;
goto v___jp_4304_;
}
}
else
{
lean_dec_ref(v_env_4299_);
return v_b_4303_;
}
v___jp_4304_:
{
size_t v___x_4306_; size_t v___x_4307_; 
v___x_4306_ = ((size_t)1ULL);
v___x_4307_ = lean_usize_add(v_i_4301_, v___x_4306_);
v_i_4301_ = v___x_4307_;
v_b_4303_ = v___y_4305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4314_, lean_object* v_as_4315_, lean_object* v_i_4316_, lean_object* v_stop_4317_, lean_object* v_b_4318_){
_start:
{
size_t v_i_boxed_4319_; size_t v_stop_boxed_4320_; lean_object* v_res_4321_; 
v_i_boxed_4319_ = lean_unbox_usize(v_i_4316_);
lean_dec(v_i_4316_);
v_stop_boxed_4320_ = lean_unbox_usize(v_stop_4317_);
lean_dec(v_stop_4317_);
v_res_4321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4314_, v_as_4315_, v_i_boxed_4319_, v_stop_boxed_4320_, v_b_4318_);
lean_dec_ref(v_as_4315_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4322_, lean_object* v_x_4323_){
_start:
{
if (lean_obj_tag(v_x_4323_) == 0)
{
lean_object* v_k_4324_; lean_object* v_v_4325_; lean_object* v_l_4326_; lean_object* v_r_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_k_4324_ = lean_ctor_get(v_x_4323_, 1);
v_v_4325_ = lean_ctor_get(v_x_4323_, 2);
v_l_4326_ = lean_ctor_get(v_x_4323_, 3);
v_r_4327_ = lean_ctor_get(v_x_4323_, 4);
v___x_4328_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4322_, v_l_4326_);
lean_inc(v_v_4325_);
lean_inc(v_k_4324_);
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v_k_4324_);
lean_ctor_set(v___x_4329_, 1, v_v_4325_);
v___x_4330_ = lean_array_push(v___x_4328_, v___x_4329_);
v_init_4322_ = v___x_4330_;
v_x_4323_ = v_r_4327_;
goto _start;
}
else
{
return v_init_4322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4332_, lean_object* v_x_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4332_, v_x_4333_);
lean_dec(v_x_4333_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4339_, lean_object* v_s_4340_, uint8_t v_x_4341_){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; 
v___x_4342_ = lean_unsigned_to_nat(0u);
v___x_4343_ = ((lean_object*)(l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4344_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4343_, v_s_4340_);
v___x_4345_ = lean_array_get_size(v___x_4344_);
v___x_4346_ = ((lean_object*)(l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4347_ = lean_nat_dec_lt(v___x_4342_, v___x_4345_);
if (v___x_4347_ == 0)
{
lean_dec_ref(v___x_4344_);
lean_dec_ref(v_env_4339_);
return v___x_4346_;
}
else
{
uint8_t v___x_4348_; 
v___x_4348_ = lean_nat_dec_le(v___x_4345_, v___x_4345_);
if (v___x_4348_ == 0)
{
if (v___x_4347_ == 0)
{
lean_dec_ref(v___x_4344_);
lean_dec_ref(v_env_4339_);
return v___x_4346_;
}
else
{
size_t v___x_4349_; size_t v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = ((size_t)0ULL);
v___x_4350_ = lean_usize_of_nat(v___x_4345_);
v___x_4351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4339_, v___x_4344_, v___x_4349_, v___x_4350_, v___x_4346_);
lean_dec_ref(v___x_4344_);
return v___x_4351_;
}
}
else
{
size_t v___x_4352_; size_t v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = ((size_t)0ULL);
v___x_4353_ = lean_usize_of_nat(v___x_4345_);
v___x_4354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4339_, v___x_4344_, v___x_4352_, v___x_4353_, v___x_4346_);
lean_dec_ref(v___x_4344_);
return v___x_4354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4355_, lean_object* v_s_4356_, lean_object* v_x_4357_){
_start:
{
uint8_t v_x_410__boxed_4358_; lean_object* v_res_4359_; 
v_x_410__boxed_4358_ = lean_unbox(v_x_4357_);
v_res_4359_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4355_, v_s_4356_, v_x_410__boxed_4358_);
lean_dec(v_s_4356_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___f_4369_ = ((lean_object*)(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4370_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4371_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4372_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4370_, v___x_4371_, v___f_4369_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4375_, lean_object* v_t_4376_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4375_, v_t_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4378_, lean_object* v_t_4379_){
_start:
{
lean_object* v_res_4380_; 
v_res_4380_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4378_, v_t_4379_);
lean_dec(v_t_4379_);
return v_res_4380_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object* v_env_4381_, lean_object* v_n_4382_){
_start:
{
if (lean_obj_tag(v_n_4382_) == 1)
{
lean_object* v_pre_4383_; lean_object* v_str_4384_; uint8_t v___y_4386_; uint8_t v___x_4388_; 
v_pre_4383_ = lean_ctor_get(v_n_4382_, 0);
lean_inc(v_pre_4383_);
v_str_4384_ = lean_ctor_get(v_n_4382_, 1);
lean_inc_ref(v_str_4384_);
lean_dec_ref(v_n_4382_);
lean_inc_ref(v_str_4384_);
v___x_4388_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4384_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; uint8_t v___x_4390_; 
v___x_4389_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4390_ = lean_string_dec_eq(v_str_4384_, v___x_4389_);
lean_dec_ref(v_str_4384_);
v___y_4386_ = v___x_4390_;
goto v___jp_4385_;
}
else
{
lean_dec_ref(v_str_4384_);
v___y_4386_ = v___x_4388_;
goto v___jp_4385_;
}
v___jp_4385_:
{
if (v___y_4386_ == 0)
{
lean_dec(v_pre_4383_);
lean_dec_ref(v_env_4381_);
return v___y_4386_;
}
else
{
uint8_t v___x_4387_; 
v___x_4387_ = l_Lean_Environment_contains(v_env_4381_, v_pre_4383_, v___y_4386_);
return v___x_4387_;
}
}
}
else
{
uint8_t v___x_4391_; 
lean_dec(v_n_4382_);
lean_dec_ref(v_env_4381_);
v___x_4391_ = 0;
return v___x_4391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_env_4392_, lean_object* v_n_4393_){
_start:
{
uint8_t v_res_4394_; lean_object* v_r_4395_; 
v_res_4394_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4392_, v_n_4393_);
v_r_4395_ = lean_box(v_res_4394_);
return v_r_4395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4398_; lean_object* v___x_4399_; 
v___f_4398_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_));
v___x_4399_ = l_Lean_registerReservedNamePredicate(v___f_4398_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object* v_thm_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v___x_4405_; lean_object* v_env_4406_; lean_object* v_toConstantVal_4407_; lean_object* v_value_4408_; lean_object* v_all_4409_; uint8_t v___y_4411_; lean_object* v_type_4419_; uint8_t v___x_4420_; 
v___x_4405_ = lean_st_ref_get(v___y_4403_);
v_env_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc_ref(v_env_4406_);
lean_dec(v___x_4405_);
v_toConstantVal_4407_ = lean_ctor_get(v_thm_4402_, 0);
v_value_4408_ = lean_ctor_get(v_thm_4402_, 1);
v_all_4409_ = lean_ctor_get(v_thm_4402_, 2);
v_type_4419_ = lean_ctor_get(v_toConstantVal_4407_, 2);
lean_inc_ref(v_env_4406_);
v___x_4420_ = l_Lean_Environment_hasUnsafe(v_env_4406_, v_type_4419_);
if (v___x_4420_ == 0)
{
uint8_t v___x_4421_; 
v___x_4421_ = l_Lean_Environment_hasUnsafe(v_env_4406_, v_value_4408_);
v___y_4411_ = v___x_4421_;
goto v___jp_4410_;
}
else
{
lean_dec_ref(v_env_4406_);
v___y_4411_ = v___x_4420_;
goto v___jp_4410_;
}
v___jp_4410_:
{
if (v___y_4411_ == 0)
{
lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4412_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4412_, 0, v_thm_4402_);
v___x_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
return v___x_4413_;
}
else
{
lean_object* v___x_4414_; uint8_t v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_inc(v_all_4409_);
lean_inc_ref(v_value_4408_);
lean_inc_ref(v_toConstantVal_4407_);
lean_dec_ref(v_thm_4402_);
v___x_4414_ = lean_box(0);
v___x_4415_ = 0;
v___x_4416_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4416_, 0, v_toConstantVal_4407_);
lean_ctor_set(v___x_4416_, 1, v_value_4408_);
lean_ctor_set(v___x_4416_, 2, v___x_4414_);
lean_ctor_set(v___x_4416_, 3, v_all_4409_);
lean_ctor_set_uint8(v___x_4416_, sizeof(void*)*4, v___x_4415_);
v___x_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
v___x_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
return v___x_4418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_thm_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4422_, v___y_4423_);
lean_dec(v___y_4423_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_thm_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4426_, v___y_4430_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object* v_thm_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(lean_object* v_cls_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_options_4446_; uint8_t v_hasTrace_4447_; 
v_options_4446_ = lean_ctor_get(v___y_4444_, 2);
v_hasTrace_4447_ = lean_ctor_get_uint8(v_options_4446_, sizeof(void*)*1);
if (v_hasTrace_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_dec(v_cls_4443_);
v___x_4448_ = lean_box(v_hasTrace_4447_);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
else
{
lean_object* v_inheritedTraceOptions_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_inheritedTraceOptions_4450_ = lean_ctor_get(v___y_4444_, 13);
v___x_4451_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__1));
v___x_4452_ = l_Lean_Name_append(v___x_4451_, v_cls_4443_);
v___x_4453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4450_, v_options_4446_, v___x_4452_);
lean_dec(v___x_4452_);
v___x_4454_ = lean_box(v___x_4453_);
v___x_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4454_);
return v___x_4455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_cls_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v_cls_4456_, v___y_4457_);
lean_dec_ref(v___y_4457_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_cls_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v_cls_4460_, v___y_4463_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
return v_res_4473_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0(void){
_start:
{
lean_object* v___x_4474_; double v___x_4475_; 
v___x_4474_ = lean_unsigned_to_nat(0u);
v___x_4475_ = lean_float_of_nat(v___x_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(lean_object* v_cls_4479_, lean_object* v_msg_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_ref_4486_; lean_object* v___x_4487_; lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4532_; 
v_ref_4486_ = lean_ctor_get(v___y_4483_, 5);
v___x_4487_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4532_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4532_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4492_; lean_object* v_traceState_4493_; lean_object* v_env_4494_; lean_object* v_nextMacroScope_4495_; lean_object* v_ngen_4496_; lean_object* v_auxDeclNGen_4497_; lean_object* v_cache_4498_; lean_object* v_messages_4499_; lean_object* v_infoState_4500_; lean_object* v_snapshotTasks_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4531_; 
v___x_4492_ = lean_st_ref_take(v___y_4484_);
v_traceState_4493_ = lean_ctor_get(v___x_4492_, 4);
v_env_4494_ = lean_ctor_get(v___x_4492_, 0);
v_nextMacroScope_4495_ = lean_ctor_get(v___x_4492_, 1);
v_ngen_4496_ = lean_ctor_get(v___x_4492_, 2);
v_auxDeclNGen_4497_ = lean_ctor_get(v___x_4492_, 3);
v_cache_4498_ = lean_ctor_get(v___x_4492_, 5);
v_messages_4499_ = lean_ctor_get(v___x_4492_, 6);
v_infoState_4500_ = lean_ctor_get(v___x_4492_, 7);
v_snapshotTasks_4501_ = lean_ctor_get(v___x_4492_, 8);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4503_ = v___x_4492_;
v_isShared_4504_ = v_isSharedCheck_4531_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_snapshotTasks_4501_);
lean_inc(v_infoState_4500_);
lean_inc(v_messages_4499_);
lean_inc(v_cache_4498_);
lean_inc(v_traceState_4493_);
lean_inc(v_auxDeclNGen_4497_);
lean_inc(v_ngen_4496_);
lean_inc(v_nextMacroScope_4495_);
lean_inc(v_env_4494_);
lean_dec(v___x_4492_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4531_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
uint64_t v_tid_4505_; lean_object* v_traces_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4530_; 
v_tid_4505_ = lean_ctor_get_uint64(v_traceState_4493_, sizeof(void*)*1);
v_traces_4506_ = lean_ctor_get(v_traceState_4493_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v_traceState_4493_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4508_ = v_traceState_4493_;
v_isShared_4509_ = v_isSharedCheck_4530_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_traces_4506_);
lean_dec(v_traceState_4493_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4530_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; double v___x_4511_; uint8_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
v___x_4510_ = lean_box(0);
v___x_4511_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0);
v___x_4512_ = 0;
v___x_4513_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__1));
v___x_4514_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4514_, 0, v_cls_4479_);
lean_ctor_set(v___x_4514_, 1, v___x_4510_);
lean_ctor_set(v___x_4514_, 2, v___x_4513_);
lean_ctor_set_float(v___x_4514_, sizeof(void*)*3, v___x_4511_);
lean_ctor_set_float(v___x_4514_, sizeof(void*)*3 + 8, v___x_4511_);
lean_ctor_set_uint8(v___x_4514_, sizeof(void*)*3 + 16, v___x_4512_);
v___x_4515_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__2));
v___x_4516_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4514_);
lean_ctor_set(v___x_4516_, 1, v_a_4488_);
lean_ctor_set(v___x_4516_, 2, v___x_4515_);
lean_inc(v_ref_4486_);
v___x_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4517_, 0, v_ref_4486_);
lean_ctor_set(v___x_4517_, 1, v___x_4516_);
v___x_4518_ = l_Lean_PersistentArray_push___redArg(v_traces_4506_, v___x_4517_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v___x_4518_);
v___x_4520_ = v___x_4508_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4518_);
lean_ctor_set_uint64(v_reuseFailAlloc_4529_, sizeof(void*)*1, v_tid_4505_);
v___x_4520_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
lean_object* v___x_4522_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v___x_4520_);
v___x_4522_ = v___x_4503_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_env_4494_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v_nextMacroScope_4495_);
lean_ctor_set(v_reuseFailAlloc_4528_, 2, v_ngen_4496_);
lean_ctor_set(v_reuseFailAlloc_4528_, 3, v_auxDeclNGen_4497_);
lean_ctor_set(v_reuseFailAlloc_4528_, 4, v___x_4520_);
lean_ctor_set(v_reuseFailAlloc_4528_, 5, v_cache_4498_);
lean_ctor_set(v_reuseFailAlloc_4528_, 6, v_messages_4499_);
lean_ctor_set(v_reuseFailAlloc_4528_, 7, v_infoState_4500_);
lean_ctor_set(v_reuseFailAlloc_4528_, 8, v_snapshotTasks_4501_);
v___x_4522_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4526_; 
v___x_4523_ = lean_st_ref_set(v___y_4484_, v___x_4522_);
v___x_4524_ = lean_box(0);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4524_);
v___x_4526_ = v___x_4490_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4524_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___boxed(lean_object* v_cls_4533_, lean_object* v_msg_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(v_cls_4533_, v_msg_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
return v_res_4540_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4541_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4542_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4544_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
return v___x_4545_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4548_ = l_Lean_stringToMessageData(v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4549_, uint8_t v___x_4550_, lean_object* v_name_4551_, lean_object* v_argKinds_4552_, lean_object* v___x_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___x_4599_; lean_object* v_a_4600_; lean_object* v___x_4601_; 
v___x_4599_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_4549_, v___y_4557_);
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4599_);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
v___x_4601_ = l_Lean_addDecl(v_a_4600_, v___x_4550_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v_a_4604_; uint8_t v___x_4605_; 
lean_dec_ref(v___x_4601_);
v___x_4602_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4603_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v___x_4602_, v___y_4556_);
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
lean_inc(v_a_4604_);
lean_dec_ref(v___x_4603_);
v___x_4605_ = lean_unbox(v_a_4604_);
lean_dec(v_a_4604_);
if (v___x_4605_ == 0)
{
lean_dec_ref(v___y_4556_);
v___y_4560_ = v___y_4555_;
v___y_4561_ = v___y_4557_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4606_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4551_);
v___x_4607_ = l_Lean_MessageData_ofName(v_name_4551_);
v___x_4608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4606_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4608_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
v___x_4611_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(v___x_4602_, v___x_4610_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
lean_dec_ref(v___y_4556_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_dec_ref(v___x_4611_);
v___y_4560_ = v___y_4555_;
v___y_4561_ = v___y_4557_;
goto v___jp_4559_;
}
else
{
lean_dec(v___y_4557_);
lean_dec_ref(v___x_4553_);
lean_dec_ref(v_argKinds_4552_);
lean_dec(v_name_4551_);
return v___x_4611_;
}
}
}
else
{
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec_ref(v___x_4553_);
lean_dec_ref(v_argKinds_4552_);
lean_dec(v_name_4551_);
return v___x_4601_;
}
v___jp_4559_:
{
lean_object* v___x_4562_; lean_object* v_env_4563_; lean_object* v_nextMacroScope_4564_; lean_object* v_ngen_4565_; lean_object* v_auxDeclNGen_4566_; lean_object* v_traceState_4567_; lean_object* v_messages_4568_; lean_object* v_infoState_4569_; lean_object* v_snapshotTasks_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4597_; 
v___x_4562_ = lean_st_ref_take(v___y_4561_);
v_env_4563_ = lean_ctor_get(v___x_4562_, 0);
v_nextMacroScope_4564_ = lean_ctor_get(v___x_4562_, 1);
v_ngen_4565_ = lean_ctor_get(v___x_4562_, 2);
v_auxDeclNGen_4566_ = lean_ctor_get(v___x_4562_, 3);
v_traceState_4567_ = lean_ctor_get(v___x_4562_, 4);
v_messages_4568_ = lean_ctor_get(v___x_4562_, 6);
v_infoState_4569_ = lean_ctor_get(v___x_4562_, 7);
v_snapshotTasks_4570_ = lean_ctor_get(v___x_4562_, 8);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4597_ == 0)
{
lean_object* v_unused_4598_; 
v_unused_4598_ = lean_ctor_get(v___x_4562_, 5);
lean_dec(v_unused_4598_);
v___x_4572_ = v___x_4562_;
v_isShared_4573_ = v_isSharedCheck_4597_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_snapshotTasks_4570_);
lean_inc(v_infoState_4569_);
lean_inc(v_messages_4568_);
lean_inc(v_traceState_4567_);
lean_inc(v_auxDeclNGen_4566_);
lean_inc(v_ngen_4565_);
lean_inc(v_nextMacroScope_4564_);
lean_inc(v_env_4563_);
lean_dec(v___x_4562_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4597_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4578_; 
v___x_4574_ = l_Lean_Meta_congrKindsExt;
v___x_4575_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4574_, v_env_4563_, v_name_4551_, v_argKinds_4552_);
v___x_4576_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 5, v___x_4576_);
lean_ctor_set(v___x_4572_, 0, v___x_4575_);
v___x_4578_ = v___x_4572_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4575_);
lean_ctor_set(v_reuseFailAlloc_4596_, 1, v_nextMacroScope_4564_);
lean_ctor_set(v_reuseFailAlloc_4596_, 2, v_ngen_4565_);
lean_ctor_set(v_reuseFailAlloc_4596_, 3, v_auxDeclNGen_4566_);
lean_ctor_set(v_reuseFailAlloc_4596_, 4, v_traceState_4567_);
lean_ctor_set(v_reuseFailAlloc_4596_, 5, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4596_, 6, v_messages_4568_);
lean_ctor_set(v_reuseFailAlloc_4596_, 7, v_infoState_4569_);
lean_ctor_set(v_reuseFailAlloc_4596_, 8, v_snapshotTasks_4570_);
v___x_4578_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v_mctx_4581_; lean_object* v_zetaDeltaFVarIds_4582_; lean_object* v_postponed_4583_; lean_object* v_diag_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4594_; 
v___x_4579_ = lean_st_ref_set(v___y_4561_, v___x_4578_);
lean_dec(v___y_4561_);
v___x_4580_ = lean_st_ref_take(v___y_4560_);
v_mctx_4581_ = lean_ctor_get(v___x_4580_, 0);
v_zetaDeltaFVarIds_4582_ = lean_ctor_get(v___x_4580_, 2);
v_postponed_4583_ = lean_ctor_get(v___x_4580_, 3);
v_diag_4584_ = lean_ctor_get(v___x_4580_, 4);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v___x_4580_, 1);
lean_dec(v_unused_4595_);
v___x_4586_ = v___x_4580_;
v_isShared_4587_ = v_isSharedCheck_4594_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_diag_4584_);
lean_inc(v_postponed_4583_);
lean_inc(v_zetaDeltaFVarIds_4582_);
lean_inc(v_mctx_4581_);
lean_dec(v___x_4580_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4594_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 1, v___x_4553_);
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_mctx_4581_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v___x_4553_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_zetaDeltaFVarIds_4582_);
lean_ctor_set(v_reuseFailAlloc_4593_, 3, v_postponed_4583_);
lean_ctor_set(v_reuseFailAlloc_4593_, 4, v_diag_4584_);
v___x_4589_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4590_ = lean_st_ref_set(v___y_4560_, v___x_4589_);
v___x_4591_ = lean_box(0);
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
return v___x_4592_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4612_, lean_object* v___x_4613_, lean_object* v_name_4614_, lean_object* v_argKinds_4615_, lean_object* v___x_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
uint8_t v___x_15500__boxed_4622_; lean_object* v_res_4623_; 
v___x_15500__boxed_4622_ = lean_unbox(v___x_4613_);
v_res_4623_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4612_, v___x_15500__boxed_4622_, v_name_4614_, v_argKinds_4615_, v___x_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
if (lean_obj_tag(v_a_4624_) == 0)
{
lean_object* v___x_4626_; 
v___x_4626_ = l_List_reverse___redArg(v_a_4625_);
return v___x_4626_;
}
else
{
lean_object* v_head_4627_; lean_object* v_tail_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4637_; 
v_head_4627_ = lean_ctor_get(v_a_4624_, 0);
v_tail_4628_ = lean_ctor_get(v_a_4624_, 1);
v_isSharedCheck_4637_ = !lean_is_exclusive(v_a_4624_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4630_ = v_a_4624_;
v_isShared_4631_ = v_isSharedCheck_4637_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_tail_4628_);
lean_inc(v_head_4627_);
lean_dec(v_a_4624_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4637_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4632_; lean_object* v___x_4634_; 
v___x_4632_ = l_Lean_mkLevelParam(v_head_4627_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 1, v_a_4625_);
lean_ctor_set(v___x_4630_, 0, v___x_4632_);
v___x_4634_ = v___x_4630_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4632_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_a_4625_);
v___x_4634_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
v_a_4624_ = v_tail_4628_;
v_a_4625_ = v___x_4634_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4638_; 
v___x_4638_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4638_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
return v___x_4640_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4641_ = lean_box(1);
v___x_4642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4643_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
lean_ctor_set(v___x_4644_, 1, v___x_4642_);
lean_ctor_set(v___x_4644_, 2, v___x_4641_);
return v___x_4644_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4648_ = lean_unsigned_to_nat(0u);
v___x_4649_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
lean_ctor_set(v___x_4649_, 1, v___x_4648_);
lean_ctor_set(v___x_4649_, 2, v___x_4648_);
lean_ctor_set(v___x_4649_, 3, v___x_4647_);
lean_ctor_set(v___x_4649_, 4, v___x_4647_);
lean_ctor_set(v___x_4649_, 5, v___x_4647_);
lean_ctor_set(v___x_4649_, 6, v___x_4647_);
lean_ctor_set(v___x_4649_, 7, v___x_4647_);
lean_ctor_set(v___x_4649_, 8, v___x_4647_);
return v___x_4649_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4651_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4650_);
lean_ctor_set(v___x_4651_, 1, v___x_4650_);
lean_ctor_set(v___x_4651_, 2, v___x_4650_);
lean_ctor_set(v___x_4651_, 3, v___x_4650_);
lean_ctor_set(v___x_4651_, 4, v___x_4650_);
lean_ctor_set(v___x_4651_, 5, v___x_4650_);
return v___x_4651_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
lean_ctor_set(v___x_4653_, 1, v___x_4652_);
lean_ctor_set(v___x_4653_, 2, v___x_4652_);
lean_ctor_set(v___x_4653_, 3, v___x_4652_);
lean_ctor_set(v___x_4653_, 4, v___x_4652_);
return v___x_4653_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4654_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4655_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4656_ = lean_box(1);
v___x_4657_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4658_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
lean_ctor_set(v___x_4659_, 1, v___x_4657_);
lean_ctor_set(v___x_4659_, 2, v___x_4656_);
lean_ctor_set(v___x_4659_, 3, v___x_4655_);
lean_ctor_set(v___x_4659_, 4, v___x_4654_);
return v___x_4659_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4660_ = 1;
v___x_4661_ = lean_unsigned_to_nat(0u);
v___x_4662_ = lean_box(0);
v___x_4663_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4664_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4665_ = lean_box(1);
v___x_4666_ = 0;
v___x_4667_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_4668_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4668_, 0, v___x_4667_);
lean_ctor_set(v___x_4668_, 1, v___x_4665_);
lean_ctor_set(v___x_4668_, 2, v___x_4664_);
lean_ctor_set(v___x_4668_, 3, v___x_4663_);
lean_ctor_set(v___x_4668_, 4, v___x_4662_);
lean_ctor_set(v___x_4668_, 5, v___x_4661_);
lean_ctor_set(v___x_4668_, 6, v___x_4662_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*7, v___x_4666_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*7 + 1, v___x_4666_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*7 + 2, v___x_4666_);
lean_ctor_set_uint8(v___x_4668_, sizeof(void*)*7 + 3, v___x_4660_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v_name_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
if (lean_obj_tag(v_name_4669_) == 1)
{
lean_object* v_pre_4673_; lean_object* v_str_4674_; lean_object* v___x_4675_; lean_object* v_env_4676_; uint8_t v___x_4677_; uint8_t v___x_4678_; 
v_pre_4673_ = lean_ctor_get(v_name_4669_, 0);
lean_inc(v_pre_4673_);
v_str_4674_ = lean_ctor_get(v_name_4669_, 1);
v___x_4675_ = lean_st_ref_get(v___y_4671_);
v_env_4676_ = lean_ctor_get(v___x_4675_, 0);
lean_inc_ref(v_env_4676_);
lean_dec(v___x_4675_);
v___x_4677_ = 1;
lean_inc(v_pre_4673_);
v___x_4678_ = l_Lean_Environment_contains(v_env_4676_, v_pre_4673_, v___x_4677_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
lean_dec(v_pre_4673_);
lean_dec_ref(v_name_4669_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v___x_4679_ = lean_box(v___x_4678_);
v___x_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4679_);
return v___x_4680_;
}
else
{
uint8_t v___x_4681_; lean_object* v___y_4683_; uint8_t v___y_4684_; lean_object* v_a_4689_; 
lean_inc_ref(v_str_4674_);
v___x_4681_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4674_);
if (v___x_4681_ == 0)
{
lean_object* v___x_4692_; uint8_t v___x_4693_; 
v___x_4692_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4693_ = lean_string_dec_eq(v_str_4674_, v___x_4692_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; 
lean_dec(v_pre_4673_);
lean_dec_ref(v_name_4669_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v___x_4694_ = lean_box(v___x_4693_);
v___x_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4694_);
return v___x_4695_;
}
else
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; uint8_t v_a_4707_; lean_object* v___x_4711_; 
v___x_4696_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_4697_ = lean_box(1);
v___x_4698_ = lean_unsigned_to_nat(0u);
v___x_4699_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4700_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4701_ = lean_box(0);
v___x_4702_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4702_, 0, v___x_4696_);
lean_ctor_set(v___x_4702_, 1, v___x_4697_);
lean_ctor_set(v___x_4702_, 2, v___x_4699_);
lean_ctor_set(v___x_4702_, 3, v___x_4700_);
lean_ctor_set(v___x_4702_, 4, v___x_4701_);
lean_ctor_set(v___x_4702_, 5, v___x_4698_);
lean_ctor_set(v___x_4702_, 6, v___x_4701_);
lean_ctor_set_uint8(v___x_4702_, sizeof(void*)*7, v___x_4681_);
lean_ctor_set_uint8(v___x_4702_, sizeof(void*)*7 + 1, v___x_4681_);
lean_ctor_set_uint8(v___x_4702_, sizeof(void*)*7 + 2, v___x_4681_);
lean_ctor_set_uint8(v___x_4702_, sizeof(void*)*7 + 3, v___x_4677_);
v___x_4703_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4704_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4705_ = lean_st_mk_ref(v___x_4704_);
lean_inc_ref(v___y_4670_);
lean_inc(v_pre_4673_);
v___x_4711_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4673_, v___x_4702_, v___x_4705_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4712_);
lean_dec_ref(v___x_4711_);
v___x_4713_ = l_Lean_ConstantInfo_levelParams(v_a_4712_);
lean_dec(v_a_4712_);
v___x_4714_ = lean_box(0);
lean_inc(v___x_4713_);
v___x_4715_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4713_, v___x_4714_);
lean_inc(v_pre_4673_);
v___x_4716_ = l_Lean_mkConst(v_pre_4673_, v___x_4715_);
lean_inc(v___y_4671_);
lean_inc_ref(v___y_4670_);
lean_inc(v___x_4705_);
lean_inc_ref(v___x_4702_);
lean_inc_ref(v___x_4716_);
v___x_4717_ = l_Lean_Meta_getFunInfo(v___x_4716_, v___x_4701_, v___x_4702_, v___x_4705_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; lean_object* v___x_4719_; 
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref(v___x_4717_);
lean_inc(v___y_4671_);
lean_inc_ref(v___y_4670_);
lean_inc(v___x_4705_);
lean_inc_ref(v___x_4702_);
lean_inc_ref(v___x_4716_);
v___x_4719_ = l_Lean_Meta_getCongrSimpKinds(v___x_4716_, v_a_4718_, v___x_4702_, v___x_4705_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4721_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
lean_dec_ref(v___x_4719_);
lean_inc(v___y_4671_);
lean_inc_ref(v___y_4670_);
lean_inc(v___x_4705_);
lean_inc_ref(v___x_4702_);
v___x_4721_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4716_, v_a_4718_, v_a_4720_, v___x_4677_, v___x_4702_, v___x_4705_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4722_);
lean_dec_ref(v___x_4721_);
if (lean_obj_tag(v_a_4722_) == 1)
{
lean_object* v_val_4723_; lean_object* v_type_4724_; lean_object* v_proof_4725_; lean_object* v_argKinds_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4739_; 
v_val_4723_ = lean_ctor_get(v_a_4722_, 0);
lean_inc(v_val_4723_);
lean_dec_ref(v_a_4722_);
v_type_4724_ = lean_ctor_get(v_val_4723_, 0);
v_proof_4725_ = lean_ctor_get(v_val_4723_, 1);
v_argKinds_4726_ = lean_ctor_get(v_val_4723_, 2);
v_isSharedCheck_4739_ = !lean_is_exclusive(v_val_4723_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4728_ = v_val_4723_;
v_isShared_4729_ = v_isSharedCheck_4739_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_argKinds_4726_);
lean_inc(v_proof_4725_);
lean_inc(v_type_4724_);
lean_dec(v_val_4723_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4739_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
lean_inc_ref(v_name_4669_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 2, v_type_4724_);
lean_ctor_set(v___x_4728_, 1, v___x_4713_);
lean_ctor_set(v___x_4728_, 0, v_name_4669_);
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_name_4669_);
lean_ctor_set(v_reuseFailAlloc_4738_, 1, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4738_, 2, v_type_4724_);
v___x_4731_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___f_4735_; lean_object* v___x_4736_; 
lean_inc_ref(v_name_4669_);
v___x_4732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4732_, 0, v_name_4669_);
lean_ctor_set(v___x_4732_, 1, v___x_4714_);
v___x_4733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4731_);
lean_ctor_set(v___x_4733_, 1, v_proof_4725_);
lean_ctor_set(v___x_4733_, 2, v___x_4732_);
v___x_4734_ = lean_box(v___x_4681_);
lean_inc_ref(v_name_4669_);
v___f_4735_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4735_, 0, v___x_4733_);
lean_closure_set(v___f_4735_, 1, v___x_4734_);
lean_closure_set(v___f_4735_, 2, v_name_4669_);
lean_closure_set(v___f_4735_, 3, v_argKinds_4726_);
lean_closure_set(v___f_4735_, 4, v___x_4703_);
lean_inc(v___x_4705_);
v___x_4736_ = l_Lean_Meta_realizeConst(v_pre_4673_, v_name_4669_, v___f_4735_, v___x_4702_, v___x_4705_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_dec_ref(v___x_4736_);
v_a_4707_ = v___x_4677_;
goto v___jp_4706_;
}
else
{
lean_object* v_a_4737_; 
lean_dec(v___x_4705_);
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4737_);
lean_dec_ref(v___x_4736_);
v_a_4689_ = v_a_4737_;
goto v___jp_4688_;
}
}
}
}
else
{
lean_dec(v_a_4722_);
lean_dec(v___x_4713_);
lean_dec_ref(v___x_4702_);
lean_dec_ref(v_name_4669_);
lean_dec(v_pre_4673_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v_a_4707_ = v___x_4681_;
goto v___jp_4706_;
}
}
else
{
lean_object* v_a_4740_; 
lean_dec(v___x_4713_);
lean_dec(v___x_4705_);
lean_dec_ref(v___x_4702_);
lean_dec_ref(v_name_4669_);
lean_dec(v_pre_4673_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v_a_4740_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4740_);
lean_dec_ref(v___x_4721_);
v_a_4689_ = v_a_4740_;
goto v___jp_4688_;
}
}
else
{
lean_object* v_a_4741_; 
lean_dec(v_a_4718_);
lean_dec_ref(v___x_4716_);
lean_dec(v___x_4713_);
lean_dec(v___x_4705_);
lean_dec_ref(v___x_4702_);
lean_dec_ref(v_name_4669_);
lean_dec(v_pre_4673_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v_a_4741_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4741_);
lean_dec_ref(v___x_4719_);
v_a_4689_ = v_a_4741_;
goto v___jp_4688_;
}
}
else
{
lean_object* v_a_4742_; 
lean_dec_ref(v___x_4716_);
lean_dec(v___x_4713_);
lean_dec(v___x_4705_);
lean_dec_ref(v___x_4702_);
lean_dec_ref(v_name_4669_);
lean_dec(v_pre_4673_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v_a_4742_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4742_);
lean_dec_ref(v___x_4717_);
v_a_4689_ = v_a_4742_;
goto v___jp_4688_;
}
}
else
{
lean_object* v_a_4743_; 
lean_dec(v___x_4705_);
lean_dec_ref(v___x_4702_);
lean_dec_ref(v_name_4669_);
lean_dec(v_pre_4673_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v_a_4743_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4743_);
lean_dec_ref(v___x_4711_);
v_a_4689_ = v_a_4743_;
goto v___jp_4688_;
}
v___jp_4706_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_st_ref_get(v___x_4705_);
lean_dec(v___x_4705_);
lean_dec(v___x_4708_);
v___x_4709_ = lean_box(v_a_4707_);
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
return v___x_4710_;
}
}
}
else
{
lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; uint8_t v___x_4749_; lean_object* v___y_4751_; uint8_t v___y_4752_; lean_object* v_a_4757_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4744_ = lean_unsigned_to_nat(7u);
v___x_4745_ = lean_unsigned_to_nat(0u);
v___x_4746_ = lean_string_utf8_byte_size(v_str_4674_);
lean_inc_ref(v_str_4674_);
v___x_4747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4747_, 0, v_str_4674_);
lean_ctor_set(v___x_4747_, 1, v___x_4745_);
lean_ctor_set(v___x_4747_, 2, v___x_4746_);
v___x_4748_ = l_String_Slice_Pos_nextn(v___x_4747_, v___x_4745_, v___x_4744_);
lean_dec_ref(v___x_4747_);
v___x_4749_ = 0;
v___x_4760_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4761_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4762_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4763_ = lean_st_mk_ref(v___x_4762_);
lean_inc_ref(v___y_4670_);
lean_inc(v_pre_4673_);
v___x_4764_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4673_, v___x_4760_, v___x_4763_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref(v___x_4764_);
lean_inc_ref(v_str_4674_);
v___x_4766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4766_, 0, v_str_4674_);
lean_ctor_set(v___x_4766_, 1, v___x_4748_);
lean_ctor_set(v___x_4766_, 2, v___x_4746_);
v___x_4767_ = l_String_Slice_toNat_x21(v___x_4766_);
lean_dec_ref(v___x_4766_);
v___x_4768_ = l_Lean_ConstantInfo_levelParams(v_a_4765_);
lean_dec(v_a_4765_);
v___x_4769_ = lean_box(0);
lean_inc(v___x_4768_);
v___x_4770_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4768_, v___x_4769_);
lean_inc(v_pre_4673_);
v___x_4771_ = l_Lean_mkConst(v_pre_4673_, v___x_4770_);
lean_inc(v___y_4671_);
lean_inc_ref(v___y_4670_);
lean_inc(v___x_4763_);
v___x_4772_ = l_Lean_Meta_mkHCongrWithArity(v___x_4771_, v___x_4767_, v___x_4760_, v___x_4763_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_object* v_a_4773_; lean_object* v_type_4774_; lean_object* v_proof_4775_; lean_object* v_argKinds_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4799_; 
v_a_4773_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_a_4773_);
lean_dec_ref(v___x_4772_);
v_type_4774_ = lean_ctor_get(v_a_4773_, 0);
v_proof_4775_ = lean_ctor_get(v_a_4773_, 1);
v_argKinds_4776_ = lean_ctor_get(v_a_4773_, 2);
v_isSharedCheck_4799_ = !lean_is_exclusive(v_a_4773_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4778_ = v_a_4773_;
v_isShared_4779_ = v_isSharedCheck_4799_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_argKinds_4776_);
lean_inc(v_proof_4775_);
lean_inc(v_type_4774_);
lean_dec(v_a_4773_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4799_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
lean_inc_ref(v_name_4669_);
if (v_isShared_4779_ == 0)
{
lean_ctor_set(v___x_4778_, 2, v_type_4774_);
lean_ctor_set(v___x_4778_, 1, v___x_4768_);
lean_ctor_set(v___x_4778_, 0, v_name_4669_);
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_name_4669_);
lean_ctor_set(v_reuseFailAlloc_4798_, 1, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_type_4774_);
v___x_4781_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___f_4785_; lean_object* v___x_4786_; 
lean_inc_ref(v_name_4669_);
v___x_4782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4782_, 0, v_name_4669_);
lean_ctor_set(v___x_4782_, 1, v___x_4769_);
v___x_4783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4781_);
lean_ctor_set(v___x_4783_, 1, v_proof_4775_);
lean_ctor_set(v___x_4783_, 2, v___x_4782_);
v___x_4784_ = lean_box(v___x_4749_);
lean_inc_ref(v_name_4669_);
v___f_4785_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4785_, 0, v___x_4783_);
lean_closure_set(v___f_4785_, 1, v___x_4784_);
lean_closure_set(v___f_4785_, 2, v_name_4669_);
lean_closure_set(v___f_4785_, 3, v_argKinds_4776_);
lean_closure_set(v___f_4785_, 4, v___x_4761_);
lean_inc(v___x_4763_);
v___x_4786_ = l_Lean_Meta_realizeConst(v_pre_4673_, v_name_4669_, v___f_4785_, v___x_4760_, v___x_4763_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4795_; 
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4795_ == 0)
{
lean_object* v_unused_4796_; 
v_unused_4796_ = lean_ctor_get(v___x_4786_, 0);
lean_dec(v_unused_4796_);
v___x_4788_ = v___x_4786_;
v_isShared_4789_ = v_isSharedCheck_4795_;
goto v_resetjp_4787_;
}
else
{
lean_dec(v___x_4786_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4795_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4793_; 
v___x_4790_ = lean_st_ref_get(v___x_4763_);
lean_dec(v___x_4763_);
lean_dec(v___x_4790_);
v___x_4791_ = lean_box(v___x_4677_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4791_);
v___x_4793_ = v___x_4788_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4791_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
else
{
lean_object* v_a_4797_; 
lean_dec(v___x_4763_);
v_a_4797_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_a_4797_);
lean_dec_ref(v___x_4786_);
v_a_4757_ = v_a_4797_;
goto v___jp_4756_;
}
}
}
}
else
{
lean_object* v_a_4800_; 
lean_dec(v___x_4768_);
lean_dec(v___x_4763_);
lean_dec_ref(v_name_4669_);
lean_dec(v_pre_4673_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v_a_4800_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_a_4800_);
lean_dec_ref(v___x_4772_);
v_a_4757_ = v_a_4800_;
goto v___jp_4756_;
}
}
else
{
lean_object* v_a_4801_; 
lean_dec(v___x_4763_);
lean_dec(v___x_4748_);
lean_dec(v_pre_4673_);
lean_dec_ref(v_name_4669_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
v_a_4801_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4801_);
lean_dec_ref(v___x_4764_);
v_a_4757_ = v_a_4801_;
goto v___jp_4756_;
}
v___jp_4750_:
{
if (v___y_4752_ == 0)
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
lean_dec_ref(v___y_4751_);
v___x_4753_ = lean_box(v___x_4749_);
v___x_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
return v___x_4754_;
}
else
{
lean_object* v___x_4755_; 
v___x_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4755_, 0, v___y_4751_);
return v___x_4755_;
}
}
v___jp_4756_:
{
uint8_t v___x_4758_; 
v___x_4758_ = l_Lean_Exception_isInterrupt(v_a_4757_);
if (v___x_4758_ == 0)
{
uint8_t v___x_4759_; 
lean_inc_ref(v_a_4757_);
v___x_4759_ = l_Lean_Exception_isRuntime(v_a_4757_);
v___y_4751_ = v_a_4757_;
v___y_4752_ = v___x_4759_;
goto v___jp_4750_;
}
else
{
v___y_4751_ = v_a_4757_;
v___y_4752_ = v___x_4758_;
goto v___jp_4750_;
}
}
}
v___jp_4682_:
{
if (v___y_4684_ == 0)
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
lean_dec_ref(v___y_4683_);
v___x_4685_ = lean_box(v___x_4681_);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
return v___x_4686_;
}
else
{
lean_object* v___x_4687_; 
v___x_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4687_, 0, v___y_4683_);
return v___x_4687_;
}
}
v___jp_4688_:
{
uint8_t v___x_4690_; 
v___x_4690_ = l_Lean_Exception_isInterrupt(v_a_4689_);
if (v___x_4690_ == 0)
{
uint8_t v___x_4691_; 
lean_inc_ref(v_a_4689_);
v___x_4691_ = l_Lean_Exception_isRuntime(v_a_4689_);
v___y_4683_ = v_a_4689_;
v___y_4684_ = v___x_4691_;
goto v___jp_4682_;
}
else
{
v___y_4683_ = v_a_4689_;
v___y_4684_ = v___x_4690_;
goto v___jp_4682_;
}
}
}
}
else
{
uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v_name_4669_);
v___x_4802_ = 0;
v___x_4803_ = lean_box(v___x_4802_);
v___x_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
return v___x_4804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_name_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_4805_, v___y_4806_, v___y_4807_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4812_; lean_object* v___x_4813_; 
v___f_4812_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4813_ = l_Lean_registerReservedNameAction(v___f_4812_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_a_4814_){
_start:
{
lean_object* v_res_4815_; 
v_res_4815_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
return v_res_4815_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* v_msg_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_){
_start:
{
lean_object* v___f_4822_; lean_object* v___x_1864__overap_4823_; lean_object* v___x_4824_; 
v___f_4822_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1864__overap_4823_ = lean_panic_fn(v___f_4822_, v_msg_4816_);
v___x_4824_ = lean_apply_5(v___x_1864__overap_4823_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, lean_box(0));
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
return v_res_4831_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4833_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4834_ = lean_unsigned_to_nat(8u);
v___x_4835_ = lean_unsigned_to_nat(461u);
v___x_4836_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0));
v___x_4837_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4838_ = l_mkPanicMessageWithDecl(v___x_4837_, v___x_4836_, v___x_4835_, v___x_4834_, v___x_4833_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* v_thmName_4839_, lean_object* v_levels_4840_, lean_object* v___x_4841_, lean_object* v_____r_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
lean_inc(v_thmName_4839_);
v___x_4848_ = l_Lean_mkConst(v_thmName_4839_, v_levels_4840_);
lean_inc(v___y_4846_);
lean_inc_ref(v___y_4845_);
lean_inc(v___y_4844_);
lean_inc_ref(v___y_4843_);
lean_inc_ref(v___x_4848_);
v___x_4849_ = lean_infer_type(v___x_4848_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4893_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4852_ = v___x_4849_;
v_isShared_4853_ = v_isSharedCheck_4893_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4849_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4893_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4854_; lean_object* v_env_4855_; lean_object* v___x_4856_; lean_object* v_toEnvExtension_4857_; lean_object* v_asyncMode_4858_; uint8_t v___x_4859_; lean_object* v___x_4860_; 
v___x_4854_ = lean_st_ref_get(v___y_4846_);
v_env_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc_ref(v_env_4855_);
lean_dec(v___x_4854_);
v___x_4856_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc_ref(v_toEnvExtension_4857_);
v_asyncMode_4858_ = lean_ctor_get(v_toEnvExtension_4857_, 2);
lean_inc(v_asyncMode_4858_);
lean_dec_ref(v_toEnvExtension_4857_);
v___x_4859_ = 0;
v___x_4860_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4841_, v___x_4856_, v_env_4855_, v_thmName_4839_, v_asyncMode_4858_, v___x_4859_);
lean_dec(v_asyncMode_4858_);
if (lean_obj_tag(v___x_4860_) == 1)
{
lean_object* v_val_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4873_; 
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
v_val_4861_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4863_ = v___x_4860_;
v_isShared_4864_ = v_isSharedCheck_4873_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_val_4861_);
lean_dec(v___x_4860_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4873_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4865_; lean_object* v___x_4867_; 
v___x_4865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4865_, 0, v_a_4850_);
lean_ctor_set(v___x_4865_, 1, v___x_4848_);
lean_ctor_set(v___x_4865_, 2, v_val_4861_);
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 0, v___x_4865_);
v___x_4867_ = v___x_4863_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
lean_object* v___x_4868_; lean_object* v___x_4870_; 
v___x_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4867_);
if (v_isShared_4853_ == 0)
{
lean_ctor_set(v___x_4852_, 0, v___x_4868_);
v___x_4870_ = v___x_4852_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4868_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
else
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
lean_dec(v___x_4860_);
lean_del_object(v___x_4852_);
lean_dec(v_a_4850_);
lean_dec_ref(v___x_4848_);
v___x_4874_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1);
v___x_4875_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4874_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4884_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4878_ = v___x_4875_;
v_isShared_4879_ = v_isSharedCheck_4884_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4875_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4884_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4880_, 0, v_a_4876_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4880_);
v___x_4882_ = v___x_4878_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
v_a_4885_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4875_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4875_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
}
else
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4901_; 
lean_dec_ref(v___x_4848_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
lean_dec_ref(v___x_4841_);
lean_dec(v_thmName_4839_);
v_a_4894_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4896_ = v___x_4849_;
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4849_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4899_; 
if (v_isShared_4897_ == 0)
{
v___x_4899_ = v___x_4896_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_a_4894_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* v_thmName_4902_, lean_object* v_levels_4903_, lean_object* v___x_4904_, lean_object* v_____r_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4902_, v_levels_4903_, v___x_4904_, v_____r_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
return v_res_4911_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0(void){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = l_Array_instInhabited(lean_box(0));
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* v_declName_4913_, lean_object* v_levels_4914_, lean_object* v_numArgs_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_){
_start:
{
lean_object* v___y_4922_; uint8_t v___y_4923_; lean_object* v_a_4928_; lean_object* v___y_4932_; lean_object* v___x_4943_; lean_object* v_env_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v_suffix_4948_; lean_object* v_thmName_4949_; uint8_t v___x_4950_; 
v___x_4943_ = lean_st_ref_get(v_a_4919_);
v_env_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc_ref(v_env_4944_);
lean_dec(v___x_4943_);
v___x_4945_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_4946_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4947_ = l_Nat_reprFast(v_numArgs_4915_);
v_suffix_4948_ = lean_string_append(v___x_4946_, v___x_4947_);
lean_dec_ref(v___x_4947_);
v_thmName_4949_ = l_Lean_Name_str___override(v_declName_4913_, v_suffix_4948_);
v___x_4950_ = l_Lean_Environment_containsOnBranch(v_env_4944_, v_thmName_4949_);
if (v___x_4950_ == 0)
{
lean_object* v___x_4951_; 
lean_inc(v_a_4919_);
lean_inc_ref(v_a_4918_);
lean_inc(v_thmName_4949_);
v___x_4951_ = l_Lean_executeReservedNameAction(v_thmName_4949_, v_a_4918_, v_a_4919_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_dec_ref(v___x_4951_);
v___x_4952_ = lean_box(0);
v___x_4953_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4949_, v_levels_4914_, v___x_4945_, v___x_4952_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_);
v___y_4932_ = v___x_4953_;
goto v___jp_4931_;
}
else
{
lean_object* v_a_4954_; 
lean_dec(v_thmName_4949_);
lean_dec(v_a_4919_);
lean_dec_ref(v_a_4918_);
lean_dec(v_a_4917_);
lean_dec_ref(v_a_4916_);
lean_dec(v_levels_4914_);
v_a_4954_ = lean_ctor_get(v___x_4951_, 0);
lean_inc(v_a_4954_);
lean_dec_ref(v___x_4951_);
v_a_4928_ = v_a_4954_;
goto v___jp_4927_;
}
}
else
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4955_ = lean_box(0);
v___x_4956_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4949_, v_levels_4914_, v___x_4945_, v___x_4955_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_);
v___y_4932_ = v___x_4956_;
goto v___jp_4931_;
}
v___jp_4921_:
{
if (v___y_4923_ == 0)
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
lean_dec_ref(v___y_4922_);
v___x_4924_ = lean_box(0);
v___x_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
return v___x_4925_;
}
else
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4926_, 0, v___y_4922_);
return v___x_4926_;
}
}
v___jp_4927_:
{
uint8_t v___x_4929_; 
v___x_4929_ = l_Lean_Exception_isInterrupt(v_a_4928_);
if (v___x_4929_ == 0)
{
uint8_t v___x_4930_; 
lean_inc_ref(v_a_4928_);
v___x_4930_ = l_Lean_Exception_isRuntime(v_a_4928_);
v___y_4922_ = v_a_4928_;
v___y_4923_ = v___x_4930_;
goto v___jp_4921_;
}
else
{
v___y_4922_ = v_a_4928_;
v___y_4923_ = v___x_4929_;
goto v___jp_4921_;
}
}
v___jp_4931_:
{
if (lean_obj_tag(v___y_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4941_; 
v_a_4933_ = lean_ctor_get(v___y_4932_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___y_4932_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4935_ = v___y_4932_;
v_isShared_4936_ = v_isSharedCheck_4941_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___y_4932_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4941_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v_a_4937_; lean_object* v___x_4939_; 
v_a_4937_ = lean_ctor_get(v_a_4933_, 0);
lean_inc(v_a_4937_);
lean_dec(v_a_4933_);
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 0, v_a_4937_);
v___x_4939_ = v___x_4935_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4937_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
else
{
lean_object* v_a_4942_; 
v_a_4942_ = lean_ctor_get(v___y_4932_, 0);
lean_inc(v_a_4942_);
lean_dec_ref(v___y_4932_);
v_a_4928_ = v_a_4942_;
goto v___jp_4927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object* v_declName_4957_, lean_object* v_levels_4958_, lean_object* v_numArgs_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_4957_, v_levels_4958_, v_numArgs_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* v_____r_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_){
_start:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4974_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0));
v___x_4975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4974_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* v_____r_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
return v_res_4982_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4984_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4985_ = lean_unsigned_to_nat(8u);
v___x_4986_ = lean_unsigned_to_nat(478u);
v___x_4987_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0));
v___x_4988_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4989_ = l_mkPanicMessageWithDecl(v___x_4988_, v___x_4987_, v___x_4986_, v___x_4985_, v___x_4984_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object* v_thmName_4990_, lean_object* v_levels_4991_, lean_object* v___x_4992_, lean_object* v_____r_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
lean_inc(v_thmName_4990_);
v___x_4999_ = l_Lean_mkConst(v_thmName_4990_, v_levels_4991_);
lean_inc(v___y_4997_);
lean_inc_ref(v___y_4996_);
lean_inc(v___y_4995_);
lean_inc_ref(v___y_4994_);
lean_inc_ref(v___x_4999_);
v___x_5000_ = lean_infer_type(v___x_4999_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5044_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5003_ = v___x_5000_;
v_isShared_5004_ = v_isSharedCheck_5044_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_5000_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5044_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5005_; lean_object* v_env_5006_; lean_object* v___x_5007_; lean_object* v_toEnvExtension_5008_; lean_object* v_asyncMode_5009_; uint8_t v___x_5010_; lean_object* v___x_5011_; 
v___x_5005_ = lean_st_ref_get(v___y_4997_);
v_env_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc_ref(v_env_5006_);
lean_dec(v___x_5005_);
v___x_5007_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_5008_ = lean_ctor_get(v___x_5007_, 0);
lean_inc_ref(v_toEnvExtension_5008_);
v_asyncMode_5009_ = lean_ctor_get(v_toEnvExtension_5008_, 2);
lean_inc(v_asyncMode_5009_);
lean_dec_ref(v_toEnvExtension_5008_);
v___x_5010_ = 0;
v___x_5011_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4992_, v___x_5007_, v_env_5006_, v_thmName_4990_, v_asyncMode_5009_, v___x_5010_);
lean_dec(v_asyncMode_5009_);
if (lean_obj_tag(v___x_5011_) == 1)
{
lean_object* v_val_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5024_; 
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
v_val_5012_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5014_ = v___x_5011_;
v_isShared_5015_ = v_isSharedCheck_5024_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_val_5012_);
lean_dec(v___x_5011_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5024_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5016_; lean_object* v___x_5018_; 
v___x_5016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5016_, 0, v_a_5001_);
lean_ctor_set(v___x_5016_, 1, v___x_4999_);
lean_ctor_set(v___x_5016_, 2, v_val_5012_);
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v___x_5016_);
v___x_5018_ = v___x_5014_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5016_);
v___x_5018_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 0, v___x_5019_);
v___x_5021_ = v___x_5003_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
else
{
lean_object* v___x_5025_; lean_object* v___x_5026_; 
lean_dec(v___x_5011_);
lean_del_object(v___x_5003_);
lean_dec(v_a_5001_);
lean_dec_ref(v___x_4999_);
v___x_5025_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1);
v___x_5026_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_5025_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5035_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5029_ = v___x_5026_;
v_isShared_5030_ = v_isSharedCheck_5035_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5026_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5035_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5031_, 0, v_a_5027_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5031_);
v___x_5033_ = v___x_5029_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5031_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
else
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
v_a_5036_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v___x_5026_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_5026_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5036_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
}
}
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_dec_ref(v___x_4999_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec_ref(v___x_4992_);
lean_dec(v_thmName_4990_);
v_a_5045_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_5000_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5000_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object* v_thmName_5053_, lean_object* v_levels_5054_, lean_object* v___x_5055_, lean_object* v_____r_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5053_, v_levels_5054_, v___x_5055_, v_____r_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
return v_res_5062_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1(void){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5064_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0));
v___x_5065_ = l_Lean_stringToMessageData(v___x_5064_);
return v___x_5065_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3(void){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2));
v___x_5068_ = l_Lean_stringToMessageData(v___x_5067_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* v_declName_5069_, lean_object* v_levels_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_){
_start:
{
lean_object* v_a_5077_; lean_object* v___y_5095_; lean_object* v___x_5097_; lean_object* v_env_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v_thmName_5101_; lean_object* v___y_5103_; uint8_t v___y_5104_; lean_object* v_a_5131_; lean_object* v___y_5135_; uint8_t v___x_5138_; 
v___x_5097_ = lean_st_ref_get(v_a_5074_);
v_env_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc_ref(v_env_5098_);
lean_dec(v___x_5097_);
v___x_5099_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_5100_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v_thmName_5101_ = l_Lean_Name_str___override(v_declName_5069_, v___x_5100_);
v___x_5138_ = l_Lean_Environment_containsOnBranch(v_env_5098_, v_thmName_5101_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; 
lean_inc(v_a_5074_);
lean_inc_ref(v_a_5073_);
lean_inc(v_thmName_5101_);
v___x_5139_ = l_Lean_executeReservedNameAction(v_thmName_5101_, v_a_5073_, v_a_5074_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v___x_5140_; lean_object* v___x_5141_; 
lean_dec_ref(v___x_5139_);
v___x_5140_ = lean_box(0);
lean_inc(v_a_5074_);
lean_inc_ref(v_a_5073_);
lean_inc(v_a_5072_);
lean_inc_ref(v_a_5071_);
lean_inc(v_thmName_5101_);
v___x_5141_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5101_, v_levels_5070_, v___x_5099_, v___x_5140_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
v___y_5135_ = v___x_5141_;
goto v___jp_5134_;
}
else
{
lean_object* v_a_5142_; 
lean_dec(v_levels_5070_);
v_a_5142_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5142_);
lean_dec_ref(v___x_5139_);
v_a_5131_ = v_a_5142_;
goto v___jp_5130_;
}
}
else
{
lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5143_ = lean_box(0);
lean_inc(v_a_5074_);
lean_inc_ref(v_a_5073_);
lean_inc(v_a_5072_);
lean_inc_ref(v_a_5071_);
lean_inc(v_thmName_5101_);
v___x_5144_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5101_, v_levels_5070_, v___x_5099_, v___x_5143_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
v___y_5135_ = v___x_5144_;
goto v___jp_5134_;
}
v___jp_5076_:
{
if (lean_obj_tag(v_a_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
v_a_5078_ = lean_ctor_get(v_a_5077_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_a_5077_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5080_ = v_a_5077_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v_a_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5078_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
v_a_5086_ = lean_ctor_get(v_a_5077_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v_a_5077_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v_a_5077_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v_a_5077_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
lean_ctor_set_tag(v___x_5088_, 0);
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
v___jp_5094_:
{
lean_object* v_a_5096_; 
v_a_5096_ = lean_ctor_get(v___y_5095_, 0);
lean_inc(v_a_5096_);
lean_dec_ref(v___y_5095_);
v_a_5077_ = v_a_5096_;
goto v___jp_5076_;
}
v___jp_5102_:
{
if (v___y_5104_ == 0)
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v_a_5107_; uint8_t v___x_5108_; 
v___x_5105_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_5106_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v___x_5105_, v_a_5073_);
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5107_);
lean_dec_ref(v___x_5106_);
v___x_5108_ = lean_unbox(v_a_5107_);
lean_dec(v_a_5107_);
if (v___x_5108_ == 0)
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
lean_dec_ref(v___y_5103_);
lean_dec(v_thmName_5101_);
v___x_5109_ = lean_box(0);
v___x_5110_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v___x_5109_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
v___y_5095_ = v___x_5110_;
goto v___jp_5094_;
}
else
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; 
v___x_5111_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1);
v___x_5112_ = l_Lean_MessageData_ofName(v_thmName_5101_);
v___x_5113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5113_, 0, v___x_5111_);
lean_ctor_set(v___x_5113_, 1, v___x_5112_);
v___x_5114_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3);
v___x_5115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5115_, 0, v___x_5113_);
lean_ctor_set(v___x_5115_, 1, v___x_5114_);
v___x_5116_ = l_Lean_Exception_toMessageData(v___y_5103_);
v___x_5117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5117_, 0, v___x_5115_);
lean_ctor_set(v___x_5117_, 1, v___x_5116_);
v___x_5118_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(v___x_5105_, v___x_5117_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v_a_5119_; lean_object* v___x_5120_; 
v_a_5119_ = lean_ctor_get(v___x_5118_, 0);
lean_inc(v_a_5119_);
lean_dec_ref(v___x_5118_);
v___x_5120_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_a_5119_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
v___y_5095_ = v___x_5120_;
goto v___jp_5094_;
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
v_a_5121_ = lean_ctor_get(v___x_5118_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5118_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5118_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5118_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
}
else
{
lean_object* v___x_5129_; 
lean_dec(v_thmName_5101_);
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
v___x_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___y_5103_);
return v___x_5129_;
}
}
v___jp_5130_:
{
uint8_t v___x_5132_; 
v___x_5132_ = l_Lean_Exception_isInterrupt(v_a_5131_);
if (v___x_5132_ == 0)
{
uint8_t v___x_5133_; 
lean_inc_ref(v_a_5131_);
v___x_5133_ = l_Lean_Exception_isRuntime(v_a_5131_);
v___y_5103_ = v_a_5131_;
v___y_5104_ = v___x_5133_;
goto v___jp_5102_;
}
else
{
v___y_5103_ = v_a_5131_;
v___y_5104_ = v___x_5132_;
goto v___jp_5102_;
}
}
v___jp_5134_:
{
if (lean_obj_tag(v___y_5135_) == 0)
{
lean_object* v_a_5136_; 
lean_dec(v_thmName_5101_);
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
v_a_5136_ = lean_ctor_get(v___y_5135_, 0);
lean_inc(v_a_5136_);
lean_dec_ref(v___y_5135_);
v_a_5077_ = v_a_5136_;
goto v___jp_5076_;
}
else
{
lean_object* v_a_5137_; 
v_a_5137_ = lean_ctor_get(v___y_5135_, 0);
lean_inc(v_a_5137_);
lean_dec_ref(v___y_5135_);
v_a_5131_ = v_a_5137_;
goto v___jp_5130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object* v_declName_5145_, lean_object* v_levels_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_5145_, v_levels_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_);
return v_res_5152_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
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
