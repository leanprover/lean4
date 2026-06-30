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
lean_object* l_Array_instInhabited(lean_object*);
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declared `"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
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
lean_inc(v___y_136_);
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
lean_inc(v___y_143_);
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
lean_inc(v___y_150_);
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
lean_inc(v___y_157_);
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
lean_inc(v___y_164_);
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
lean_inc(v___y_171_);
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
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
v___x_286_ = lean_apply_6(v_k_279_, v_b_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, lean_box(0));
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_287_, lean_object* v_b_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_287_, v_b_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
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
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
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
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_eqs_359_, lean_object* v_kinds_360_, lean_object* v_xs_361_, lean_object* v_ys_362_, lean_object* v_k_363_, lean_object* v___x_364_, lean_object* v_h_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(v_eqs_359_, v_kinds_360_, v_xs_361_, v_ys_362_, v_k_363_, v___x_364_, v_h_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
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
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
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
lean_inc(v_a_411_);
lean_inc_ref(v_a_410_);
lean_inc(v_a_409_);
lean_inc_ref(v_a_408_);
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
lean_dec_ref_known(v___x_418_, 1);
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
lean_dec_ref_known(v___x_421_, 1);
v___x_423_ = l_Lean_Expr_cleanupAnnotations(v_a_419_);
v___x_424_ = l_Lean_Expr_cleanupAnnotations(v_a_422_);
v___x_425_ = lean_expr_eqv(v___x_423_, v___x_424_);
lean_dec_ref(v___x_424_);
lean_dec_ref(v___x_423_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_inc(v_y_420_);
lean_inc(v_x_417_);
v___x_426_ = l_Lean_Meta_mkHEq(v_x_417_, v_y_420_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
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
lean_inc(v_y_420_);
lean_inc(v_x_417_);
v___x_442_ = l_Lean_Meta_mkEq(v_x_417_, v_y_420_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___f_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
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
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
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
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
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
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
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
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
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
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
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
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(lean_object* v_k_617_, lean_object* v_b_618_, lean_object* v_c_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
lean_inc(v___y_623_);
lean_inc_ref(v___y_622_);
lean_inc(v___y_621_);
lean_inc_ref(v___y_620_);
v___x_625_ = lean_apply_7(v_k_617_, v_b_618_, v_c_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, lean_box(0));
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed(lean_object* v_k_626_, lean_object* v_b_627_, lean_object* v_c_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(v_k_626_, v_b_627_, v_c_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
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
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
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
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_a_715_, lean_object* v_type_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v___x_1902__boxed_722_; lean_object* v_res_723_; 
v___x_1902__boxed_722_ = lean_unbox(v___x_712_);
v_res_723_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(v___x_710_, v___x_711_, v___x_1902__boxed_722_, v___x_713_, v___x_714_, v_a_715_, v_type_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
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
v___x_764_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_763_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
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
lean_dec_ref_known(v___x_766_, 1);
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
lean_dec_ref_known(v___x_768_, 1);
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
lean_inc_ref(v_eqPr_757_);
v___x_791_ = l_Lean_Meta_mkEqOfHEq(v_eqPr_757_, v___x_790_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
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
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_Meta_mkEqNDRec(v_a_782_, v_a_765_, v_major_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_755_);
v___x_786_ = lean_array_push(v___x_785_, v_a_756_);
v___x_787_ = lean_array_push(v___x_786_, v_b_753_);
v___x_788_ = lean_array_push(v___x_787_, v_eqPr_757_);
v___x_789_ = l_Lean_Meta_mkLambdaFVars(v___x_788_, v_a_784_, v___x_754_, v___x_779_, v___x_754_, v___x_779_, v___x_780_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec_ref(v___x_788_);
return v___x_789_;
}
else
{
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_783_;
}
}
else
{
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
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_768_;
}
}
else
{
lean_dec(v_a_765_);
lean_dec_ref(v_eqPr_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_b_753_);
return v___x_766_;
}
}
else
{
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
uint8_t v___x_1958__boxed_806_; lean_object* v_res_807_; 
v___x_1958__boxed_806_ = lean_unbox(v___x_797_);
v_res_807_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(v_type_793_, v_motive_794_, v___x_795_, v_b_796_, v___x_1958__boxed_806_, v___x_798_, v_a_799_, v_eqPr_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
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
uint8_t v___x_1917__boxed_844_; lean_object* v_res_845_; 
v___x_1917__boxed_844_ = lean_unbox(v___x_835_);
v_res_845_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(v___x_830_, v___x_831_, v_type_832_, v_a_833_, v___x_834_, v___x_1917__boxed_844_, v___x_836_, v_b_837_, v_motive_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v_b_837_);
lean_dec_ref(v_type_832_);
lean_dec(v___x_831_);
lean_dec_ref(v___x_830_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object* v___x_846_, lean_object* v___x_847_, uint8_t v___x_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v_a_851_, lean_object* v_type_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___f_861_; uint8_t v___x_862_; lean_object* v___x_863_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v_a_859_ = lean_array_get(v___x_846_, v_a_851_, v___x_858_);
v___x_860_ = lean_box(v___x_848_);
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
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
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
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
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
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
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
lean_dec_ref_known(v___x_1036_, 1);
lean_inc_ref(v_f_1016_);
v___x_1038_ = l_Lean_mkAppN(v_f_1016_, v_xs_1015_);
v___x_1039_ = l_Lean_mkAppN(v_f_1016_, v_ys_1014_);
lean_dec_ref(v_ys_1014_);
v___x_1040_ = l_Lean_Meta_mkHEq(v___x_1038_, v___x_1039_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v_fst_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
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
lean_inc_n(v_a_1045_, 2);
lean_dec_ref_known(v___x_1044_, 1);
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
uint8_t v___x_4841__boxed_1100_; uint8_t v___x_4842__boxed_1101_; lean_object* v_res_1102_; 
v___x_4841__boxed_1100_ = lean_unbox(v___x_1091_);
v___x_4842__boxed_1101_ = lean_unbox(v___x_1092_);
v_res_1102_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1088_, v_xs_1089_, v_f_1090_, v___x_4841__boxed_1100_, v___x_4842__boxed_1101_, v_eqs_1093_, v_argKinds_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
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
return v___x_1185_;
}
else
{
lean_object* v_lctx_1186_; lean_object* v_localInstances_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v_numArgs_1159_);
v_lctx_1186_ = lean_ctor_get(v___y_1163_, 2);
v_localInstances_1187_ = lean_ctor_get(v___y_1163_, 3);
v___x_1188_ = 0;
v___x_1189_ = lean_box(v___x_1188_);
v___x_1190_ = lean_box(v___x_1169_);
lean_inc_ref(v_xs_1158_);
lean_inc_ref(v_ys_1161_);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1191_, 0, v_ys_1161_);
lean_closure_set(v___f_1191_, 1, v_xs_1158_);
lean_closure_set(v___f_1191_, 2, v_f_1160_);
lean_closure_set(v___f_1191_, 3, v___x_1189_);
lean_closure_set(v___f_1191_, 4, v___x_1190_);
lean_inc_ref(v_lctx_1186_);
v___x_1192_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_1161_, v_lctx_1186_);
v___x_1193_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_1161_, v___x_1192_);
v___x_1194_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_xs_1158_, v___x_1193_);
v___x_1195_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed), 9, 4);
lean_closure_set(v___x_1195_, 0, lean_box(0));
lean_closure_set(v___x_1195_, 1, v_xs_1158_);
lean_closure_set(v___x_1195_, 2, v_ys_1161_);
lean_closure_set(v___x_1195_, 3, v___f_1191_);
lean_inc_ref(v_localInstances_1187_);
v___x_1196_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v___x_1194_, v_localInstances_1187_, v___x_1195_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object* v_xs_1197_, lean_object* v_numArgs_1198_, lean_object* v_f_1199_, lean_object* v_ys_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_mkHCongrWithArity___lam__1(v_xs_1197_, v_numArgs_1198_, v_f_1199_, v_ys_1200_, v_x_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_x_1201_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object* v_numArgs_1208_, lean_object* v_f_1209_, lean_object* v_a_1210_, lean_object* v___x_1211_, lean_object* v_xs_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___f_1219_; uint8_t v___x_1220_; uint8_t v___x_1221_; lean_object* v___x_1222_; 
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1219_, 0, v_xs_1212_);
lean_closure_set(v___f_1219_, 1, v_numArgs_1208_);
lean_closure_set(v___f_1219_, 2, v_f_1209_);
v___x_1220_ = 1;
v___x_1221_ = 0;
v___x_1222_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1210_, v___x_1211_, v___f_1219_, v___x_1220_, v___x_1221_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object* v_numArgs_1223_, lean_object* v_f_1224_, lean_object* v_a_1225_, lean_object* v___x_1226_, lean_object* v_xs_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Meta_mkHCongrWithArity___lam__2(v_numArgs_1223_, v_f_1224_, v_a_1225_, v___x_1226_, v_xs_1227_, v_x_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_x_1228_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object* v_f_1235_, lean_object* v_numArgs_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1242_; 
lean_inc(v_a_1240_);
lean_inc_ref(v_a_1239_);
lean_inc(v_a_1238_);
lean_inc_ref(v_a_1237_);
lean_inc_ref(v_f_1235_);
v___x_1242_ = lean_infer_type(v_f_1235_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; lean_object* v___f_1245_; uint8_t v___x_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_n(v_a_1243_, 2);
lean_dec_ref_known(v___x_1242_, 1);
lean_inc(v_numArgs_1236_);
v___x_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_numArgs_1236_);
lean_inc_ref(v___x_1244_);
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1245_, 0, v_numArgs_1236_);
lean_closure_set(v___f_1245_, 1, v_f_1235_);
lean_closure_set(v___f_1245_, 2, v_a_1243_);
lean_closure_set(v___f_1245_, 3, v___x_1244_);
v___x_1246_ = 1;
v___x_1247_ = 0;
v___x_1248_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1243_, v___x_1244_, v___f_1245_, v___x_1246_, v___x_1247_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
return v___x_1248_;
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_numArgs_1236_);
lean_dec_ref(v_f_1235_);
v_a_1249_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1242_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1242_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___boxed(lean_object* v_f_1257_, lean_object* v_numArgs_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Meta_mkHCongrWithArity(v_f_1257_, v_numArgs_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object* v_00_u03b1_1265_, lean_object* v_msg_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_msg_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(v_00_u03b1_1273_, v_msg_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object* v_as_1281_, size_t v_sz_1282_, size_t v_i_1283_, lean_object* v_b_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_1281_, v_sz_1282_, v_i_1283_, v_b_1284_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object* v_as_1291_, lean_object* v_sz_1292_, lean_object* v_i_1293_, lean_object* v_b_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
size_t v_sz_boxed_1300_; size_t v_i_boxed_1301_; lean_object* v_res_1302_; 
v_sz_boxed_1300_ = lean_unbox_usize(v_sz_1292_);
lean_dec(v_sz_1292_);
v_i_boxed_1301_ = lean_unbox_usize(v_i_1293_);
lean_dec(v_i_1293_);
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(v_as_1291_, v_sz_boxed_1300_, v_i_boxed_1301_, v_b_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec_ref(v_as_1291_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object* v_f_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
lean_inc_ref(v_f_1303_);
v___x_1310_ = l_Lean_Meta_getFunInfo(v_f_1303_, v___x_1309_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = l_Lean_Meta_FunInfo_getArity(v_a_1311_);
lean_dec(v_a_1311_);
v___x_1313_ = l_Lean_Meta_mkHCongrWithArity(v_f_1303_, v___x_1312_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
return v___x_1313_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v_f_1303_);
v_a_1314_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1310_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1310_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr___boxed(lean_object* v_f_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Meta_mkHCongr(v_f_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
return v_res_1328_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object* v_a_1329_, lean_object* v_as_1330_, size_t v_i_1331_, size_t v_stop_1332_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_eq(v_i_1331_, v_stop_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_array_uget_borrowed(v_as_1330_, v_i_1331_);
v___x_1335_ = lean_nat_dec_eq(v_a_1329_, v___x_1334_);
if (v___x_1335_ == 0)
{
size_t v___x_1336_; size_t v___x_1337_; 
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_add(v_i_1331_, v___x_1336_);
v_i_1331_ = v___x_1337_;
goto _start;
}
else
{
return v___x_1335_;
}
}
else
{
uint8_t v___x_1339_; 
v___x_1339_ = 0;
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object* v_a_1340_, lean_object* v_as_1341_, lean_object* v_i_1342_, lean_object* v_stop_1343_){
_start:
{
size_t v_i_boxed_1344_; size_t v_stop_boxed_1345_; uint8_t v_res_1346_; lean_object* v_r_1347_; 
v_i_boxed_1344_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_stop_boxed_1345_ = lean_unbox_usize(v_stop_1343_);
lean_dec(v_stop_1343_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1340_, v_as_1341_, v_i_boxed_1344_, v_stop_boxed_1345_);
lean_dec_ref(v_as_1341_);
lean_dec(v_a_1340_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object* v_as_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_array_get_size(v_as_1348_);
v___x_1352_ = lean_nat_dec_lt(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
return v___x_1352_;
}
else
{
if (v___x_1352_ == 0)
{
return v___x_1352_;
}
else
{
size_t v___x_1353_; size_t v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = lean_usize_of_nat(v___x_1351_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1349_, v_as_1348_, v___x_1353_, v___x_1354_);
return v___x_1355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object* v_as_1356_, lean_object* v_a_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_as_1356_, v_a_1357_);
lean_dec(v_a_1357_);
lean_dec_ref(v_as_1356_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(lean_object* v_next_1360_, lean_object* v_upperBound_1361_, lean_object* v___x_1362_, lean_object* v_a_1363_, lean_object* v_b_1364_){
_start:
{
lean_object* v_a_1366_; uint8_t v___x_1374_; 
v___x_1374_ = lean_nat_dec_lt(v_a_1363_, v_upperBound_1361_);
if (v___x_1374_ == 0)
{
lean_dec(v_a_1363_);
return v_b_1364_;
}
else
{
lean_object* v___x_1375_; lean_object* v_backDeps_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_array_fget_borrowed(v___x_1362_, v_a_1363_);
v_backDeps_1376_ = lean_ctor_get(v___x_1375_, 0);
v___x_1377_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_backDeps_1376_, v_next_1360_);
if (v___x_1377_ == 0)
{
v_a_1366_ = v_b_1364_;
goto v___jp_1365_;
}
else
{
uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1378_ = 0;
v___x_1379_ = lean_box(v___x_1378_);
v___x_1380_ = lean_array_get(v___x_1379_, v_b_1364_, v_a_1363_);
lean_dec(v___x_1379_);
v___x_1381_ = lean_unbox(v___x_1380_);
lean_dec(v___x_1380_);
switch(v___x_1381_)
{
case 2:
{
lean_dec(v_a_1363_);
goto v___jp_1370_;
}
case 0:
{
lean_dec(v_a_1363_);
goto v___jp_1370_;
}
default: 
{
v_a_1366_ = v_b_1364_;
goto v___jp_1365_;
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v_a_1363_, v___x_1367_);
lean_dec(v_a_1363_);
v_a_1363_ = v___x_1368_;
v_b_1364_ = v_a_1366_;
goto _start;
}
v___jp_1370_:
{
uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = 0;
v___x_1372_ = lean_box(v___x_1371_);
v___x_1373_ = lean_array_set(v_b_1364_, v_next_1360_, v___x_1372_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(lean_object* v_next_1382_, lean_object* v_upperBound_1383_, lean_object* v___x_1384_, lean_object* v_a_1385_, lean_object* v_b_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1382_, v_upperBound_1383_, v___x_1384_, v_a_1385_, v_b_1386_);
lean_dec_ref(v___x_1384_);
lean_dec(v_upperBound_1383_);
lean_dec(v_next_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object* v_upperBound_1388_, lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v_a_1391_, lean_object* v_b_1392_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_nat_dec_lt(v_a_1391_, v_upperBound_1388_);
if (v___x_1393_ == 0)
{
lean_dec(v_a_1391_);
return v_b_1392_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_unsigned_to_nat(1u);
v___x_1395_ = lean_nat_add(v_a_1391_, v___x_1394_);
lean_inc(v___x_1395_);
v___x_1396_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_a_1391_, v___x_1389_, v___x_1390_, v___x_1395_, v_b_1392_);
lean_dec(v_a_1391_);
v_a_1391_ = v___x_1395_;
v_b_1392_ = v___x_1396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object* v_upperBound_1398_, lean_object* v___x_1399_, lean_object* v___x_1400_, lean_object* v_a_1401_, lean_object* v_b_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1398_, v___x_1399_, v___x_1400_, v_a_1401_, v_b_1402_);
lean_dec_ref(v___x_1400_);
lean_dec(v___x_1399_);
lean_dec(v_upperBound_1398_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object* v_info_1404_, lean_object* v_kinds_1405_){
_start:
{
lean_object* v_paramInfo_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_paramInfo_1406_ = lean_ctor_get(v_info_1404_, 0);
v___x_1407_ = lean_array_get_size(v_paramInfo_1406_);
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v___x_1407_, v___x_1407_, v_paramInfo_1406_, v___x_1408_, v_kinds_1405_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object* v_info_1410_, lean_object* v_kinds_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_1410_, v_kinds_1411_);
lean_dec_ref(v_info_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(lean_object* v_next_1413_, lean_object* v_upperBound_1414_, lean_object* v___x_1415_, lean_object* v_inst_1416_, lean_object* v_R_1417_, lean_object* v_a_1418_, lean_object* v_b_1419_, lean_object* v_c_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1413_, v_upperBound_1414_, v___x_1415_, v_a_1418_, v_b_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(lean_object* v_next_1422_, lean_object* v_upperBound_1423_, lean_object* v___x_1424_, lean_object* v_inst_1425_, lean_object* v_R_1426_, lean_object* v_a_1427_, lean_object* v_b_1428_, lean_object* v_c_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(v_next_1422_, v_upperBound_1423_, v___x_1424_, v_inst_1425_, v_R_1426_, v_a_1427_, v_b_1428_, v_c_1429_);
lean_dec_ref(v___x_1424_);
lean_dec(v_upperBound_1423_);
lean_dec(v_next_1422_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object* v_upperBound_1431_, lean_object* v___x_1432_, lean_object* v___x_1433_, lean_object* v_inst_1434_, lean_object* v_R_1435_, lean_object* v_a_1436_, lean_object* v_b_1437_, lean_object* v_c_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1431_, v___x_1432_, v___x_1433_, v_a_1436_, v_b_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object* v_upperBound_1440_, lean_object* v___x_1441_, lean_object* v___x_1442_, lean_object* v_inst_1443_, lean_object* v_R_1444_, lean_object* v_a_1445_, lean_object* v_b_1446_, lean_object* v_c_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(v_upperBound_1440_, v___x_1441_, v___x_1442_, v_inst_1443_, v_R_1444_, v_a_1445_, v_b_1446_, v_c_1447_);
lean_dec_ref(v___x_1442_);
lean_dec(v___x_1441_);
lean_dec(v_upperBound_1440_);
return v_res_1448_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object* v_as_1449_, size_t v_i_1450_, size_t v_stop_1451_){
_start:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_usize_dec_eq(v_i_1450_, v_stop_1451_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = 1;
v___x_1454_ = lean_array_uget_borrowed(v_as_1449_, v_i_1450_);
v___x_1455_ = lean_unbox(v___x_1454_);
switch(v___x_1455_)
{
case 3:
{
return v___x_1453_;
}
case 5:
{
return v___x_1453_;
}
default: 
{
if (v___x_1452_ == 0)
{
size_t v___x_1456_; size_t v___x_1457_; 
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1450_, v___x_1456_);
v_i_1450_ = v___x_1457_;
goto _start;
}
else
{
return v___x_1453_;
}
}
}
}
else
{
uint8_t v___x_1459_; 
v___x_1459_ = 0;
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object* v_as_1460_, lean_object* v_i_1461_, lean_object* v_stop_1462_){
_start:
{
size_t v_i_boxed_1463_; size_t v_stop_boxed_1464_; uint8_t v_res_1465_; lean_object* v_r_1466_; 
v_i_boxed_1463_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_stop_boxed_1464_ = lean_unbox_usize(v_stop_1462_);
lean_dec(v_stop_1462_);
v_res_1465_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_as_1460_, v_i_boxed_1463_, v_stop_boxed_1464_);
lean_dec_ref(v_as_1460_);
v_r_1466_ = lean_box(v_res_1465_);
return v_r_1466_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object* v_kinds_1467_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_array_get_size(v_kinds_1467_);
v___x_1470_ = lean_nat_dec_lt(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
return v___x_1470_;
}
else
{
if (v___x_1470_ == 0)
{
return v___x_1470_;
}
else
{
size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = lean_usize_of_nat(v___x_1469_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_kinds_1467_, v___x_1471_, v___x_1472_);
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object* v_kinds_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_1474_);
lean_dec_ref(v_kinds_1474_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object* v___x_1477_, lean_object* v_k_1478_, lean_object* v_xs_1479_, lean_object* v_type_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_array_get_borrowed(v___x_1477_, v_xs_1479_, v___x_1486_);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___x_1487_);
v___x_1488_ = lean_apply_7(v_k_1478_, v___x_1487_, v_type_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, lean_box(0));
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object* v___x_1489_, lean_object* v_k_1490_, lean_object* v_xs_1491_, lean_object* v_type_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(v___x_1489_, v_k_1490_, v_xs_1491_, v_type_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec_ref(v_xs_1491_);
lean_dec_ref(v___x_1489_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object* v_type_1499_, lean_object* v_k_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___f_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1506_ = l_Lean_instInhabitedExpr;
v___f_1507_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1507_, 0, v___x_1506_);
lean_closure_set(v___f_1507_, 1, v_k_1500_);
v___x_1508_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_1509_ = 1;
v___x_1510_ = 0;
v___x_1511_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_1499_, v___x_1508_, v___f_1507_, v___x_1509_, v___x_1510_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(lean_object* v_type_1512_, lean_object* v_k_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1512_, v_k_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object* v_00_u03b1_1520_, lean_object* v_type_1521_, lean_object* v_k_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1521_, v_k_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(lean_object* v_00_u03b1_1529_, lean_object* v_type_1530_, lean_object* v_k_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(v_00_u03b1_1529_, v_type_1530_, v_k_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object* v_kinds_1541_, uint8_t v___x_1542_, lean_object* v_as_1543_, size_t v_sz_1544_, size_t v_i_1545_, lean_object* v_b_1546_){
_start:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_usize_dec_lt(v_i_1545_, v_sz_1544_);
if (v___x_1547_ == 0)
{
lean_inc_ref(v_b_1546_);
return v_b_1546_;
}
else
{
lean_object* v___x_1548_; lean_object* v_a_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1548_ = lean_box(0);
v_a_1549_ = lean_array_uget_borrowed(v_as_1543_, v_i_1545_);
v___x_1550_ = 0;
v___x_1551_ = lean_box(v___x_1550_);
v___x_1552_ = lean_array_get(v___x_1551_, v_kinds_1541_, v_a_1549_);
lean_dec(v___x_1551_);
v___x_1553_ = lean_unbox(v___x_1552_);
lean_dec(v___x_1552_);
if (v___x_1553_ == 2)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_box(v___x_1542_);
v___x_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1548_);
return v___x_1556_;
}
else
{
lean_object* v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; 
v___x_1557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_add(v_i_1545_, v___x_1558_);
v_i_1545_ = v___x_1559_;
v_b_1546_ = v___x_1557_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object* v_kinds_1561_, lean_object* v___x_1562_, lean_object* v_as_1563_, lean_object* v_sz_1564_, lean_object* v_i_1565_, lean_object* v_b_1566_){
_start:
{
uint8_t v___x_663__boxed_1567_; size_t v_sz_boxed_1568_; size_t v_i_boxed_1569_; lean_object* v_res_1570_; 
v___x_663__boxed_1567_ = lean_unbox(v___x_1562_);
v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1569_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1561_, v___x_663__boxed_1567_, v_as_1563_, v_sz_boxed_1568_, v_i_boxed_1569_, v_b_1566_);
lean_dec_ref(v_b_1566_);
lean_dec_ref(v_as_1563_);
lean_dec_ref(v_kinds_1561_);
return v_res_1570_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object* v_info_1571_, lean_object* v_kinds_1572_, lean_object* v_i_1573_){
_start:
{
lean_object* v_paramInfo_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v_isDecInst_1577_; 
v_paramInfo_1574_ = lean_ctor_get(v_info_1571_, 0);
v___x_1575_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_1576_ = lean_array_get_borrowed(v___x_1575_, v_paramInfo_1574_, v_i_1573_);
v_isDecInst_1577_ = lean_ctor_get_uint8(v___x_1576_, sizeof(void*)*1 + 3);
if (v_isDecInst_1577_ == 0)
{
return v_isDecInst_1577_;
}
else
{
lean_object* v_backDeps_1578_; lean_object* v___x_1579_; size_t v_sz_1580_; size_t v___x_1581_; lean_object* v___x_1582_; lean_object* v_fst_1583_; 
v_backDeps_1578_ = lean_ctor_get(v___x_1576_, 0);
v___x_1579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v_sz_1580_ = lean_array_size(v_backDeps_1578_);
v___x_1581_ = ((size_t)0ULL);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1572_, v_isDecInst_1577_, v_backDeps_1578_, v_sz_1580_, v___x_1581_, v___x_1579_);
v_fst_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_fst_1583_);
lean_dec_ref(v___x_1582_);
if (lean_obj_tag(v_fst_1583_) == 0)
{
uint8_t v___x_1584_; 
v___x_1584_ = 0;
return v___x_1584_;
}
else
{
lean_object* v_val_1585_; uint8_t v___x_1586_; 
v_val_1585_ = lean_ctor_get(v_fst_1583_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_fst_1583_, 1);
v___x_1586_ = lean_unbox(v_val_1585_);
lean_dec(v_val_1585_);
return v___x_1586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object* v_info_1587_, lean_object* v_kinds_1588_, lean_object* v_i_1589_){
_start:
{
uint8_t v_res_1590_; lean_object* v_r_1591_; 
v_res_1590_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_1587_, v_kinds_1588_, v_i_1589_);
lean_dec(v_i_1589_);
lean_dec_ref(v_kinds_1588_);
lean_dec_ref(v_info_1587_);
v_r_1591_ = lean_box(v_res_1590_);
return v_r_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(lean_object* v_type_1592_, lean_object* v_k_1593_, uint8_t v_cleanupAnnotations_1594_, uint8_t v_whnfType_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___f_1601_; lean_object* v___x_1602_; 
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1601_, 0, v_k_1593_);
v___x_1602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1592_, v___f_1601_, v_cleanupAnnotations_1594_, v_whnfType_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1602_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1602_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(lean_object* v_type_1619_, lean_object* v_k_1620_, lean_object* v_cleanupAnnotations_1621_, lean_object* v_whnfType_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1628_; uint8_t v_whnfType_boxed_1629_; lean_object* v_res_1630_; 
v_cleanupAnnotations_boxed_1628_ = lean_unbox(v_cleanupAnnotations_1621_);
v_whnfType_boxed_1629_ = lean_unbox(v_whnfType_1622_);
v_res_1630_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1619_, v_k_1620_, v_cleanupAnnotations_boxed_1628_, v_whnfType_boxed_1629_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_object* v_00_u03b1_1631_, lean_object* v_type_1632_, lean_object* v_k_1633_, uint8_t v_cleanupAnnotations_1634_, uint8_t v_whnfType_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1632_, v_k_1633_, v_cleanupAnnotations_1634_, v_whnfType_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(lean_object* v_00_u03b1_1642_, lean_object* v_type_1643_, lean_object* v_k_1644_, lean_object* v_cleanupAnnotations_1645_, lean_object* v_whnfType_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1652_; uint8_t v_whnfType_boxed_1653_; lean_object* v_res_1654_; 
v_cleanupAnnotations_boxed_1652_ = lean_unbox(v_cleanupAnnotations_1645_);
v_whnfType_boxed_1653_ = lean_unbox(v_whnfType_1646_);
v_res_1654_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(v_00_u03b1_1642_, v_type_1643_, v_k_1644_, v_cleanupAnnotations_boxed_1652_, v_whnfType_boxed_1653_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(lean_object* v_upperBound_1655_, lean_object* v_val_1656_, lean_object* v_xs_1657_, lean_object* v___x_1658_, lean_object* v___x_1659_, uint8_t v___x_1660_, lean_object* v_a_1661_, lean_object* v_b_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_a_1668_; uint8_t v___x_1672_; 
v___x_1672_ = lean_nat_dec_lt(v_a_1661_, v_upperBound_1655_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_dec(v_a_1661_);
lean_dec(v___x_1659_);
lean_dec_ref(v___x_1658_);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_b_1662_);
return v___x_1673_;
}
else
{
lean_object* v_numParams_1674_; uint8_t v___x_1675_; 
v_numParams_1674_ = lean_ctor_get(v_val_1656_, 3);
v___x_1675_ = lean_nat_dec_lt(v_a_1661_, v_numParams_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_array_fget_borrowed(v_xs_1657_, v_a_1661_);
v___x_1677_ = l_Lean_Expr_fvarId_x21(v___x_1676_);
v___x_1678_ = l_Lean_FVarId_getDecl___redArg(v___x_1677_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; uint8_t v___y_1681_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1678_, 1);
v___x_1684_ = l_Lean_LocalDecl_userName(v_a_1679_);
lean_dec(v_a_1679_);
lean_inc(v___x_1659_);
lean_inc_ref(v___x_1658_);
v___x_1685_ = l_Lean_isSubobjectField_x3f(v___x_1658_, v___x_1659_, v___x_1684_);
if (lean_obj_tag(v___x_1685_) == 0)
{
v___y_1681_ = v___x_1675_;
goto v___jp_1680_;
}
else
{
lean_dec_ref_known(v___x_1685_, 1);
v___y_1681_ = v___x_1660_;
goto v___jp_1680_;
}
v___jp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_box(v___y_1681_);
v___x_1683_ = lean_array_push(v_b_1662_, v___x_1682_);
v_a_1668_ = v___x_1683_;
goto v___jp_1667_;
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_b_1662_);
lean_dec(v_a_1661_);
lean_dec(v___x_1659_);
lean_dec_ref(v___x_1658_);
v_a_1686_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1678_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1678_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
uint8_t v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = 0;
v___x_1695_ = lean_box(v___x_1694_);
v___x_1696_ = lean_array_push(v_b_1662_, v___x_1695_);
v_a_1668_ = v___x_1696_;
goto v___jp_1667_;
}
}
v___jp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_add(v_a_1661_, v___x_1669_);
lean_dec(v_a_1661_);
v_a_1661_ = v___x_1670_;
v_b_1662_ = v_a_1668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_1697_, lean_object* v_val_1698_, lean_object* v_xs_1699_, lean_object* v___x_1700_, lean_object* v___x_1701_, lean_object* v___x_1702_, lean_object* v_a_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v___x_5663__boxed_1709_; lean_object* v_res_1710_; 
v___x_5663__boxed_1709_ = lean_unbox(v___x_1702_);
v_res_1710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1697_, v_val_1698_, v_xs_1699_, v___x_1700_, v___x_1701_, v___x_5663__boxed_1709_, v_a_1703_, v_b_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec_ref(v_xs_1699_);
lean_dec_ref(v_val_1698_);
lean_dec(v_upperBound_1697_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object* v_val_1713_, lean_object* v_induct_1714_, uint8_t v___x_1715_, lean_object* v_xs_1716_, lean_object* v_x_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; lean_object* v_env_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1723_ = lean_st_ref_get(v___y_1721_);
v_env_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_ref(v_env_1724_);
lean_dec(v___x_1723_);
v___x_1725_ = lean_array_get_size(v_xs_1716_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0));
v___x_1728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v___x_1725_, v_val_1713_, v_xs_1716_, v_env_1724_, v_induct_1714_, v___x_1715_, v___x_1726_, v___x_1727_, v___y_1718_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_a_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
v_a_1738_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1728_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1728_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object* v_val_1746_, lean_object* v_induct_1747_, lean_object* v___x_1748_, lean_object* v_xs_1749_, lean_object* v_x_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v___x_5750__boxed_1756_; lean_object* v_res_1757_; 
v___x_5750__boxed_1756_ = lean_unbox(v___x_1748_);
v_res_1757_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1746_, v_induct_1747_, v___x_5750__boxed_1756_, v_xs_1749_, v_x_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec_ref(v_x_1750_);
lean_dec_ref(v_xs_1749_);
lean_dec_ref(v_val_1746_);
return v_res_1757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
lean_ctor_set(v___x_1763_, 2, v___x_1762_);
lean_ctor_set(v___x_1763_, 3, v___x_1762_);
lean_ctor_set(v___x_1763_, 4, v___x_1761_);
lean_ctor_set(v___x_1763_, 5, v___x_1761_);
lean_ctor_set(v___x_1763_, 6, v___x_1761_);
lean_ctor_set(v___x_1763_, 7, v___x_1761_);
lean_ctor_set(v___x_1763_, 8, v___x_1761_);
lean_ctor_set(v___x_1763_, 9, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = lean_unsigned_to_nat(32u);
v___x_1765_ = lean_mk_empty_array_with_capacity(v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1767_ = ((size_t)5ULL);
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_unsigned_to_nat(32u);
v___x_1770_ = lean_mk_empty_array_with_capacity(v___x_1769_);
v___x_1771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1772_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1770_);
lean_ctor_set(v___x_1772_, 2, v___x_1768_);
lean_ctor_set(v___x_1772_, 3, v___x_1768_);
lean_ctor_set_usize(v___x_1772_, 4, v___x_1767_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1773_ = lean_box(1);
v___x_1774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1774_);
lean_ctor_set(v___x_1776_, 2, v___x_1773_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1779_ = l_Lean_stringToMessageData(v___x_1778_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1785_ = l_Lean_stringToMessageData(v___x_1784_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1798_, lean_object* v_declHint_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; lean_object* v_env_1803_; uint8_t v___x_1804_; 
v___x_1802_ = lean_st_ref_get(v___y_1800_);
v_env_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc_ref(v_env_1803_);
lean_dec(v___x_1802_);
v___x_1804_ = l_Lean_Name_isAnonymous(v_declHint_1799_);
if (v___x_1804_ == 0)
{
uint8_t v_isExporting_1805_; 
v_isExporting_1805_ = lean_ctor_get_uint8(v_env_1803_, sizeof(void*)*8);
if (v_isExporting_1805_ == 0)
{
lean_object* v___x_1806_; 
lean_dec_ref(v_env_1803_);
lean_dec(v_declHint_1799_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_msg_1798_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_inc_ref(v_env_1803_);
v___x_1807_ = l_Lean_Environment_setExporting(v_env_1803_, v___x_1804_);
lean_inc(v_declHint_1799_);
lean_inc_ref(v___x_1807_);
v___x_1808_ = l_Lean_Environment_contains(v___x_1807_, v_declHint_1799_, v_isExporting_1805_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_env_1803_);
lean_dec(v_declHint_1799_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_msg_1798_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_c_1815_; lean_object* v___x_1816_; 
v___x_1810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1812_ = l_Lean_Options_empty;
v___x_1813_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1807_);
lean_ctor_set(v___x_1813_, 1, v___x_1810_);
lean_ctor_set(v___x_1813_, 2, v___x_1811_);
lean_ctor_set(v___x_1813_, 3, v___x_1812_);
lean_inc(v_declHint_1799_);
v___x_1814_ = l_Lean_MessageData_ofConstName(v_declHint_1799_, v___x_1804_);
v_c_1815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1815_, 0, v___x_1813_);
lean_ctor_set(v_c_1815_, 1, v___x_1814_);
v___x_1816_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1803_, v_declHint_1799_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v_env_1803_);
lean_dec(v_declHint_1799_);
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v_c_1815_);
v___x_1819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_MessageData_note(v___x_1820_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v_msg_1798_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v_val_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1859_; 
v_val_1824_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1826_ = v___x_1816_;
v_isShared_1827_ = v_isSharedCheck_1859_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_val_1824_);
lean_dec(v___x_1816_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1859_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v_mod_1831_; uint8_t v___x_1832_; 
v___x_1828_ = lean_box(0);
v___x_1829_ = l_Lean_Environment_header(v_env_1803_);
lean_dec_ref(v_env_1803_);
v___x_1830_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1829_);
v_mod_1831_ = lean_array_get(v___x_1828_, v___x_1830_, v_val_1824_);
lean_dec(v_val_1824_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = l_Lean_isPrivateName(v_declHint_1799_);
lean_dec(v_declHint_1799_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v_c_1815_);
v___x_1835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = l_Lean_MessageData_ofName(v_mod_1831_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Lean_MessageData_note(v___x_1840_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_msg_1798_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1842_);
v___x_1844_ = v___x_1826_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v_c_1815_);
v___x_1848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_MessageData_ofName(v_mod_1831_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_MessageData_note(v___x_1853_);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_msg_1798_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1855_);
v___x_1857_ = v___x_1826_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1860_; 
lean_dec_ref(v_env_1803_);
lean_dec(v_declHint_1799_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_msg_1798_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1861_, lean_object* v_declHint_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1861_, v_declHint_1862_, v___y_1863_);
lean_dec(v___y_1863_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msg_1866_, lean_object* v_declHint_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1883_; 
v___x_1873_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1866_, v_declHint_1867_, v___y_1871_);
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1878_ = l_Lean_unknownIdentifierMessageTag;
v___x_1879_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1879_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1884_, lean_object* v_declHint_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1884_, v_declHint_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1892_, lean_object* v_msg_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_fileName_1899_; lean_object* v_fileMap_1900_; lean_object* v_options_1901_; lean_object* v_currRecDepth_1902_; lean_object* v_maxRecDepth_1903_; lean_object* v_ref_1904_; lean_object* v_currNamespace_1905_; lean_object* v_openDecls_1906_; lean_object* v_initHeartbeats_1907_; lean_object* v_maxHeartbeats_1908_; lean_object* v_quotContext_1909_; lean_object* v_currMacroScope_1910_; uint8_t v_diag_1911_; lean_object* v_cancelTk_x3f_1912_; uint8_t v_suppressElabErrors_1913_; lean_object* v_inheritedTraceOptions_1914_; lean_object* v_ref_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_fileName_1899_ = lean_ctor_get(v___y_1896_, 0);
v_fileMap_1900_ = lean_ctor_get(v___y_1896_, 1);
v_options_1901_ = lean_ctor_get(v___y_1896_, 2);
v_currRecDepth_1902_ = lean_ctor_get(v___y_1896_, 3);
v_maxRecDepth_1903_ = lean_ctor_get(v___y_1896_, 4);
v_ref_1904_ = lean_ctor_get(v___y_1896_, 5);
v_currNamespace_1905_ = lean_ctor_get(v___y_1896_, 6);
v_openDecls_1906_ = lean_ctor_get(v___y_1896_, 7);
v_initHeartbeats_1907_ = lean_ctor_get(v___y_1896_, 8);
v_maxHeartbeats_1908_ = lean_ctor_get(v___y_1896_, 9);
v_quotContext_1909_ = lean_ctor_get(v___y_1896_, 10);
v_currMacroScope_1910_ = lean_ctor_get(v___y_1896_, 11);
v_diag_1911_ = lean_ctor_get_uint8(v___y_1896_, sizeof(void*)*14);
v_cancelTk_x3f_1912_ = lean_ctor_get(v___y_1896_, 12);
v_suppressElabErrors_1913_ = lean_ctor_get_uint8(v___y_1896_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1914_ = lean_ctor_get(v___y_1896_, 13);
v_ref_1915_ = l_Lean_replaceRef(v_ref_1892_, v_ref_1904_);
lean_inc_ref(v_inheritedTraceOptions_1914_);
lean_inc(v_cancelTk_x3f_1912_);
lean_inc(v_currMacroScope_1910_);
lean_inc(v_quotContext_1909_);
lean_inc(v_maxHeartbeats_1908_);
lean_inc(v_initHeartbeats_1907_);
lean_inc(v_openDecls_1906_);
lean_inc(v_currNamespace_1905_);
lean_inc(v_maxRecDepth_1903_);
lean_inc(v_currRecDepth_1902_);
lean_inc_ref(v_options_1901_);
lean_inc_ref(v_fileMap_1900_);
lean_inc_ref(v_fileName_1899_);
v___x_1916_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1916_, 0, v_fileName_1899_);
lean_ctor_set(v___x_1916_, 1, v_fileMap_1900_);
lean_ctor_set(v___x_1916_, 2, v_options_1901_);
lean_ctor_set(v___x_1916_, 3, v_currRecDepth_1902_);
lean_ctor_set(v___x_1916_, 4, v_maxRecDepth_1903_);
lean_ctor_set(v___x_1916_, 5, v_ref_1915_);
lean_ctor_set(v___x_1916_, 6, v_currNamespace_1905_);
lean_ctor_set(v___x_1916_, 7, v_openDecls_1906_);
lean_ctor_set(v___x_1916_, 8, v_initHeartbeats_1907_);
lean_ctor_set(v___x_1916_, 9, v_maxHeartbeats_1908_);
lean_ctor_set(v___x_1916_, 10, v_quotContext_1909_);
lean_ctor_set(v___x_1916_, 11, v_currMacroScope_1910_);
lean_ctor_set(v___x_1916_, 12, v_cancelTk_x3f_1912_);
lean_ctor_set(v___x_1916_, 13, v_inheritedTraceOptions_1914_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*14, v_diag_1911_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*14 + 1, v_suppressElabErrors_1913_);
v___x_1917_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1893_, v___y_1894_, v___y_1895_, v___x_1916_, v___y_1897_);
lean_dec_ref_known(v___x_1916_, 14);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1918_, lean_object* v_msg_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1918_, v_msg_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v_ref_1918_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1926_, lean_object* v_msg_1927_, lean_object* v_declHint_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; lean_object* v_a_1935_; lean_object* v___x_1936_; 
v___x_1934_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1927_, v_declHint_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
v___x_1936_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1926_, v_a_1935_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1937_, lean_object* v_msg_1938_, lean_object* v_declHint_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1937_, v_msg_1938_, v_declHint_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v_ref_1937_);
return v_res_1945_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1948_ = l_Lean_stringToMessageData(v___x_1947_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1951_ = l_Lean_stringToMessageData(v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1952_, lean_object* v_constName_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1959_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1960_ = 0;
lean_inc(v_constName_1953_);
v___x_1961_ = l_Lean_MessageData_ofConstName(v_constName_1953_, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1952_, v___x_1964_, v_constName_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1966_, lean_object* v_constName_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1966_, v_constName_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v_ref_1966_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_ref_1980_; lean_object* v___x_1981_; 
v_ref_1980_ = lean_ctor_get(v___y_1977_, 5);
v___x_1981_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1980_, v_constName_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___x_1995_; lean_object* v_env_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = lean_st_ref_get(v___y_1993_);
v_env_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc_ref(v_env_1996_);
lean_dec(v___x_1995_);
v___x_1997_ = 0;
lean_inc(v_constName_1989_);
v___x_1998_ = l_Lean_Environment_find_x3f(v_env_1996_, v_constName_1989_, v___x_1997_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_1999_;
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_constName_1989_);
v_val_2000_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1998_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v___x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 0);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_val_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
if (lean_obj_tag(v_f_2015_) == 4)
{
lean_object* v_declName_2021_; lean_object* v___x_2022_; 
v_declName_2021_ = lean_ctor_get(v_f_2015_, 0);
lean_inc(v_declName_2021_);
lean_dec_ref_known(v_f_2015_, 2);
v___x_2022_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2021_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2046_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2046_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2046_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
if (lean_obj_tag(v_a_2023_) == 6)
{
lean_object* v_val_2027_; lean_object* v___x_2028_; lean_object* v_env_2029_; lean_object* v_toConstantVal_2030_; lean_object* v_induct_2031_; uint8_t v___x_2032_; 
v_val_2027_ = lean_ctor_get(v_a_2023_, 0);
lean_inc_ref(v_val_2027_);
lean_dec_ref_known(v_a_2023_, 1);
v___x_2028_ = lean_st_ref_get(v_a_2019_);
v_env_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref(v_env_2029_);
lean_dec(v___x_2028_);
v_toConstantVal_2030_ = lean_ctor_get(v_val_2027_, 0);
v_induct_2031_ = lean_ctor_get(v_val_2027_, 1);
lean_inc_n(v_induct_2031_, 2);
v___x_2032_ = lean_is_class(v_env_2029_, v_induct_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
lean_dec(v_induct_2031_);
lean_dec_ref(v_val_2027_);
v___x_2033_ = lean_box(0);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2033_);
v___x_2035_ = v___x_2025_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
else
{
lean_object* v_type_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; 
lean_del_object(v___x_2025_);
v_type_2037_ = lean_ctor_get(v_toConstantVal_2030_, 2);
lean_inc_ref(v_type_2037_);
v___x_2038_ = lean_box(v___x_2032_);
v___f_2039_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2039_, 0, v_val_2027_);
lean_closure_set(v___f_2039_, 1, v_induct_2031_);
lean_closure_set(v___f_2039_, 2, v___x_2038_);
v___x_2040_ = 0;
v___x_2041_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2037_, v___f_2039_, v___x_2032_, v___x_2040_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
return v___x_2041_;
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
lean_dec(v_a_2023_);
v___x_2042_ = lean_box(0);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2042_);
v___x_2044_ = v___x_2025_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
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
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
v_a_2047_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2022_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2022_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec_ref(v_f_2015_);
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2064_, lean_object* v_val_2065_, lean_object* v_xs_2066_, lean_object* v___x_2067_, lean_object* v___x_2068_, uint8_t v___x_2069_, lean_object* v_inst_2070_, lean_object* v_R_2071_, lean_object* v_a_2072_, lean_object* v_b_2073_, lean_object* v_c_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2064_, v_val_2065_, v_xs_2066_, v___x_2067_, v___x_2068_, v___x_2069_, v_a_2072_, v_b_2073_, v___y_2075_, v___y_2077_, v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2081_, lean_object* v_val_2082_, lean_object* v_xs_2083_, lean_object* v___x_2084_, lean_object* v___x_2085_, lean_object* v___x_2086_, lean_object* v_inst_2087_, lean_object* v_R_2088_, lean_object* v_a_2089_, lean_object* v_b_2090_, lean_object* v_c_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
uint8_t v___x_6330__boxed_2097_; lean_object* v_res_2098_; 
v___x_6330__boxed_2097_ = lean_unbox(v___x_2086_);
v_res_2098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2081_, v_val_2082_, v_xs_2083_, v___x_2084_, v___x_2085_, v___x_6330__boxed_2097_, v_inst_2087_, v_R_2088_, v_a_2089_, v_b_2090_, v_c_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v_xs_2083_);
lean_dec_ref(v_val_2082_);
lean_dec(v_upperBound_2081_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2099_, lean_object* v_constName_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2107_, lean_object* v_constName_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2107_, v_constName_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2115_, lean_object* v_ref_2116_, lean_object* v_constName_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2116_, v_constName_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2124_, lean_object* v_ref_2125_, lean_object* v_constName_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2124_, v_ref_2125_, v_constName_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v_ref_2125_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2133_, lean_object* v_ref_2134_, lean_object* v_msg_2135_, lean_object* v_declHint_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2134_, v_msg_2135_, v_declHint_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_ref_2144_, lean_object* v_msg_2145_, lean_object* v_declHint_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2143_, v_ref_2144_, v_msg_2145_, v_declHint_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v_ref_2144_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2153_, lean_object* v_declHint_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2153_, v_declHint_2154_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2161_, lean_object* v_declHint_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2161_, v_declHint_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2169_, lean_object* v_ref_2170_, lean_object* v_msg_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2170_, v_msg_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2178_, lean_object* v_ref_2179_, lean_object* v_msg_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2178_, v_ref_2179_, v_msg_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v_ref_2179_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2187_, lean_object* v_a_2188_, lean_object* v_____r_2189_, lean_object* v_result_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v___x_2196_; 
v___x_2196_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2187_, v_result_2190_, v_a_2188_);
if (v___x_2196_ == 0)
{
uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2197_ = 0;
v___x_2198_ = lean_box(v___x_2197_);
v___x_2199_ = lean_array_push(v_result_2190_, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
else
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2202_ = 5;
v___x_2203_ = lean_box(v___x_2202_);
v___x_2204_ = lean_array_push(v_result_2190_, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2207_, lean_object* v_a_2208_, lean_object* v_____r_2209_, lean_object* v_result_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2207_, v_a_2208_, v_____r_2209_, v_result_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v_a_2208_);
lean_dec_ref(v_info_2207_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2217_, lean_object* v_upperBound_2218_, lean_object* v___x_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_b_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_a_2229_; lean_object* v___y_2234_; uint8_t v___x_2253_; 
v___x_2253_ = lean_nat_dec_lt(v_a_2221_, v_upperBound_2218_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec(v_a_2221_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_b_2222_);
return v___x_2254_;
}
else
{
lean_object* v_resultDeps_2255_; uint8_t v___x_2256_; 
v_resultDeps_2255_ = lean_ctor_get(v_info_2217_, 1);
v___x_2256_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2255_, v_a_2221_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; uint8_t v_isProp_2258_; 
v___x_2257_ = lean_array_fget_borrowed(v___x_2219_, v_a_2221_);
v_isProp_2258_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*1 + 2);
if (v_isProp_2258_ == 0)
{
uint8_t v_isInstance_2259_; 
v_isInstance_2259_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*1 + 4);
if (v_isInstance_2259_ == 0)
{
uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = 2;
v___x_2261_ = lean_box(v___x_2260_);
v___x_2262_ = lean_array_push(v_b_2222_, v___x_2261_);
v_a_2229_ = v___x_2262_;
goto v___jp_2228_;
}
else
{
if (lean_obj_tag(v_a_2220_) == 1)
{
lean_object* v_val_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v_val_2263_ = lean_ctor_get(v_a_2220_, 0);
v___x_2264_ = lean_array_get_size(v_val_2263_);
v___x_2265_ = lean_nat_dec_lt(v_a_2221_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2217_, v_a_2221_, v___x_2266_, v_b_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
v___y_2234_ = v___x_2267_;
goto v___jp_2233_;
}
else
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = lean_array_fget_borrowed(v_val_2263_, v_a_2221_);
v___x_2269_ = lean_unbox(v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_box(0);
v___x_2271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2217_, v_a_2221_, v___x_2270_, v_b_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
v___y_2234_ = v___x_2271_;
goto v___jp_2233_;
}
else
{
uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = 2;
v___x_2273_ = lean_box(v___x_2272_);
v___x_2274_ = lean_array_push(v_b_2222_, v___x_2273_);
v_a_2229_ = v___x_2274_;
goto v___jp_2228_;
}
}
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2217_, v_a_2221_, v___x_2275_, v_b_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
v___y_2234_ = v___x_2276_;
goto v___jp_2233_;
}
}
}
else
{
uint8_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = 3;
v___x_2278_ = lean_box(v___x_2277_);
v___x_2279_ = lean_array_push(v_b_2222_, v___x_2278_);
v_a_2229_ = v___x_2279_;
goto v___jp_2228_;
}
}
else
{
uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = 0;
v___x_2281_ = lean_box(v___x_2280_);
v___x_2282_ = lean_array_push(v_b_2222_, v___x_2281_);
v_a_2229_ = v___x_2282_;
goto v___jp_2228_;
}
}
v___jp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = lean_nat_add(v_a_2221_, v___x_2230_);
lean_dec(v_a_2221_);
v_a_2221_ = v___x_2231_;
v_b_2222_ = v_a_2229_;
goto _start;
}
v___jp_2233_:
{
if (lean_obj_tag(v___y_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2244_; 
v_a_2235_ = lean_ctor_get(v___y_2234_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___y_2234_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2237_ = v___y_2234_;
v_isShared_2238_ = v_isSharedCheck_2244_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___y_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2244_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
if (lean_obj_tag(v_a_2235_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; 
lean_dec(v_a_2221_);
v_a_2239_ = lean_ctor_get(v_a_2235_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v_a_2235_, 1);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v_a_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
else
{
lean_object* v_a_2243_; 
lean_del_object(v___x_2237_);
v_a_2243_ = lean_ctor_get(v_a_2235_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v_a_2235_, 1);
v_a_2229_ = v_a_2243_;
goto v___jp_2228_;
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_a_2221_);
v_a_2245_ = lean_ctor_get(v___y_2234_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___y_2234_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___y_2234_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___y_2234_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2283_, lean_object* v_upperBound_2284_, lean_object* v___x_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_b_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2283_, v_upperBound_2284_, v___x_2285_, v_a_2286_, v_a_2287_, v_b_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v_a_2286_);
lean_dec_ref(v___x_2285_);
lean_dec(v_upperBound_2284_);
lean_dec_ref(v_info_2283_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2297_, lean_object* v_info_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2297_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v_paramInfo_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_result_2309_; lean_object* v___x_2310_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v_paramInfo_2306_ = lean_ctor_get(v_info_2298_, 0);
v___x_2307_ = lean_array_get_size(v_paramInfo_2306_);
v___x_2308_ = lean_unsigned_to_nat(0u);
v_result_2309_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2310_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2298_, v___x_2307_, v_paramInfo_2306_, v_a_2305_, v___x_2308_, v_result_2309_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2305_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2319_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2298_, v_a_2311_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2315_);
v___x_2317_ = v___x_2313_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
else
{
return v___x_2310_;
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
v_a_2320_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2304_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2304_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2328_, lean_object* v_info_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Meta_getCongrSimpKinds(v_f_2328_, v_info_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec_ref(v_info_2329_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2336_, lean_object* v_upperBound_2337_, lean_object* v___x_2338_, lean_object* v_a_2339_, lean_object* v_inst_2340_, lean_object* v_R_2341_, lean_object* v_a_2342_, lean_object* v_b_2343_, lean_object* v_c_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2336_, v_upperBound_2337_, v___x_2338_, v_a_2339_, v_a_2342_, v_b_2343_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2351_, lean_object* v_upperBound_2352_, lean_object* v___x_2353_, lean_object* v_a_2354_, lean_object* v_inst_2355_, lean_object* v_R_2356_, lean_object* v_a_2357_, lean_object* v_b_2358_, lean_object* v_c_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2351_, v_upperBound_2352_, v___x_2353_, v_a_2354_, v_inst_2355_, v_R_2356_, v_a_2357_, v_b_2358_, v_c_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v_a_2354_);
lean_dec_ref(v___x_2353_);
lean_dec(v_upperBound_2352_);
lean_dec_ref(v_info_2351_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2366_, lean_object* v_info_2367_, lean_object* v___x_2368_, lean_object* v_a_2369_, lean_object* v_b_2370_){
_start:
{
lean_object* v_a_2373_; uint8_t v___x_2377_; 
v___x_2377_ = lean_nat_dec_lt(v_a_2369_, v_upperBound_2366_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; 
lean_dec(v_a_2369_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_b_2370_);
return v___x_2378_;
}
else
{
lean_object* v_resultDeps_2379_; uint8_t v___x_2380_; 
v_resultDeps_2379_ = lean_ctor_get(v_info_2367_, 1);
v___x_2380_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2379_, v_a_2369_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = lean_unsigned_to_nat(0u);
v___x_2382_ = lean_nat_dec_eq(v_a_2369_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; uint8_t v_isProp_2384_; 
v___x_2383_ = lean_array_fget_borrowed(v___x_2368_, v_a_2369_);
v_isProp_2384_ = lean_ctor_get_uint8(v___x_2383_, sizeof(void*)*1 + 2);
if (v_isProp_2384_ == 0)
{
uint8_t v_isInstance_2385_; 
v_isInstance_2385_ = lean_ctor_get_uint8(v___x_2383_, sizeof(void*)*1 + 4);
if (v_isInstance_2385_ == 0)
{
uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = 0;
v___x_2387_ = lean_box(v___x_2386_);
v___x_2388_ = lean_array_push(v_b_2370_, v___x_2387_);
v_a_2373_ = v___x_2388_;
goto v___jp_2372_;
}
else
{
uint8_t v___x_2389_; 
v___x_2389_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2367_, v_b_2370_, v_a_2369_);
if (v___x_2389_ == 0)
{
uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = 0;
v___x_2391_ = lean_box(v___x_2390_);
v___x_2392_ = lean_array_push(v_b_2370_, v___x_2391_);
v_a_2373_ = v___x_2392_;
goto v___jp_2372_;
}
else
{
uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2393_ = 5;
v___x_2394_ = lean_box(v___x_2393_);
v___x_2395_ = lean_array_push(v_b_2370_, v___x_2394_);
v_a_2373_ = v___x_2395_;
goto v___jp_2372_;
}
}
}
else
{
uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = 3;
v___x_2397_ = lean_box(v___x_2396_);
v___x_2398_ = lean_array_push(v_b_2370_, v___x_2397_);
v_a_2373_ = v___x_2398_;
goto v___jp_2372_;
}
}
else
{
uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = 2;
v___x_2400_ = lean_box(v___x_2399_);
v___x_2401_ = lean_array_push(v_b_2370_, v___x_2400_);
v_a_2373_ = v___x_2401_;
goto v___jp_2372_;
}
}
else
{
uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = 0;
v___x_2403_ = lean_box(v___x_2402_);
v___x_2404_ = lean_array_push(v_b_2370_, v___x_2403_);
v_a_2373_ = v___x_2404_;
goto v___jp_2372_;
}
}
v___jp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_unsigned_to_nat(1u);
v___x_2375_ = lean_nat_add(v_a_2369_, v___x_2374_);
lean_dec(v_a_2369_);
v_a_2369_ = v___x_2375_;
v_b_2370_ = v_a_2373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2405_, lean_object* v_info_2406_, lean_object* v___x_2407_, lean_object* v_a_2408_, lean_object* v_b_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2405_, v_info_2406_, v___x_2407_, v_a_2408_, v_b_2409_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_info_2406_);
lean_dec(v_upperBound_2405_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_paramInfo_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v_result_2421_; lean_object* v___x_2422_; 
v_paramInfo_2418_ = lean_ctor_get(v_info_2412_, 0);
v___x_2419_ = lean_array_get_size(v_paramInfo_2418_);
v___x_2420_ = lean_unsigned_to_nat(0u);
v_result_2421_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2419_, v_info_2412_, v_paramInfo_2418_, v___x_2420_, v_result_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2431_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2412_, v_a_2423_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
else
{
return v___x_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_info_2432_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2439_, lean_object* v_info_2440_, lean_object* v___x_2441_, lean_object* v_inst_2442_, lean_object* v_R_2443_, lean_object* v_a_2444_, lean_object* v_b_2445_, lean_object* v_c_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2439_, v_info_2440_, v___x_2441_, v_a_2444_, v_b_2445_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2453_, lean_object* v_info_2454_, lean_object* v___x_2455_, lean_object* v_inst_2456_, lean_object* v_R_2457_, lean_object* v_a_2458_, lean_object* v_b_2459_, lean_object* v_c_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2453_, v_info_2454_, v___x_2455_, v_inst_2456_, v_R_2457_, v_a_2458_, v_b_2459_, v_c_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v___x_2455_);
lean_dec_ref(v_info_2454_);
lean_dec(v_upperBound_2453_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(lean_object* v_x_2467_){
_start:
{
if (lean_obj_tag(v_x_2467_) == 0)
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_unsigned_to_nat(0u);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_unsigned_to_nat(1u);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___boxed(lean_object* v_x_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(v_x_2470_);
lean_dec_ref(v_x_2470_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2472_, lean_object* v_k_2473_){
_start:
{
if (lean_obj_tag(v_t_2472_) == 0)
{
lean_object* v_fvarId_2474_; lean_object* v___x_2475_; 
v_fvarId_2474_ = lean_ctor_get(v_t_2472_, 0);
lean_inc(v_fvarId_2474_);
lean_dec_ref_known(v_t_2472_, 1);
v___x_2475_ = lean_apply_1(v_k_2473_, v_fvarId_2474_);
return v___x_2475_;
}
else
{
lean_object* v_lhs_2476_; lean_object* v_rhs_2477_; lean_object* v___x_2478_; 
v_lhs_2476_ = lean_ctor_get(v_t_2472_, 0);
lean_inc(v_lhs_2476_);
v_rhs_2477_ = lean_ctor_get(v_t_2472_, 1);
lean_inc(v_rhs_2477_);
lean_dec_ref_known(v_t_2472_, 2);
v___x_2478_ = lean_apply_2(v_k_2473_, v_lhs_2476_, v_rhs_2477_);
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2479_, lean_object* v_ctorIdx_2480_, lean_object* v_t_2481_, lean_object* v_h_2482_, lean_object* v_k_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2481_, v_k_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2485_, lean_object* v_ctorIdx_2486_, lean_object* v_t_2487_, lean_object* v_h_2488_, lean_object* v_k_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2485_, v_ctorIdx_2486_, v_t_2487_, v_h_2488_, v_k_2489_);
lean_dec(v_ctorIdx_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2491_, lean_object* v_hyp_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2491_, v_hyp_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2494_, lean_object* v_t_2495_, lean_object* v_h_2496_, lean_object* v_hyp_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2495_, v_hyp_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2499_, lean_object* v_decSubsingleton_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2499_, v_decSubsingleton_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2502_, lean_object* v_t_2503_, lean_object* v_h_2504_, lean_object* v_decSubsingleton_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2503_, v_decSubsingleton_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2507_, lean_object* v_fvarId_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2507_, v_fvarId_2508_);
if (lean_obj_tag(v___x_2509_) == 1)
{
lean_object* v_val_2510_; lean_object* v___x_2511_; 
v_val_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_val_2510_);
lean_dec_ref_known(v___x_2509_, 1);
v___x_2511_ = l_Lean_Expr_fvarId_x21(v_val_2510_);
lean_dec(v_val_2510_);
return v___x_2511_;
}
else
{
lean_dec(v___x_2509_);
lean_inc(v_fvarId_2508_);
return v_fvarId_2508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2512_, lean_object* v_fvarId_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2512_, v_fvarId_2513_);
lean_dec(v_fvarId_2513_);
lean_dec(v_s_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2515_, lean_object* v_x_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2515_, v_x_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
v_a_2531_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2522_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2522_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2539_, lean_object* v_x_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2539_, v_x_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2547_, lean_object* v_mvarId_2548_, lean_object* v_x_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2548_, v_x_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2556_, lean_object* v_mvarId_2557_, lean_object* v_x_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2556_, v_mvarId_2557_, v_x_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2565_, lean_object* v___y_2566_){
_start:
{
uint8_t v___x_2568_; 
v___x_2568_ = l_Lean_Expr_hasMVar(v_e_2565_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_e_2565_);
return v___x_2569_;
}
else
{
lean_object* v___x_2570_; lean_object* v_mctx_2571_; lean_object* v___x_2572_; lean_object* v_fst_2573_; lean_object* v_snd_2574_; lean_object* v___x_2575_; lean_object* v_cache_2576_; lean_object* v_zetaDeltaFVarIds_2577_; lean_object* v_postponed_2578_; lean_object* v_diag_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2588_; 
v___x_2570_ = lean_st_ref_get(v___y_2566_);
v_mctx_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_ref(v_mctx_2571_);
lean_dec(v___x_2570_);
v___x_2572_ = l_Lean_instantiateMVarsCore(v_mctx_2571_, v_e_2565_);
v_fst_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_fst_2573_);
v_snd_2574_ = lean_ctor_get(v___x_2572_, 1);
lean_inc(v_snd_2574_);
lean_dec_ref(v___x_2572_);
v___x_2575_ = lean_st_ref_take(v___y_2566_);
v_cache_2576_ = lean_ctor_get(v___x_2575_, 1);
v_zetaDeltaFVarIds_2577_ = lean_ctor_get(v___x_2575_, 2);
v_postponed_2578_ = lean_ctor_get(v___x_2575_, 3);
v_diag_2579_ = lean_ctor_get(v___x_2575_, 4);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2575_, 0);
lean_dec(v_unused_2589_);
v___x_2581_ = v___x_2575_;
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_diag_2579_);
lean_inc(v_postponed_2578_);
lean_inc(v_zetaDeltaFVarIds_2577_);
lean_inc(v_cache_2576_);
lean_dec(v___x_2575_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v_snd_2574_);
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_snd_2574_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_cache_2576_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_zetaDeltaFVarIds_2577_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_postponed_2578_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v_diag_2579_);
v___x_2584_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_st_ref_set(v___y_2566_, v___x_2584_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_fst_2573_);
return v___x_2586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2590_, v___y_2591_);
lean_dec(v___y_2591_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2594_, v___y_2596_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2608_, lean_object* v_x_2609_, lean_object* v_x_2610_, lean_object* v_x_2611_){
_start:
{
lean_object* v_ks_2612_; lean_object* v_vs_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2637_; 
v_ks_2612_ = lean_ctor_get(v_x_2608_, 0);
v_vs_2613_ = lean_ctor_get(v_x_2608_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_x_2608_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2615_ = v_x_2608_;
v_isShared_2616_ = v_isSharedCheck_2637_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_vs_2613_);
lean_inc(v_ks_2612_);
lean_dec(v_x_2608_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2637_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = lean_array_get_size(v_ks_2612_);
v___x_2618_ = lean_nat_dec_lt(v_x_2609_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_dec(v_x_2609_);
v___x_2619_ = lean_array_push(v_ks_2612_, v_x_2610_);
v___x_2620_ = lean_array_push(v_vs_2613_, v_x_2611_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 1, v___x_2620_);
lean_ctor_set(v___x_2615_, 0, v___x_2619_);
v___x_2622_ = v___x_2615_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
else
{
lean_object* v_k_x27_2624_; uint8_t v___x_2625_; 
v_k_x27_2624_ = lean_array_fget_borrowed(v_ks_2612_, v_x_2609_);
v___x_2625_ = l_Lean_instBEqMVarId_beq(v_x_2610_, v_k_x27_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2627_; 
if (v_isShared_2616_ == 0)
{
v___x_2627_ = v___x_2615_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_ks_2612_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_vs_2613_);
v___x_2627_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = lean_unsigned_to_nat(1u);
v___x_2629_ = lean_nat_add(v_x_2609_, v___x_2628_);
lean_dec(v_x_2609_);
v_x_2608_ = v___x_2627_;
v_x_2609_ = v___x_2629_;
goto _start;
}
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2632_ = lean_array_fset(v_ks_2612_, v_x_2609_, v_x_2610_);
v___x_2633_ = lean_array_fset(v_vs_2613_, v_x_2609_, v_x_2611_);
lean_dec(v_x_2609_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 1, v___x_2633_);
lean_ctor_set(v___x_2615_, 0, v___x_2632_);
v___x_2635_ = v___x_2615_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2638_, lean_object* v_k_2639_, lean_object* v_v_2640_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2638_, v___x_2641_, v_k_2639_, v_v_2640_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2644_, size_t v_x_2645_, size_t v_x_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_){
_start:
{
if (lean_obj_tag(v_x_2644_) == 0)
{
lean_object* v_es_2649_; size_t v___x_2650_; size_t v___x_2651_; lean_object* v_j_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v_es_2649_ = lean_ctor_get(v_x_2644_, 0);
v___x_2650_ = ((size_t)31ULL);
v___x_2651_ = lean_usize_land(v_x_2645_, v___x_2650_);
v_j_2652_ = lean_usize_to_nat(v___x_2651_);
v___x_2653_ = lean_array_get_size(v_es_2649_);
v___x_2654_ = lean_nat_dec_lt(v_j_2652_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_dec(v_j_2652_);
lean_dec(v_x_2648_);
lean_dec(v_x_2647_);
return v_x_2644_;
}
else
{
lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2693_; 
lean_inc_ref(v_es_2649_);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v_x_2644_, 0);
lean_dec(v_unused_2694_);
v___x_2656_ = v_x_2644_;
v_isShared_2657_ = v_isSharedCheck_2693_;
goto v_resetjp_2655_;
}
else
{
lean_dec(v_x_2644_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2693_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_v_2658_; lean_object* v___x_2659_; lean_object* v_xs_x27_2660_; lean_object* v___y_2662_; 
v_v_2658_ = lean_array_fget(v_es_2649_, v_j_2652_);
v___x_2659_ = lean_box(0);
v_xs_x27_2660_ = lean_array_fset(v_es_2649_, v_j_2652_, v___x_2659_);
switch(lean_obj_tag(v_v_2658_))
{
case 0:
{
lean_object* v_key_2667_; lean_object* v_val_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2678_; 
v_key_2667_ = lean_ctor_get(v_v_2658_, 0);
v_val_2668_ = lean_ctor_get(v_v_2658_, 1);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_v_2658_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2670_ = v_v_2658_;
v_isShared_2671_ = v_isSharedCheck_2678_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_val_2668_);
lean_inc(v_key_2667_);
lean_dec(v_v_2658_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2678_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
uint8_t v___x_2672_; 
v___x_2672_ = l_Lean_instBEqMVarId_beq(v_x_2647_, v_key_2667_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_del_object(v___x_2670_);
v___x_2673_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2667_, v_val_2668_, v_x_2647_, v_x_2648_);
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
v___y_2662_ = v___x_2674_;
goto v___jp_2661_;
}
else
{
lean_object* v___x_2676_; 
lean_dec(v_val_2668_);
lean_dec(v_key_2667_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v_x_2648_);
lean_ctor_set(v___x_2670_, 0, v_x_2647_);
v___x_2676_ = v___x_2670_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_x_2647_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_x_2648_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
v___y_2662_ = v___x_2676_;
goto v___jp_2661_;
}
}
}
}
case 1:
{
lean_object* v_node_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2691_; 
v_node_2679_ = lean_ctor_get(v_v_2658_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_v_2658_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2681_ = v_v_2658_;
v_isShared_2682_ = v_isSharedCheck_2691_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_node_2679_);
lean_dec(v_v_2658_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2691_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
size_t v___x_2683_; size_t v___x_2684_; size_t v___x_2685_; size_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2683_ = ((size_t)5ULL);
v___x_2684_ = lean_usize_shift_right(v_x_2645_, v___x_2683_);
v___x_2685_ = ((size_t)1ULL);
v___x_2686_ = lean_usize_add(v_x_2646_, v___x_2685_);
v___x_2687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2679_, v___x_2684_, v___x_2686_, v_x_2647_, v_x_2648_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2687_);
v___x_2689_ = v___x_2681_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
v___y_2662_ = v___x_2689_;
goto v___jp_2661_;
}
}
}
default: 
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_x_2647_);
lean_ctor_set(v___x_2692_, 1, v_x_2648_);
v___y_2662_ = v___x_2692_;
goto v___jp_2661_;
}
}
v___jp_2661_:
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = lean_array_fset(v_xs_x27_2660_, v_j_2652_, v___y_2662_);
lean_dec(v_j_2652_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2663_);
v___x_2665_ = v___x_2656_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
else
{
lean_object* v_ks_2695_; lean_object* v_vs_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2716_; 
v_ks_2695_ = lean_ctor_get(v_x_2644_, 0);
v_vs_2696_ = lean_ctor_get(v_x_2644_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2698_ = v_x_2644_;
v_isShared_2699_ = v_isSharedCheck_2716_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_vs_2696_);
lean_inc(v_ks_2695_);
lean_dec(v_x_2644_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2716_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_ks_2695_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_vs_2696_);
v___x_2701_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v_newNode_2702_; uint8_t v___y_2704_; size_t v___x_2710_; uint8_t v___x_2711_; 
v_newNode_2702_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2701_, v_x_2647_, v_x_2648_);
v___x_2710_ = ((size_t)7ULL);
v___x_2711_ = lean_usize_dec_le(v___x_2710_, v_x_2646_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2712_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2702_);
v___x_2713_ = lean_unsigned_to_nat(4u);
v___x_2714_ = lean_nat_dec_lt(v___x_2712_, v___x_2713_);
lean_dec(v___x_2712_);
v___y_2704_ = v___x_2714_;
goto v___jp_2703_;
}
else
{
v___y_2704_ = v___x_2711_;
goto v___jp_2703_;
}
v___jp_2703_:
{
if (v___y_2704_ == 0)
{
lean_object* v_ks_2705_; lean_object* v_vs_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_ks_2705_ = lean_ctor_get(v_newNode_2702_, 0);
lean_inc_ref(v_ks_2705_);
v_vs_2706_ = lean_ctor_get(v_newNode_2702_, 1);
lean_inc_ref(v_vs_2706_);
lean_dec_ref(v_newNode_2702_);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2646_, v_ks_2705_, v_vs_2706_, v___x_2707_, v___x_2708_);
lean_dec_ref(v_vs_2706_);
lean_dec_ref(v_ks_2705_);
return v___x_2709_;
}
else
{
return v_newNode_2702_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_2717_, lean_object* v_keys_2718_, lean_object* v_vals_2719_, lean_object* v_i_2720_, lean_object* v_entries_2721_){
_start:
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = lean_array_get_size(v_keys_2718_);
v___x_2723_ = lean_nat_dec_lt(v_i_2720_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_dec(v_i_2720_);
return v_entries_2721_;
}
else
{
lean_object* v_k_2724_; lean_object* v_v_2725_; uint64_t v___x_2726_; size_t v_h_2727_; size_t v___x_2728_; lean_object* v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; size_t v_h_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_k_2724_ = lean_array_fget_borrowed(v_keys_2718_, v_i_2720_);
v_v_2725_ = lean_array_fget_borrowed(v_vals_2719_, v_i_2720_);
v___x_2726_ = l_Lean_instHashableMVarId_hash(v_k_2724_);
v_h_2727_ = lean_uint64_to_usize(v___x_2726_);
v___x_2728_ = ((size_t)5ULL);
v___x_2729_ = lean_unsigned_to_nat(1u);
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_sub(v_depth_2717_, v___x_2730_);
v___x_2732_ = lean_usize_mul(v___x_2728_, v___x_2731_);
v_h_2733_ = lean_usize_shift_right(v_h_2727_, v___x_2732_);
v___x_2734_ = lean_nat_add(v_i_2720_, v___x_2729_);
lean_dec(v_i_2720_);
lean_inc(v_v_2725_);
lean_inc(v_k_2724_);
v___x_2735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_2721_, v_h_2733_, v_depth_2717_, v_k_2724_, v_v_2725_);
v_i_2720_ = v___x_2734_;
v_entries_2721_ = v___x_2735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2737_, lean_object* v_keys_2738_, lean_object* v_vals_2739_, lean_object* v_i_2740_, lean_object* v_entries_2741_){
_start:
{
size_t v_depth_boxed_2742_; lean_object* v_res_2743_; 
v_depth_boxed_2742_ = lean_unbox_usize(v_depth_2737_);
lean_dec(v_depth_2737_);
v_res_2743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_2742_, v_keys_2738_, v_vals_2739_, v_i_2740_, v_entries_2741_);
lean_dec_ref(v_vals_2739_);
lean_dec_ref(v_keys_2738_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_){
_start:
{
size_t v_x_4152__boxed_2749_; size_t v_x_4153__boxed_2750_; lean_object* v_res_2751_; 
v_x_4152__boxed_2749_ = lean_unbox_usize(v_x_2745_);
lean_dec(v_x_2745_);
v_x_4153__boxed_2750_ = lean_unbox_usize(v_x_2746_);
lean_dec(v_x_2746_);
v_res_2751_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2744_, v_x_4152__boxed_2749_, v_x_4153__boxed_2750_, v_x_2747_, v_x_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
uint64_t v___x_2755_; size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
v___x_2755_ = l_Lean_instHashableMVarId_hash(v_x_2753_);
v___x_2756_ = lean_uint64_to_usize(v___x_2755_);
v___x_2757_ = ((size_t)1ULL);
v___x_2758_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2752_, v___x_2756_, v___x_2757_, v_x_2753_, v_x_2754_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object* v_mvarId_2759_, lean_object* v_val_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; lean_object* v_mctx_2764_; lean_object* v_cache_2765_; lean_object* v_zetaDeltaFVarIds_2766_; lean_object* v_postponed_2767_; lean_object* v_diag_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2796_; 
v___x_2763_ = lean_st_ref_take(v___y_2761_);
v_mctx_2764_ = lean_ctor_get(v___x_2763_, 0);
v_cache_2765_ = lean_ctor_get(v___x_2763_, 1);
v_zetaDeltaFVarIds_2766_ = lean_ctor_get(v___x_2763_, 2);
v_postponed_2767_ = lean_ctor_get(v___x_2763_, 3);
v_diag_2768_ = lean_ctor_get(v___x_2763_, 4);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2770_ = v___x_2763_;
v_isShared_2771_ = v_isSharedCheck_2796_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_diag_2768_);
lean_inc(v_postponed_2767_);
lean_inc(v_zetaDeltaFVarIds_2766_);
lean_inc(v_cache_2765_);
lean_inc(v_mctx_2764_);
lean_dec(v___x_2763_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2796_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v_depth_2772_; lean_object* v_levelAssignDepth_2773_; lean_object* v_lmvarCounter_2774_; lean_object* v_mvarCounter_2775_; lean_object* v_lDecls_2776_; lean_object* v_decls_2777_; lean_object* v_userNames_2778_; lean_object* v_lAssignment_2779_; lean_object* v_eAssignment_2780_; lean_object* v_dAssignment_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2795_; 
v_depth_2772_ = lean_ctor_get(v_mctx_2764_, 0);
v_levelAssignDepth_2773_ = lean_ctor_get(v_mctx_2764_, 1);
v_lmvarCounter_2774_ = lean_ctor_get(v_mctx_2764_, 2);
v_mvarCounter_2775_ = lean_ctor_get(v_mctx_2764_, 3);
v_lDecls_2776_ = lean_ctor_get(v_mctx_2764_, 4);
v_decls_2777_ = lean_ctor_get(v_mctx_2764_, 5);
v_userNames_2778_ = lean_ctor_get(v_mctx_2764_, 6);
v_lAssignment_2779_ = lean_ctor_get(v_mctx_2764_, 7);
v_eAssignment_2780_ = lean_ctor_get(v_mctx_2764_, 8);
v_dAssignment_2781_ = lean_ctor_get(v_mctx_2764_, 9);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_mctx_2764_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2783_ = v_mctx_2764_;
v_isShared_2784_ = v_isSharedCheck_2795_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_dAssignment_2781_);
lean_inc(v_eAssignment_2780_);
lean_inc(v_lAssignment_2779_);
lean_inc(v_userNames_2778_);
lean_inc(v_decls_2777_);
lean_inc(v_lDecls_2776_);
lean_inc(v_mvarCounter_2775_);
lean_inc(v_lmvarCounter_2774_);
lean_inc(v_levelAssignDepth_2773_);
lean_inc(v_depth_2772_);
lean_dec(v_mctx_2764_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2795_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2780_, v_mvarId_2759_, v_val_2760_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 8, v___x_2785_);
v___x_2787_ = v___x_2783_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_depth_2772_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_levelAssignDepth_2773_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_lmvarCounter_2774_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v_mvarCounter_2775_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_lDecls_2776_);
lean_ctor_set(v_reuseFailAlloc_2794_, 5, v_decls_2777_);
lean_ctor_set(v_reuseFailAlloc_2794_, 6, v_userNames_2778_);
lean_ctor_set(v_reuseFailAlloc_2794_, 7, v_lAssignment_2779_);
lean_ctor_set(v_reuseFailAlloc_2794_, 8, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2794_, 9, v_dAssignment_2781_);
v___x_2787_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2787_);
v___x_2789_ = v___x_2770_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_cache_2765_);
lean_ctor_set(v_reuseFailAlloc_2793_, 2, v_zetaDeltaFVarIds_2766_);
lean_ctor_set(v_reuseFailAlloc_2793_, 3, v_postponed_2767_);
lean_ctor_set(v_reuseFailAlloc_2793_, 4, v_diag_2768_);
v___x_2789_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2790_ = lean_st_ref_set(v___y_2761_, v___x_2789_);
v___x_2791_ = lean_box(0);
v___x_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
return v___x_2792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2797_, lean_object* v_val_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2797_, v_val_2798_, v___y_2799_);
lean_dec(v___y_2799_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2810_, lean_object* v_as_2811_, size_t v_sz_2812_, size_t v_i_2813_, lean_object* v_b_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_a_2821_; uint8_t v___x_2825_; 
v___x_2825_ = lean_usize_dec_lt(v_i_2813_, v_sz_2812_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_b_2814_);
return v___x_2826_;
}
else
{
lean_object* v_fst_2827_; lean_object* v_snd_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; lean_object* v_a_2831_; 
v_fst_2827_ = lean_ctor_get(v_b_2814_, 0);
lean_inc(v_fst_2827_);
v_snd_2828_ = lean_ctor_get(v_b_2814_, 1);
lean_inc(v_snd_2828_);
lean_dec_ref(v_b_2814_);
v___x_2829_ = lean_unsigned_to_nat(0u);
v___x_2830_ = lean_nat_dec_eq(v___x_2810_, v___x_2829_);
v_a_2831_ = lean_array_uget_borrowed(v_as_2811_, v_i_2813_);
if (lean_obj_tag(v_a_2831_) == 0)
{
lean_object* v_fvarId_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_fvarId_2832_ = lean_ctor_get(v_a_2831_, 0);
v___x_2833_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2828_, v_fvarId_2832_);
v___x_2834_ = l_Lean_Meta_substCore(v_fst_2827_, v___x_2833_, v___x_2825_, v_snd_2828_, v___x_2825_, v___x_2830_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v_fst_2836_; lean_object* v_snd_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v_fst_2836_ = lean_ctor_get(v_a_2835_, 0);
v_snd_2837_ = lean_ctor_get(v_a_2835_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_a_2835_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v_a_2835_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_snd_2837_);
lean_inc(v_fst_2836_);
lean_dec(v_a_2835_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_fst_2836_);
lean_ctor_set(v___x_2839_, 0, v_snd_2837_);
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_snd_2837_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_fst_2836_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
v_a_2821_ = v___x_2842_;
goto v___jp_2820_;
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2845_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2834_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2834_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v_lhs_2853_; lean_object* v_rhs_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_lhs_2853_ = lean_ctor_get(v_a_2831_, 0);
v_rhs_2854_ = lean_ctor_get(v_a_2831_, 1);
v___x_2855_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2828_, v_lhs_2853_);
v___x_2856_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2828_, v_rhs_2854_);
v___x_2857_ = l_Lean_mkFVar(v___x_2855_);
v___x_2858_ = l_Lean_mkFVar(v___x_2856_);
lean_inc_ref(v___x_2858_);
lean_inc_ref(v___x_2857_);
v___x_2859_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2859_, 0, v___x_2857_);
lean_closure_set(v___x_2859_, 1, v___x_2858_);
lean_inc(v_fst_2827_);
v___x_2860_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2827_, v___x_2859_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2863_ = lean_unsigned_to_nat(2u);
v___x_2864_ = lean_mk_empty_array_with_capacity(v___x_2863_);
v___x_2865_ = lean_array_push(v___x_2864_, v___x_2857_);
v___x_2866_ = lean_array_push(v___x_2865_, v___x_2858_);
v___x_2867_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2867_, 0, v___x_2862_);
lean_closure_set(v___x_2867_, 1, v___x_2866_);
lean_inc(v_fst_2827_);
v___x_2868_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2827_, v___x_2867_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
v___x_2871_ = l_Lean_MVarId_assert(v_fst_2827_, v___x_2870_, v_a_2861_, v_a_2869_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_Meta_intro1Core(v_a_2872_, v___x_2830_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v_fst_2875_; lean_object* v_snd_2876_; lean_object* v___x_2877_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v_fst_2875_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_fst_2875_);
v_snd_2876_ = lean_ctor_get(v_a_2874_, 1);
lean_inc(v_snd_2876_);
lean_dec(v_a_2874_);
v___x_2877_ = l_Lean_Meta_substCore(v_snd_2876_, v_fst_2875_, v___x_2825_, v_snd_2828_, v___x_2825_, v___x_2830_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v_fst_2879_; lean_object* v_snd_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v_fst_2879_ = lean_ctor_get(v_a_2878_, 0);
v_snd_2880_ = lean_ctor_get(v_a_2878_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_a_2878_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v_a_2878_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_snd_2880_);
lean_inc(v_fst_2879_);
lean_dec(v_a_2878_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v_fst_2879_);
lean_ctor_set(v___x_2882_, 0, v_snd_2880_);
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_snd_2880_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_fst_2879_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
v_a_2821_ = v___x_2885_;
goto v___jp_2820_;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2877_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2877_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_snd_2828_);
v_a_2896_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2873_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2873_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_snd_2828_);
v_a_2904_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2871_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2871_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2861_);
lean_dec(v_snd_2828_);
lean_dec(v_fst_2827_);
v_a_2912_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2868_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2868_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec_ref(v___x_2858_);
lean_dec_ref(v___x_2857_);
lean_dec(v_snd_2828_);
lean_dec(v_fst_2827_);
v_a_2920_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2860_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2860_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
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
v___jp_2820_:
{
size_t v___x_2822_; size_t v___x_2823_; 
v___x_2822_ = ((size_t)1ULL);
v___x_2823_ = lean_usize_add(v_i_2813_, v___x_2822_);
v_i_2813_ = v___x_2823_;
v_b_2814_ = v_a_2821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_2928_, lean_object* v_as_2929_, lean_object* v_sz_2930_, lean_object* v_i_2931_, lean_object* v_b_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
size_t v_sz_boxed_2938_; size_t v_i_boxed_2939_; lean_object* v_res_2940_; 
v_sz_boxed_2938_ = lean_unbox_usize(v_sz_2930_);
lean_dec(v_sz_2930_);
v_i_boxed_2939_ = lean_unbox_usize(v_i_2931_);
lean_dec(v_i_2931_);
v_res_2940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2928_, v_as_2929_, v_sz_boxed_2938_, v_i_boxed_2939_, v_b_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec_ref(v_as_2929_);
lean_dec(v___x_2928_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_2941_, lean_object* v_as_2942_, size_t v_i_2943_, size_t v_stop_2944_, lean_object* v_b_2945_){
_start:
{
lean_object* v___y_2947_; uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_eq(v_i_2943_, v_stop_2944_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_array_uget_borrowed(v_as_2942_, v_i_2943_);
v___x_2954_ = lean_array_get_borrowed(v___x_2952_, v_eqs_2941_, v___x_2953_);
if (lean_obj_tag(v___x_2954_) == 0)
{
v___y_2947_ = v_b_2945_;
goto v___jp_2946_;
}
else
{
lean_object* v_val_2955_; lean_object* v___x_2956_; 
v_val_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_val_2955_);
v___x_2956_ = lean_array_push(v_b_2945_, v_val_2955_);
v___y_2947_ = v___x_2956_;
goto v___jp_2946_;
}
}
else
{
return v_b_2945_;
}
v___jp_2946_:
{
size_t v___x_2948_; size_t v___x_2949_; 
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_add(v_i_2943_, v___x_2948_);
v_i_2943_ = v___x_2949_;
v_b_2945_ = v___y_2947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_2957_, lean_object* v_as_2958_, lean_object* v_i_2959_, lean_object* v_stop_2960_, lean_object* v_b_2961_){
_start:
{
size_t v_i_boxed_2962_; size_t v_stop_boxed_2963_; lean_object* v_res_2964_; 
v_i_boxed_2962_ = lean_unbox_usize(v_i_2959_);
lean_dec(v_i_2959_);
v_stop_boxed_2963_ = lean_unbox_usize(v_stop_2960_);
lean_dec(v_stop_2960_);
v_res_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2957_, v_as_2958_, v_i_boxed_2962_, v_stop_boxed_2963_, v_b_2961_);
lean_dec_ref(v_as_2958_);
lean_dec_ref(v_eqs_2957_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_2967_, lean_object* v_as_2968_, lean_object* v_start_2969_, lean_object* v_stop_2970_){
_start:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_2972_ = lean_nat_dec_lt(v_start_2969_, v_stop_2970_);
if (v___x_2972_ == 0)
{
return v___x_2971_;
}
else
{
lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = lean_array_get_size(v_as_2968_);
v___x_2974_ = lean_nat_dec_le(v_stop_2970_, v___x_2973_);
if (v___x_2974_ == 0)
{
uint8_t v___x_2975_; 
v___x_2975_ = lean_nat_dec_lt(v_start_2969_, v___x_2973_);
if (v___x_2975_ == 0)
{
return v___x_2971_;
}
else
{
size_t v___x_2976_; size_t v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = lean_usize_of_nat(v_start_2969_);
v___x_2977_ = lean_usize_of_nat(v___x_2973_);
v___x_2978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2967_, v_as_2968_, v___x_2976_, v___x_2977_, v___x_2971_);
return v___x_2978_;
}
}
else
{
size_t v___x_2979_; size_t v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = lean_usize_of_nat(v_start_2969_);
v___x_2980_ = lean_usize_of_nat(v_stop_2970_);
v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2967_, v_as_2968_, v___x_2979_, v___x_2980_, v___x_2971_);
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_2982_, lean_object* v_as_2983_, lean_object* v_start_2984_, lean_object* v_stop_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2982_, v_as_2983_, v_start_2984_, v_stop_2985_);
lean_dec(v_stop_2985_);
lean_dec(v_start_2984_);
lean_dec_ref(v_as_2983_);
lean_dec_ref(v_eqs_2982_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_2987_, lean_object* v_type_2988_, lean_object* v_deps_2989_, lean_object* v_eqs_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_eqs_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2996_ = lean_unsigned_to_nat(0u);
v___x_2997_ = lean_array_get_size(v_deps_2989_);
v_eqs_2998_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2990_, v_deps_2989_, v___x_2996_, v___x_2997_);
v___x_2999_ = lean_array_get_size(v_eqs_2998_);
v___x_3000_ = lean_nat_dec_eq(v___x_2999_, v___x_2996_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; uint8_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_type_2988_);
v___x_3002_ = 0;
v___x_3003_ = lean_box(0);
v___x_3004_ = l_Lean_Meta_mkFreshExprMVar(v___x_3001_, v___x_3002_, v___x_3003_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; size_t v_sz_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = l_Lean_Expr_mvarId_x21(v_a_3005_);
v___x_3007_ = lean_box(0);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v_sz_3009_ = lean_array_size(v_eqs_2998_);
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2999_, v_eqs_2998_, v_sz_3009_, v___x_3010_, v___x_3008_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
lean_dec_ref(v_eqs_2998_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v_fst_3013_; lean_object* v_snd_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v_fst_3013_ = lean_ctor_get(v_a_3012_, 0);
lean_inc(v_fst_3013_);
v_snd_3014_ = lean_ctor_get(v_a_3012_, 1);
lean_inc(v_snd_3014_);
lean_dec(v_a_3012_);
v___x_3015_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_3014_, v_fvarId_2987_);
lean_dec(v_fvarId_2987_);
lean_dec(v_snd_3014_);
v___x_3016_ = l_Lean_mkFVar(v___x_3015_);
v___x_3017_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_3013_, v___x_3016_, v_a_2992_);
lean_dec_ref(v___x_3017_);
v___x_3018_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_3005_, v_a_2992_);
return v___x_3018_;
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_a_3005_);
lean_dec(v_fvarId_2987_);
v_a_3019_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3011_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3011_);
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
lean_dec_ref(v_eqs_2998_);
lean_dec(v_fvarId_2987_);
return v___x_3004_;
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_dec_ref(v_eqs_2998_);
lean_dec_ref(v_type_2988_);
v___x_3027_ = l_Lean_mkFVar(v_fvarId_2987_);
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
return v___x_3028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3029_, lean_object* v_type_3030_, lean_object* v_deps_3031_, lean_object* v_eqs_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3029_, v_type_3030_, v_deps_3031_, v_eqs_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec_ref(v_eqs_3032_);
lean_dec_ref(v_deps_3031_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3039_, lean_object* v_val_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3039_, v_val_3040_, v___y_3042_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3047_, lean_object* v_val_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3047_, v_val_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3055_, lean_object* v_x_3056_, lean_object* v_x_3057_, lean_object* v_x_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3056_, v_x_3057_, v_x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3060_, lean_object* v_x_3061_, size_t v_x_3062_, size_t v_x_3063_, lean_object* v_x_3064_, lean_object* v_x_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3061_, v_x_3062_, v_x_3063_, v_x_3064_, v_x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3067_, lean_object* v_x_3068_, lean_object* v_x_3069_, lean_object* v_x_3070_, lean_object* v_x_3071_, lean_object* v_x_3072_){
_start:
{
size_t v_x_4757__boxed_3073_; size_t v_x_4758__boxed_3074_; lean_object* v_res_3075_; 
v_x_4757__boxed_3073_ = lean_unbox_usize(v_x_3069_);
lean_dec(v_x_3069_);
v_x_4758__boxed_3074_ = lean_unbox_usize(v_x_3070_);
lean_dec(v_x_3070_);
v_res_3075_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3067_, v_x_3068_, v_x_4757__boxed_3073_, v_x_4758__boxed_3074_, v_x_3071_, v_x_3072_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3076_, lean_object* v_n_3077_, lean_object* v_k_3078_, lean_object* v_v_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3077_, v_k_3078_, v_v_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3081_, size_t v_depth_3082_, lean_object* v_keys_3083_, lean_object* v_vals_3084_, lean_object* v_heq_3085_, lean_object* v_i_3086_, lean_object* v_entries_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3082_, v_keys_3083_, v_vals_3084_, v_i_3086_, v_entries_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3089_, lean_object* v_depth_3090_, lean_object* v_keys_3091_, lean_object* v_vals_3092_, lean_object* v_heq_3093_, lean_object* v_i_3094_, lean_object* v_entries_3095_){
_start:
{
size_t v_depth_boxed_3096_; lean_object* v_res_3097_; 
v_depth_boxed_3096_ = lean_unbox_usize(v_depth_3090_);
lean_dec(v_depth_3090_);
v_res_3097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3089_, v_depth_boxed_3096_, v_keys_3091_, v_vals_3092_, v_heq_3093_, v_i_3094_, v_entries_3095_);
lean_dec_ref(v_vals_3092_);
lean_dec_ref(v_keys_3091_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3098_, lean_object* v_x_3099_, lean_object* v_x_3100_, lean_object* v_x_3101_, lean_object* v_x_3102_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3099_, v_x_3100_, v_x_3101_, v_x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___f_3111_; lean_object* v___x_1803__overap_3112_; lean_object* v___x_3113_; 
v___f_3111_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1803__overap_3112_ = lean_panic_fn_borrowed(v___f_3111_, v_msg_3105_);
lean_inc(v___y_3109_);
lean_inc_ref(v___y_3108_);
lean_inc(v___y_3107_);
lean_inc_ref(v___y_3106_);
v___x_3113_ = lean_apply_5(v___x_1803__overap_3112_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, lean_box(0));
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
return v_res_3120_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3124_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3125_ = lean_unsigned_to_nat(34u);
v___x_3126_ = lean_unsigned_to_nat(360u);
v___x_3127_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3128_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3129_ = l_mkPanicMessageWithDecl(v___x_3128_, v___x_3127_, v___x_3126_, v___x_3125_, v___x_3124_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3130_, lean_object* v___x_3131_, lean_object* v___x_3132_, lean_object* v_i_3133_, lean_object* v_kinds_3134_, lean_object* v___x_3135_, lean_object* v_lhs_3136_, lean_object* v_rhs_3137_, lean_object* v_type_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
uint8_t v___x_1990__boxed_3144_; uint8_t v___x_1991__boxed_3145_; lean_object* v_res_3146_; 
v___x_1990__boxed_3144_ = lean_unbox(v___x_3131_);
v___x_1991__boxed_3145_ = lean_unbox(v___x_3132_);
v_res_3146_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3130_, v___x_1990__boxed_3144_, v___x_1991__boxed_3145_, v_i_3133_, v_kinds_3134_, v___x_3135_, v_lhs_3136_, v_rhs_3137_, v_type_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3147_, uint8_t v___x_3148_, uint8_t v___x_3149_, lean_object* v_i_3150_, lean_object* v___x_3151_, lean_object* v_kinds_3152_, lean_object* v_typeSub_3153_, lean_object* v_lhs_3154_, lean_object* v_rhs_3155_, lean_object* v_type_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v___x_3162_; uint8_t v___x_3163_; lean_object* v___x_3164_; 
lean_inc_ref(v_rhs_3155_);
v___x_3162_ = lean_array_push(v___x_3147_, v_rhs_3155_);
v___x_3163_ = 1;
v___x_3164_ = l_Lean_Meta_mkLambdaFVars(v___x_3162_, v_type_3156_, v___x_3148_, v___x_3149_, v___x_3148_, v___x_3149_, v___x_3163_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec_ref(v___x_3162_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v___x_3166_ = lean_nat_add(v_i_3150_, v___x_3151_);
v___x_3167_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3152_, v___x_3166_, v_typeSub_3153_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3167_, 1);
v___x_3169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3170_ = lean_unsigned_to_nat(2u);
v___x_3171_ = lean_mk_empty_array_with_capacity(v___x_3170_);
v___x_3172_ = lean_array_push(v___x_3171_, v_lhs_3154_);
v___x_3173_ = lean_array_push(v___x_3172_, v_rhs_3155_);
lean_inc_ref(v___x_3173_);
v___x_3174_ = l_Lean_Meta_mkAppM(v___x_3169_, v___x_3173_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
v___x_3176_ = l_Lean_Meta_mkEqNDRec(v_a_3165_, v_a_3168_, v_a_3175_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
v___x_3178_ = l_Lean_Meta_mkLambdaFVars(v___x_3173_, v_a_3177_, v___x_3148_, v___x_3149_, v___x_3148_, v___x_3149_, v___x_3163_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec_ref(v___x_3173_);
return v___x_3178_;
}
else
{
lean_dec_ref(v___x_3173_);
return v___x_3176_;
}
}
else
{
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3168_);
lean_dec(v_a_3165_);
return v___x_3174_;
}
}
else
{
lean_dec(v_a_3165_);
lean_dec_ref(v_rhs_3155_);
lean_dec_ref(v_lhs_3154_);
return v___x_3167_;
}
}
else
{
lean_dec_ref(v_rhs_3155_);
lean_dec_ref(v_lhs_3154_);
lean_dec_ref(v_typeSub_3153_);
lean_dec_ref(v_kinds_3152_);
return v___x_3164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3179_, lean_object* v___x_3180_, lean_object* v___x_3181_, lean_object* v_i_3182_, lean_object* v___x_3183_, lean_object* v_kinds_3184_, lean_object* v_typeSub_3185_, lean_object* v_lhs_3186_, lean_object* v_rhs_3187_, lean_object* v_type_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v___x_2053__boxed_3194_; uint8_t v___x_2054__boxed_3195_; lean_object* v_res_3196_; 
v___x_2053__boxed_3194_ = lean_unbox(v___x_3180_);
v___x_2054__boxed_3195_ = lean_unbox(v___x_3181_);
v_res_3196_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3179_, v___x_2053__boxed_3194_, v___x_2054__boxed_3195_, v_i_3182_, v___x_3183_, v_kinds_3184_, v_typeSub_3185_, v_lhs_3186_, v_rhs_3187_, v_type_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___x_3183_);
lean_dec(v_i_3182_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(lean_object* v_kinds_3197_, lean_object* v_i_3198_, uint8_t v___x_3199_, uint8_t v___x_3200_, lean_object* v_lhs_3201_, lean_object* v_type_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
uint8_t v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3211_ = 0;
v___x_3212_ = lean_box(v___x_3211_);
v___x_3213_ = lean_array_get(v___x_3212_, v_kinds_3197_, v_i_3198_);
lean_dec(v___x_3212_);
v___x_3214_ = lean_unbox(v___x_3213_);
lean_dec(v___x_3213_);
switch(v___x_3214_)
{
case 1:
{
lean_dec_ref(v_type_3202_);
lean_dec_ref(v_lhs_3201_);
lean_dec(v_i_3198_);
lean_dec_ref(v_kinds_3197_);
goto v___jp_3208_;
}
case 2:
{
lean_object* v___x_3215_; 
lean_inc_ref(v_lhs_3201_);
v___x_3215_ = l_Lean_Meta_mkEqRefl(v_lhs_3201_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___f_3226_; lean_object* v___x_3227_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v___x_3217_ = l_Lean_Expr_bindingBody_x21(v_type_3202_);
v___x_3218_ = l_Lean_Expr_bindingBody_x21(v___x_3217_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = lean_unsigned_to_nat(2u);
v___x_3220_ = lean_mk_empty_array_with_capacity(v___x_3219_);
lean_inc_ref(v___x_3220_);
v___x_3221_ = lean_array_push(v___x_3220_, v_a_3216_);
lean_inc_ref(v_lhs_3201_);
v___x_3222_ = lean_array_push(v___x_3221_, v_lhs_3201_);
v___x_3223_ = lean_expr_instantiate(v___x_3218_, v___x_3222_);
lean_dec_ref(v___x_3222_);
lean_dec_ref(v___x_3218_);
v___x_3224_ = lean_box(v___x_3199_);
v___x_3225_ = lean_box(v___x_3200_);
v___f_3226_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3226_, 0, v___x_3220_);
lean_closure_set(v___f_3226_, 1, v___x_3224_);
lean_closure_set(v___f_3226_, 2, v___x_3225_);
lean_closure_set(v___f_3226_, 3, v_i_3198_);
lean_closure_set(v___f_3226_, 4, v_kinds_3197_);
lean_closure_set(v___f_3226_, 5, v___x_3223_);
lean_closure_set(v___f_3226_, 6, v_lhs_3201_);
v___x_3227_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3202_, v___f_3226_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3227_;
}
else
{
lean_dec_ref(v_type_3202_);
lean_dec_ref(v_lhs_3201_);
lean_dec(v_i_3198_);
lean_dec_ref(v_kinds_3197_);
return v___x_3215_;
}
}
case 4:
{
lean_dec_ref(v_type_3202_);
lean_dec_ref(v_lhs_3201_);
lean_dec(v_i_3198_);
lean_dec_ref(v_kinds_3197_);
goto v___jp_3208_;
}
case 5:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v_typeSub_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___f_3235_; lean_object* v___x_3236_; 
v___x_3228_ = l_Lean_Expr_bindingBody_x21(v_type_3202_);
v___x_3229_ = lean_unsigned_to_nat(1u);
v___x_3230_ = lean_mk_empty_array_with_capacity(v___x_3229_);
lean_inc_ref(v_lhs_3201_);
lean_inc_ref(v___x_3230_);
v___x_3231_ = lean_array_push(v___x_3230_, v_lhs_3201_);
v_typeSub_3232_ = lean_expr_instantiate(v___x_3228_, v___x_3231_);
lean_dec_ref(v___x_3231_);
lean_dec_ref(v___x_3228_);
v___x_3233_ = lean_box(v___x_3199_);
v___x_3234_ = lean_box(v___x_3200_);
v___f_3235_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3235_, 0, v___x_3230_);
lean_closure_set(v___f_3235_, 1, v___x_3233_);
lean_closure_set(v___f_3235_, 2, v___x_3234_);
lean_closure_set(v___f_3235_, 3, v_i_3198_);
lean_closure_set(v___f_3235_, 4, v___x_3229_);
lean_closure_set(v___f_3235_, 5, v_kinds_3197_);
lean_closure_set(v___f_3235_, 6, v_typeSub_3232_);
lean_closure_set(v___f_3235_, 7, v_lhs_3201_);
v___x_3236_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3202_, v___f_3235_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3236_;
}
default: 
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_nat_add(v_i_3198_, v___x_3237_);
lean_dec(v_i_3198_);
v___x_3239_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3197_, v___x_3238_, v_type_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
v___x_3241_ = lean_mk_empty_array_with_capacity(v___x_3237_);
v___x_3242_ = lean_array_push(v___x_3241_, v_lhs_3201_);
v___x_3243_ = 1;
v___x_3244_ = l_Lean_Meta_mkLambdaFVars(v___x_3242_, v_a_3240_, v___x_3199_, v___x_3200_, v___x_3199_, v___x_3200_, v___x_3243_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec_ref(v___x_3242_);
return v___x_3244_;
}
else
{
lean_dec_ref(v_lhs_3201_);
return v___x_3239_;
}
}
}
v___jp_3208_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3210_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3209_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v_kinds_3245_, lean_object* v_i_3246_, lean_object* v___x_3247_, lean_object* v___x_3248_, lean_object* v_lhs_3249_, lean_object* v_type_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v___x_2090__boxed_3256_; uint8_t v___x_2091__boxed_3257_; lean_object* v_res_3258_; 
v___x_2090__boxed_3256_ = lean_unbox(v___x_3247_);
v___x_2091__boxed_3257_ = lean_unbox(v___x_3248_);
v_res_3258_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v_kinds_3245_, v_i_3246_, v___x_2090__boxed_3256_, v___x_2091__boxed_3257_, v_lhs_3249_, v_type_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
return v_res_3258_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3259_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3260_ = lean_unsigned_to_nat(43u);
v___x_3261_ = lean_unsigned_to_nat(355u);
v___x_3262_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3263_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3264_ = l_mkPanicMessageWithDecl(v___x_3263_, v___x_3262_, v___x_3261_, v___x_3260_, v___x_3259_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3265_, lean_object* v_i_3266_, lean_object* v_type_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = lean_array_get_size(v_kinds_3265_);
v___x_3274_ = lean_nat_dec_eq(v_i_3266_, v___x_3273_);
if (v___x_3274_ == 0)
{
uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___f_3278_; lean_object* v___x_3279_; 
v___x_3275_ = 1;
v___x_3276_ = lean_box(v___x_3274_);
v___x_3277_ = lean_box(v___x_3275_);
v___f_3278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3278_, 0, v_kinds_3265_);
lean_closure_set(v___f_3278_, 1, v_i_3266_);
lean_closure_set(v___f_3278_, 2, v___x_3276_);
lean_closure_set(v___f_3278_, 3, v___x_3277_);
v___x_3279_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3267_, v___f_3278_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
return v___x_3279_;
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
lean_dec(v_i_3266_);
lean_dec_ref(v_kinds_3265_);
v___x_3280_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3281_ = lean_unsigned_to_nat(3u);
v___x_3282_ = l_Lean_Expr_isAppOfArity(v_type_3267_, v___x_3280_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec_ref(v_type_3267_);
v___x_3283_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3284_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3283_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
return v___x_3284_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = l_Lean_Expr_appFn_x21(v_type_3267_);
lean_dec_ref(v_type_3267_);
v___x_3286_ = l_Lean_Expr_appArg_x21(v___x_3285_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = l_Lean_Meta_mkEqRefl(v___x_3286_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
return v___x_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* v___x_3288_, lean_object* v_rhs_3289_, uint8_t v___x_3290_, uint8_t v___x_3291_, lean_object* v_i_3292_, lean_object* v_kinds_3293_, lean_object* v___x_3294_, lean_object* v_lhs_3295_, lean_object* v_heq_3296_, lean_object* v_type_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; lean_object* v___x_3306_; 
lean_inc_ref(v_rhs_3289_);
v___x_3303_ = lean_array_push(v___x_3288_, v_rhs_3289_);
lean_inc_ref(v_heq_3296_);
v___x_3304_ = lean_array_push(v___x_3303_, v_heq_3296_);
v___x_3305_ = 1;
v___x_3306_ = l_Lean_Meta_mkLambdaFVars(v___x_3304_, v_type_3297_, v___x_3290_, v___x_3291_, v___x_3290_, v___x_3291_, v___x_3305_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec_ref(v___x_3304_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = lean_unsigned_to_nat(1u);
v___x_3309_ = lean_nat_add(v_i_3292_, v___x_3308_);
v___x_3310_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3293_, v___x_3309_, v___x_3294_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3312_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
lean_inc_ref(v_heq_3296_);
v___x_3312_ = l_Lean_Meta_mkEqRec(v_a_3307_, v_a_3311_, v_heq_3296_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3314_ = lean_unsigned_to_nat(3u);
v___x_3315_ = lean_mk_empty_array_with_capacity(v___x_3314_);
v___x_3316_ = lean_array_push(v___x_3315_, v_lhs_3295_);
v___x_3317_ = lean_array_push(v___x_3316_, v_rhs_3289_);
v___x_3318_ = lean_array_push(v___x_3317_, v_heq_3296_);
v___x_3319_ = l_Lean_Meta_mkLambdaFVars(v___x_3318_, v_a_3313_, v___x_3290_, v___x_3291_, v___x_3290_, v___x_3291_, v___x_3305_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec_ref(v___x_3318_);
return v___x_3319_;
}
else
{
lean_dec_ref(v_heq_3296_);
lean_dec_ref(v_lhs_3295_);
lean_dec_ref(v_rhs_3289_);
return v___x_3312_;
}
}
else
{
lean_dec(v_a_3307_);
lean_dec_ref(v_heq_3296_);
lean_dec_ref(v_lhs_3295_);
lean_dec_ref(v_rhs_3289_);
return v___x_3310_;
}
}
else
{
lean_dec_ref(v_heq_3296_);
lean_dec_ref(v_lhs_3295_);
lean_dec_ref(v___x_3294_);
lean_dec_ref(v_kinds_3293_);
lean_dec_ref(v_rhs_3289_);
return v___x_3306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* v___x_3320_, lean_object* v_rhs_3321_, lean_object* v___x_3322_, lean_object* v___x_3323_, lean_object* v_i_3324_, lean_object* v_kinds_3325_, lean_object* v___x_3326_, lean_object* v_lhs_3327_, lean_object* v_heq_3328_, lean_object* v_type_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
uint8_t v___x_2001__boxed_3335_; uint8_t v___x_2002__boxed_3336_; lean_object* v_res_3337_; 
v___x_2001__boxed_3335_ = lean_unbox(v___x_3322_);
v___x_2002__boxed_3336_ = lean_unbox(v___x_3323_);
v_res_3337_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3320_, v_rhs_3321_, v___x_2001__boxed_3335_, v___x_2002__boxed_3336_, v_i_3324_, v_kinds_3325_, v___x_3326_, v_lhs_3327_, v_heq_3328_, v_type_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v_i_3324_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* v___x_3338_, uint8_t v___x_3339_, uint8_t v___x_3340_, lean_object* v_i_3341_, lean_object* v_kinds_3342_, lean_object* v___x_3343_, lean_object* v_lhs_3344_, lean_object* v_rhs_3345_, lean_object* v_type_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___f_3354_; lean_object* v___x_3355_; 
v___x_3352_ = lean_box(v___x_3339_);
v___x_3353_ = lean_box(v___x_3340_);
v___f_3354_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3354_, 0, v___x_3338_);
lean_closure_set(v___f_3354_, 1, v_rhs_3345_);
lean_closure_set(v___f_3354_, 2, v___x_3352_);
lean_closure_set(v___f_3354_, 3, v___x_3353_);
lean_closure_set(v___f_3354_, 4, v_i_3341_);
lean_closure_set(v___f_3354_, 5, v_kinds_3342_);
lean_closure_set(v___f_3354_, 6, v___x_3343_);
lean_closure_set(v___f_3354_, 7, v_lhs_3344_);
v___x_3355_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3346_, v___f_3354_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object* v_kinds_3356_, lean_object* v_i_3357_, lean_object* v_type_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3356_, v_i_3357_, v_type_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* v_type_3365_, lean_object* v_kinds_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = lean_unsigned_to_nat(0u);
v___x_3373_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3366_, v___x_3372_, v_type_3365_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object* v_type_3374_, lean_object* v_kinds_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3374_, v_kinds_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_msg_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___f_3388_; lean_object* v___x_2082__overap_3389_; lean_object* v___x_3390_; 
v___f_3388_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_2082__overap_3389_ = lean_panic_fn_borrowed(v___f_3388_, v_msg_3382_);
lean_inc(v___y_3386_);
lean_inc_ref(v___y_3385_);
lean_inc(v___y_3384_);
lean_inc_ref(v___y_3383_);
v___x_3390_ = lean_apply_5(v___x_2082__overap_3389_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, lean_box(0));
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_msg_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_msg_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(lean_object* v_bs_3398_, lean_object* v_k_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3398_, v_k_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
v_a_3414_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3405_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3405_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg___boxed(lean_object* v_bs_3422_, lean_object* v_k_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3422_, v_k_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec_ref(v_bs_3422_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(lean_object* v_00_u03b1_3430_, lean_object* v_bs_3431_, lean_object* v_k_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3431_, v_k_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3439_, lean_object* v_bs_3440_, lean_object* v_k_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(v_00_u03b1_3439_, v_bs_3440_, v_k_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_bs_3440_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(size_t v_sz_3448_, size_t v_i_3449_, lean_object* v_bs_3450_){
_start:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_usize_dec_lt(v_i_3449_, v_sz_3448_);
if (v___x_3451_ == 0)
{
return v_bs_3450_;
}
else
{
lean_object* v_v_3452_; lean_object* v___x_3453_; lean_object* v_bs_x27_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; size_t v___x_3459_; size_t v___x_3460_; lean_object* v___x_3461_; 
v_v_3452_ = lean_array_uget(v_bs_3450_, v_i_3449_);
v___x_3453_ = lean_unsigned_to_nat(0u);
v_bs_x27_3454_ = lean_array_uset(v_bs_3450_, v_i_3449_, v___x_3453_);
v___x_3455_ = l_Lean_Expr_fvarId_x21(v_v_3452_);
lean_dec(v_v_3452_);
v___x_3456_ = 1;
v___x_3457_ = lean_box(v___x_3456_);
v___x_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3455_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = ((size_t)1ULL);
v___x_3460_ = lean_usize_add(v_i_3449_, v___x_3459_);
v___x_3461_ = lean_array_uset(v_bs_x27_3454_, v_i_3449_, v___x_3458_);
v_i_3449_ = v___x_3460_;
v_bs_3450_ = v___x_3461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0___boxed(lean_object* v_sz_3463_, lean_object* v_i_3464_, lean_object* v_bs_3465_){
_start:
{
size_t v_sz_boxed_3466_; size_t v_i_boxed_3467_; lean_object* v_res_3468_; 
v_sz_boxed_3466_ = lean_unbox_usize(v_sz_3463_);
lean_dec(v_sz_3463_);
v_i_boxed_3467_ = lean_unbox_usize(v_i_3464_);
lean_dec(v_i_3464_);
v_res_3468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_boxed_3466_, v_i_boxed_3467_, v_bs_3465_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(lean_object* v_bs_3469_, lean_object* v_k_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
size_t v_sz_3476_; size_t v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v_sz_3476_ = lean_array_size(v_bs_3469_);
v___x_3477_ = ((size_t)0ULL);
v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_3476_, v___x_3477_, v_bs_3469_);
v___x_3479_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v___x_3478_, v_k_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec_ref(v___x_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg___boxed(lean_object* v_bs_3480_, lean_object* v_k_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3480_, v_k_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_00_u03b1_3488_, lean_object* v_bs_3489_, lean_object* v_k_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3489_, v_k_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3497_, lean_object* v_bs_3498_, lean_object* v_k_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_00_u03b1_3497_, v_bs_3498_, v_k_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3506_, lean_object* v_rhss_3507_, lean_object* v_lhs_3508_, lean_object* v_eqs_3509_, lean_object* v_hyps_3510_, uint8_t v_subsingletonInstImplicitRhs_3511_, lean_object* v_f_3512_, lean_object* v_info_3513_, lean_object* v_kinds_3514_, lean_object* v_lhss_3515_, lean_object* v_b_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3522_ = lean_unsigned_to_nat(1u);
v___x_3523_ = lean_nat_add(v_i_3506_, v___x_3522_);
lean_inc_ref(v_b_3516_);
v___x_3524_ = lean_array_push(v_rhss_3507_, v_b_3516_);
v___x_3525_ = l_Lean_Expr_fvarId_x21(v_lhs_3508_);
v___x_3526_ = l_Lean_Expr_fvarId_x21(v_b_3516_);
v___x_3527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
v___x_3529_ = lean_array_push(v_eqs_3509_, v___x_3528_);
v___x_3530_ = lean_array_push(v_hyps_3510_, v_b_3516_);
v___x_3531_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3511_, v_f_3512_, v_info_3513_, v_kinds_3514_, v_lhss_3515_, v___x_3523_, v___x_3524_, v___x_3529_, v___x_3530_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3532_, lean_object* v_rhss_3533_, lean_object* v_lhs_3534_, lean_object* v_eqs_3535_, lean_object* v_hyps_3536_, lean_object* v_subsingletonInstImplicitRhs_3537_, lean_object* v_f_3538_, lean_object* v_info_3539_, lean_object* v_kinds_3540_, lean_object* v_lhss_3541_, lean_object* v_b_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3548_; lean_object* v_res_3549_; 
v_subsingletonInstImplicitRhs_boxed_3548_ = lean_unbox(v_subsingletonInstImplicitRhs_3537_);
v_res_3549_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3532_, v_rhss_3533_, v_lhs_3534_, v_eqs_3535_, v_hyps_3536_, v_subsingletonInstImplicitRhs_boxed_3548_, v_f_3538_, v_info_3539_, v_kinds_3540_, v_lhss_3541_, v_b_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec_ref(v_lhs_3534_);
lean_dec(v_i_3532_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3550_, lean_object* v_rhss_3551_, lean_object* v_lhs_3552_, lean_object* v_eqs_3553_, lean_object* v_hyps_3554_, uint8_t v_subsingletonInstImplicitRhs_3555_, lean_object* v_f_3556_, lean_object* v_info_3557_, lean_object* v_kinds_3558_, lean_object* v_lhss_3559_, lean_object* v_name_3560_, uint8_t v_bi_3561_, lean_object* v_type_3562_, uint8_t v_kind_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v___x_3569_; lean_object* v___f_3570_; lean_object* v___x_3571_; 
v___x_3569_ = lean_box(v_subsingletonInstImplicitRhs_3555_);
v___f_3570_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3570_, 0, v_i_3550_);
lean_closure_set(v___f_3570_, 1, v_rhss_3551_);
lean_closure_set(v___f_3570_, 2, v_lhs_3552_);
lean_closure_set(v___f_3570_, 3, v_eqs_3553_);
lean_closure_set(v___f_3570_, 4, v_hyps_3554_);
lean_closure_set(v___f_3570_, 5, v___x_3569_);
lean_closure_set(v___f_3570_, 6, v_f_3556_);
lean_closure_set(v___f_3570_, 7, v_info_3557_);
lean_closure_set(v___f_3570_, 8, v_kinds_3558_);
lean_closure_set(v___f_3570_, 9, v_lhss_3559_);
v___x_3571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3560_, v_bi_3561_, v_type_3562_, v___f_3570_, v_kind_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
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
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
v_a_3580_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3571_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3571_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3588_, lean_object* v_rhss_3589_, lean_object* v_lhss_3590_, lean_object* v_i_3591_, lean_object* v_eqs_3592_, lean_object* v_hyps_3593_, uint8_t v_subsingletonInstImplicitRhs_3594_, lean_object* v_f_3595_, lean_object* v_info_3596_, lean_object* v_kinds_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
lean_inc(v___y_3601_);
lean_inc_ref(v___y_3600_);
lean_inc(v___y_3599_);
lean_inc_ref(v___y_3598_);
lean_inc_ref(v_lhs_3588_);
v___x_3603_ = lean_infer_type(v_lhs_3588_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___y_3611_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
v___x_3605_ = lean_array_get_size(v_rhss_3589_);
v___x_3606_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3590_);
v___x_3607_ = l_Array_toSubarray___redArg(v_lhss_3590_, v___x_3606_, v___x_3605_);
v___x_3608_ = l_Subarray_copy___redArg(v___x_3607_);
v___x_3609_ = l_Lean_Expr_replaceFVars(v_a_3604_, v___x_3608_, v_rhss_3589_);
lean_dec_ref(v___x_3608_);
lean_dec(v_a_3604_);
if (v_subsingletonInstImplicitRhs_3594_ == 0)
{
uint8_t v___x_3626_; 
v___x_3626_ = 1;
v___y_3611_ = v___x_3626_;
goto v___jp_3610_;
}
else
{
uint8_t v___x_3627_; 
v___x_3627_ = 3;
v___y_3611_ = v___x_3627_;
goto v___jp_3610_;
}
v___jp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = l_Lean_Expr_fvarId_x21(v_lhs_3588_);
v___x_3613_ = l_Lean_FVarId_getDecl___redArg(v___x_3612_, v___y_3598_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; lean_object* v___x_3617_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v___x_3615_ = l_Lean_LocalDecl_userName(v_a_3614_);
lean_dec(v_a_3614_);
v___x_3616_ = 0;
v___x_3617_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3591_, v_rhss_3589_, v_lhs_3588_, v_eqs_3592_, v_hyps_3593_, v_subsingletonInstImplicitRhs_3594_, v_f_3595_, v_info_3596_, v_kinds_3597_, v_lhss_3590_, v___x_3615_, v___y_3611_, v___x_3609_, v___x_3616_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v___x_3617_;
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v___x_3609_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v_kinds_3597_);
lean_dec_ref(v_info_3596_);
lean_dec_ref(v_f_3595_);
lean_dec_ref(v_hyps_3593_);
lean_dec_ref(v_eqs_3592_);
lean_dec(v_i_3591_);
lean_dec_ref(v_lhss_3590_);
lean_dec_ref(v_rhss_3589_);
lean_dec_ref(v_lhs_3588_);
v_a_3618_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3613_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3613_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v_kinds_3597_);
lean_dec_ref(v_info_3596_);
lean_dec_ref(v_f_3595_);
lean_dec_ref(v_hyps_3593_);
lean_dec_ref(v_eqs_3592_);
lean_dec(v_i_3591_);
lean_dec_ref(v_lhss_3590_);
lean_dec_ref(v_rhss_3589_);
lean_dec_ref(v_lhs_3588_);
v_a_3628_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3603_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3603_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3636_, lean_object* v_rhss_3637_, lean_object* v_lhss_3638_, lean_object* v_i_3639_, lean_object* v_eqs_3640_, lean_object* v_hyps_3641_, lean_object* v_subsingletonInstImplicitRhs_3642_, lean_object* v_f_3643_, lean_object* v_info_3644_, lean_object* v_kinds_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3651_; lean_object* v_res_3652_; 
v_subsingletonInstImplicitRhs_boxed_3651_ = lean_unbox(v_subsingletonInstImplicitRhs_3642_);
v_res_3652_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3636_, v_rhss_3637_, v_lhss_3638_, v_i_3639_, v_eqs_3640_, v_hyps_3641_, v_subsingletonInstImplicitRhs_boxed_3651_, v_f_3643_, v_info_3644_, v_kinds_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
return v_res_3652_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3654_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3655_ = lean_unsigned_to_nat(38u);
v___x_3656_ = lean_unsigned_to_nat(328u);
v___x_3657_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3658_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3659_ = l_mkPanicMessageWithDecl(v___x_3658_, v___x_3657_, v___x_3656_, v___x_3655_, v___x_3654_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3660_, lean_object* v_f_3661_, lean_object* v_info_3662_, lean_object* v_kinds_3663_, lean_object* v_lhss_3664_, lean_object* v_i_3665_, lean_object* v_rhss_3666_, lean_object* v_eqs_3667_, lean_object* v_hyps_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v___x_3674_; uint8_t v___x_3675_; 
v___x_3674_ = lean_array_get_size(v_kinds_3663_);
v___x_3675_ = lean_nat_dec_eq(v_i_3665_, v___x_3674_);
if (v___x_3675_ == 0)
{
lean_object* v___x_3676_; lean_object* v_lhs_3677_; lean_object* v_hyps_3678_; uint8_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v___x_3676_ = l_Lean_instInhabitedExpr;
v_lhs_3677_ = lean_array_get_borrowed(v___x_3676_, v_lhss_3664_, v_i_3665_);
lean_inc(v_lhs_3677_);
v_hyps_3678_ = lean_array_push(v_hyps_3668_, v_lhs_3677_);
v___x_3679_ = 0;
v___x_3680_ = lean_box(v___x_3679_);
v___x_3681_ = lean_array_get(v___x_3680_, v_kinds_3663_, v_i_3665_);
lean_dec(v___x_3680_);
v___x_3682_ = lean_unbox(v___x_3681_);
lean_dec(v___x_3681_);
switch(v___x_3682_)
{
case 0:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3683_ = lean_unsigned_to_nat(1u);
v___x_3684_ = lean_nat_add(v_i_3665_, v___x_3683_);
lean_dec(v_i_3665_);
lean_inc(v_lhs_3677_);
v___x_3685_ = lean_array_push(v_rhss_3666_, v_lhs_3677_);
v___x_3686_ = lean_box(0);
v___x_3687_ = lean_array_push(v_eqs_3667_, v___x_3686_);
v_i_3665_ = v___x_3684_;
v_rhss_3666_ = v___x_3685_;
v_eqs_3667_ = v___x_3687_;
v_hyps_3668_ = v_hyps_3678_;
goto _start;
}
case 2:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_inc(v_lhs_3677_);
v___x_3689_ = l_Lean_Expr_fvarId_x21(v_lhs_3677_);
v___x_3690_ = l_Lean_FVarId_getDecl___redArg(v___x_3689_, v_a_3669_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; lean_object* v___x_3696_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
v___x_3692_ = l_Lean_LocalDecl_userName(v_a_3691_);
v___x_3693_ = l_Lean_LocalDecl_binderInfo(v_a_3691_);
v___x_3694_ = l_Lean_LocalDecl_type(v_a_3691_);
lean_dec(v_a_3691_);
v___x_3695_ = 0;
lean_inc(v___x_3692_);
v___x_3696_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3665_, v_rhss_3666_, v_eqs_3667_, v_hyps_3678_, v_subsingletonInstImplicitRhs_3660_, v_f_3661_, v_info_3662_, v_kinds_3663_, v_lhss_3664_, v_lhs_3677_, v___x_3692_, v___x_3692_, v___x_3693_, v___x_3694_, v___x_3695_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3696_;
}
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_dec_ref(v_hyps_3678_);
lean_dec(v_lhs_3677_);
lean_dec_ref(v_eqs_3667_);
lean_dec_ref(v_rhss_3666_);
lean_dec(v_i_3665_);
lean_dec_ref(v_lhss_3664_);
lean_dec_ref(v_kinds_3663_);
lean_dec_ref(v_info_3662_);
lean_dec_ref(v_f_3661_);
v_a_3697_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3690_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3690_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
case 3:
{
lean_object* v___x_3705_; 
lean_inc(v_a_3672_);
lean_inc_ref(v_a_3671_);
lean_inc(v_a_3670_);
lean_inc_ref(v_a_3669_);
lean_inc(v_lhs_3677_);
v___x_3705_ = lean_infer_type(v_lhs_3677_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v_paramInfo_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v_backDeps_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3705_, 1);
v_paramInfo_3707_ = lean_ctor_get(v_info_3662_, 0);
v___x_3708_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_3709_ = lean_array_get_borrowed(v___x_3708_, v_paramInfo_3707_, v_i_3665_);
v_backDeps_3710_ = lean_ctor_get(v___x_3709_, 0);
v___x_3711_ = lean_array_get_size(v_rhss_3666_);
v___x_3712_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3664_);
v___x_3713_ = l_Array_toSubarray___redArg(v_lhss_3664_, v___x_3712_, v___x_3711_);
v___x_3714_ = l_Subarray_copy___redArg(v___x_3713_);
v___x_3715_ = l_Lean_Expr_replaceFVars(v_a_3706_, v___x_3714_, v_rhss_3666_);
lean_dec_ref(v___x_3714_);
lean_dec(v_a_3706_);
v___x_3716_ = l_Lean_Expr_fvarId_x21(v_lhs_3677_);
v___x_3717_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3716_, v___x_3715_, v_backDeps_3710_, v_eqs_3667_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = lean_unsigned_to_nat(1u);
v___x_3720_ = lean_nat_add(v_i_3665_, v___x_3719_);
lean_dec(v_i_3665_);
v___x_3721_ = lean_array_push(v_rhss_3666_, v_a_3718_);
v___x_3722_ = lean_box(0);
v___x_3723_ = lean_array_push(v_eqs_3667_, v___x_3722_);
v_i_3665_ = v___x_3720_;
v_rhss_3666_ = v___x_3721_;
v_eqs_3667_ = v___x_3723_;
v_hyps_3668_ = v_hyps_3678_;
goto _start;
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec_ref(v_hyps_3678_);
lean_dec_ref(v_eqs_3667_);
lean_dec_ref(v_rhss_3666_);
lean_dec(v_i_3665_);
lean_dec_ref(v_lhss_3664_);
lean_dec_ref(v_kinds_3663_);
lean_dec_ref(v_info_3662_);
lean_dec_ref(v_f_3661_);
v_a_3725_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3717_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3717_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v_hyps_3678_);
lean_dec_ref(v_eqs_3667_);
lean_dec_ref(v_rhss_3666_);
lean_dec(v_i_3665_);
lean_dec_ref(v_lhss_3664_);
lean_dec_ref(v_kinds_3663_);
lean_dec_ref(v_info_3662_);
lean_dec_ref(v_f_3661_);
v_a_3733_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3705_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3705_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
case 5:
{
lean_object* v___x_3741_; lean_object* v___f_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_inc_n(v_lhs_3677_, 2);
v___x_3741_ = lean_box(v_subsingletonInstImplicitRhs_3660_);
v___f_3742_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3742_, 0, v_lhs_3677_);
lean_closure_set(v___f_3742_, 1, v_rhss_3666_);
lean_closure_set(v___f_3742_, 2, v_lhss_3664_);
lean_closure_set(v___f_3742_, 3, v_i_3665_);
lean_closure_set(v___f_3742_, 4, v_eqs_3667_);
lean_closure_set(v___f_3742_, 5, v_hyps_3678_);
lean_closure_set(v___f_3742_, 6, v___x_3741_);
lean_closure_set(v___f_3742_, 7, v_f_3661_);
lean_closure_set(v___f_3742_, 8, v_info_3662_);
lean_closure_set(v___f_3742_, 9, v_kinds_3663_);
v___x_3743_ = lean_unsigned_to_nat(1u);
v___x_3744_ = lean_mk_empty_array_with_capacity(v___x_3743_);
v___x_3745_ = lean_array_push(v___x_3744_, v_lhs_3677_);
v___x_3746_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v___x_3745_, v___f_3742_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3746_;
}
default: 
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
lean_dec_ref(v_hyps_3678_);
lean_dec_ref(v_eqs_3667_);
lean_dec_ref(v_rhss_3666_);
lean_dec(v_i_3665_);
lean_dec_ref(v_lhss_3664_);
lean_dec_ref(v_kinds_3663_);
lean_dec_ref(v_info_3662_);
lean_dec_ref(v_f_3661_);
v___x_3747_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3748_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v___x_3747_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3748_;
}
}
}
else
{
lean_object* v_lhs_3749_; lean_object* v_rhs_3750_; lean_object* v___x_3751_; 
lean_dec_ref(v_eqs_3667_);
lean_dec(v_i_3665_);
lean_dec_ref(v_info_3662_);
lean_inc_ref(v_f_3661_);
v_lhs_3749_ = l_Lean_mkAppN(v_f_3661_, v_lhss_3664_);
lean_dec_ref(v_lhss_3664_);
v_rhs_3750_ = l_Lean_mkAppN(v_f_3661_, v_rhss_3666_);
lean_dec_ref(v_rhss_3666_);
v___x_3751_ = l_Lean_Meta_mkEq(v_lhs_3749_, v_rhs_3750_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; uint8_t v___x_3753_; uint8_t v___x_3754_; lean_object* v___x_3755_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3751_, 1);
v___x_3753_ = 0;
v___x_3754_ = 1;
v___x_3755_ = l_Lean_Meta_mkForallFVars(v_hyps_3668_, v_a_3752_, v___x_3753_, v___x_3675_, v___x_3675_, v___x_3754_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec_ref(v_hyps_3668_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3757_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc_n(v_a_3756_, 2);
lean_dec_ref_known(v___x_3755_, 1);
lean_inc_ref(v_kinds_3663_);
v___x_3757_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3756_, v_kinds_3663_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3766_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3760_ = v___x_3757_;
v_isShared_3761_ = v_isSharedCheck_3766_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3757_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3766_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3762_, 0, v_a_3756_);
lean_ctor_set(v___x_3762_, 1, v_a_3758_);
lean_ctor_set(v___x_3762_, 2, v_kinds_3663_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v___x_3762_);
v___x_3764_ = v___x_3760_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3756_);
lean_dec_ref(v_kinds_3663_);
v_a_3767_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3757_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3757_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v_kinds_3663_);
v_a_3775_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3755_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3755_);
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
lean_dec_ref(v_hyps_3668_);
lean_dec_ref(v_kinds_3663_);
v_a_3783_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3751_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3751_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3791_, lean_object* v_rhss_3792_, lean_object* v_b_3793_, lean_object* v_eqs_3794_, lean_object* v_hyps_3795_, uint8_t v_subsingletonInstImplicitRhs_3796_, lean_object* v_f_3797_, lean_object* v_info_3798_, lean_object* v_kinds_3799_, lean_object* v_lhss_3800_, lean_object* v_eq_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3807_ = lean_unsigned_to_nat(1u);
v___x_3808_ = lean_nat_add(v_i_3791_, v___x_3807_);
lean_inc_ref(v_b_3793_);
v___x_3809_ = lean_array_push(v_rhss_3792_, v_b_3793_);
v___x_3810_ = l_Lean_Expr_fvarId_x21(v_eq_3801_);
v___x_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
v___x_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
v___x_3813_ = lean_array_push(v_eqs_3794_, v___x_3812_);
v___x_3814_ = lean_array_push(v_hyps_3795_, v_b_3793_);
v___x_3815_ = lean_array_push(v___x_3814_, v_eq_3801_);
v___x_3816_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3796_, v_f_3797_, v_info_3798_, v_kinds_3799_, v_lhss_3800_, v___x_3808_, v___x_3809_, v___x_3813_, v___x_3815_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_3817_, lean_object* v_rhss_3818_, lean_object* v_b_3819_, lean_object* v_eqs_3820_, lean_object* v_hyps_3821_, lean_object* v_subsingletonInstImplicitRhs_3822_, lean_object* v_f_3823_, lean_object* v_info_3824_, lean_object* v_kinds_3825_, lean_object* v_lhss_3826_, lean_object* v_eq_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3833_; lean_object* v_res_3834_; 
v_subsingletonInstImplicitRhs_boxed_3833_ = lean_unbox(v_subsingletonInstImplicitRhs_3822_);
v_res_3834_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3817_, v_rhss_3818_, v_b_3819_, v_eqs_3820_, v_hyps_3821_, v_subsingletonInstImplicitRhs_boxed_3833_, v_f_3823_, v_info_3824_, v_kinds_3825_, v_lhss_3826_, v_eq_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v_i_3817_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(lean_object* v_lhs_3836_, lean_object* v_i_3837_, lean_object* v_rhss_3838_, lean_object* v_eqs_3839_, lean_object* v_hyps_3840_, uint8_t v_subsingletonInstImplicitRhs_3841_, lean_object* v_f_3842_, lean_object* v_info_3843_, lean_object* v_kinds_3844_, lean_object* v_lhss_3845_, lean_object* v___x_3846_, lean_object* v_b_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v___x_3853_; 
lean_inc_ref(v_b_3847_);
v___x_3853_ = l_Lean_Meta_mkEq(v_lhs_3836_, v_b_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; lean_object* v___f_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
v___x_3855_ = lean_box(v_subsingletonInstImplicitRhs_3841_);
v___f_3856_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3856_, 0, v_i_3837_);
lean_closure_set(v___f_3856_, 1, v_rhss_3838_);
lean_closure_set(v___f_3856_, 2, v_b_3847_);
lean_closure_set(v___f_3856_, 3, v_eqs_3839_);
lean_closure_set(v___f_3856_, 4, v_hyps_3840_);
lean_closure_set(v___f_3856_, 5, v___x_3855_);
lean_closure_set(v___f_3856_, 6, v_f_3842_);
lean_closure_set(v___f_3856_, 7, v_info_3843_);
lean_closure_set(v___f_3856_, 8, v_kinds_3844_);
lean_closure_set(v___f_3856_, 9, v_lhss_3845_);
v___x_3857_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0));
v___x_3858_ = lean_name_append_before(v___x_3846_, v___x_3857_);
v___x_3859_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3858_, v_a_3854_, v___f_3856_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
return v___x_3859_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v_b_3847_);
lean_dec(v___x_3846_);
lean_dec_ref(v_lhss_3845_);
lean_dec_ref(v_kinds_3844_);
lean_dec_ref(v_info_3843_);
lean_dec_ref(v_f_3842_);
lean_dec_ref(v_hyps_3840_);
lean_dec_ref(v_eqs_3839_);
lean_dec_ref(v_rhss_3838_);
lean_dec(v_i_3837_);
v_a_3860_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3853_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3853_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v_lhs_3868_ = _args[0];
lean_object* v_i_3869_ = _args[1];
lean_object* v_rhss_3870_ = _args[2];
lean_object* v_eqs_3871_ = _args[3];
lean_object* v_hyps_3872_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3873_ = _args[5];
lean_object* v_f_3874_ = _args[6];
lean_object* v_info_3875_ = _args[7];
lean_object* v_kinds_3876_ = _args[8];
lean_object* v_lhss_3877_ = _args[9];
lean_object* v___x_3878_ = _args[10];
lean_object* v_b_3879_ = _args[11];
lean_object* v___y_3880_ = _args[12];
lean_object* v___y_3881_ = _args[13];
lean_object* v___y_3882_ = _args[14];
lean_object* v___y_3883_ = _args[15];
lean_object* v___y_3884_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3885_; lean_object* v_res_3886_; 
v_subsingletonInstImplicitRhs_boxed_3885_ = lean_unbox(v_subsingletonInstImplicitRhs_3873_);
v_res_3886_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(v_lhs_3868_, v_i_3869_, v_rhss_3870_, v_eqs_3871_, v_hyps_3872_, v_subsingletonInstImplicitRhs_boxed_3885_, v_f_3874_, v_info_3875_, v_kinds_3876_, v_lhss_3877_, v___x_3878_, v_b_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_3887_, lean_object* v_rhss_3888_, lean_object* v_eqs_3889_, lean_object* v_hyps_3890_, uint8_t v_subsingletonInstImplicitRhs_3891_, lean_object* v_f_3892_, lean_object* v_info_3893_, lean_object* v_kinds_3894_, lean_object* v_lhss_3895_, lean_object* v_lhs_3896_, lean_object* v___x_3897_, lean_object* v_name_3898_, uint8_t v_bi_3899_, lean_object* v_type_3900_, uint8_t v_kind_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; lean_object* v___f_3908_; lean_object* v___x_3909_; 
v___x_3907_ = lean_box(v_subsingletonInstImplicitRhs_3891_);
v___f_3908_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3908_, 0, v_lhs_3896_);
lean_closure_set(v___f_3908_, 1, v_i_3887_);
lean_closure_set(v___f_3908_, 2, v_rhss_3888_);
lean_closure_set(v___f_3908_, 3, v_eqs_3889_);
lean_closure_set(v___f_3908_, 4, v_hyps_3890_);
lean_closure_set(v___f_3908_, 5, v___x_3907_);
lean_closure_set(v___f_3908_, 6, v_f_3892_);
lean_closure_set(v___f_3908_, 7, v_info_3893_);
lean_closure_set(v___f_3908_, 8, v_kinds_3894_);
lean_closure_set(v___f_3908_, 9, v_lhss_3895_);
lean_closure_set(v___f_3908_, 10, v___x_3897_);
v___x_3909_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3898_, v_bi_3899_, v_type_3900_, v___f_3908_, v_kind_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3909_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3909_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
v_a_3918_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3909_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3909_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object** _args){
lean_object* v_i_3926_ = _args[0];
lean_object* v_rhss_3927_ = _args[1];
lean_object* v_eqs_3928_ = _args[2];
lean_object* v_hyps_3929_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3930_ = _args[4];
lean_object* v_f_3931_ = _args[5];
lean_object* v_info_3932_ = _args[6];
lean_object* v_kinds_3933_ = _args[7];
lean_object* v_lhss_3934_ = _args[8];
lean_object* v_lhs_3935_ = _args[9];
lean_object* v___x_3936_ = _args[10];
lean_object* v_name_3937_ = _args[11];
lean_object* v_bi_3938_ = _args[12];
lean_object* v_type_3939_ = _args[13];
lean_object* v_kind_3940_ = _args[14];
lean_object* v___y_3941_ = _args[15];
lean_object* v___y_3942_ = _args[16];
lean_object* v___y_3943_ = _args[17];
lean_object* v___y_3944_ = _args[18];
lean_object* v___y_3945_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3946_; uint8_t v_bi_boxed_3947_; uint8_t v_kind_boxed_3948_; lean_object* v_res_3949_; 
v_subsingletonInstImplicitRhs_boxed_3946_ = lean_unbox(v_subsingletonInstImplicitRhs_3930_);
v_bi_boxed_3947_ = lean_unbox(v_bi_3938_);
v_kind_boxed_3948_ = lean_unbox(v_kind_3940_);
v_res_3949_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3926_, v_rhss_3927_, v_eqs_3928_, v_hyps_3929_, v_subsingletonInstImplicitRhs_boxed_3946_, v_f_3931_, v_info_3932_, v_kinds_3933_, v_lhss_3934_, v_lhs_3935_, v___x_3936_, v_name_3937_, v_bi_boxed_3947_, v_type_3939_, v_kind_boxed_3948_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_3950_ = _args[0];
lean_object* v_rhss_3951_ = _args[1];
lean_object* v_lhs_3952_ = _args[2];
lean_object* v_eqs_3953_ = _args[3];
lean_object* v_hyps_3954_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3955_ = _args[5];
lean_object* v_f_3956_ = _args[6];
lean_object* v_info_3957_ = _args[7];
lean_object* v_kinds_3958_ = _args[8];
lean_object* v_lhss_3959_ = _args[9];
lean_object* v_name_3960_ = _args[10];
lean_object* v_bi_3961_ = _args[11];
lean_object* v_type_3962_ = _args[12];
lean_object* v_kind_3963_ = _args[13];
lean_object* v___y_3964_ = _args[14];
lean_object* v___y_3965_ = _args[15];
lean_object* v___y_3966_ = _args[16];
lean_object* v___y_3967_ = _args[17];
lean_object* v___y_3968_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3969_; uint8_t v_bi_boxed_3970_; uint8_t v_kind_boxed_3971_; lean_object* v_res_3972_; 
v_subsingletonInstImplicitRhs_boxed_3969_ = lean_unbox(v_subsingletonInstImplicitRhs_3955_);
v_bi_boxed_3970_ = lean_unbox(v_bi_3961_);
v_kind_boxed_3971_ = lean_unbox(v_kind_3963_);
v_res_3972_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3950_, v_rhss_3951_, v_lhs_3952_, v_eqs_3953_, v_hyps_3954_, v_subsingletonInstImplicitRhs_boxed_3969_, v_f_3956_, v_info_3957_, v_kinds_3958_, v_lhss_3959_, v_name_3960_, v_bi_boxed_3970_, v_type_3962_, v_kind_boxed_3971_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* v_subsingletonInstImplicitRhs_3973_, lean_object* v_f_3974_, lean_object* v_info_3975_, lean_object* v_kinds_3976_, lean_object* v_lhss_3977_, lean_object* v_i_3978_, lean_object* v_rhss_3979_, lean_object* v_eqs_3980_, lean_object* v_hyps_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3987_; lean_object* v_res_3988_; 
v_subsingletonInstImplicitRhs_boxed_3987_ = lean_unbox(v_subsingletonInstImplicitRhs_3973_);
v_res_3988_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_boxed_3987_, v_f_3974_, v_info_3975_, v_kinds_3976_, v_lhss_3977_, v_i_3978_, v_rhss_3979_, v_eqs_3980_, v_hyps_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* v___x_3989_, uint8_t v_subsingletonInstImplicitRhs_3990_, lean_object* v_f_3991_, lean_object* v_info_3992_, lean_object* v_kinds_3993_, lean_object* v_lhss_3994_, lean_object* v_x_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_4001_ = lean_array_get_size(v_lhss_3994_);
v___x_4002_ = lean_nat_dec_eq(v___x_4001_, v___x_3989_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
lean_dec_ref(v_lhss_3994_);
lean_dec_ref(v_kinds_3993_);
lean_dec_ref(v_info_3992_);
lean_dec_ref(v_f_3991_);
v___x_4003_ = lean_box(0);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
return v___x_4004_;
}
else
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = lean_unsigned_to_nat(0u);
v___x_4006_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_4007_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3990_, v_f_3991_, v_info_3992_, v_kinds_3993_, v_lhss_3994_, v___x_4005_, v___x_4006_, v___x_4006_, v___x_4006_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4016_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4010_ = v___x_4007_;
v_isShared_4011_ = v_isSharedCheck_4016_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4007_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4016_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_a_4008_);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 0, v___x_4012_);
v___x_4014_ = v___x_4010_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
v_a_4017_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4007_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4007_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* v___x_4025_, lean_object* v_subsingletonInstImplicitRhs_4026_, lean_object* v_f_4027_, lean_object* v_info_4028_, lean_object* v_kinds_4029_, lean_object* v_lhss_4030_, lean_object* v_x_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4037_; lean_object* v_res_4038_; 
v_subsingletonInstImplicitRhs_boxed_4037_ = lean_unbox(v_subsingletonInstImplicitRhs_4026_);
v_res_4038_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4025_, v_subsingletonInstImplicitRhs_boxed_4037_, v_f_4027_, v_info_4028_, v_kinds_4029_, v_lhss_4030_, v_x_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec_ref(v_x_4031_);
lean_dec(v___x_4025_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t v_subsingletonInstImplicitRhs_4039_, lean_object* v_f_4040_, lean_object* v_info_4041_, lean_object* v_kinds_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v___y_4049_; uint8_t v___y_4050_; lean_object* v_a_4055_; lean_object* v___x_4058_; 
lean_inc(v_a_4046_);
lean_inc_ref(v_a_4045_);
lean_inc(v_a_4044_);
lean_inc_ref(v_a_4043_);
lean_inc_ref(v_f_4040_);
v___x_4058_ = lean_infer_type(v_f_4040_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4073_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4061_ = v___x_4058_;
v_isShared_4062_ = v_isSharedCheck_4073_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4058_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4073_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___f_4065_; lean_object* v___x_4067_; 
v___x_4063_ = lean_array_get_size(v_kinds_4042_);
v___x_4064_ = lean_box(v_subsingletonInstImplicitRhs_4039_);
v___f_4065_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4065_, 0, v___x_4063_);
lean_closure_set(v___f_4065_, 1, v___x_4064_);
lean_closure_set(v___f_4065_, 2, v_f_4040_);
lean_closure_set(v___f_4065_, 3, v_info_4041_);
lean_closure_set(v___f_4065_, 4, v_kinds_4042_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set_tag(v___x_4061_, 1);
lean_ctor_set(v___x_4061_, 0, v___x_4063_);
v___x_4067_ = v___x_4061_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4063_);
v___x_4067_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
uint8_t v___x_4068_; uint8_t v___x_4069_; lean_object* v___x_4070_; 
v___x_4068_ = 1;
v___x_4069_ = 0;
v___x_4070_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_4059_, v___x_4067_, v___f_4065_, v___x_4068_, v___x_4069_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
if (lean_obj_tag(v___x_4070_) == 0)
{
return v___x_4070_;
}
else
{
lean_object* v_a_4071_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v_a_4055_ = v_a_4071_;
goto v___jp_4054_;
}
}
}
}
else
{
lean_object* v_a_4074_; 
lean_dec_ref(v_kinds_4042_);
lean_dec_ref(v_info_4041_);
lean_dec_ref(v_f_4040_);
v_a_4074_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4058_, 1);
v_a_4055_ = v_a_4074_;
goto v___jp_4054_;
}
v___jp_4048_:
{
if (v___y_4050_ == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_dec_ref(v___y_4049_);
v___x_4051_ = lean_box(0);
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
else
{
lean_object* v___x_4053_; 
v___x_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___y_4049_);
return v___x_4053_;
}
}
v___jp_4054_:
{
uint8_t v___x_4056_; 
v___x_4056_ = l_Lean_Exception_isInterrupt(v_a_4055_);
if (v___x_4056_ == 0)
{
uint8_t v___x_4057_; 
lean_inc_ref(v_a_4055_);
v___x_4057_ = l_Lean_Exception_isRuntime(v_a_4055_);
v___y_4049_ = v_a_4055_;
v___y_4050_ = v___x_4057_;
goto v___jp_4048_;
}
else
{
v___y_4049_ = v_a_4055_;
v___y_4050_ = v___x_4056_;
goto v___jp_4048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* v_subsingletonInstImplicitRhs_4075_, lean_object* v_f_4076_, lean_object* v_info_4077_, lean_object* v_kinds_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4084_; lean_object* v_res_4085_; 
v_subsingletonInstImplicitRhs_boxed_4084_ = lean_unbox(v_subsingletonInstImplicitRhs_4075_);
v_res_4085_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_boxed_4084_, v_f_4076_, v_info_4077_, v_kinds_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t v_sz_4086_, size_t v_i_4087_, lean_object* v_bs_4088_){
_start:
{
uint8_t v___x_4089_; 
v___x_4089_ = lean_usize_dec_lt(v_i_4087_, v_sz_4086_);
if (v___x_4089_ == 0)
{
return v_bs_4088_;
}
else
{
lean_object* v_v_4090_; lean_object* v___x_4091_; lean_object* v_bs_x27_4092_; uint8_t v___y_4094_; uint8_t v___x_4100_; 
v_v_4090_ = lean_array_uget(v_bs_4088_, v_i_4087_);
v___x_4091_ = lean_unsigned_to_nat(0u);
v_bs_x27_4092_ = lean_array_uset(v_bs_4088_, v_i_4087_, v___x_4091_);
v___x_4100_ = lean_unbox(v_v_4090_);
switch(v___x_4100_)
{
case 3:
{
uint8_t v___x_4101_; 
lean_dec(v_v_4090_);
v___x_4101_ = 0;
v___y_4094_ = v___x_4101_;
goto v___jp_4093_;
}
case 5:
{
uint8_t v___x_4102_; 
lean_dec(v_v_4090_);
v___x_4102_ = 0;
v___y_4094_ = v___x_4102_;
goto v___jp_4093_;
}
default: 
{
uint8_t v___x_4103_; 
v___x_4103_ = lean_unbox(v_v_4090_);
lean_dec(v_v_4090_);
v___y_4094_ = v___x_4103_;
goto v___jp_4093_;
}
}
v___jp_4093_:
{
size_t v___x_4095_; size_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4095_ = ((size_t)1ULL);
v___x_4096_ = lean_usize_add(v_i_4087_, v___x_4095_);
v___x_4097_ = lean_box(v___y_4094_);
v___x_4098_ = lean_array_uset(v_bs_x27_4092_, v_i_4087_, v___x_4097_);
v_i_4087_ = v___x_4096_;
v_bs_4088_ = v___x_4098_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* v_sz_4104_, lean_object* v_i_4105_, lean_object* v_bs_4106_){
_start:
{
size_t v_sz_boxed_4107_; size_t v_i_boxed_4108_; lean_object* v_res_4109_; 
v_sz_boxed_4107_ = lean_unbox_usize(v_sz_4104_);
lean_dec(v_sz_4104_);
v_i_boxed_4108_ = lean_unbox_usize(v_i_4105_);
lean_dec(v_i_4105_);
v_res_4109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_4107_, v_i_boxed_4108_, v_bs_4106_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* v_f_4110_, lean_object* v_info_4111_, lean_object* v_kinds_4112_, uint8_t v_subsingletonInstImplicitRhs_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v___x_4119_; 
lean_inc_ref(v_kinds_4112_);
lean_inc_ref(v_info_4111_);
lean_inc_ref(v_f_4110_);
v___x_4119_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4113_, v_f_4110_, v_info_4111_, v_kinds_4112_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
if (lean_obj_tag(v_a_4120_) == 1)
{
lean_dec_ref_known(v_a_4120_, 1);
lean_dec_ref(v_kinds_4112_);
lean_dec_ref(v_info_4111_);
lean_dec_ref(v_f_4110_);
return v___x_4119_;
}
else
{
lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4133_; 
lean_dec(v_a_4120_);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4133_ == 0)
{
lean_object* v_unused_4134_; 
v_unused_4134_ = lean_ctor_get(v___x_4119_, 0);
lean_dec(v_unused_4134_);
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4133_;
goto v_resetjp_4121_;
}
else
{
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4133_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
uint8_t v___x_4124_; 
v___x_4124_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_4112_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; lean_object* v___x_4127_; 
lean_dec_ref(v_kinds_4112_);
lean_dec_ref(v_info_4111_);
lean_dec_ref(v_f_4110_);
v___x_4125_ = lean_box(0);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v___x_4125_);
v___x_4127_ = v___x_4122_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
else
{
size_t v_sz_4129_; size_t v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_del_object(v___x_4122_);
v_sz_4129_ = lean_array_size(v_kinds_4112_);
v___x_4130_ = ((size_t)0ULL);
v___x_4131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4129_, v___x_4130_, v_kinds_4112_);
v___x_4132_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4113_, v_f_4110_, v_info_4111_, v___x_4131_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4132_;
}
}
}
}
else
{
lean_dec_ref(v_kinds_4112_);
lean_dec_ref(v_info_4111_);
lean_dec_ref(v_f_4110_);
return v___x_4119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* v_f_4135_, lean_object* v_info_4136_, lean_object* v_kinds_4137_, lean_object* v_subsingletonInstImplicitRhs_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4144_; lean_object* v_res_4145_; 
v_subsingletonInstImplicitRhs_boxed_4144_ = lean_unbox(v_subsingletonInstImplicitRhs_4138_);
v_res_4145_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4135_, v_info_4136_, v_kinds_4137_, v_subsingletonInstImplicitRhs_boxed_4144_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* v_f_4146_, uint8_t v_subsingletonInstImplicitRhs_4147_, lean_object* v_maxArgs_x3f_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___x_4154_; lean_object* v_a_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4154_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_4146_, v_a_4150_);
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref(v___x_4154_);
v___x_4156_ = l_Lean_Expr_cleanupAnnotations(v_a_4155_);
lean_inc_ref(v___x_4156_);
v___x_4157_ = l_Lean_Meta_getFunInfo(v___x_4156_, v_maxArgs_x3f_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4159_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
lean_inc_ref(v___x_4156_);
v___x_4159_ = l_Lean_Meta_getCongrSimpKinds(v___x_4156_, v_a_4158_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4156_, v_a_4158_, v_a_4160_, v_subsingletonInstImplicitRhs_4147_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
return v___x_4161_;
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec(v_a_4158_);
lean_dec_ref(v___x_4156_);
v_a_4162_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4159_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4159_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v___x_4156_);
v_a_4170_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4157_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4157_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* v_f_4178_, lean_object* v_subsingletonInstImplicitRhs_4179_, lean_object* v_maxArgs_x3f_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4186_; lean_object* v_res_4187_; 
v_subsingletonInstImplicitRhs_boxed_4186_ = lean_unbox(v_subsingletonInstImplicitRhs_4179_);
v_res_4187_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4178_, v_subsingletonInstImplicitRhs_boxed_4186_, v_maxArgs_x3f_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
return v_res_4187_;
}
}
static lean_object* _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4193_ = lean_string_utf8_byte_size(v___x_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4194_){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4195_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4196_ = lean_string_utf8_byte_size(v_s_4194_);
v___x_4197_ = lean_obj_once(&l_Lean_Meta_isHCongrReservedNameSuffix___closed__0, &l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0);
v___x_4198_ = lean_nat_dec_le(v___x_4197_, v___x_4196_);
if (v___x_4198_ == 0)
{
lean_dec_ref(v_s_4194_);
return v___x_4198_;
}
else
{
lean_object* v___x_4199_; uint8_t v___x_4200_; 
v___x_4199_ = lean_unsigned_to_nat(0u);
v___x_4200_ = lean_string_memcmp(v_s_4194_, v___x_4195_, v___x_4199_, v___x_4199_, v___x_4197_);
if (v___x_4200_ == 0)
{
lean_dec_ref(v_s_4194_);
return v___x_4200_;
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_4201_ = lean_unsigned_to_nat(7u);
lean_inc_ref(v_s_4194_);
v___x_4202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4202_, 0, v_s_4194_);
lean_ctor_set(v___x_4202_, 1, v___x_4199_);
lean_ctor_set(v___x_4202_, 2, v___x_4196_);
v___x_4203_ = l_String_Slice_Pos_nextn(v___x_4202_, v___x_4199_, v___x_4201_);
lean_dec_ref_known(v___x_4202_, 3);
v___x_4204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4204_, 0, v_s_4194_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
lean_ctor_set(v___x_4204_, 2, v___x_4196_);
v___x_4205_ = l_String_Slice_isNat(v___x_4204_);
lean_dec_ref_known(v___x_4204_, 3);
return v___x_4205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* v_s_4206_){
_start:
{
uint8_t v_res_4207_; lean_object* v_r_4208_; 
v_res_4207_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4206_);
v_r_4208_ = lean_box(v_res_4207_);
return v_r_4208_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4258_ = lean_unsigned_to_nat(3482611248u);
v___x_4259_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4260_ = l_Lean_Name_num___override(v___x_4259_, v___x_4258_);
return v___x_4260_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4262_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4263_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4264_ = l_Lean_Name_str___override(v___x_4263_, v___x_4262_);
return v___x_4264_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4266_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4267_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4268_ = l_Lean_Name_str___override(v___x_4267_, v___x_4266_);
return v___x_4268_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4269_ = lean_unsigned_to_nat(2u);
v___x_4270_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4271_ = l_Lean_Name_num___override(v___x_4270_, v___x_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4273_; uint8_t v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4273_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4274_ = 0;
v___x_4275_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4276_ = l_Lean_registerTraceClass(v___x_4273_, v___x_4274_, v___x_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object* v_a_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4279_, lean_object* v_as_4280_, size_t v_i_4281_, size_t v_stop_4282_, lean_object* v_b_4283_){
_start:
{
lean_object* v___y_4285_; uint8_t v___x_4289_; 
v___x_4289_ = lean_usize_dec_eq(v_i_4281_, v_stop_4282_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v_fst_4291_; uint8_t v___x_4292_; 
v___x_4290_ = lean_array_uget_borrowed(v_as_4280_, v_i_4281_);
v_fst_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_fst_4291_);
lean_inc_ref(v_env_4279_);
v___x_4292_ = l_Lean_Environment_contains(v_env_4279_, v_fst_4291_, v___x_4289_);
if (v___x_4292_ == 0)
{
v___y_4285_ = v_b_4283_;
goto v___jp_4284_;
}
else
{
lean_object* v___x_4293_; 
lean_inc(v___x_4290_);
v___x_4293_ = lean_array_push(v_b_4283_, v___x_4290_);
v___y_4285_ = v___x_4293_;
goto v___jp_4284_;
}
}
else
{
lean_dec_ref(v_env_4279_);
return v_b_4283_;
}
v___jp_4284_:
{
size_t v___x_4286_; size_t v___x_4287_; 
v___x_4286_ = ((size_t)1ULL);
v___x_4287_ = lean_usize_add(v_i_4281_, v___x_4286_);
v_i_4281_ = v___x_4287_;
v_b_4283_ = v___y_4285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4294_, lean_object* v_as_4295_, lean_object* v_i_4296_, lean_object* v_stop_4297_, lean_object* v_b_4298_){
_start:
{
size_t v_i_boxed_4299_; size_t v_stop_boxed_4300_; lean_object* v_res_4301_; 
v_i_boxed_4299_ = lean_unbox_usize(v_i_4296_);
lean_dec(v_i_4296_);
v_stop_boxed_4300_ = lean_unbox_usize(v_stop_4297_);
lean_dec(v_stop_4297_);
v_res_4301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4294_, v_as_4295_, v_i_boxed_4299_, v_stop_boxed_4300_, v_b_4298_);
lean_dec_ref(v_as_4295_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4302_, lean_object* v_x_4303_){
_start:
{
if (lean_obj_tag(v_x_4303_) == 0)
{
lean_object* v_k_4304_; lean_object* v_v_4305_; lean_object* v_l_4306_; lean_object* v_r_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v_k_4304_ = lean_ctor_get(v_x_4303_, 1);
v_v_4305_ = lean_ctor_get(v_x_4303_, 2);
v_l_4306_ = lean_ctor_get(v_x_4303_, 3);
v_r_4307_ = lean_ctor_get(v_x_4303_, 4);
v___x_4308_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4302_, v_l_4306_);
lean_inc(v_v_4305_);
lean_inc(v_k_4304_);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v_k_4304_);
lean_ctor_set(v___x_4309_, 1, v_v_4305_);
v___x_4310_ = lean_array_push(v___x_4308_, v___x_4309_);
v_init_4302_ = v___x_4310_;
v_x_4303_ = v_r_4307_;
goto _start;
}
else
{
return v_init_4302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4312_, lean_object* v_x_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4312_, v_x_4313_);
lean_dec(v_x_4313_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4321_, lean_object* v_s_4322_){
_start:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; uint8_t v___x_4328_; 
v___x_4323_ = lean_unsigned_to_nat(0u);
v___x_4324_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4325_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4324_, v_s_4322_);
v___x_4326_ = lean_array_get_size(v___x_4325_);
v___x_4327_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4328_ = lean_nat_dec_lt(v___x_4323_, v___x_4326_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; 
lean_dec_ref(v___x_4325_);
lean_dec_ref(v_env_4321_);
v___x_4329_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4329_;
}
else
{
uint8_t v___x_4330_; 
v___x_4330_ = lean_nat_dec_le(v___x_4326_, v___x_4326_);
if (v___x_4330_ == 0)
{
if (v___x_4328_ == 0)
{
lean_object* v___x_4331_; 
lean_dec_ref(v___x_4325_);
lean_dec_ref(v_env_4321_);
v___x_4331_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4331_;
}
else
{
size_t v___x_4332_; size_t v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4332_ = ((size_t)0ULL);
v___x_4333_ = lean_usize_of_nat(v___x_4326_);
v___x_4334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4321_, v___x_4325_, v___x_4332_, v___x_4333_, v___x_4327_);
lean_dec_ref(v___x_4325_);
lean_inc_ref_n(v___x_4334_, 2);
v___x_4335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
lean_ctor_set(v___x_4335_, 1, v___x_4334_);
lean_ctor_set(v___x_4335_, 2, v___x_4334_);
return v___x_4335_;
}
}
else
{
size_t v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4336_ = ((size_t)0ULL);
v___x_4337_ = lean_usize_of_nat(v___x_4326_);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4321_, v___x_4325_, v___x_4336_, v___x_4337_, v___x_4327_);
lean_dec_ref(v___x_4325_);
lean_inc_ref_n(v___x_4338_, 2);
v___x_4339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
lean_ctor_set(v___x_4339_, 2, v___x_4338_);
return v___x_4339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4340_, lean_object* v_s_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4340_, v_s_4341_);
lean_dec(v_s_4341_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___f_4352_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4353_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4354_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4355_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4353_, v___x_4354_, v___f_4352_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4358_, lean_object* v_t_4359_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4358_, v_t_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4361_, lean_object* v_t_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4361_, v_t_4362_);
lean_dec(v_t_4362_);
return v_res_4363_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object* v_env_4364_, lean_object* v_n_4365_){
_start:
{
if (lean_obj_tag(v_n_4365_) == 1)
{
lean_object* v_pre_4366_; lean_object* v_str_4367_; uint8_t v___y_4369_; uint8_t v___x_4371_; 
v_pre_4366_ = lean_ctor_get(v_n_4365_, 0);
lean_inc(v_pre_4366_);
v_str_4367_ = lean_ctor_get(v_n_4365_, 1);
lean_inc_ref_n(v_str_4367_, 2);
lean_dec_ref_known(v_n_4365_, 2);
v___x_4371_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4367_);
if (v___x_4371_ == 0)
{
lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4372_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4373_ = lean_string_dec_eq(v_str_4367_, v___x_4372_);
lean_dec_ref(v_str_4367_);
v___y_4369_ = v___x_4373_;
goto v___jp_4368_;
}
else
{
lean_dec_ref(v_str_4367_);
v___y_4369_ = v___x_4371_;
goto v___jp_4368_;
}
v___jp_4368_:
{
if (v___y_4369_ == 0)
{
lean_dec(v_pre_4366_);
lean_dec_ref(v_env_4364_);
return v___y_4369_;
}
else
{
uint8_t v___x_4370_; 
v___x_4370_ = l_Lean_Environment_contains(v_env_4364_, v_pre_4366_, v___y_4369_);
return v___x_4370_;
}
}
}
else
{
uint8_t v___x_4374_; 
lean_dec(v_n_4365_);
lean_dec_ref(v_env_4364_);
v___x_4374_ = 0;
return v___x_4374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_env_4375_, lean_object* v_n_4376_){
_start:
{
uint8_t v_res_4377_; lean_object* v_r_4378_; 
v_res_4377_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4375_, v_n_4376_);
v_r_4378_ = lean_box(v_res_4377_);
return v_r_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4381_; lean_object* v___x_4382_; 
v___f_4381_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_));
v___x_4382_ = l_Lean_registerReservedNamePredicate(v___f_4381_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_a_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object* v_thm_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v___x_4388_; lean_object* v_env_4389_; lean_object* v_toConstantVal_4390_; lean_object* v_value_4391_; lean_object* v_all_4392_; uint8_t v___y_4394_; lean_object* v_type_4402_; uint8_t v___x_4403_; 
v___x_4388_ = lean_st_ref_get(v___y_4386_);
v_env_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc_ref_n(v_env_4389_, 2);
lean_dec(v___x_4388_);
v_toConstantVal_4390_ = lean_ctor_get(v_thm_4385_, 0);
v_value_4391_ = lean_ctor_get(v_thm_4385_, 1);
v_all_4392_ = lean_ctor_get(v_thm_4385_, 2);
v_type_4402_ = lean_ctor_get(v_toConstantVal_4390_, 2);
v___x_4403_ = l_Lean_Environment_hasUnsafe(v_env_4389_, v_type_4402_);
if (v___x_4403_ == 0)
{
uint8_t v___x_4404_; 
v___x_4404_ = l_Lean_Environment_hasUnsafe(v_env_4389_, v_value_4391_);
v___y_4394_ = v___x_4404_;
goto v___jp_4393_;
}
else
{
lean_dec_ref(v_env_4389_);
v___y_4394_ = v___x_4403_;
goto v___jp_4393_;
}
v___jp_4393_:
{
if (v___y_4394_ == 0)
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4395_, 0, v_thm_4385_);
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
else
{
lean_object* v___x_4397_; uint8_t v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
lean_inc(v_all_4392_);
lean_inc_ref(v_value_4391_);
lean_inc_ref(v_toConstantVal_4390_);
lean_dec_ref(v_thm_4385_);
v___x_4397_ = lean_box(0);
v___x_4398_ = 0;
v___x_4399_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4399_, 0, v_toConstantVal_4390_);
lean_ctor_set(v___x_4399_, 1, v_value_4391_);
lean_ctor_set(v___x_4399_, 2, v___x_4397_);
lean_ctor_set(v___x_4399_, 3, v_all_4392_);
lean_ctor_set_uint8(v___x_4399_, sizeof(void*)*4, v___x_4398_);
v___x_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
v___x_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4400_);
return v___x_4401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_thm_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4405_, v___y_4406_);
lean_dec(v___y_4406_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_thm_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4409_, v___y_4413_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object* v_thm_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
return v_res_4422_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_4423_; double v___x_4424_; 
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = lean_float_of_nat(v___x_4423_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_cls_4428_, lean_object* v_msg_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_ref_4435_; lean_object* v___x_4436_; lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4481_; 
v_ref_4435_ = lean_ctor_get(v___y_4432_, 5);
v___x_4436_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4439_ = v___x_4436_;
v_isShared_4440_ = v_isSharedCheck_4481_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4481_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v_traceState_4442_; lean_object* v_env_4443_; lean_object* v_nextMacroScope_4444_; lean_object* v_ngen_4445_; lean_object* v_auxDeclNGen_4446_; lean_object* v_cache_4447_; lean_object* v_messages_4448_; lean_object* v_infoState_4449_; lean_object* v_snapshotTasks_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4480_; 
v___x_4441_ = lean_st_ref_take(v___y_4433_);
v_traceState_4442_ = lean_ctor_get(v___x_4441_, 4);
v_env_4443_ = lean_ctor_get(v___x_4441_, 0);
v_nextMacroScope_4444_ = lean_ctor_get(v___x_4441_, 1);
v_ngen_4445_ = lean_ctor_get(v___x_4441_, 2);
v_auxDeclNGen_4446_ = lean_ctor_get(v___x_4441_, 3);
v_cache_4447_ = lean_ctor_get(v___x_4441_, 5);
v_messages_4448_ = lean_ctor_get(v___x_4441_, 6);
v_infoState_4449_ = lean_ctor_get(v___x_4441_, 7);
v_snapshotTasks_4450_ = lean_ctor_get(v___x_4441_, 8);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4452_ = v___x_4441_;
v_isShared_4453_ = v_isSharedCheck_4480_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_snapshotTasks_4450_);
lean_inc(v_infoState_4449_);
lean_inc(v_messages_4448_);
lean_inc(v_cache_4447_);
lean_inc(v_traceState_4442_);
lean_inc(v_auxDeclNGen_4446_);
lean_inc(v_ngen_4445_);
lean_inc(v_nextMacroScope_4444_);
lean_inc(v_env_4443_);
lean_dec(v___x_4441_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4480_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
uint64_t v_tid_4454_; lean_object* v_traces_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4479_; 
v_tid_4454_ = lean_ctor_get_uint64(v_traceState_4442_, sizeof(void*)*1);
v_traces_4455_ = lean_ctor_get(v_traceState_4442_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_traceState_4442_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4457_ = v_traceState_4442_;
v_isShared_4458_ = v_isSharedCheck_4479_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_traces_4455_);
lean_dec(v_traceState_4442_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4479_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4459_; double v___x_4460_; uint8_t v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4459_ = lean_box(0);
v___x_4460_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0);
v___x_4461_ = 0;
v___x_4462_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1));
v___x_4463_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4463_, 0, v_cls_4428_);
lean_ctor_set(v___x_4463_, 1, v___x_4459_);
lean_ctor_set(v___x_4463_, 2, v___x_4462_);
lean_ctor_set_float(v___x_4463_, sizeof(void*)*3, v___x_4460_);
lean_ctor_set_float(v___x_4463_, sizeof(void*)*3 + 8, v___x_4460_);
lean_ctor_set_uint8(v___x_4463_, sizeof(void*)*3 + 16, v___x_4461_);
v___x_4464_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2));
v___x_4465_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4463_);
lean_ctor_set(v___x_4465_, 1, v_a_4437_);
lean_ctor_set(v___x_4465_, 2, v___x_4464_);
lean_inc(v_ref_4435_);
v___x_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4466_, 0, v_ref_4435_);
lean_ctor_set(v___x_4466_, 1, v___x_4465_);
v___x_4467_ = l_Lean_PersistentArray_push___redArg(v_traces_4455_, v___x_4466_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 0, v___x_4467_);
v___x_4469_ = v___x_4457_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4467_);
lean_ctor_set_uint64(v_reuseFailAlloc_4478_, sizeof(void*)*1, v_tid_4454_);
v___x_4469_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4471_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 4, v___x_4469_);
v___x_4471_ = v___x_4452_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_env_4443_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_nextMacroScope_4444_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_ngen_4445_);
lean_ctor_set(v_reuseFailAlloc_4477_, 3, v_auxDeclNGen_4446_);
lean_ctor_set(v_reuseFailAlloc_4477_, 4, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4477_, 5, v_cache_4447_);
lean_ctor_set(v_reuseFailAlloc_4477_, 6, v_messages_4448_);
lean_ctor_set(v_reuseFailAlloc_4477_, 7, v_infoState_4449_);
lean_ctor_set(v_reuseFailAlloc_4477_, 8, v_snapshotTasks_4450_);
v___x_4471_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4472_ = lean_st_ref_set(v___y_4433_, v___x_4471_);
v___x_4473_ = lean_box(0);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v___x_4473_);
v___x_4475_ = v___x_4439_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_4482_, lean_object* v_msg_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4482_, v_msg_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
return v_res_4489_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4490_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4491_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
return v___x_4492_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
return v___x_4494_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4498_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4499_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4500_ = l_Lean_Name_append(v___x_4499_, v___x_4498_);
return v___x_4500_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4503_ = l_Lean_stringToMessageData(v___x_4502_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4504_, uint8_t v___x_4505_, lean_object* v_name_4506_, lean_object* v_argKinds_4507_, lean_object* v___x_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___x_4554_; lean_object* v_a_4555_; lean_object* v___x_4556_; 
v___x_4554_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_4504_, v___y_4512_);
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref(v___x_4554_);
v___x_4556_ = l_Lean_addDecl(v_a_4555_, v___x_4505_, v___y_4511_, v___y_4512_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_options_4557_; uint8_t v_hasTrace_4558_; 
lean_dec_ref_known(v___x_4556_, 1);
v_options_4557_ = lean_ctor_get(v___y_4511_, 2);
v_hasTrace_4558_ = lean_ctor_get_uint8(v_options_4557_, sizeof(void*)*1);
if (v_hasTrace_4558_ == 0)
{
v___y_4515_ = v___y_4510_;
v___y_4516_ = v___y_4512_;
goto v___jp_4514_;
}
else
{
lean_object* v_inheritedTraceOptions_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; uint8_t v___x_4562_; 
v_inheritedTraceOptions_4559_ = lean_ctor_get(v___y_4511_, 13);
v___x_4560_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4561_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4559_, v_options_4557_, v___x_4561_);
if (v___x_4562_ == 0)
{
v___y_4515_ = v___y_4510_;
v___y_4516_ = v___y_4512_;
goto v___jp_4514_;
}
else
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4563_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4506_);
v___x_4564_ = l_Lean_MessageData_ofName(v_name_4506_);
v___x_4565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4563_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
v___x_4566_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4565_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_4560_, v___x_4567_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_dec_ref_known(v___x_4568_, 1);
v___y_4515_ = v___y_4510_;
v___y_4516_ = v___y_4512_;
goto v___jp_4514_;
}
else
{
lean_dec_ref(v___x_4508_);
lean_dec_ref(v_argKinds_4507_);
lean_dec(v_name_4506_);
return v___x_4568_;
}
}
}
}
else
{
lean_dec_ref(v___x_4508_);
lean_dec_ref(v_argKinds_4507_);
lean_dec(v_name_4506_);
return v___x_4556_;
}
v___jp_4514_:
{
lean_object* v___x_4517_; lean_object* v_env_4518_; lean_object* v_nextMacroScope_4519_; lean_object* v_ngen_4520_; lean_object* v_auxDeclNGen_4521_; lean_object* v_traceState_4522_; lean_object* v_messages_4523_; lean_object* v_infoState_4524_; lean_object* v_snapshotTasks_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4552_; 
v___x_4517_ = lean_st_ref_take(v___y_4516_);
v_env_4518_ = lean_ctor_get(v___x_4517_, 0);
v_nextMacroScope_4519_ = lean_ctor_get(v___x_4517_, 1);
v_ngen_4520_ = lean_ctor_get(v___x_4517_, 2);
v_auxDeclNGen_4521_ = lean_ctor_get(v___x_4517_, 3);
v_traceState_4522_ = lean_ctor_get(v___x_4517_, 4);
v_messages_4523_ = lean_ctor_get(v___x_4517_, 6);
v_infoState_4524_ = lean_ctor_get(v___x_4517_, 7);
v_snapshotTasks_4525_ = lean_ctor_get(v___x_4517_, 8);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4552_ == 0)
{
lean_object* v_unused_4553_; 
v_unused_4553_ = lean_ctor_get(v___x_4517_, 5);
lean_dec(v_unused_4553_);
v___x_4527_ = v___x_4517_;
v_isShared_4528_ = v_isSharedCheck_4552_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_snapshotTasks_4525_);
lean_inc(v_infoState_4524_);
lean_inc(v_messages_4523_);
lean_inc(v_traceState_4522_);
lean_inc(v_auxDeclNGen_4521_);
lean_inc(v_ngen_4520_);
lean_inc(v_nextMacroScope_4519_);
lean_inc(v_env_4518_);
lean_dec(v___x_4517_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4552_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4533_; 
v___x_4529_ = l_Lean_Meta_congrKindsExt;
v___x_4530_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4529_, v_env_4518_, v_name_4506_, v_argKinds_4507_);
v___x_4531_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 5, v___x_4531_);
lean_ctor_set(v___x_4527_, 0, v___x_4530_);
v___x_4533_ = v___x_4527_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_nextMacroScope_4519_);
lean_ctor_set(v_reuseFailAlloc_4551_, 2, v_ngen_4520_);
lean_ctor_set(v_reuseFailAlloc_4551_, 3, v_auxDeclNGen_4521_);
lean_ctor_set(v_reuseFailAlloc_4551_, 4, v_traceState_4522_);
lean_ctor_set(v_reuseFailAlloc_4551_, 5, v___x_4531_);
lean_ctor_set(v_reuseFailAlloc_4551_, 6, v_messages_4523_);
lean_ctor_set(v_reuseFailAlloc_4551_, 7, v_infoState_4524_);
lean_ctor_set(v_reuseFailAlloc_4551_, 8, v_snapshotTasks_4525_);
v___x_4533_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v_mctx_4536_; lean_object* v_zetaDeltaFVarIds_4537_; lean_object* v_postponed_4538_; lean_object* v_diag_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4549_; 
v___x_4534_ = lean_st_ref_set(v___y_4516_, v___x_4533_);
v___x_4535_ = lean_st_ref_take(v___y_4515_);
v_mctx_4536_ = lean_ctor_get(v___x_4535_, 0);
v_zetaDeltaFVarIds_4537_ = lean_ctor_get(v___x_4535_, 2);
v_postponed_4538_ = lean_ctor_get(v___x_4535_, 3);
v_diag_4539_ = lean_ctor_get(v___x_4535_, 4);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4549_ == 0)
{
lean_object* v_unused_4550_; 
v_unused_4550_ = lean_ctor_get(v___x_4535_, 1);
lean_dec(v_unused_4550_);
v___x_4541_ = v___x_4535_;
v_isShared_4542_ = v_isSharedCheck_4549_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_diag_4539_);
lean_inc(v_postponed_4538_);
lean_inc(v_zetaDeltaFVarIds_4537_);
lean_inc(v_mctx_4536_);
lean_dec(v___x_4535_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4549_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 1, v___x_4508_);
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_mctx_4536_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4548_, 2, v_zetaDeltaFVarIds_4537_);
lean_ctor_set(v_reuseFailAlloc_4548_, 3, v_postponed_4538_);
lean_ctor_set(v_reuseFailAlloc_4548_, 4, v_diag_4539_);
v___x_4544_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4545_ = lean_st_ref_set(v___y_4515_, v___x_4544_);
v___x_4546_ = lean_box(0);
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
return v___x_4547_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4569_, lean_object* v___x_4570_, lean_object* v_name_4571_, lean_object* v_argKinds_4572_, lean_object* v___x_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v___x_15938__boxed_4579_; lean_object* v_res_4580_; 
v___x_15938__boxed_4579_ = lean_unbox(v___x_4570_);
v_res_4580_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4569_, v___x_15938__boxed_4579_, v_name_4571_, v_argKinds_4572_, v___x_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_a_4581_, lean_object* v_a_4582_){
_start:
{
if (lean_obj_tag(v_a_4581_) == 0)
{
lean_object* v___x_4583_; 
v___x_4583_ = l_List_reverse___redArg(v_a_4582_);
return v___x_4583_;
}
else
{
lean_object* v_head_4584_; lean_object* v_tail_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4594_; 
v_head_4584_ = lean_ctor_get(v_a_4581_, 0);
v_tail_4585_ = lean_ctor_get(v_a_4581_, 1);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_a_4581_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4587_ = v_a_4581_;
v_isShared_4588_ = v_isSharedCheck_4594_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_tail_4585_);
lean_inc(v_head_4584_);
lean_dec(v_a_4581_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4594_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4589_; lean_object* v___x_4591_; 
v___x_4589_ = l_Lean_mkLevelParam(v_head_4584_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 1, v_a_4582_);
lean_ctor_set(v___x_4587_, 0, v___x_4589_);
v___x_4591_ = v___x_4587_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_a_4582_);
v___x_4591_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
v_a_4581_ = v_tail_4585_;
v_a_4582_ = v___x_4591_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4595_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
return v___x_4597_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4598_ = lean_box(1);
v___x_4599_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4600_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
lean_ctor_set(v___x_4601_, 1, v___x_4599_);
lean_ctor_set(v___x_4601_, 2, v___x_4598_);
return v___x_4601_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4604_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4605_ = lean_unsigned_to_nat(0u);
v___x_4606_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
lean_ctor_set(v___x_4606_, 1, v___x_4605_);
lean_ctor_set(v___x_4606_, 2, v___x_4605_);
lean_ctor_set(v___x_4606_, 3, v___x_4605_);
lean_ctor_set(v___x_4606_, 4, v___x_4604_);
lean_ctor_set(v___x_4606_, 5, v___x_4604_);
lean_ctor_set(v___x_4606_, 6, v___x_4604_);
lean_ctor_set(v___x_4606_, 7, v___x_4604_);
lean_ctor_set(v___x_4606_, 8, v___x_4604_);
lean_ctor_set(v___x_4606_, 9, v___x_4604_);
return v___x_4606_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4608_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
lean_ctor_set(v___x_4608_, 2, v___x_4607_);
lean_ctor_set(v___x_4608_, 3, v___x_4607_);
lean_ctor_set(v___x_4608_, 4, v___x_4607_);
lean_ctor_set(v___x_4608_, 5, v___x_4607_);
return v___x_4608_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
lean_ctor_set(v___x_4610_, 2, v___x_4609_);
lean_ctor_set(v___x_4610_, 3, v___x_4609_);
lean_ctor_set(v___x_4610_, 4, v___x_4609_);
return v___x_4610_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4611_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4612_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4613_ = lean_box(1);
v___x_4614_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4615_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
lean_ctor_set(v___x_4616_, 1, v___x_4614_);
lean_ctor_set(v___x_4616_, 2, v___x_4613_);
lean_ctor_set(v___x_4616_, 3, v___x_4612_);
lean_ctor_set(v___x_4616_, 4, v___x_4611_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v_name_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
if (lean_obj_tag(v_name_4617_) == 1)
{
lean_object* v_pre_4621_; lean_object* v_str_4622_; lean_object* v___x_4623_; lean_object* v_env_4624_; uint8_t v___x_4625_; uint8_t v___x_4626_; 
v_pre_4621_ = lean_ctor_get(v_name_4617_, 0);
lean_inc_n(v_pre_4621_, 2);
v_str_4622_ = lean_ctor_get(v_name_4617_, 1);
v___x_4623_ = lean_st_ref_get(v___y_4619_);
v_env_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc_ref(v_env_4624_);
lean_dec(v___x_4623_);
v___x_4625_ = 1;
v___x_4626_ = l_Lean_Environment_contains(v_env_4624_, v_pre_4621_, v___x_4625_);
if (v___x_4626_ == 0)
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
lean_dec(v_pre_4621_);
lean_dec_ref_known(v_name_4617_, 2);
v___x_4627_ = lean_box(v___x_4626_);
v___x_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
return v___x_4628_;
}
else
{
uint8_t v___x_4629_; lean_object* v___y_4631_; uint8_t v___y_4632_; lean_object* v_a_4637_; 
lean_inc_ref(v_str_4622_);
v___x_4629_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4622_);
if (v___x_4629_ == 0)
{
lean_object* v___x_4640_; uint8_t v___x_4641_; 
v___x_4640_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4641_ = lean_string_dec_eq(v_str_4622_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_object* v___x_4642_; lean_object* v___x_4643_; 
lean_dec(v_pre_4621_);
lean_dec_ref_known(v_name_4617_, 2);
v___x_4642_ = lean_box(v___x_4641_);
v___x_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
return v___x_4643_;
}
else
{
uint8_t v___x_4644_; uint8_t v___x_4645_; uint8_t v___x_4646_; lean_object* v___x_4647_; uint64_t v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; uint8_t v_a_4660_; lean_object* v___x_4664_; 
v___x_4644_ = 1;
v___x_4645_ = 0;
v___x_4646_ = 2;
v___x_4647_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4647_, 0, v___x_4629_);
lean_ctor_set_uint8(v___x_4647_, 1, v___x_4629_);
lean_ctor_set_uint8(v___x_4647_, 2, v___x_4629_);
lean_ctor_set_uint8(v___x_4647_, 3, v___x_4629_);
lean_ctor_set_uint8(v___x_4647_, 4, v___x_4629_);
lean_ctor_set_uint8(v___x_4647_, 5, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 6, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 7, v___x_4629_);
lean_ctor_set_uint8(v___x_4647_, 8, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 9, v___x_4644_);
lean_ctor_set_uint8(v___x_4647_, 10, v___x_4645_);
lean_ctor_set_uint8(v___x_4647_, 11, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 12, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 13, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 14, v___x_4646_);
lean_ctor_set_uint8(v___x_4647_, 15, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 16, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 17, v___x_4641_);
lean_ctor_set_uint8(v___x_4647_, 18, v___x_4641_);
v___x_4648_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4647_);
v___x_4649_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4649_, 0, v___x_4647_);
lean_ctor_set_uint64(v___x_4649_, sizeof(void*)*1, v___x_4648_);
v___x_4650_ = lean_box(1);
v___x_4651_ = lean_unsigned_to_nat(0u);
v___x_4652_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4653_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4654_ = lean_box(0);
v___x_4655_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4655_, 0, v___x_4649_);
lean_ctor_set(v___x_4655_, 1, v___x_4650_);
lean_ctor_set(v___x_4655_, 2, v___x_4652_);
lean_ctor_set(v___x_4655_, 3, v___x_4653_);
lean_ctor_set(v___x_4655_, 4, v___x_4654_);
lean_ctor_set(v___x_4655_, 5, v___x_4651_);
lean_ctor_set(v___x_4655_, 6, v___x_4654_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*7, v___x_4629_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*7 + 1, v___x_4629_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*7 + 2, v___x_4629_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*7 + 3, v___x_4625_);
v___x_4656_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4657_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4658_ = lean_st_mk_ref(v___x_4657_);
lean_inc(v_pre_4621_);
v___x_4664_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4621_, v___x_4655_, v___x_4658_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
v___x_4666_ = l_Lean_ConstantInfo_levelParams(v_a_4665_);
lean_dec(v_a_4665_);
v___x_4667_ = lean_box(0);
lean_inc(v___x_4666_);
v___x_4668_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4666_, v___x_4667_);
lean_inc(v_pre_4621_);
v___x_4669_ = l_Lean_mkConst(v_pre_4621_, v___x_4668_);
lean_inc_ref(v___x_4669_);
v___x_4670_ = l_Lean_Meta_getFunInfo(v___x_4669_, v___x_4654_, v___x_4655_, v___x_4658_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4672_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
lean_inc_ref(v___x_4669_);
v___x_4672_ = l_Lean_Meta_getCongrSimpKinds(v___x_4669_, v_a_4671_, v___x_4655_, v___x_4658_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4674_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v___x_4672_, 1);
v___x_4674_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4669_, v_a_4671_, v_a_4673_, v___x_4625_, v___x_4655_, v___x_4658_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
if (lean_obj_tag(v_a_4675_) == 1)
{
lean_object* v_val_4676_; lean_object* v_type_4677_; lean_object* v_proof_4678_; lean_object* v_argKinds_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4692_; 
v_val_4676_ = lean_ctor_get(v_a_4675_, 0);
lean_inc(v_val_4676_);
lean_dec_ref_known(v_a_4675_, 1);
v_type_4677_ = lean_ctor_get(v_val_4676_, 0);
v_proof_4678_ = lean_ctor_get(v_val_4676_, 1);
v_argKinds_4679_ = lean_ctor_get(v_val_4676_, 2);
v_isSharedCheck_4692_ = !lean_is_exclusive(v_val_4676_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4681_ = v_val_4676_;
v_isShared_4682_ = v_isSharedCheck_4692_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_argKinds_4679_);
lean_inc(v_proof_4678_);
lean_inc(v_type_4677_);
lean_dec(v_val_4676_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4692_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
lean_inc_ref(v_name_4617_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 2, v_type_4677_);
lean_ctor_set(v___x_4681_, 1, v___x_4666_);
lean_ctor_set(v___x_4681_, 0, v_name_4617_);
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_name_4617_);
lean_ctor_set(v_reuseFailAlloc_4691_, 1, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4691_, 2, v_type_4677_);
v___x_4684_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___f_4688_; lean_object* v___x_4689_; 
lean_inc_ref_n(v_name_4617_, 2);
v___x_4685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4685_, 0, v_name_4617_);
lean_ctor_set(v___x_4685_, 1, v___x_4667_);
v___x_4686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4684_);
lean_ctor_set(v___x_4686_, 1, v_proof_4678_);
lean_ctor_set(v___x_4686_, 2, v___x_4685_);
v___x_4687_ = lean_box(v___x_4629_);
v___f_4688_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4688_, 0, v___x_4686_);
lean_closure_set(v___f_4688_, 1, v___x_4687_);
lean_closure_set(v___f_4688_, 2, v_name_4617_);
lean_closure_set(v___f_4688_, 3, v_argKinds_4679_);
lean_closure_set(v___f_4688_, 4, v___x_4656_);
v___x_4689_ = l_Lean_Meta_realizeConst(v_pre_4621_, v_name_4617_, v___f_4688_, v___x_4655_, v___x_4658_, v___y_4618_, v___y_4619_);
lean_dec_ref_known(v___x_4655_, 7);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_dec_ref_known(v___x_4689_, 1);
v_a_4660_ = v___x_4625_;
goto v___jp_4659_;
}
else
{
lean_object* v_a_4690_; 
lean_dec(v___x_4658_);
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_a_4690_);
lean_dec_ref_known(v___x_4689_, 1);
v_a_4637_ = v_a_4690_;
goto v___jp_4636_;
}
}
}
}
else
{
lean_dec(v_a_4675_);
lean_dec(v___x_4666_);
lean_dec_ref_known(v___x_4655_, 7);
lean_dec_ref_known(v_name_4617_, 2);
lean_dec(v_pre_4621_);
v_a_4660_ = v___x_4629_;
goto v___jp_4659_;
}
}
else
{
lean_object* v_a_4693_; 
lean_dec(v___x_4666_);
lean_dec(v___x_4658_);
lean_dec_ref_known(v___x_4655_, 7);
lean_dec_ref_known(v_name_4617_, 2);
lean_dec(v_pre_4621_);
v_a_4693_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4693_);
lean_dec_ref_known(v___x_4674_, 1);
v_a_4637_ = v_a_4693_;
goto v___jp_4636_;
}
}
else
{
lean_object* v_a_4694_; 
lean_dec(v_a_4671_);
lean_dec_ref(v___x_4669_);
lean_dec(v___x_4666_);
lean_dec(v___x_4658_);
lean_dec_ref_known(v___x_4655_, 7);
lean_dec(v_pre_4621_);
lean_dec_ref_known(v_name_4617_, 2);
v_a_4694_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4694_);
lean_dec_ref_known(v___x_4672_, 1);
v_a_4637_ = v_a_4694_;
goto v___jp_4636_;
}
}
else
{
lean_object* v_a_4695_; 
lean_dec_ref(v___x_4669_);
lean_dec(v___x_4666_);
lean_dec(v___x_4658_);
lean_dec_ref_known(v___x_4655_, 7);
lean_dec(v_pre_4621_);
lean_dec_ref_known(v_name_4617_, 2);
v_a_4695_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4695_);
lean_dec_ref_known(v___x_4670_, 1);
v_a_4637_ = v_a_4695_;
goto v___jp_4636_;
}
}
else
{
lean_object* v_a_4696_; 
lean_dec(v___x_4658_);
lean_dec_ref_known(v___x_4655_, 7);
lean_dec_ref_known(v_name_4617_, 2);
lean_dec(v_pre_4621_);
v_a_4696_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4664_, 1);
v_a_4637_ = v_a_4696_;
goto v___jp_4636_;
}
v___jp_4659_:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = lean_st_ref_get(v___x_4658_);
lean_dec(v___x_4658_);
lean_dec(v___x_4661_);
v___x_4662_ = lean_box(v_a_4660_);
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
}
}
else
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___y_4704_; uint8_t v___y_4705_; lean_object* v_a_4710_; uint8_t v___x_4713_; uint8_t v___x_4714_; uint8_t v___x_4715_; lean_object* v___x_4716_; uint64_t v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4697_ = lean_unsigned_to_nat(7u);
v___x_4698_ = lean_unsigned_to_nat(0u);
v___x_4699_ = lean_string_utf8_byte_size(v_str_4622_);
lean_inc_ref(v_str_4622_);
v___x_4700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4700_, 0, v_str_4622_);
lean_ctor_set(v___x_4700_, 1, v___x_4698_);
lean_ctor_set(v___x_4700_, 2, v___x_4699_);
v___x_4701_ = l_String_Slice_Pos_nextn(v___x_4700_, v___x_4698_, v___x_4697_);
lean_dec_ref_known(v___x_4700_, 3);
v___x_4702_ = 0;
v___x_4713_ = 1;
v___x_4714_ = 0;
v___x_4715_ = 2;
v___x_4716_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4716_, 0, v___x_4702_);
lean_ctor_set_uint8(v___x_4716_, 1, v___x_4702_);
lean_ctor_set_uint8(v___x_4716_, 2, v___x_4702_);
lean_ctor_set_uint8(v___x_4716_, 3, v___x_4702_);
lean_ctor_set_uint8(v___x_4716_, 4, v___x_4702_);
lean_ctor_set_uint8(v___x_4716_, 5, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 6, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 7, v___x_4702_);
lean_ctor_set_uint8(v___x_4716_, 8, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 9, v___x_4713_);
lean_ctor_set_uint8(v___x_4716_, 10, v___x_4714_);
lean_ctor_set_uint8(v___x_4716_, 11, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 12, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 13, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 14, v___x_4715_);
lean_ctor_set_uint8(v___x_4716_, 15, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 16, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 17, v___x_4629_);
lean_ctor_set_uint8(v___x_4716_, 18, v___x_4629_);
v___x_4717_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4716_);
v___x_4718_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4718_, 0, v___x_4716_);
lean_ctor_set_uint64(v___x_4718_, sizeof(void*)*1, v___x_4717_);
v___x_4719_ = lean_box(1);
v___x_4720_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4721_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4722_ = lean_box(0);
v___x_4723_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4723_, 0, v___x_4718_);
lean_ctor_set(v___x_4723_, 1, v___x_4719_);
lean_ctor_set(v___x_4723_, 2, v___x_4720_);
lean_ctor_set(v___x_4723_, 3, v___x_4721_);
lean_ctor_set(v___x_4723_, 4, v___x_4722_);
lean_ctor_set(v___x_4723_, 5, v___x_4698_);
lean_ctor_set(v___x_4723_, 6, v___x_4722_);
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*7, v___x_4702_);
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*7 + 1, v___x_4702_);
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*7 + 2, v___x_4702_);
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*7 + 3, v___x_4625_);
v___x_4724_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4725_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4726_ = lean_st_mk_ref(v___x_4725_);
lean_inc(v_pre_4621_);
v___x_4727_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4621_, v___x_4723_, v___x_4726_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4728_);
lean_dec_ref_known(v___x_4727_, 1);
lean_inc_ref(v_str_4622_);
v___x_4729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4729_, 0, v_str_4622_);
lean_ctor_set(v___x_4729_, 1, v___x_4701_);
lean_ctor_set(v___x_4729_, 2, v___x_4699_);
v___x_4730_ = l_String_Slice_toNat_x21(v___x_4729_);
lean_dec_ref_known(v___x_4729_, 3);
v___x_4731_ = l_Lean_ConstantInfo_levelParams(v_a_4728_);
lean_dec(v_a_4728_);
v___x_4732_ = lean_box(0);
lean_inc(v___x_4731_);
v___x_4733_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4731_, v___x_4732_);
lean_inc(v_pre_4621_);
v___x_4734_ = l_Lean_mkConst(v_pre_4621_, v___x_4733_);
v___x_4735_ = l_Lean_Meta_mkHCongrWithArity(v___x_4734_, v___x_4730_, v___x_4723_, v___x_4726_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v_type_4737_; lean_object* v_proof_4738_; lean_object* v_argKinds_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4762_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v___x_4735_, 1);
v_type_4737_ = lean_ctor_get(v_a_4736_, 0);
v_proof_4738_ = lean_ctor_get(v_a_4736_, 1);
v_argKinds_4739_ = lean_ctor_get(v_a_4736_, 2);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_a_4736_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4741_ = v_a_4736_;
v_isShared_4742_ = v_isSharedCheck_4762_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_argKinds_4739_);
lean_inc(v_proof_4738_);
lean_inc(v_type_4737_);
lean_dec(v_a_4736_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4762_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4744_; 
lean_inc_ref(v_name_4617_);
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 2, v_type_4737_);
lean_ctor_set(v___x_4741_, 1, v___x_4731_);
lean_ctor_set(v___x_4741_, 0, v_name_4617_);
v___x_4744_ = v___x_4741_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_name_4617_);
lean_ctor_set(v_reuseFailAlloc_4761_, 1, v___x_4731_);
lean_ctor_set(v_reuseFailAlloc_4761_, 2, v_type_4737_);
v___x_4744_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___f_4748_; lean_object* v___x_4749_; 
lean_inc_ref_n(v_name_4617_, 2);
v___x_4745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4745_, 0, v_name_4617_);
lean_ctor_set(v___x_4745_, 1, v___x_4732_);
v___x_4746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4744_);
lean_ctor_set(v___x_4746_, 1, v_proof_4738_);
lean_ctor_set(v___x_4746_, 2, v___x_4745_);
v___x_4747_ = lean_box(v___x_4702_);
v___f_4748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4748_, 0, v___x_4746_);
lean_closure_set(v___f_4748_, 1, v___x_4747_);
lean_closure_set(v___f_4748_, 2, v_name_4617_);
lean_closure_set(v___f_4748_, 3, v_argKinds_4739_);
lean_closure_set(v___f_4748_, 4, v___x_4724_);
v___x_4749_ = l_Lean_Meta_realizeConst(v_pre_4621_, v_name_4617_, v___f_4748_, v___x_4723_, v___x_4726_, v___y_4618_, v___y_4619_);
lean_dec_ref_known(v___x_4723_, 7);
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4758_; 
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4758_ == 0)
{
lean_object* v_unused_4759_; 
v_unused_4759_ = lean_ctor_get(v___x_4749_, 0);
lean_dec(v_unused_4759_);
v___x_4751_ = v___x_4749_;
v_isShared_4752_ = v_isSharedCheck_4758_;
goto v_resetjp_4750_;
}
else
{
lean_dec(v___x_4749_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4758_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4756_; 
v___x_4753_ = lean_st_ref_get(v___x_4726_);
lean_dec(v___x_4726_);
lean_dec(v___x_4753_);
v___x_4754_ = lean_box(v___x_4625_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4754_);
v___x_4756_ = v___x_4751_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4754_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
else
{
lean_object* v_a_4760_; 
lean_dec(v___x_4726_);
v_a_4760_ = lean_ctor_get(v___x_4749_, 0);
lean_inc(v_a_4760_);
lean_dec_ref_known(v___x_4749_, 1);
v_a_4710_ = v_a_4760_;
goto v___jp_4709_;
}
}
}
}
else
{
lean_object* v_a_4763_; 
lean_dec(v___x_4731_);
lean_dec(v___x_4726_);
lean_dec_ref_known(v___x_4723_, 7);
lean_dec_ref_known(v_name_4617_, 2);
lean_dec(v_pre_4621_);
v_a_4763_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4763_);
lean_dec_ref_known(v___x_4735_, 1);
v_a_4710_ = v_a_4763_;
goto v___jp_4709_;
}
}
else
{
lean_object* v_a_4764_; 
lean_dec(v___x_4726_);
lean_dec_ref_known(v___x_4723_, 7);
lean_dec(v___x_4701_);
lean_dec_ref_known(v_name_4617_, 2);
lean_dec(v_pre_4621_);
v_a_4764_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4764_);
lean_dec_ref_known(v___x_4727_, 1);
v_a_4710_ = v_a_4764_;
goto v___jp_4709_;
}
v___jp_4703_:
{
if (v___y_4705_ == 0)
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
lean_dec_ref(v___y_4704_);
v___x_4706_ = lean_box(v___x_4702_);
v___x_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
return v___x_4707_;
}
else
{
lean_object* v___x_4708_; 
v___x_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4708_, 0, v___y_4704_);
return v___x_4708_;
}
}
v___jp_4709_:
{
uint8_t v___x_4711_; 
v___x_4711_ = l_Lean_Exception_isInterrupt(v_a_4710_);
if (v___x_4711_ == 0)
{
uint8_t v___x_4712_; 
lean_inc_ref(v_a_4710_);
v___x_4712_ = l_Lean_Exception_isRuntime(v_a_4710_);
v___y_4704_ = v_a_4710_;
v___y_4705_ = v___x_4712_;
goto v___jp_4703_;
}
else
{
v___y_4704_ = v_a_4710_;
v___y_4705_ = v___x_4711_;
goto v___jp_4703_;
}
}
}
v___jp_4630_:
{
if (v___y_4632_ == 0)
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
lean_dec_ref(v___y_4631_);
v___x_4633_ = lean_box(v___x_4629_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
return v___x_4634_;
}
else
{
lean_object* v___x_4635_; 
v___x_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___y_4631_);
return v___x_4635_;
}
}
v___jp_4636_:
{
uint8_t v___x_4638_; 
v___x_4638_ = l_Lean_Exception_isInterrupt(v_a_4637_);
if (v___x_4638_ == 0)
{
uint8_t v___x_4639_; 
lean_inc_ref(v_a_4637_);
v___x_4639_ = l_Lean_Exception_isRuntime(v_a_4637_);
v___y_4631_ = v_a_4637_;
v___y_4632_ = v___x_4639_;
goto v___jp_4630_;
}
else
{
v___y_4631_ = v_a_4637_;
v___y_4632_ = v___x_4638_;
goto v___jp_4630_;
}
}
}
}
else
{
uint8_t v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
lean_dec(v_name_4617_);
v___x_4765_ = 0;
v___x_4766_ = lean_box(v___x_4765_);
v___x_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
return v___x_4767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_name_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_4768_, v___y_4769_, v___y_4770_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4775_; lean_object* v___x_4776_; 
v___f_4775_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4776_ = l_Lean_registerReservedNameAction(v___f_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_a_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* v_msg_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
lean_object* v___f_4785_; lean_object* v___x_1830__overap_4786_; lean_object* v___x_4787_; 
v___f_4785_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1830__overap_4786_ = lean_panic_fn_borrowed(v___f_4785_, v_msg_4779_);
lean_inc(v___y_4783_);
lean_inc_ref(v___y_4782_);
lean_inc(v___y_4781_);
lean_inc_ref(v___y_4780_);
v___x_4787_ = lean_apply_5(v___x_1830__overap_4786_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, lean_box(0));
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
return v_res_4794_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4796_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4797_ = lean_unsigned_to_nat(8u);
v___x_4798_ = lean_unsigned_to_nat(461u);
v___x_4799_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0));
v___x_4800_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4801_ = l_mkPanicMessageWithDecl(v___x_4800_, v___x_4799_, v___x_4798_, v___x_4797_, v___x_4796_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* v_thmName_4802_, lean_object* v_levels_4803_, lean_object* v___x_4804_, lean_object* v_____r_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_){
_start:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; 
lean_inc(v_thmName_4802_);
v___x_4811_ = l_Lean_mkConst(v_thmName_4802_, v_levels_4803_);
lean_inc(v___y_4809_);
lean_inc_ref(v___y_4808_);
lean_inc(v___y_4807_);
lean_inc_ref(v___y_4806_);
lean_inc_ref(v___x_4811_);
v___x_4812_ = lean_infer_type(v___x_4811_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4856_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4815_ = v___x_4812_;
v_isShared_4816_ = v_isSharedCheck_4856_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4812_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4856_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4817_; lean_object* v_env_4818_; lean_object* v___x_4819_; lean_object* v_toEnvExtension_4820_; lean_object* v_asyncMode_4821_; uint8_t v___x_4822_; lean_object* v___x_4823_; 
v___x_4817_ = lean_st_ref_get(v___y_4809_);
v_env_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc_ref(v_env_4818_);
lean_dec(v___x_4817_);
v___x_4819_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4820_ = lean_ctor_get(v___x_4819_, 0);
v_asyncMode_4821_ = lean_ctor_get(v_toEnvExtension_4820_, 2);
v___x_4822_ = 0;
v___x_4823_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4804_, v___x_4819_, v_env_4818_, v_thmName_4802_, v_asyncMode_4821_, v___x_4822_);
if (lean_obj_tag(v___x_4823_) == 1)
{
lean_object* v_val_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4836_; 
v_val_4824_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4826_ = v___x_4823_;
v_isShared_4827_ = v_isSharedCheck_4836_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_val_4824_);
lean_dec(v___x_4823_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4836_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4828_; lean_object* v___x_4830_; 
v___x_4828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4828_, 0, v_a_4813_);
lean_ctor_set(v___x_4828_, 1, v___x_4811_);
lean_ctor_set(v___x_4828_, 2, v_val_4824_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v___x_4828_);
v___x_4830_ = v___x_4826_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4831_; lean_object* v___x_4833_; 
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v___x_4831_);
v___x_4833_ = v___x_4815_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4831_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
else
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
lean_dec(v___x_4823_);
lean_del_object(v___x_4815_);
lean_dec(v_a_4813_);
lean_dec_ref(v___x_4811_);
v___x_4837_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1);
v___x_4838_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4837_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4847_; 
v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4841_ = v___x_4838_;
v_isShared_4842_ = v_isSharedCheck_4847_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4838_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4847_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4843_; lean_object* v___x_4845_; 
v___x_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4843_, 0, v_a_4839_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set(v___x_4841_, 0, v___x_4843_);
v___x_4845_ = v___x_4841_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4843_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
v_a_4848_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4838_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4838_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_dec_ref(v___x_4811_);
lean_dec_ref(v___x_4804_);
lean_dec(v_thmName_4802_);
v_a_4857_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4812_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4812_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* v_thmName_4865_, lean_object* v_levels_4866_, lean_object* v___x_4867_, lean_object* v_____r_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4865_, v_levels_4866_, v___x_4867_, v_____r_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
return v_res_4874_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0(void){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l_Array_instInhabited(lean_box(0));
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* v_declName_4876_, lean_object* v_levels_4877_, lean_object* v_numArgs_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v___y_4885_; uint8_t v___y_4886_; lean_object* v_a_4891_; lean_object* v___y_4895_; lean_object* v___x_4906_; lean_object* v_env_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v_suffix_4911_; lean_object* v_thmName_4912_; uint8_t v___x_4913_; 
v___x_4906_ = lean_st_ref_get(v_a_4882_);
v_env_4907_ = lean_ctor_get(v___x_4906_, 0);
lean_inc_ref(v_env_4907_);
lean_dec(v___x_4906_);
v___x_4908_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_4909_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4910_ = l_Nat_reprFast(v_numArgs_4878_);
v_suffix_4911_ = lean_string_append(v___x_4909_, v___x_4910_);
lean_dec_ref(v___x_4910_);
v_thmName_4912_ = l_Lean_Name_str___override(v_declName_4876_, v_suffix_4911_);
v___x_4913_ = l_Lean_Environment_containsOnBranch(v_env_4907_, v_thmName_4912_);
lean_dec_ref(v_env_4907_);
if (v___x_4913_ == 0)
{
lean_object* v___x_4914_; 
lean_inc(v_thmName_4912_);
v___x_4914_ = l_Lean_executeReservedNameAction(v_thmName_4912_, v_a_4881_, v_a_4882_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v___x_4915_; lean_object* v___x_4916_; 
lean_dec_ref_known(v___x_4914_, 1);
v___x_4915_ = lean_box(0);
v___x_4916_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4912_, v_levels_4877_, v___x_4908_, v___x_4915_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
v___y_4895_ = v___x_4916_;
goto v___jp_4894_;
}
else
{
lean_object* v_a_4917_; 
lean_dec(v_thmName_4912_);
lean_dec(v_levels_4877_);
v_a_4917_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4917_);
lean_dec_ref_known(v___x_4914_, 1);
v_a_4891_ = v_a_4917_;
goto v___jp_4890_;
}
}
else
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = lean_box(0);
v___x_4919_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4912_, v_levels_4877_, v___x_4908_, v___x_4918_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
v___y_4895_ = v___x_4919_;
goto v___jp_4894_;
}
v___jp_4884_:
{
if (v___y_4886_ == 0)
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
lean_dec_ref(v___y_4885_);
v___x_4887_ = lean_box(0);
v___x_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4887_);
return v___x_4888_;
}
else
{
lean_object* v___x_4889_; 
v___x_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4889_, 0, v___y_4885_);
return v___x_4889_;
}
}
v___jp_4890_:
{
uint8_t v___x_4892_; 
v___x_4892_ = l_Lean_Exception_isInterrupt(v_a_4891_);
if (v___x_4892_ == 0)
{
uint8_t v___x_4893_; 
lean_inc_ref(v_a_4891_);
v___x_4893_ = l_Lean_Exception_isRuntime(v_a_4891_);
v___y_4885_ = v_a_4891_;
v___y_4886_ = v___x_4893_;
goto v___jp_4884_;
}
else
{
v___y_4885_ = v_a_4891_;
v___y_4886_ = v___x_4892_;
goto v___jp_4884_;
}
}
v___jp_4894_:
{
if (lean_obj_tag(v___y_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4904_; 
v_a_4896_ = lean_ctor_get(v___y_4895_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___y_4895_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4898_ = v___y_4895_;
v_isShared_4899_ = v_isSharedCheck_4904_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___y_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4904_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v_a_4900_; lean_object* v___x_4902_; 
v_a_4900_ = lean_ctor_get(v_a_4896_, 0);
lean_inc(v_a_4900_);
lean_dec(v_a_4896_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v_a_4900_);
v___x_4902_ = v___x_4898_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4900_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
else
{
lean_object* v_a_4905_; 
v_a_4905_ = lean_ctor_get(v___y_4895_, 0);
lean_inc(v_a_4905_);
lean_dec_ref_known(v___y_4895_, 1);
v_a_4891_ = v_a_4905_;
goto v___jp_4890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object* v_declName_4920_, lean_object* v_levels_4921_, lean_object* v_numArgs_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_4920_, v_levels_4921_, v_numArgs_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* v_____r_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4937_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0));
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* v_____r_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
return v_res_4945_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4947_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4948_ = lean_unsigned_to_nat(8u);
v___x_4949_ = lean_unsigned_to_nat(478u);
v___x_4950_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0));
v___x_4951_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4952_ = l_mkPanicMessageWithDecl(v___x_4951_, v___x_4950_, v___x_4949_, v___x_4948_, v___x_4947_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object* v_thmName_4953_, lean_object* v_levels_4954_, lean_object* v___x_4955_, lean_object* v_____r_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
lean_inc(v_thmName_4953_);
v___x_4962_ = l_Lean_mkConst(v_thmName_4953_, v_levels_4954_);
lean_inc(v___y_4960_);
lean_inc_ref(v___y_4959_);
lean_inc(v___y_4958_);
lean_inc_ref(v___y_4957_);
lean_inc_ref(v___x_4962_);
v___x_4963_ = lean_infer_type(v___x_4962_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_5007_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_4966_ = v___x_4963_;
v_isShared_4967_ = v_isSharedCheck_5007_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4963_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_5007_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4968_; lean_object* v_env_4969_; lean_object* v___x_4970_; lean_object* v_toEnvExtension_4971_; lean_object* v_asyncMode_4972_; uint8_t v___x_4973_; lean_object* v___x_4974_; 
v___x_4968_ = lean_st_ref_get(v___y_4960_);
v_env_4969_ = lean_ctor_get(v___x_4968_, 0);
lean_inc_ref(v_env_4969_);
lean_dec(v___x_4968_);
v___x_4970_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4971_ = lean_ctor_get(v___x_4970_, 0);
v_asyncMode_4972_ = lean_ctor_get(v_toEnvExtension_4971_, 2);
v___x_4973_ = 0;
v___x_4974_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4955_, v___x_4970_, v_env_4969_, v_thmName_4953_, v_asyncMode_4972_, v___x_4973_);
if (lean_obj_tag(v___x_4974_) == 1)
{
lean_object* v_val_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4987_; 
v_val_4975_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4977_ = v___x_4974_;
v_isShared_4978_ = v_isSharedCheck_4987_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_val_4975_);
lean_dec(v___x_4974_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4987_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4979_; lean_object* v___x_4981_; 
v___x_4979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4979_, 0, v_a_4964_);
lean_ctor_set(v___x_4979_, 1, v___x_4962_);
lean_ctor_set(v___x_4979_, 2, v_val_4975_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 0, v___x_4979_);
v___x_4981_ = v___x_4977_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v___x_4979_);
v___x_4981_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4981_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v___x_4982_);
v___x_4984_ = v___x_4966_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
else
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
lean_dec(v___x_4974_);
lean_del_object(v___x_4966_);
lean_dec(v_a_4964_);
lean_dec_ref(v___x_4962_);
v___x_4988_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1);
v___x_4989_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4988_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4998_; 
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4992_ = v___x_4989_;
v_isShared_4993_ = v_isSharedCheck_4998_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4989_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4998_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4994_; lean_object* v___x_4996_; 
v___x_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4994_, 0, v_a_4990_);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v___x_4994_);
v___x_4996_ = v___x_4992_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4994_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
v_a_4999_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4989_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4989_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_dec_ref(v___x_4962_);
lean_dec_ref(v___x_4955_);
lean_dec(v_thmName_4953_);
v_a_5008_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4963_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4963_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object* v_thmName_5016_, lean_object* v_levels_5017_, lean_object* v___x_5018_, lean_object* v_____r_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5016_, v_levels_5017_, v___x_5018_, v_____r_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
return v_res_5025_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1(void){
_start:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5027_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0));
v___x_5028_ = l_Lean_stringToMessageData(v___x_5027_);
return v___x_5028_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3(void){
_start:
{
lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5030_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2));
v___x_5031_ = l_Lean_stringToMessageData(v___x_5030_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* v_declName_5032_, lean_object* v_levels_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v_a_5040_; lean_object* v___y_5058_; lean_object* v___x_5060_; lean_object* v_env_5061_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v_thmName_5067_; lean_object* v___y_5069_; uint8_t v___y_5070_; lean_object* v_a_5097_; lean_object* v___y_5101_; uint8_t v___x_5104_; 
v___x_5060_ = lean_st_ref_get(v_a_5037_);
v_env_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc_ref(v_env_5061_);
lean_dec(v___x_5060_);
v___x_5065_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_5066_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v_thmName_5067_ = l_Lean_Name_str___override(v_declName_5032_, v___x_5066_);
v___x_5104_ = l_Lean_Environment_containsOnBranch(v_env_5061_, v_thmName_5067_);
lean_dec_ref(v_env_5061_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; 
lean_inc(v_thmName_5067_);
v___x_5105_ = l_Lean_executeReservedNameAction(v_thmName_5067_, v_a_5036_, v_a_5037_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
lean_dec_ref_known(v___x_5105_, 1);
v___x_5106_ = lean_box(0);
lean_inc(v_thmName_5067_);
v___x_5107_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5067_, v_levels_5033_, v___x_5065_, v___x_5106_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
v___y_5101_ = v___x_5107_;
goto v___jp_5100_;
}
else
{
lean_object* v_a_5108_; 
lean_dec(v_levels_5033_);
v_a_5108_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5108_);
lean_dec_ref_known(v___x_5105_, 1);
v_a_5097_ = v_a_5108_;
goto v___jp_5096_;
}
}
else
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = lean_box(0);
lean_inc(v_thmName_5067_);
v___x_5110_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5067_, v_levels_5033_, v___x_5065_, v___x_5109_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
v___y_5101_ = v___x_5110_;
goto v___jp_5100_;
}
v___jp_5039_:
{
if (lean_obj_tag(v_a_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
v_a_5041_ = lean_ctor_get(v_a_5040_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v_a_5040_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v_a_5040_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v_a_5040_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
else
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5056_; 
v_a_5049_ = lean_ctor_get(v_a_5040_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v_a_5040_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5051_ = v_a_5040_;
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v_a_5040_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5054_; 
if (v_isShared_5052_ == 0)
{
lean_ctor_set_tag(v___x_5051_, 0);
v___x_5054_ = v___x_5051_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_a_5049_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
v___jp_5057_:
{
lean_object* v_a_5059_; 
v_a_5059_ = lean_ctor_get(v___y_5058_, 0);
lean_inc(v_a_5059_);
lean_dec_ref(v___y_5058_);
v_a_5040_ = v_a_5059_;
goto v___jp_5039_;
}
v___jp_5062_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_box(0);
v___x_5064_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v___x_5063_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
v___y_5058_ = v___x_5064_;
goto v___jp_5057_;
}
v___jp_5068_:
{
if (v___y_5070_ == 0)
{
lean_object* v_options_5071_; uint8_t v_hasTrace_5072_; 
v_options_5071_ = lean_ctor_get(v_a_5036_, 2);
v_hasTrace_5072_ = lean_ctor_get_uint8(v_options_5071_, sizeof(void*)*1);
if (v_hasTrace_5072_ == 0)
{
lean_dec_ref(v___y_5069_);
lean_dec(v_thmName_5067_);
goto v___jp_5062_;
}
else
{
lean_object* v_inheritedTraceOptions_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; uint8_t v___x_5076_; 
v_inheritedTraceOptions_5073_ = lean_ctor_get(v_a_5036_, 13);
v___x_5074_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_5075_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_5076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5073_, v_options_5071_, v___x_5075_);
if (v___x_5076_ == 0)
{
lean_dec_ref(v___y_5069_);
lean_dec(v_thmName_5067_);
goto v___jp_5062_;
}
else
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5077_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1);
v___x_5078_ = l_Lean_MessageData_ofName(v_thmName_5067_);
v___x_5079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5079_, 0, v___x_5077_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
v___x_5080_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3);
v___x_5081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5079_);
lean_ctor_set(v___x_5081_, 1, v___x_5080_);
v___x_5082_ = l_Lean_Exception_toMessageData(v___y_5069_);
v___x_5083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5083_, 0, v___x_5081_);
lean_ctor_set(v___x_5083_, 1, v___x_5082_);
v___x_5084_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_5074_, v___x_5083_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5086_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___x_5084_, 1);
v___x_5086_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_a_5085_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
v___y_5058_ = v___x_5086_;
goto v___jp_5057_;
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
v_a_5087_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5084_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5084_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
}
}
else
{
lean_object* v___x_5095_; 
lean_dec(v_thmName_5067_);
v___x_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5095_, 0, v___y_5069_);
return v___x_5095_;
}
}
v___jp_5096_:
{
uint8_t v___x_5098_; 
v___x_5098_ = l_Lean_Exception_isInterrupt(v_a_5097_);
if (v___x_5098_ == 0)
{
uint8_t v___x_5099_; 
lean_inc_ref(v_a_5097_);
v___x_5099_ = l_Lean_Exception_isRuntime(v_a_5097_);
v___y_5069_ = v_a_5097_;
v___y_5070_ = v___x_5099_;
goto v___jp_5068_;
}
else
{
v___y_5069_ = v_a_5097_;
v___y_5070_ = v___x_5098_;
goto v___jp_5068_;
}
}
v___jp_5100_:
{
if (lean_obj_tag(v___y_5101_) == 0)
{
lean_object* v_a_5102_; 
lean_dec(v_thmName_5067_);
v_a_5102_ = lean_ctor_get(v___y_5101_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___y_5101_, 1);
v_a_5040_ = v_a_5102_;
goto v___jp_5039_;
}
else
{
lean_object* v_a_5103_; 
v_a_5103_ = lean_ctor_get(v___y_5101_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___y_5101_, 1);
v_a_5097_ = v_a_5103_;
goto v___jp_5096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object* v_declName_5111_, lean_object* v_levels_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_5111_, v_levels_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_);
lean_dec(v_a_5116_);
lean_dec_ref(v_a_5115_);
lean_dec(v_a_5114_);
lean_dec_ref(v_a_5113_);
return v_res_5118_;
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
