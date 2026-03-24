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
uint8_t v___x_1901__boxed_722_; lean_object* v_res_723_; 
v___x_1901__boxed_722_ = lean_unbox(v___x_712_);
v_res_723_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(v___x_710_, v___x_711_, v___x_1901__boxed_722_, v___x_713_, v___x_714_, v_a_715_, v_type_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
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
uint8_t v___x_1957__boxed_806_; lean_object* v_res_807_; 
v___x_1957__boxed_806_ = lean_unbox(v___x_797_);
v_res_807_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(v_type_793_, v_motive_794_, v___x_795_, v_b_796_, v___x_1957__boxed_806_, v___x_798_, v_a_799_, v_eqPr_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
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
uint8_t v___x_1916__boxed_844_; lean_object* v_res_845_; 
v___x_1916__boxed_844_ = lean_unbox(v___x_835_);
v_res_845_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(v___x_830_, v___x_831_, v_type_832_, v_a_833_, v___x_834_, v___x_1916__boxed_844_, v___x_836_, v_b_837_, v_motive_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
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
lean_dec_ref(v___x_1036_);
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
uint8_t v___x_4883__boxed_1100_; uint8_t v___x_4884__boxed_1101_; lean_object* v_res_1102_; 
v___x_4883__boxed_1100_ = lean_unbox(v___x_1091_);
v___x_4884__boxed_1101_ = lean_unbox(v___x_1092_);
v_res_1102_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1088_, v_xs_1089_, v_f_1090_, v___x_4883__boxed_1100_, v___x_4884__boxed_1101_, v_eqs_1093_, v_argKinds_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
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
lean_dec_ref(v___y_1163_);
return v___x_1197_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
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
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
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
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
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
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
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
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
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
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
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
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
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
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
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
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
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
uint8_t v___x_662__boxed_1576_; size_t v_sz_boxed_1577_; size_t v_i_boxed_1578_; lean_object* v_res_1579_; 
v___x_662__boxed_1576_ = lean_unbox(v___x_1571_);
v_sz_boxed_1577_ = lean_unbox_usize(v_sz_1573_);
lean_dec(v_sz_1573_);
v_i_boxed_1578_ = lean_unbox_usize(v_i_1574_);
lean_dec(v_i_1574_);
v_res_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1570_, v___x_662__boxed_1576_, v_as_1572_, v_sz_boxed_1577_, v_i_boxed_1578_, v_b_1575_);
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
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
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
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
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
uint8_t v___x_5663__boxed_1718_; lean_object* v_res_1719_; 
v___x_5663__boxed_1718_ = lean_unbox(v___x_1711_);
v_res_1719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1706_, v_val_1707_, v_xs_1708_, v___x_1709_, v___x_1710_, v___x_5663__boxed_1718_, v_a_1712_, v_b_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec_ref(v___y_1714_);
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
uint8_t v___x_5750__boxed_1765_; lean_object* v_res_1766_; 
v___x_5750__boxed_1765_ = lean_unbox(v___x_1757_);
v_res_1766_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1755_, v_induct_1756_, v___x_5750__boxed_1765_, v_xs_1758_, v_x_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
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
lean_object* v_fileName_1908_; lean_object* v_fileMap_1909_; lean_object* v_options_1910_; lean_object* v_currRecDepth_1911_; lean_object* v_maxRecDepth_1912_; lean_object* v_ref_1913_; lean_object* v_currNamespace_1914_; lean_object* v_openDecls_1915_; lean_object* v_initHeartbeats_1916_; lean_object* v_maxHeartbeats_1917_; lean_object* v_quotContext_1918_; lean_object* v_currMacroScope_1919_; uint8_t v_diag_1920_; lean_object* v_cancelTk_x3f_1921_; uint8_t v_suppressElabErrors_1922_; lean_object* v_inheritedTraceOptions_1923_; lean_object* v_ref_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
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
v_ref_1924_ = l_Lean_replaceRef(v_ref_1901_, v_ref_1913_);
lean_inc_ref(v_inheritedTraceOptions_1923_);
lean_inc(v_cancelTk_x3f_1921_);
lean_inc(v_currMacroScope_1919_);
lean_inc(v_quotContext_1918_);
lean_inc(v_maxHeartbeats_1917_);
lean_inc(v_initHeartbeats_1916_);
lean_inc(v_openDecls_1915_);
lean_inc(v_currNamespace_1914_);
lean_inc(v_maxRecDepth_1912_);
lean_inc(v_currRecDepth_1911_);
lean_inc_ref(v_options_1910_);
lean_inc_ref(v_fileMap_1909_);
lean_inc_ref(v_fileName_1908_);
v___x_1925_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1925_, 0, v_fileName_1908_);
lean_ctor_set(v___x_1925_, 1, v_fileMap_1909_);
lean_ctor_set(v___x_1925_, 2, v_options_1910_);
lean_ctor_set(v___x_1925_, 3, v_currRecDepth_1911_);
lean_ctor_set(v___x_1925_, 4, v_maxRecDepth_1912_);
lean_ctor_set(v___x_1925_, 5, v_ref_1924_);
lean_ctor_set(v___x_1925_, 6, v_currNamespace_1914_);
lean_ctor_set(v___x_1925_, 7, v_openDecls_1915_);
lean_ctor_set(v___x_1925_, 8, v_initHeartbeats_1916_);
lean_ctor_set(v___x_1925_, 9, v_maxHeartbeats_1917_);
lean_ctor_set(v___x_1925_, 10, v_quotContext_1918_);
lean_ctor_set(v___x_1925_, 11, v_currMacroScope_1919_);
lean_ctor_set(v___x_1925_, 12, v_cancelTk_x3f_1921_);
lean_ctor_set(v___x_1925_, 13, v_inheritedTraceOptions_1923_);
lean_ctor_set_uint8(v___x_1925_, sizeof(void*)*14, v_diag_1920_);
lean_ctor_set_uint8(v___x_1925_, sizeof(void*)*14 + 1, v_suppressElabErrors_1922_);
v___x_1926_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1902_, v___y_1903_, v___y_1904_, v___x_1925_, v___y_1906_);
lean_dec_ref(v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1927_, lean_object* v_msg_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1927_, v_msg_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v_ref_1927_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1935_, lean_object* v_msg_1936_, lean_object* v_declHint_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_a_1944_; lean_object* v___x_1945_; 
v___x_1943_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1936_, v_declHint_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1935_, v_a_1944_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1946_, lean_object* v_msg_1947_, lean_object* v_declHint_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1946_, v_msg_1947_, v_declHint_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v_ref_1946_);
return v_res_1954_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1957_ = l_Lean_stringToMessageData(v___x_1956_);
return v___x_1957_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1960_ = l_Lean_stringToMessageData(v___x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1961_, lean_object* v_constName_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1968_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1969_ = 0;
lean_inc(v_constName_1962_);
v___x_1970_ = l_Lean_MessageData_ofConstName(v_constName_1962_, v___x_1969_);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1968_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1961_, v___x_1973_, v_constName_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1975_, lean_object* v_constName_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1975_, v_constName_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v_ref_1975_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_ref_1989_; lean_object* v___x_1990_; 
v_ref_1989_ = lean_ctor_get(v___y_1986_, 5);
v___x_1990_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1989_, v_constName_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; lean_object* v_env_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; 
v___x_2004_ = lean_st_ref_get(v___y_2002_);
v_env_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_ref(v_env_2005_);
lean_dec(v___x_2004_);
v___x_2006_ = 0;
lean_inc(v_constName_1998_);
v___x_2007_ = l_Lean_Environment_find_x3f(v_env_2005_, v_constName_1998_, v___x_2006_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
return v___x_2008_;
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_constName_1998_);
v_val_2009_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2007_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_dec(v___x_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 0);
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_val_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
if (lean_obj_tag(v_f_2024_) == 4)
{
lean_object* v_declName_2030_; lean_object* v___x_2031_; 
v_declName_2030_ = lean_ctor_get(v_f_2024_, 0);
lean_inc(v_declName_2030_);
lean_dec_ref(v_f_2024_);
v___x_2031_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2030_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2055_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2055_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2055_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
if (lean_obj_tag(v_a_2032_) == 6)
{
lean_object* v_val_2036_; lean_object* v___x_2037_; lean_object* v_env_2038_; lean_object* v_toConstantVal_2039_; lean_object* v_induct_2040_; uint8_t v___x_2041_; 
v_val_2036_ = lean_ctor_get(v_a_2032_, 0);
lean_inc_ref(v_val_2036_);
lean_dec_ref(v_a_2032_);
v___x_2037_ = lean_st_ref_get(v_a_2028_);
v_env_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_ref(v_env_2038_);
lean_dec(v___x_2037_);
v_toConstantVal_2039_ = lean_ctor_get(v_val_2036_, 0);
v_induct_2040_ = lean_ctor_get(v_val_2036_, 1);
lean_inc(v_induct_2040_);
lean_inc(v_induct_2040_);
v___x_2041_ = lean_is_class(v_env_2038_, v_induct_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
lean_dec(v_induct_2040_);
lean_dec_ref(v_val_2036_);
v___x_2042_ = lean_box(0);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2042_);
v___x_2044_ = v___x_2034_;
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
else
{
lean_object* v_type_2046_; lean_object* v___x_2047_; lean_object* v___f_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; 
lean_del_object(v___x_2034_);
v_type_2046_ = lean_ctor_get(v_toConstantVal_2039_, 2);
lean_inc_ref(v_type_2046_);
v___x_2047_ = lean_box(v___x_2041_);
v___f_2048_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2048_, 0, v_val_2036_);
lean_closure_set(v___f_2048_, 1, v_induct_2040_);
lean_closure_set(v___f_2048_, 2, v___x_2047_);
v___x_2049_ = 0;
v___x_2050_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2046_, v___f_2048_, v___x_2041_, v___x_2049_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
return v___x_2050_;
}
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
lean_dec(v_a_2032_);
v___x_2051_ = lean_box(0);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2051_);
v___x_2053_ = v___x_2034_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
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
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_a_2056_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2031_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2031_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec_ref(v_f_2024_);
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2073_, lean_object* v_val_2074_, lean_object* v_xs_2075_, lean_object* v___x_2076_, lean_object* v___x_2077_, uint8_t v___x_2078_, lean_object* v_inst_2079_, lean_object* v_R_2080_, lean_object* v_a_2081_, lean_object* v_b_2082_, lean_object* v_c_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2073_, v_val_2074_, v_xs_2075_, v___x_2076_, v___x_2077_, v___x_2078_, v_a_2081_, v_b_2082_, v___y_2084_, v___y_2086_, v___y_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2090_, lean_object* v_val_2091_, lean_object* v_xs_2092_, lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v_inst_2096_, lean_object* v_R_2097_, lean_object* v_a_2098_, lean_object* v_b_2099_, lean_object* v_c_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v___x_6328__boxed_2106_; lean_object* v_res_2107_; 
v___x_6328__boxed_2106_ = lean_unbox(v___x_2095_);
v_res_2107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2090_, v_val_2091_, v_xs_2092_, v___x_2093_, v___x_2094_, v___x_6328__boxed_2106_, v_inst_2096_, v_R_2097_, v_a_2098_, v_b_2099_, v_c_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_xs_2092_);
lean_dec_ref(v_val_2091_);
lean_dec(v_upperBound_2090_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2108_, lean_object* v_constName_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_constName_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2116_, v_constName_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2124_, lean_object* v_ref_2125_, lean_object* v_constName_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2125_, v_constName_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2133_, lean_object* v_ref_2134_, lean_object* v_constName_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2133_, v_ref_2134_, v_constName_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v_ref_2134_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2142_, lean_object* v_ref_2143_, lean_object* v_msg_2144_, lean_object* v_declHint_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2143_, v_msg_2144_, v_declHint_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2152_, lean_object* v_ref_2153_, lean_object* v_msg_2154_, lean_object* v_declHint_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2152_, v_ref_2153_, v_msg_2154_, v_declHint_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v_ref_2153_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2162_, lean_object* v_declHint_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2162_, v_declHint_2163_, v___y_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2170_, lean_object* v_declHint_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2170_, v_declHint_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2178_, lean_object* v_ref_2179_, lean_object* v_msg_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2179_, v_msg_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2187_, lean_object* v_ref_2188_, lean_object* v_msg_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2187_, v_ref_2188_, v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v_ref_2188_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2196_, lean_object* v_a_2197_, lean_object* v_____r_2198_, lean_object* v_result_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v___x_2205_; 
v___x_2205_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2196_, v_result_2199_, v_a_2197_);
if (v___x_2205_ == 0)
{
uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2206_ = 0;
v___x_2207_ = lean_box(v___x_2206_);
v___x_2208_ = lean_array_push(v_result_2199_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
else
{
uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2211_ = 5;
v___x_2212_ = lean_box(v___x_2211_);
v___x_2213_ = lean_array_push(v_result_2199_, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2216_, lean_object* v_a_2217_, lean_object* v_____r_2218_, lean_object* v_result_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2216_, v_a_2217_, v_____r_2218_, v_result_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v_a_2217_);
lean_dec_ref(v_info_2216_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2226_, lean_object* v_upperBound_2227_, lean_object* v___x_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_b_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_a_2238_; lean_object* v___y_2243_; uint8_t v___x_2262_; 
v___x_2262_ = lean_nat_dec_lt(v_a_2230_, v_upperBound_2227_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; 
lean_dec(v_a_2230_);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v_b_2231_);
return v___x_2263_;
}
else
{
lean_object* v_resultDeps_2264_; uint8_t v___x_2265_; 
v_resultDeps_2264_ = lean_ctor_get(v_info_2226_, 1);
v___x_2265_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2264_, v_a_2230_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; uint8_t v_isProp_2267_; 
v___x_2266_ = lean_array_fget_borrowed(v___x_2228_, v_a_2230_);
v_isProp_2267_ = lean_ctor_get_uint8(v___x_2266_, sizeof(void*)*1 + 2);
if (v_isProp_2267_ == 0)
{
uint8_t v_isInstance_2268_; 
v_isInstance_2268_ = lean_ctor_get_uint8(v___x_2266_, sizeof(void*)*1 + 4);
if (v_isInstance_2268_ == 0)
{
uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = 2;
v___x_2270_ = lean_box(v___x_2269_);
v___x_2271_ = lean_array_push(v_b_2231_, v___x_2270_);
v_a_2238_ = v___x_2271_;
goto v___jp_2237_;
}
else
{
if (lean_obj_tag(v_a_2229_) == 1)
{
lean_object* v_val_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_val_2272_ = lean_ctor_get(v_a_2229_, 0);
v___x_2273_ = lean_array_get_size(v_val_2272_);
v___x_2274_ = lean_nat_dec_lt(v_a_2230_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2226_, v_a_2230_, v___x_2275_, v_b_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
v___y_2243_ = v___x_2276_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_array_fget_borrowed(v_val_2272_, v_a_2230_);
v___x_2278_ = lean_unbox(v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2226_, v_a_2230_, v___x_2279_, v_b_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
v___y_2243_ = v___x_2280_;
goto v___jp_2242_;
}
else
{
uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = 2;
v___x_2282_ = lean_box(v___x_2281_);
v___x_2283_ = lean_array_push(v_b_2231_, v___x_2282_);
v_a_2238_ = v___x_2283_;
goto v___jp_2237_;
}
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2226_, v_a_2230_, v___x_2284_, v_b_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
v___y_2243_ = v___x_2285_;
goto v___jp_2242_;
}
}
}
else
{
uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = 3;
v___x_2287_ = lean_box(v___x_2286_);
v___x_2288_ = lean_array_push(v_b_2231_, v___x_2287_);
v_a_2238_ = v___x_2288_;
goto v___jp_2237_;
}
}
else
{
uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = 0;
v___x_2290_ = lean_box(v___x_2289_);
v___x_2291_ = lean_array_push(v_b_2231_, v___x_2290_);
v_a_2238_ = v___x_2291_;
goto v___jp_2237_;
}
}
v___jp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_add(v_a_2230_, v___x_2239_);
lean_dec(v_a_2230_);
v_a_2230_ = v___x_2240_;
v_b_2231_ = v_a_2238_;
goto _start;
}
v___jp_2242_:
{
if (lean_obj_tag(v___y_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2253_; 
v_a_2244_ = lean_ctor_get(v___y_2243_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___y_2243_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2246_ = v___y_2243_;
v_isShared_2247_ = v_isSharedCheck_2253_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___y_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2253_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
if (lean_obj_tag(v_a_2244_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; 
lean_dec(v_a_2230_);
v_a_2248_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v_a_2244_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_a_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_object* v_a_2252_; 
lean_del_object(v___x_2246_);
v_a_2252_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v_a_2244_);
v_a_2238_ = v_a_2252_;
goto v___jp_2237_;
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2230_);
v_a_2254_ = lean_ctor_get(v___y_2243_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___y_2243_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___y_2243_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___y_2243_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2292_, lean_object* v_upperBound_2293_, lean_object* v___x_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_b_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2292_, v_upperBound_2293_, v___x_2294_, v_a_2295_, v_a_2296_, v_b_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v_a_2295_);
lean_dec_ref(v___x_2294_);
lean_dec(v_upperBound_2293_);
lean_dec_ref(v_info_2292_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2306_, lean_object* v_info_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2306_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v_paramInfo_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v_result_2318_; lean_object* v___x_2319_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
v_paramInfo_2315_ = lean_ctor_get(v_info_2307_, 0);
v___x_2316_ = lean_array_get_size(v_paramInfo_2315_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v_result_2318_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2319_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2307_, v___x_2316_, v_paramInfo_2315_, v_a_2314_, v___x_2317_, v_result_2318_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
lean_dec(v_a_2314_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2328_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2324_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2307_, v_a_2320_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2324_);
v___x_2326_ = v___x_2322_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
return v___x_2319_;
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
v_a_2329_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2313_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2313_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2337_, lean_object* v_info_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_Meta_getCongrSimpKinds(v_f_2337_, v_info_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec_ref(v_info_2338_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2345_, lean_object* v_upperBound_2346_, lean_object* v___x_2347_, lean_object* v_a_2348_, lean_object* v_inst_2349_, lean_object* v_R_2350_, lean_object* v_a_2351_, lean_object* v_b_2352_, lean_object* v_c_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2345_, v_upperBound_2346_, v___x_2347_, v_a_2348_, v_a_2351_, v_b_2352_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2360_, lean_object* v_upperBound_2361_, lean_object* v___x_2362_, lean_object* v_a_2363_, lean_object* v_inst_2364_, lean_object* v_R_2365_, lean_object* v_a_2366_, lean_object* v_b_2367_, lean_object* v_c_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2360_, v_upperBound_2361_, v___x_2362_, v_a_2363_, v_inst_2364_, v_R_2365_, v_a_2366_, v_b_2367_, v_c_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v_a_2363_);
lean_dec_ref(v___x_2362_);
lean_dec(v_upperBound_2361_);
lean_dec_ref(v_info_2360_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2375_, lean_object* v_info_2376_, lean_object* v___x_2377_, lean_object* v_a_2378_, lean_object* v_b_2379_){
_start:
{
lean_object* v_a_2382_; uint8_t v___x_2386_; 
v___x_2386_ = lean_nat_dec_lt(v_a_2378_, v_upperBound_2375_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
lean_dec(v_a_2378_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_b_2379_);
return v___x_2387_;
}
else
{
lean_object* v_resultDeps_2388_; uint8_t v___x_2389_; 
v_resultDeps_2388_ = lean_ctor_get(v_info_2376_, 1);
v___x_2389_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2388_, v_a_2378_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = lean_nat_dec_eq(v_a_2378_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; uint8_t v_isProp_2393_; 
v___x_2392_ = lean_array_fget_borrowed(v___x_2377_, v_a_2378_);
v_isProp_2393_ = lean_ctor_get_uint8(v___x_2392_, sizeof(void*)*1 + 2);
if (v_isProp_2393_ == 0)
{
uint8_t v_isInstance_2394_; 
v_isInstance_2394_ = lean_ctor_get_uint8(v___x_2392_, sizeof(void*)*1 + 4);
if (v_isInstance_2394_ == 0)
{
uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = 0;
v___x_2396_ = lean_box(v___x_2395_);
v___x_2397_ = lean_array_push(v_b_2379_, v___x_2396_);
v_a_2382_ = v___x_2397_;
goto v___jp_2381_;
}
else
{
uint8_t v___x_2398_; 
v___x_2398_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2376_, v_b_2379_, v_a_2378_);
if (v___x_2398_ == 0)
{
uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = 0;
v___x_2400_ = lean_box(v___x_2399_);
v___x_2401_ = lean_array_push(v_b_2379_, v___x_2400_);
v_a_2382_ = v___x_2401_;
goto v___jp_2381_;
}
else
{
uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = 5;
v___x_2403_ = lean_box(v___x_2402_);
v___x_2404_ = lean_array_push(v_b_2379_, v___x_2403_);
v_a_2382_ = v___x_2404_;
goto v___jp_2381_;
}
}
}
else
{
uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = 3;
v___x_2406_ = lean_box(v___x_2405_);
v___x_2407_ = lean_array_push(v_b_2379_, v___x_2406_);
v_a_2382_ = v___x_2407_;
goto v___jp_2381_;
}
}
else
{
uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = 2;
v___x_2409_ = lean_box(v___x_2408_);
v___x_2410_ = lean_array_push(v_b_2379_, v___x_2409_);
v_a_2382_ = v___x_2410_;
goto v___jp_2381_;
}
}
else
{
uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = 0;
v___x_2412_ = lean_box(v___x_2411_);
v___x_2413_ = lean_array_push(v_b_2379_, v___x_2412_);
v_a_2382_ = v___x_2413_;
goto v___jp_2381_;
}
}
v___jp_2381_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_unsigned_to_nat(1u);
v___x_2384_ = lean_nat_add(v_a_2378_, v___x_2383_);
lean_dec(v_a_2378_);
v_a_2378_ = v___x_2384_;
v_b_2379_ = v_a_2382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2414_, lean_object* v_info_2415_, lean_object* v___x_2416_, lean_object* v_a_2417_, lean_object* v_b_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2414_, v_info_2415_, v___x_2416_, v_a_2417_, v_b_2418_);
lean_dec_ref(v___x_2416_);
lean_dec_ref(v_info_2415_);
lean_dec(v_upperBound_2414_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_paramInfo_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_result_2430_; lean_object* v___x_2431_; 
v_paramInfo_2427_ = lean_ctor_get(v_info_2421_, 0);
v___x_2428_ = lean_array_get_size(v_paramInfo_2427_);
v___x_2429_ = lean_unsigned_to_nat(0u);
v_result_2430_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2431_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2428_, v_info_2421_, v_paramInfo_2427_, v___x_2429_, v_result_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2440_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2421_, v_a_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2436_);
v___x_2438_ = v___x_2434_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
else
{
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec_ref(v_info_2441_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2448_, lean_object* v_info_2449_, lean_object* v___x_2450_, lean_object* v_inst_2451_, lean_object* v_R_2452_, lean_object* v_a_2453_, lean_object* v_b_2454_, lean_object* v_c_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2448_, v_info_2449_, v___x_2450_, v_a_2453_, v_b_2454_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2462_, lean_object* v_info_2463_, lean_object* v___x_2464_, lean_object* v_inst_2465_, lean_object* v_R_2466_, lean_object* v_a_2467_, lean_object* v_b_2468_, lean_object* v_c_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2462_, v_info_2463_, v___x_2464_, v_inst_2465_, v_R_2466_, v_a_2467_, v_b_2468_, v_c_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec_ref(v___x_2464_);
lean_dec_ref(v_info_2463_);
lean_dec(v_upperBound_2462_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(lean_object* v_x_2476_){
_start:
{
if (lean_obj_tag(v_x_2476_) == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_unsigned_to_nat(0u);
return v___x_2477_;
}
else
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_unsigned_to_nat(1u);
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___boxed(lean_object* v_x_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(v_x_2479_);
lean_dec_ref(v_x_2479_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2481_, lean_object* v_k_2482_){
_start:
{
if (lean_obj_tag(v_t_2481_) == 0)
{
lean_object* v_fvarId_2483_; lean_object* v___x_2484_; 
v_fvarId_2483_ = lean_ctor_get(v_t_2481_, 0);
lean_inc(v_fvarId_2483_);
lean_dec_ref(v_t_2481_);
v___x_2484_ = lean_apply_1(v_k_2482_, v_fvarId_2483_);
return v___x_2484_;
}
else
{
lean_object* v_lhs_2485_; lean_object* v_rhs_2486_; lean_object* v___x_2487_; 
v_lhs_2485_ = lean_ctor_get(v_t_2481_, 0);
lean_inc(v_lhs_2485_);
v_rhs_2486_ = lean_ctor_get(v_t_2481_, 1);
lean_inc(v_rhs_2486_);
lean_dec_ref(v_t_2481_);
v___x_2487_ = lean_apply_2(v_k_2482_, v_lhs_2485_, v_rhs_2486_);
return v___x_2487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2488_, lean_object* v_ctorIdx_2489_, lean_object* v_t_2490_, lean_object* v_h_2491_, lean_object* v_k_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2490_, v_k_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2494_, lean_object* v_ctorIdx_2495_, lean_object* v_t_2496_, lean_object* v_h_2497_, lean_object* v_k_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2494_, v_ctorIdx_2495_, v_t_2496_, v_h_2497_, v_k_2498_);
lean_dec(v_ctorIdx_2495_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2500_, lean_object* v_hyp_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2500_, v_hyp_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2503_, lean_object* v_t_2504_, lean_object* v_h_2505_, lean_object* v_hyp_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2504_, v_hyp_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2508_, lean_object* v_decSubsingleton_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2508_, v_decSubsingleton_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2511_, lean_object* v_t_2512_, lean_object* v_h_2513_, lean_object* v_decSubsingleton_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2512_, v_decSubsingleton_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2516_, lean_object* v_fvarId_2517_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2516_, v_fvarId_2517_);
if (lean_obj_tag(v___x_2518_) == 1)
{
lean_object* v_val_2519_; lean_object* v___x_2520_; 
v_val_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_val_2519_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = l_Lean_Expr_fvarId_x21(v_val_2519_);
lean_dec(v_val_2519_);
return v___x_2520_;
}
else
{
lean_dec(v___x_2518_);
lean_inc(v_fvarId_2517_);
return v_fvarId_2517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2521_, lean_object* v_fvarId_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2521_, v_fvarId_2522_);
lean_dec(v_fvarId_2522_);
lean_dec(v_s_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2524_, lean_object* v_x_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2524_, v_x_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2531_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2531_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2548_, lean_object* v_x_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2548_, v_x_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2556_, lean_object* v_mvarId_2557_, lean_object* v_x_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2557_, v_x_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2565_, lean_object* v_mvarId_2566_, lean_object* v_x_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2565_, v_mvarId_2566_, v_x_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v___x_2577_; 
v___x_2577_ = l_Lean_Expr_hasMVar(v_e_2574_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_e_2574_);
return v___x_2578_;
}
else
{
lean_object* v___x_2579_; lean_object* v_mctx_2580_; lean_object* v___x_2581_; lean_object* v_fst_2582_; lean_object* v_snd_2583_; lean_object* v___x_2584_; lean_object* v_cache_2585_; lean_object* v_zetaDeltaFVarIds_2586_; lean_object* v_postponed_2587_; lean_object* v_diag_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2597_; 
v___x_2579_ = lean_st_ref_get(v___y_2575_);
v_mctx_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc_ref(v_mctx_2580_);
lean_dec(v___x_2579_);
v___x_2581_ = l_Lean_instantiateMVarsCore(v_mctx_2580_, v_e_2574_);
v_fst_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_fst_2582_);
v_snd_2583_ = lean_ctor_get(v___x_2581_, 1);
lean_inc(v_snd_2583_);
lean_dec_ref(v___x_2581_);
v___x_2584_ = lean_st_ref_take(v___y_2575_);
v_cache_2585_ = lean_ctor_get(v___x_2584_, 1);
v_zetaDeltaFVarIds_2586_ = lean_ctor_get(v___x_2584_, 2);
v_postponed_2587_ = lean_ctor_get(v___x_2584_, 3);
v_diag_2588_ = lean_ctor_get(v___x_2584_, 4);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v___x_2584_, 0);
lean_dec(v_unused_2598_);
v___x_2590_ = v___x_2584_;
v_isShared_2591_ = v_isSharedCheck_2597_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_diag_2588_);
lean_inc(v_postponed_2587_);
lean_inc(v_zetaDeltaFVarIds_2586_);
lean_inc(v_cache_2585_);
lean_dec(v___x_2584_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2597_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v_snd_2583_);
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_snd_2583_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_cache_2585_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_zetaDeltaFVarIds_2586_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_postponed_2587_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_diag_2588_);
v___x_2593_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_st_ref_set(v___y_2575_, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_fst_2582_);
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2599_, v___y_2600_);
lean_dec(v___y_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2603_, v___y_2605_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v_ks_2621_; lean_object* v_vs_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2646_; 
v_ks_2621_ = lean_ctor_get(v_x_2617_, 0);
v_vs_2622_ = lean_ctor_get(v_x_2617_, 1);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_x_2617_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2624_ = v_x_2617_;
v_isShared_2625_ = v_isSharedCheck_2646_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_vs_2622_);
lean_inc(v_ks_2621_);
lean_dec(v_x_2617_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2646_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = lean_array_get_size(v_ks_2621_);
v___x_2627_ = lean_nat_dec_lt(v_x_2618_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
lean_dec(v_x_2618_);
v___x_2628_ = lean_array_push(v_ks_2621_, v_x_2619_);
v___x_2629_ = lean_array_push(v_vs_2622_, v_x_2620_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v___x_2629_);
lean_ctor_set(v___x_2624_, 0, v___x_2628_);
v___x_2631_ = v___x_2624_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
else
{
lean_object* v_k_x27_2633_; uint8_t v___x_2634_; 
v_k_x27_2633_ = lean_array_fget_borrowed(v_ks_2621_, v_x_2618_);
v___x_2634_ = l_Lean_instBEqMVarId_beq(v_x_2619_, v_k_x27_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2636_; 
if (v_isShared_2625_ == 0)
{
v___x_2636_ = v___x_2624_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_ks_2621_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_vs_2622_);
v___x_2636_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = lean_unsigned_to_nat(1u);
v___x_2638_ = lean_nat_add(v_x_2618_, v___x_2637_);
lean_dec(v_x_2618_);
v_x_2617_ = v___x_2636_;
v_x_2618_ = v___x_2638_;
goto _start;
}
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2641_ = lean_array_fset(v_ks_2621_, v_x_2618_, v_x_2619_);
v___x_2642_ = lean_array_fset(v_vs_2622_, v_x_2618_, v_x_2620_);
lean_dec(v_x_2618_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v___x_2642_);
lean_ctor_set(v___x_2624_, 0, v___x_2641_);
v___x_2644_ = v___x_2624_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2647_, lean_object* v_k_2648_, lean_object* v_v_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_unsigned_to_nat(0u);
v___x_2651_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2647_, v___x_2650_, v_k_2648_, v_v_2649_);
return v___x_2651_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_2652_; size_t v___x_2653_; size_t v___x_2654_; 
v___x_2652_ = ((size_t)5ULL);
v___x_2653_ = ((size_t)1ULL);
v___x_2654_ = lean_usize_shift_left(v___x_2653_, v___x_2652_);
return v___x_2654_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_2655_; size_t v___x_2656_; size_t v___x_2657_; 
v___x_2655_ = ((size_t)1ULL);
v___x_2656_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2657_ = lean_usize_sub(v___x_2656_, v___x_2655_);
return v___x_2657_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2659_, size_t v_x_2660_, size_t v_x_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
if (lean_obj_tag(v_x_2659_) == 0)
{
lean_object* v_es_2664_; size_t v___x_2665_; size_t v___x_2666_; size_t v___x_2667_; size_t v___x_2668_; lean_object* v_j_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_es_2664_ = lean_ctor_get(v_x_2659_, 0);
v___x_2665_ = ((size_t)5ULL);
v___x_2666_ = ((size_t)1ULL);
v___x_2667_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__1);
v___x_2668_ = lean_usize_land(v_x_2660_, v___x_2667_);
v_j_2669_ = lean_usize_to_nat(v___x_2668_);
v___x_2670_ = lean_array_get_size(v_es_2664_);
v___x_2671_ = lean_nat_dec_lt(v_j_2669_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_dec(v_j_2669_);
lean_dec(v_x_2663_);
lean_dec(v_x_2662_);
return v_x_2659_;
}
else
{
lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2708_; 
lean_inc_ref(v_es_2664_);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_x_2659_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v_x_2659_, 0);
lean_dec(v_unused_2709_);
v___x_2673_ = v_x_2659_;
v_isShared_2674_ = v_isSharedCheck_2708_;
goto v_resetjp_2672_;
}
else
{
lean_dec(v_x_2659_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2708_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v_v_2675_; lean_object* v___x_2676_; lean_object* v_xs_x27_2677_; lean_object* v___y_2679_; 
v_v_2675_ = lean_array_fget(v_es_2664_, v_j_2669_);
v___x_2676_ = lean_box(0);
v_xs_x27_2677_ = lean_array_fset(v_es_2664_, v_j_2669_, v___x_2676_);
switch(lean_obj_tag(v_v_2675_))
{
case 0:
{
lean_object* v_key_2684_; lean_object* v_val_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2695_; 
v_key_2684_ = lean_ctor_get(v_v_2675_, 0);
v_val_2685_ = lean_ctor_get(v_v_2675_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_v_2675_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2687_ = v_v_2675_;
v_isShared_2688_ = v_isSharedCheck_2695_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_val_2685_);
lean_inc(v_key_2684_);
lean_dec(v_v_2675_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2695_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
uint8_t v___x_2689_; 
v___x_2689_ = l_Lean_instBEqMVarId_beq(v_x_2662_, v_key_2684_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_del_object(v___x_2687_);
v___x_2690_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2684_, v_val_2685_, v_x_2662_, v_x_2663_);
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
v___y_2679_ = v___x_2691_;
goto v___jp_2678_;
}
else
{
lean_object* v___x_2693_; 
lean_dec(v_val_2685_);
lean_dec(v_key_2684_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v_x_2663_);
lean_ctor_set(v___x_2687_, 0, v_x_2662_);
v___x_2693_ = v___x_2687_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_x_2662_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_x_2663_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
v___y_2679_ = v___x_2693_;
goto v___jp_2678_;
}
}
}
}
case 1:
{
lean_object* v_node_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2706_; 
v_node_2696_ = lean_ctor_get(v_v_2675_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_v_2675_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2698_ = v_v_2675_;
v_isShared_2699_ = v_isSharedCheck_2706_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_node_2696_);
lean_dec(v_v_2675_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2706_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
size_t v___x_2700_; size_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2700_ = lean_usize_shift_right(v_x_2660_, v___x_2665_);
v___x_2701_ = lean_usize_add(v_x_2661_, v___x_2666_);
v___x_2702_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2696_, v___x_2700_, v___x_2701_, v_x_2662_, v_x_2663_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2702_);
v___x_2704_ = v___x_2698_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
v___y_2679_ = v___x_2704_;
goto v___jp_2678_;
}
}
}
default: 
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_x_2662_);
lean_ctor_set(v___x_2707_, 1, v_x_2663_);
v___y_2679_ = v___x_2707_;
goto v___jp_2678_;
}
}
v___jp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = lean_array_fset(v_xs_x27_2677_, v_j_2669_, v___y_2679_);
lean_dec(v_j_2669_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2680_);
v___x_2682_ = v___x_2673_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
else
{
lean_object* v_ks_2710_; lean_object* v_vs_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2731_; 
v_ks_2710_ = lean_ctor_get(v_x_2659_, 0);
v_vs_2711_ = lean_ctor_get(v_x_2659_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_x_2659_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2713_ = v_x_2659_;
v_isShared_2714_ = v_isSharedCheck_2731_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_vs_2711_);
lean_inc(v_ks_2710_);
lean_dec(v_x_2659_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2731_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_ks_2710_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_vs_2711_);
v___x_2716_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v_newNode_2717_; uint8_t v___y_2719_; size_t v___x_2725_; uint8_t v___x_2726_; 
v_newNode_2717_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2716_, v_x_2662_, v_x_2663_);
v___x_2725_ = ((size_t)7ULL);
v___x_2726_ = lean_usize_dec_le(v___x_2725_, v_x_2661_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2727_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2717_);
v___x_2728_ = lean_unsigned_to_nat(4u);
v___x_2729_ = lean_nat_dec_lt(v___x_2727_, v___x_2728_);
lean_dec(v___x_2727_);
v___y_2719_ = v___x_2729_;
goto v___jp_2718_;
}
else
{
v___y_2719_ = v___x_2726_;
goto v___jp_2718_;
}
v___jp_2718_:
{
if (v___y_2719_ == 0)
{
lean_object* v_ks_2720_; lean_object* v_vs_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_ks_2720_ = lean_ctor_get(v_newNode_2717_, 0);
lean_inc_ref(v_ks_2720_);
v_vs_2721_ = lean_ctor_get(v_newNode_2717_, 1);
lean_inc_ref(v_vs_2721_);
lean_dec_ref(v_newNode_2717_);
v___x_2722_ = lean_unsigned_to_nat(0u);
v___x_2723_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__2);
v___x_2724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2661_, v_ks_2720_, v_vs_2721_, v___x_2722_, v___x_2723_);
lean_dec_ref(v_vs_2721_);
lean_dec_ref(v_ks_2720_);
return v___x_2724_;
}
else
{
return v_newNode_2717_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_2732_, lean_object* v_keys_2733_, lean_object* v_vals_2734_, lean_object* v_i_2735_, lean_object* v_entries_2736_){
_start:
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = lean_array_get_size(v_keys_2733_);
v___x_2738_ = lean_nat_dec_lt(v_i_2735_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_dec(v_i_2735_);
return v_entries_2736_;
}
else
{
lean_object* v_k_2739_; lean_object* v_v_2740_; uint64_t v___x_2741_; size_t v_h_2742_; size_t v___x_2743_; lean_object* v___x_2744_; size_t v___x_2745_; size_t v___x_2746_; size_t v___x_2747_; size_t v_h_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_k_2739_ = lean_array_fget_borrowed(v_keys_2733_, v_i_2735_);
v_v_2740_ = lean_array_fget_borrowed(v_vals_2734_, v_i_2735_);
v___x_2741_ = l_Lean_instHashableMVarId_hash(v_k_2739_);
v_h_2742_ = lean_uint64_to_usize(v___x_2741_);
v___x_2743_ = ((size_t)5ULL);
v___x_2744_ = lean_unsigned_to_nat(1u);
v___x_2745_ = ((size_t)1ULL);
v___x_2746_ = lean_usize_sub(v_depth_2732_, v___x_2745_);
v___x_2747_ = lean_usize_mul(v___x_2743_, v___x_2746_);
v_h_2748_ = lean_usize_shift_right(v_h_2742_, v___x_2747_);
v___x_2749_ = lean_nat_add(v_i_2735_, v___x_2744_);
lean_dec(v_i_2735_);
lean_inc(v_v_2740_);
lean_inc(v_k_2739_);
v___x_2750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_2736_, v_h_2748_, v_depth_2732_, v_k_2739_, v_v_2740_);
v_i_2735_ = v___x_2749_;
v_entries_2736_ = v___x_2750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2752_, lean_object* v_keys_2753_, lean_object* v_vals_2754_, lean_object* v_i_2755_, lean_object* v_entries_2756_){
_start:
{
size_t v_depth_boxed_2757_; lean_object* v_res_2758_; 
v_depth_boxed_2757_ = lean_unbox_usize(v_depth_2752_);
lean_dec(v_depth_2752_);
v_res_2758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_2757_, v_keys_2753_, v_vals_2754_, v_i_2755_, v_entries_2756_);
lean_dec_ref(v_vals_2754_);
lean_dec_ref(v_keys_2753_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_2759_, lean_object* v_x_2760_, lean_object* v_x_2761_, lean_object* v_x_2762_, lean_object* v_x_2763_){
_start:
{
size_t v_x_4162__boxed_2764_; size_t v_x_4163__boxed_2765_; lean_object* v_res_2766_; 
v_x_4162__boxed_2764_ = lean_unbox_usize(v_x_2760_);
lean_dec(v_x_2760_);
v_x_4163__boxed_2765_ = lean_unbox_usize(v_x_2761_);
lean_dec(v_x_2761_);
v_res_2766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2759_, v_x_4162__boxed_2764_, v_x_4163__boxed_2765_, v_x_2762_, v_x_2763_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object* v_x_2767_, lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
uint64_t v___x_2770_; size_t v___x_2771_; size_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2770_ = l_Lean_instHashableMVarId_hash(v_x_2768_);
v___x_2771_ = lean_uint64_to_usize(v___x_2770_);
v___x_2772_ = ((size_t)1ULL);
v___x_2773_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2767_, v___x_2771_, v___x_2772_, v_x_2768_, v_x_2769_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object* v_mvarId_2774_, lean_object* v_val_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; lean_object* v_mctx_2779_; lean_object* v_cache_2780_; lean_object* v_zetaDeltaFVarIds_2781_; lean_object* v_postponed_2782_; lean_object* v_diag_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2810_; 
v___x_2778_ = lean_st_ref_take(v___y_2776_);
v_mctx_2779_ = lean_ctor_get(v___x_2778_, 0);
v_cache_2780_ = lean_ctor_get(v___x_2778_, 1);
v_zetaDeltaFVarIds_2781_ = lean_ctor_get(v___x_2778_, 2);
v_postponed_2782_ = lean_ctor_get(v___x_2778_, 3);
v_diag_2783_ = lean_ctor_get(v___x_2778_, 4);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2785_ = v___x_2778_;
v_isShared_2786_ = v_isSharedCheck_2810_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_diag_2783_);
lean_inc(v_postponed_2782_);
lean_inc(v_zetaDeltaFVarIds_2781_);
lean_inc(v_cache_2780_);
lean_inc(v_mctx_2779_);
lean_dec(v___x_2778_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2810_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v_depth_2787_; lean_object* v_levelAssignDepth_2788_; lean_object* v_mvarCounter_2789_; lean_object* v_lDepth_2790_; lean_object* v_decls_2791_; lean_object* v_userNames_2792_; lean_object* v_lAssignment_2793_; lean_object* v_eAssignment_2794_; lean_object* v_dAssignment_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2809_; 
v_depth_2787_ = lean_ctor_get(v_mctx_2779_, 0);
v_levelAssignDepth_2788_ = lean_ctor_get(v_mctx_2779_, 1);
v_mvarCounter_2789_ = lean_ctor_get(v_mctx_2779_, 2);
v_lDepth_2790_ = lean_ctor_get(v_mctx_2779_, 3);
v_decls_2791_ = lean_ctor_get(v_mctx_2779_, 4);
v_userNames_2792_ = lean_ctor_get(v_mctx_2779_, 5);
v_lAssignment_2793_ = lean_ctor_get(v_mctx_2779_, 6);
v_eAssignment_2794_ = lean_ctor_get(v_mctx_2779_, 7);
v_dAssignment_2795_ = lean_ctor_get(v_mctx_2779_, 8);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_mctx_2779_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2797_ = v_mctx_2779_;
v_isShared_2798_ = v_isSharedCheck_2809_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_dAssignment_2795_);
lean_inc(v_eAssignment_2794_);
lean_inc(v_lAssignment_2793_);
lean_inc(v_userNames_2792_);
lean_inc(v_decls_2791_);
lean_inc(v_lDepth_2790_);
lean_inc(v_mvarCounter_2789_);
lean_inc(v_levelAssignDepth_2788_);
lean_inc(v_depth_2787_);
lean_dec(v_mctx_2779_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2809_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2799_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2794_, v_mvarId_2774_, v_val_2775_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 7, v___x_2799_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_depth_2787_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_levelAssignDepth_2788_);
lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_mvarCounter_2789_);
lean_ctor_set(v_reuseFailAlloc_2808_, 3, v_lDepth_2790_);
lean_ctor_set(v_reuseFailAlloc_2808_, 4, v_decls_2791_);
lean_ctor_set(v_reuseFailAlloc_2808_, 5, v_userNames_2792_);
lean_ctor_set(v_reuseFailAlloc_2808_, 6, v_lAssignment_2793_);
lean_ctor_set(v_reuseFailAlloc_2808_, 7, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2808_, 8, v_dAssignment_2795_);
v___x_2801_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2803_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2801_);
v___x_2803_ = v___x_2785_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_cache_2780_);
lean_ctor_set(v_reuseFailAlloc_2807_, 2, v_zetaDeltaFVarIds_2781_);
lean_ctor_set(v_reuseFailAlloc_2807_, 3, v_postponed_2782_);
lean_ctor_set(v_reuseFailAlloc_2807_, 4, v_diag_2783_);
v___x_2803_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = lean_st_ref_set(v___y_2776_, v___x_2803_);
v___x_2805_ = lean_box(0);
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2811_, lean_object* v_val_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2811_, v_val_2812_, v___y_2813_);
lean_dec(v___y_2813_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2824_, lean_object* v_as_2825_, size_t v_sz_2826_, size_t v_i_2827_, lean_object* v_b_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_a_2835_; uint8_t v___x_2839_; 
v___x_2839_ = lean_usize_dec_lt(v_i_2827_, v_sz_2826_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2840_, 0, v_b_2828_);
return v___x_2840_;
}
else
{
lean_object* v_fst_2841_; lean_object* v_snd_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; lean_object* v_a_2845_; 
v_fst_2841_ = lean_ctor_get(v_b_2828_, 0);
lean_inc(v_fst_2841_);
v_snd_2842_ = lean_ctor_get(v_b_2828_, 1);
lean_inc(v_snd_2842_);
lean_dec_ref(v_b_2828_);
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = lean_nat_dec_eq(v___x_2824_, v___x_2843_);
v_a_2845_ = lean_array_uget_borrowed(v_as_2825_, v_i_2827_);
if (lean_obj_tag(v_a_2845_) == 0)
{
lean_object* v_fvarId_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_fvarId_2846_ = lean_ctor_get(v_a_2845_, 0);
v___x_2847_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2842_, v_fvarId_2846_);
v___x_2848_ = l_Lean_Meta_substCore(v_fst_2841_, v___x_2847_, v___x_2839_, v_snd_2842_, v___x_2839_, v___x_2844_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v_fst_2850_; lean_object* v_snd_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref(v___x_2848_);
v_fst_2850_ = lean_ctor_get(v_a_2849_, 0);
v_snd_2851_ = lean_ctor_get(v_a_2849_, 1);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_a_2849_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v_a_2849_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_snd_2851_);
lean_inc(v_fst_2850_);
lean_dec(v_a_2849_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v_fst_2850_);
lean_ctor_set(v___x_2853_, 0, v_snd_2851_);
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_snd_2851_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_fst_2850_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
v_a_2835_ = v___x_2856_;
goto v___jp_2834_;
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
v_a_2859_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2848_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2848_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_lhs_2867_; lean_object* v_rhs_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_lhs_2867_ = lean_ctor_get(v_a_2845_, 0);
v_rhs_2868_ = lean_ctor_get(v_a_2845_, 1);
v___x_2869_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2842_, v_lhs_2867_);
v___x_2870_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2842_, v_rhs_2868_);
v___x_2871_ = l_Lean_mkFVar(v___x_2869_);
v___x_2872_ = l_Lean_mkFVar(v___x_2870_);
lean_inc_ref(v___x_2872_);
lean_inc_ref(v___x_2871_);
v___x_2873_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2873_, 0, v___x_2871_);
lean_closure_set(v___x_2873_, 1, v___x_2872_);
lean_inc(v_fst_2841_);
v___x_2874_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2841_, v___x_2873_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2877_ = lean_unsigned_to_nat(2u);
v___x_2878_ = lean_mk_empty_array_with_capacity(v___x_2877_);
v___x_2879_ = lean_array_push(v___x_2878_, v___x_2871_);
v___x_2880_ = lean_array_push(v___x_2879_, v___x_2872_);
v___x_2881_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2881_, 0, v___x_2876_);
lean_closure_set(v___x_2881_, 1, v___x_2880_);
lean_inc(v_fst_2841_);
v___x_2882_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2841_, v___x_2881_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
v___x_2885_ = l_Lean_MVarId_assert(v_fst_2841_, v___x_2884_, v_a_2875_, v_a_2883_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = l_Lean_Meta_intro1Core(v_a_2886_, v___x_2844_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v_fst_2889_; lean_object* v_snd_2890_; lean_object* v___x_2891_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref(v___x_2887_);
v_fst_2889_ = lean_ctor_get(v_a_2888_, 0);
lean_inc(v_fst_2889_);
v_snd_2890_ = lean_ctor_get(v_a_2888_, 1);
lean_inc(v_snd_2890_);
lean_dec(v_a_2888_);
v___x_2891_ = l_Lean_Meta_substCore(v_snd_2890_, v_fst_2889_, v___x_2839_, v_snd_2842_, v___x_2839_, v___x_2844_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v_fst_2893_; lean_object* v_snd_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
v_fst_2893_ = lean_ctor_get(v_a_2892_, 0);
v_snd_2894_ = lean_ctor_get(v_a_2892_, 1);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_a_2892_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v_a_2892_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_snd_2894_);
lean_inc(v_fst_2893_);
lean_dec(v_a_2892_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 1, v_fst_2893_);
lean_ctor_set(v___x_2896_, 0, v_snd_2894_);
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_snd_2894_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_fst_2893_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
v_a_2835_ = v___x_2899_;
goto v___jp_2834_;
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_a_2902_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2891_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2891_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_snd_2842_);
v_a_2910_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2887_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2887_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_snd_2842_);
v_a_2918_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2885_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2885_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_a_2875_);
lean_dec(v_snd_2842_);
lean_dec(v_fst_2841_);
v_a_2926_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2882_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2882_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v___x_2872_);
lean_dec_ref(v___x_2871_);
lean_dec(v_snd_2842_);
lean_dec(v_fst_2841_);
v_a_2934_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2874_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2874_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
v___jp_2834_:
{
size_t v___x_2836_; size_t v___x_2837_; 
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = lean_usize_add(v_i_2827_, v___x_2836_);
v_i_2827_ = v___x_2837_;
v_b_2828_ = v_a_2835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_2942_, lean_object* v_as_2943_, lean_object* v_sz_2944_, lean_object* v_i_2945_, lean_object* v_b_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
size_t v_sz_boxed_2952_; size_t v_i_boxed_2953_; lean_object* v_res_2954_; 
v_sz_boxed_2952_ = lean_unbox_usize(v_sz_2944_);
lean_dec(v_sz_2944_);
v_i_boxed_2953_ = lean_unbox_usize(v_i_2945_);
lean_dec(v_i_2945_);
v_res_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2942_, v_as_2943_, v_sz_boxed_2952_, v_i_boxed_2953_, v_b_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec_ref(v_as_2943_);
lean_dec(v___x_2942_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_2955_, lean_object* v_as_2956_, size_t v_i_2957_, size_t v_stop_2958_, lean_object* v_b_2959_){
_start:
{
lean_object* v___y_2961_; uint8_t v___x_2965_; 
v___x_2965_ = lean_usize_dec_eq(v_i_2957_, v_stop_2958_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_box(0);
v___x_2967_ = lean_array_uget_borrowed(v_as_2956_, v_i_2957_);
v___x_2968_ = lean_array_get_borrowed(v___x_2966_, v_eqs_2955_, v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
v___y_2961_ = v_b_2959_;
goto v___jp_2960_;
}
else
{
lean_object* v_val_2969_; lean_object* v___x_2970_; 
v_val_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_val_2969_);
v___x_2970_ = lean_array_push(v_b_2959_, v_val_2969_);
v___y_2961_ = v___x_2970_;
goto v___jp_2960_;
}
}
else
{
return v_b_2959_;
}
v___jp_2960_:
{
size_t v___x_2962_; size_t v___x_2963_; 
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_add(v_i_2957_, v___x_2962_);
v_i_2957_ = v___x_2963_;
v_b_2959_ = v___y_2961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_2971_, lean_object* v_as_2972_, lean_object* v_i_2973_, lean_object* v_stop_2974_, lean_object* v_b_2975_){
_start:
{
size_t v_i_boxed_2976_; size_t v_stop_boxed_2977_; lean_object* v_res_2978_; 
v_i_boxed_2976_ = lean_unbox_usize(v_i_2973_);
lean_dec(v_i_2973_);
v_stop_boxed_2977_ = lean_unbox_usize(v_stop_2974_);
lean_dec(v_stop_2974_);
v_res_2978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2971_, v_as_2972_, v_i_boxed_2976_, v_stop_boxed_2977_, v_b_2975_);
lean_dec_ref(v_as_2972_);
lean_dec_ref(v_eqs_2971_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_2981_, lean_object* v_as_2982_, lean_object* v_start_2983_, lean_object* v_stop_2984_){
_start:
{
lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_2986_ = lean_nat_dec_lt(v_start_2983_, v_stop_2984_);
if (v___x_2986_ == 0)
{
return v___x_2985_;
}
else
{
lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2987_ = lean_array_get_size(v_as_2982_);
v___x_2988_ = lean_nat_dec_le(v_stop_2984_, v___x_2987_);
if (v___x_2988_ == 0)
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_nat_dec_lt(v_start_2983_, v___x_2987_);
if (v___x_2989_ == 0)
{
return v___x_2985_;
}
else
{
size_t v___x_2990_; size_t v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_usize_of_nat(v_start_2983_);
v___x_2991_ = lean_usize_of_nat(v___x_2987_);
v___x_2992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2981_, v_as_2982_, v___x_2990_, v___x_2991_, v___x_2985_);
return v___x_2992_;
}
}
else
{
size_t v___x_2993_; size_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2993_ = lean_usize_of_nat(v_start_2983_);
v___x_2994_ = lean_usize_of_nat(v_stop_2984_);
v___x_2995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2981_, v_as_2982_, v___x_2993_, v___x_2994_, v___x_2985_);
return v___x_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_2996_, lean_object* v_as_2997_, lean_object* v_start_2998_, lean_object* v_stop_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2996_, v_as_2997_, v_start_2998_, v_stop_2999_);
lean_dec(v_stop_2999_);
lean_dec(v_start_2998_);
lean_dec_ref(v_as_2997_);
lean_dec_ref(v_eqs_2996_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_3001_, lean_object* v_type_3002_, lean_object* v_deps_3003_, lean_object* v_eqs_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v_eqs_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3010_ = lean_unsigned_to_nat(0u);
v___x_3011_ = lean_array_get_size(v_deps_3003_);
v_eqs_3012_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_3004_, v_deps_3003_, v___x_3010_, v___x_3011_);
v___x_3013_ = lean_array_get_size(v_eqs_3012_);
v___x_3014_ = lean_nat_dec_eq(v___x_3013_, v___x_3010_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_type_3002_);
v___x_3016_ = 0;
v___x_3017_ = lean_box(0);
v___x_3018_ = l_Lean_Meta_mkFreshExprMVar(v___x_3015_, v___x_3016_, v___x_3017_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; size_t v_sz_3023_; size_t v___x_3024_; lean_object* v___x_3025_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref(v___x_3018_);
v___x_3020_ = l_Lean_Expr_mvarId_x21(v_a_3019_);
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v_sz_3023_ = lean_array_size(v_eqs_3012_);
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_3013_, v_eqs_3012_, v_sz_3023_, v___x_3024_, v___x_3022_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_);
lean_dec_ref(v_eqs_3012_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v_fst_3027_; lean_object* v_snd_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3025_);
v_fst_3027_ = lean_ctor_get(v_a_3026_, 0);
lean_inc(v_fst_3027_);
v_snd_3028_ = lean_ctor_get(v_a_3026_, 1);
lean_inc(v_snd_3028_);
lean_dec(v_a_3026_);
v___x_3029_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_3028_, v_fvarId_3001_);
lean_dec(v_fvarId_3001_);
lean_dec(v_snd_3028_);
v___x_3030_ = l_Lean_mkFVar(v___x_3029_);
v___x_3031_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_3027_, v___x_3030_, v_a_3006_);
lean_dec_ref(v___x_3031_);
v___x_3032_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_3019_, v_a_3006_);
return v___x_3032_;
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_a_3019_);
lean_dec(v_fvarId_3001_);
v_a_3033_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3025_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3025_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_dec_ref(v_eqs_3012_);
lean_dec(v_fvarId_3001_);
return v___x_3018_;
}
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_dec_ref(v_eqs_3012_);
lean_dec_ref(v_type_3002_);
v___x_3041_ = l_Lean_mkFVar(v_fvarId_3001_);
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
return v___x_3042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3043_, lean_object* v_type_3044_, lean_object* v_deps_3045_, lean_object* v_eqs_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3043_, v_type_3044_, v_deps_3045_, v_eqs_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec_ref(v_eqs_3046_);
lean_dec_ref(v_deps_3045_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3053_, lean_object* v_val_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3053_, v_val_3054_, v___y_3056_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3061_, lean_object* v_val_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3061_, v_val_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3069_, lean_object* v_x_3070_, lean_object* v_x_3071_, lean_object* v_x_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3070_, v_x_3071_, v_x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3074_, lean_object* v_x_3075_, size_t v_x_3076_, size_t v_x_3077_, lean_object* v_x_3078_, lean_object* v_x_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3075_, v_x_3076_, v_x_3077_, v_x_3078_, v_x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3081_, lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v_x_3084_, lean_object* v_x_3085_, lean_object* v_x_3086_){
_start:
{
size_t v_x_4773__boxed_3087_; size_t v_x_4774__boxed_3088_; lean_object* v_res_3089_; 
v_x_4773__boxed_3087_ = lean_unbox_usize(v_x_3083_);
lean_dec(v_x_3083_);
v_x_4774__boxed_3088_ = lean_unbox_usize(v_x_3084_);
lean_dec(v_x_3084_);
v_res_3089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3081_, v_x_3082_, v_x_4773__boxed_3087_, v_x_4774__boxed_3088_, v_x_3085_, v_x_3086_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3090_, lean_object* v_n_3091_, lean_object* v_k_3092_, lean_object* v_v_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3091_, v_k_3092_, v_v_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3095_, size_t v_depth_3096_, lean_object* v_keys_3097_, lean_object* v_vals_3098_, lean_object* v_heq_3099_, lean_object* v_i_3100_, lean_object* v_entries_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3096_, v_keys_3097_, v_vals_3098_, v_i_3100_, v_entries_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3103_, lean_object* v_depth_3104_, lean_object* v_keys_3105_, lean_object* v_vals_3106_, lean_object* v_heq_3107_, lean_object* v_i_3108_, lean_object* v_entries_3109_){
_start:
{
size_t v_depth_boxed_3110_; lean_object* v_res_3111_; 
v_depth_boxed_3110_ = lean_unbox_usize(v_depth_3104_);
lean_dec(v_depth_3104_);
v_res_3111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3103_, v_depth_boxed_3110_, v_keys_3105_, v_vals_3106_, v_heq_3107_, v_i_3108_, v_entries_3109_);
lean_dec_ref(v_vals_3106_);
lean_dec_ref(v_keys_3105_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_, lean_object* v_x_3115_, lean_object* v_x_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3113_, v_x_3114_, v_x_3115_, v_x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___f_3125_; lean_object* v___x_1803__overap_3126_; lean_object* v___x_3127_; 
v___f_3125_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1803__overap_3126_ = lean_panic_fn(v___f_3125_, v_msg_3119_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
lean_inc_ref(v___y_3120_);
v___x_3127_ = lean_apply_5(v___x_1803__overap_3126_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, lean_box(0));
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
return v_res_3134_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3138_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3139_ = lean_unsigned_to_nat(34u);
v___x_3140_ = lean_unsigned_to_nat(360u);
v___x_3141_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3142_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3143_ = l_mkPanicMessageWithDecl(v___x_3142_, v___x_3141_, v___x_3140_, v___x_3139_, v___x_3138_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3144_, lean_object* v___x_3145_, lean_object* v___x_3146_, lean_object* v_i_3147_, lean_object* v_kinds_3148_, lean_object* v___x_3149_, lean_object* v_lhs_3150_, lean_object* v_rhs_3151_, lean_object* v_type_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
uint8_t v___x_1990__boxed_3158_; uint8_t v___x_1991__boxed_3159_; lean_object* v_res_3160_; 
v___x_1990__boxed_3158_ = lean_unbox(v___x_3145_);
v___x_1991__boxed_3159_ = lean_unbox(v___x_3146_);
v_res_3160_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3144_, v___x_1990__boxed_3158_, v___x_1991__boxed_3159_, v_i_3147_, v_kinds_3148_, v___x_3149_, v_lhs_3150_, v_rhs_3151_, v_type_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3161_, uint8_t v___x_3162_, uint8_t v___x_3163_, lean_object* v_i_3164_, lean_object* v___x_3165_, lean_object* v_kinds_3166_, lean_object* v_typeSub_3167_, lean_object* v_lhs_3168_, lean_object* v_rhs_3169_, lean_object* v_type_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; lean_object* v___x_3178_; 
lean_inc_ref(v_rhs_3169_);
v___x_3176_ = lean_array_push(v___x_3161_, v_rhs_3169_);
v___x_3177_ = 1;
v___x_3178_ = l_Lean_Meta_mkLambdaFVars(v___x_3176_, v_type_3170_, v___x_3162_, v___x_3163_, v___x_3162_, v___x_3163_, v___x_3177_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec_ref(v___x_3176_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref(v___x_3178_);
v___x_3180_ = lean_nat_add(v_i_3164_, v___x_3165_);
v___x_3181_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3166_, v___x_3180_, v_typeSub_3167_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref(v___x_3181_);
v___x_3183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3184_ = lean_unsigned_to_nat(2u);
v___x_3185_ = lean_mk_empty_array_with_capacity(v___x_3184_);
v___x_3186_ = lean_array_push(v___x_3185_, v_lhs_3168_);
v___x_3187_ = lean_array_push(v___x_3186_, v_rhs_3169_);
lean_inc_ref(v___x_3187_);
v___x_3188_ = l_Lean_Meta_mkAppM(v___x_3183_, v___x_3187_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref(v___x_3188_);
v___x_3190_ = l_Lean_Meta_mkEqNDRec(v_a_3179_, v_a_3182_, v_a_3189_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v___x_3190_);
v___x_3192_ = l_Lean_Meta_mkLambdaFVars(v___x_3187_, v_a_3191_, v___x_3162_, v___x_3163_, v___x_3162_, v___x_3163_, v___x_3177_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec_ref(v___x_3187_);
return v___x_3192_;
}
else
{
lean_dec_ref(v___x_3187_);
return v___x_3190_;
}
}
else
{
lean_dec_ref(v___x_3187_);
lean_dec(v_a_3182_);
lean_dec(v_a_3179_);
return v___x_3188_;
}
}
else
{
lean_dec(v_a_3179_);
lean_dec_ref(v_rhs_3169_);
lean_dec_ref(v_lhs_3168_);
return v___x_3181_;
}
}
else
{
lean_dec_ref(v_rhs_3169_);
lean_dec_ref(v_lhs_3168_);
lean_dec_ref(v_typeSub_3167_);
lean_dec_ref(v_kinds_3166_);
return v___x_3178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3193_, lean_object* v___x_3194_, lean_object* v___x_3195_, lean_object* v_i_3196_, lean_object* v___x_3197_, lean_object* v_kinds_3198_, lean_object* v_typeSub_3199_, lean_object* v_lhs_3200_, lean_object* v_rhs_3201_, lean_object* v_type_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v___x_2053__boxed_3208_; uint8_t v___x_2054__boxed_3209_; lean_object* v_res_3210_; 
v___x_2053__boxed_3208_ = lean_unbox(v___x_3194_);
v___x_2054__boxed_3209_ = lean_unbox(v___x_3195_);
v_res_3210_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3193_, v___x_2053__boxed_3208_, v___x_2054__boxed_3209_, v_i_3196_, v___x_3197_, v_kinds_3198_, v_typeSub_3199_, v_lhs_3200_, v_rhs_3201_, v_type_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___x_3197_);
lean_dec(v_i_3196_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(lean_object* v_kinds_3211_, lean_object* v_i_3212_, uint8_t v___x_3213_, uint8_t v___x_3214_, lean_object* v_lhs_3215_, lean_object* v_type_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3225_ = 0;
v___x_3226_ = lean_box(v___x_3225_);
v___x_3227_ = lean_array_get_borrowed(v___x_3226_, v_kinds_3211_, v_i_3212_);
v___x_3228_ = lean_unbox(v___x_3227_);
switch(v___x_3228_)
{
case 1:
{
lean_dec_ref(v_type_3216_);
lean_dec_ref(v_lhs_3215_);
lean_dec(v_i_3212_);
lean_dec_ref(v_kinds_3211_);
goto v___jp_3222_;
}
case 2:
{
lean_object* v___x_3229_; 
lean_inc_ref(v_lhs_3215_);
v___x_3229_ = l_Lean_Meta_mkEqRefl(v_lhs_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___f_3240_; lean_object* v___x_3241_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = l_Lean_Expr_bindingBody_x21(v_type_3216_);
v___x_3232_ = l_Lean_Expr_bindingBody_x21(v___x_3231_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = lean_unsigned_to_nat(2u);
v___x_3234_ = lean_mk_empty_array_with_capacity(v___x_3233_);
lean_inc_ref(v___x_3234_);
v___x_3235_ = lean_array_push(v___x_3234_, v_a_3230_);
lean_inc_ref(v_lhs_3215_);
v___x_3236_ = lean_array_push(v___x_3235_, v_lhs_3215_);
v___x_3237_ = lean_expr_instantiate(v___x_3232_, v___x_3236_);
lean_dec_ref(v___x_3236_);
lean_dec_ref(v___x_3232_);
v___x_3238_ = lean_box(v___x_3213_);
v___x_3239_ = lean_box(v___x_3214_);
v___f_3240_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3240_, 0, v___x_3234_);
lean_closure_set(v___f_3240_, 1, v___x_3238_);
lean_closure_set(v___f_3240_, 2, v___x_3239_);
lean_closure_set(v___f_3240_, 3, v_i_3212_);
lean_closure_set(v___f_3240_, 4, v_kinds_3211_);
lean_closure_set(v___f_3240_, 5, v___x_3237_);
lean_closure_set(v___f_3240_, 6, v_lhs_3215_);
v___x_3241_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3216_, v___f_3240_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3241_;
}
else
{
lean_dec_ref(v_type_3216_);
lean_dec_ref(v_lhs_3215_);
lean_dec(v_i_3212_);
lean_dec_ref(v_kinds_3211_);
return v___x_3229_;
}
}
case 4:
{
lean_dec_ref(v_type_3216_);
lean_dec_ref(v_lhs_3215_);
lean_dec(v_i_3212_);
lean_dec_ref(v_kinds_3211_);
goto v___jp_3222_;
}
case 5:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v_typeSub_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___f_3249_; lean_object* v___x_3250_; 
v___x_3242_ = l_Lean_Expr_bindingBody_x21(v_type_3216_);
v___x_3243_ = lean_unsigned_to_nat(1u);
v___x_3244_ = lean_mk_empty_array_with_capacity(v___x_3243_);
lean_inc_ref(v_lhs_3215_);
lean_inc_ref(v___x_3244_);
v___x_3245_ = lean_array_push(v___x_3244_, v_lhs_3215_);
v_typeSub_3246_ = lean_expr_instantiate(v___x_3242_, v___x_3245_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v___x_3242_);
v___x_3247_ = lean_box(v___x_3213_);
v___x_3248_ = lean_box(v___x_3214_);
v___f_3249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3249_, 0, v___x_3244_);
lean_closure_set(v___f_3249_, 1, v___x_3247_);
lean_closure_set(v___f_3249_, 2, v___x_3248_);
lean_closure_set(v___f_3249_, 3, v_i_3212_);
lean_closure_set(v___f_3249_, 4, v___x_3243_);
lean_closure_set(v___f_3249_, 5, v_kinds_3211_);
lean_closure_set(v___f_3249_, 6, v_typeSub_3246_);
lean_closure_set(v___f_3249_, 7, v_lhs_3215_);
v___x_3250_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3216_, v___f_3249_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3250_;
}
default: 
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3251_ = lean_unsigned_to_nat(1u);
v___x_3252_ = lean_nat_add(v_i_3212_, v___x_3251_);
lean_dec(v_i_3212_);
v___x_3253_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3211_, v___x_3252_, v_type_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___x_3253_);
v___x_3255_ = lean_mk_empty_array_with_capacity(v___x_3251_);
v___x_3256_ = lean_array_push(v___x_3255_, v_lhs_3215_);
v___x_3257_ = 1;
v___x_3258_ = l_Lean_Meta_mkLambdaFVars(v___x_3256_, v_a_3254_, v___x_3213_, v___x_3214_, v___x_3213_, v___x_3214_, v___x_3257_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec_ref(v___x_3256_);
return v___x_3258_;
}
else
{
lean_dec_ref(v_lhs_3215_);
return v___x_3253_;
}
}
}
v___jp_3222_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3224_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3223_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v_kinds_3259_, lean_object* v_i_3260_, lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v_lhs_3263_, lean_object* v_type_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
uint8_t v___x_2090__boxed_3270_; uint8_t v___x_2091__boxed_3271_; lean_object* v_res_3272_; 
v___x_2090__boxed_3270_ = lean_unbox(v___x_3261_);
v___x_2091__boxed_3271_ = lean_unbox(v___x_3262_);
v_res_3272_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v_kinds_3259_, v_i_3260_, v___x_2090__boxed_3270_, v___x_2091__boxed_3271_, v_lhs_3263_, v_type_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
return v_res_3272_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3273_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3274_ = lean_unsigned_to_nat(43u);
v___x_3275_ = lean_unsigned_to_nat(355u);
v___x_3276_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3277_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3278_ = l_mkPanicMessageWithDecl(v___x_3277_, v___x_3276_, v___x_3275_, v___x_3274_, v___x_3273_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3279_, lean_object* v_i_3280_, lean_object* v_type_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = lean_array_get_size(v_kinds_3279_);
v___x_3288_ = lean_nat_dec_eq(v_i_3280_, v___x_3287_);
if (v___x_3288_ == 0)
{
uint8_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___f_3292_; lean_object* v___x_3293_; 
v___x_3289_ = 1;
v___x_3290_ = lean_box(v___x_3288_);
v___x_3291_ = lean_box(v___x_3289_);
v___f_3292_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3292_, 0, v_kinds_3279_);
lean_closure_set(v___f_3292_, 1, v_i_3280_);
lean_closure_set(v___f_3292_, 2, v___x_3290_);
lean_closure_set(v___f_3292_, 3, v___x_3291_);
v___x_3293_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3281_, v___f_3292_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
return v___x_3293_;
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
lean_dec(v_i_3280_);
lean_dec_ref(v_kinds_3279_);
v___x_3294_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3295_ = lean_unsigned_to_nat(3u);
v___x_3296_ = l_Lean_Expr_isAppOfArity(v_type_3281_, v___x_3294_, v___x_3295_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec_ref(v_type_3281_);
v___x_3297_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3298_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3297_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
return v___x_3298_;
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = l_Lean_Expr_appFn_x21(v_type_3281_);
lean_dec_ref(v_type_3281_);
v___x_3300_ = l_Lean_Expr_appArg_x21(v___x_3299_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = l_Lean_Meta_mkEqRefl(v___x_3300_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
return v___x_3301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* v___x_3302_, lean_object* v_rhs_3303_, uint8_t v___x_3304_, uint8_t v___x_3305_, lean_object* v_i_3306_, lean_object* v_kinds_3307_, lean_object* v___x_3308_, lean_object* v_lhs_3309_, lean_object* v_heq_3310_, lean_object* v_type_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; lean_object* v___x_3320_; 
lean_inc_ref(v_rhs_3303_);
v___x_3317_ = lean_array_push(v___x_3302_, v_rhs_3303_);
lean_inc_ref(v_heq_3310_);
v___x_3318_ = lean_array_push(v___x_3317_, v_heq_3310_);
v___x_3319_ = 1;
v___x_3320_ = l_Lean_Meta_mkLambdaFVars(v___x_3318_, v_type_3311_, v___x_3304_, v___x_3305_, v___x_3304_, v___x_3305_, v___x_3319_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec_ref(v___x_3318_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref(v___x_3320_);
v___x_3322_ = lean_unsigned_to_nat(1u);
v___x_3323_ = lean_nat_add(v_i_3306_, v___x_3322_);
v___x_3324_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3307_, v___x_3323_, v___x_3308_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3324_);
lean_inc_ref(v_heq_3310_);
v___x_3326_ = l_Lean_Meta_mkEqRec(v_a_3321_, v_a_3325_, v_heq_3310_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(3u);
v___x_3329_ = lean_mk_empty_array_with_capacity(v___x_3328_);
v___x_3330_ = lean_array_push(v___x_3329_, v_lhs_3309_);
v___x_3331_ = lean_array_push(v___x_3330_, v_rhs_3303_);
v___x_3332_ = lean_array_push(v___x_3331_, v_heq_3310_);
v___x_3333_ = l_Lean_Meta_mkLambdaFVars(v___x_3332_, v_a_3327_, v___x_3304_, v___x_3305_, v___x_3304_, v___x_3305_, v___x_3319_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec_ref(v___x_3332_);
return v___x_3333_;
}
else
{
lean_dec_ref(v_heq_3310_);
lean_dec_ref(v_lhs_3309_);
lean_dec_ref(v_rhs_3303_);
return v___x_3326_;
}
}
else
{
lean_dec(v_a_3321_);
lean_dec_ref(v_heq_3310_);
lean_dec_ref(v_lhs_3309_);
lean_dec_ref(v_rhs_3303_);
return v___x_3324_;
}
}
else
{
lean_dec_ref(v_heq_3310_);
lean_dec_ref(v_lhs_3309_);
lean_dec_ref(v___x_3308_);
lean_dec_ref(v_kinds_3307_);
lean_dec_ref(v_rhs_3303_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* v___x_3334_, lean_object* v_rhs_3335_, lean_object* v___x_3336_, lean_object* v___x_3337_, lean_object* v_i_3338_, lean_object* v_kinds_3339_, lean_object* v___x_3340_, lean_object* v_lhs_3341_, lean_object* v_heq_3342_, lean_object* v_type_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
uint8_t v___x_2001__boxed_3349_; uint8_t v___x_2002__boxed_3350_; lean_object* v_res_3351_; 
v___x_2001__boxed_3349_ = lean_unbox(v___x_3336_);
v___x_2002__boxed_3350_ = lean_unbox(v___x_3337_);
v_res_3351_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3334_, v_rhs_3335_, v___x_2001__boxed_3349_, v___x_2002__boxed_3350_, v_i_3338_, v_kinds_3339_, v___x_3340_, v_lhs_3341_, v_heq_3342_, v_type_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v_i_3338_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* v___x_3352_, uint8_t v___x_3353_, uint8_t v___x_3354_, lean_object* v_i_3355_, lean_object* v_kinds_3356_, lean_object* v___x_3357_, lean_object* v_lhs_3358_, lean_object* v_rhs_3359_, lean_object* v_type_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___f_3368_; lean_object* v___x_3369_; 
v___x_3366_ = lean_box(v___x_3353_);
v___x_3367_ = lean_box(v___x_3354_);
v___f_3368_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3368_, 0, v___x_3352_);
lean_closure_set(v___f_3368_, 1, v_rhs_3359_);
lean_closure_set(v___f_3368_, 2, v___x_3366_);
lean_closure_set(v___f_3368_, 3, v___x_3367_);
lean_closure_set(v___f_3368_, 4, v_i_3355_);
lean_closure_set(v___f_3368_, 5, v_kinds_3356_);
lean_closure_set(v___f_3368_, 6, v___x_3357_);
lean_closure_set(v___f_3368_, 7, v_lhs_3358_);
v___x_3369_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3360_, v___f_3368_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object* v_kinds_3370_, lean_object* v_i_3371_, lean_object* v_type_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3370_, v_i_3371_, v_type_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* v_type_3379_, lean_object* v_kinds_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_unsigned_to_nat(0u);
v___x_3387_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3380_, v___x_3386_, v_type_3379_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object* v_type_3388_, lean_object* v_kinds_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3388_, v_kinds_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_msg_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___f_3402_; lean_object* v___x_2082__overap_3403_; lean_object* v___x_3404_; 
v___f_3402_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_2082__overap_3403_ = lean_panic_fn(v___f_3402_, v_msg_3396_);
lean_inc(v___y_3400_);
lean_inc_ref(v___y_3399_);
lean_inc(v___y_3398_);
lean_inc_ref(v___y_3397_);
v___x_3404_ = lean_apply_5(v___x_2082__overap_3403_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, lean_box(0));
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_msg_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_msg_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(lean_object* v_bs_3412_, lean_object* v_k_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3412_, v_k_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_a_3428_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3419_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3419_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg___boxed(lean_object* v_bs_3436_, lean_object* v_k_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3436_, v_k_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec_ref(v_bs_3436_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(lean_object* v_00_u03b1_3444_, lean_object* v_bs_3445_, lean_object* v_k_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3445_, v_k_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3453_, lean_object* v_bs_3454_, lean_object* v_k_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(v_00_u03b1_3453_, v_bs_3454_, v_k_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec_ref(v_bs_3454_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(size_t v_sz_3462_, size_t v_i_3463_, lean_object* v_bs_3464_){
_start:
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_usize_dec_lt(v_i_3463_, v_sz_3462_);
if (v___x_3465_ == 0)
{
return v_bs_3464_;
}
else
{
lean_object* v_v_3466_; lean_object* v___x_3467_; lean_object* v_bs_x27_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; size_t v___x_3473_; size_t v___x_3474_; lean_object* v___x_3475_; 
v_v_3466_ = lean_array_uget(v_bs_3464_, v_i_3463_);
v___x_3467_ = lean_unsigned_to_nat(0u);
v_bs_x27_3468_ = lean_array_uset(v_bs_3464_, v_i_3463_, v___x_3467_);
v___x_3469_ = l_Lean_Expr_fvarId_x21(v_v_3466_);
lean_dec(v_v_3466_);
v___x_3470_ = 1;
v___x_3471_ = lean_box(v___x_3470_);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3469_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = ((size_t)1ULL);
v___x_3474_ = lean_usize_add(v_i_3463_, v___x_3473_);
v___x_3475_ = lean_array_uset(v_bs_x27_3468_, v_i_3463_, v___x_3472_);
v_i_3463_ = v___x_3474_;
v_bs_3464_ = v___x_3475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0___boxed(lean_object* v_sz_3477_, lean_object* v_i_3478_, lean_object* v_bs_3479_){
_start:
{
size_t v_sz_boxed_3480_; size_t v_i_boxed_3481_; lean_object* v_res_3482_; 
v_sz_boxed_3480_ = lean_unbox_usize(v_sz_3477_);
lean_dec(v_sz_3477_);
v_i_boxed_3481_ = lean_unbox_usize(v_i_3478_);
lean_dec(v_i_3478_);
v_res_3482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_boxed_3480_, v_i_boxed_3481_, v_bs_3479_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(lean_object* v_bs_3483_, lean_object* v_k_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
size_t v_sz_3490_; size_t v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_sz_3490_ = lean_array_size(v_bs_3483_);
v___x_3491_ = ((size_t)0ULL);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_3490_, v___x_3491_, v_bs_3483_);
v___x_3493_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v___x_3492_, v_k_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec_ref(v___x_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg___boxed(lean_object* v_bs_3494_, lean_object* v_k_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3494_, v_k_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_00_u03b1_3502_, lean_object* v_bs_3503_, lean_object* v_k_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3503_, v_k_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3511_, lean_object* v_bs_3512_, lean_object* v_k_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_00_u03b1_3511_, v_bs_3512_, v_k_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3520_, lean_object* v_rhss_3521_, lean_object* v_lhs_3522_, lean_object* v_eqs_3523_, lean_object* v_hyps_3524_, uint8_t v_subsingletonInstImplicitRhs_3525_, lean_object* v_f_3526_, lean_object* v_info_3527_, lean_object* v_kinds_3528_, lean_object* v_lhss_3529_, lean_object* v_b_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3536_ = lean_unsigned_to_nat(1u);
v___x_3537_ = lean_nat_add(v_i_3520_, v___x_3536_);
lean_inc_ref(v_b_3530_);
v___x_3538_ = lean_array_push(v_rhss_3521_, v_b_3530_);
v___x_3539_ = l_Lean_Expr_fvarId_x21(v_lhs_3522_);
v___x_3540_ = l_Lean_Expr_fvarId_x21(v_b_3530_);
v___x_3541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
v___x_3543_ = lean_array_push(v_eqs_3523_, v___x_3542_);
v___x_3544_ = lean_array_push(v_hyps_3524_, v_b_3530_);
v___x_3545_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3525_, v_f_3526_, v_info_3527_, v_kinds_3528_, v_lhss_3529_, v___x_3537_, v___x_3538_, v___x_3543_, v___x_3544_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3546_, lean_object* v_rhss_3547_, lean_object* v_lhs_3548_, lean_object* v_eqs_3549_, lean_object* v_hyps_3550_, lean_object* v_subsingletonInstImplicitRhs_3551_, lean_object* v_f_3552_, lean_object* v_info_3553_, lean_object* v_kinds_3554_, lean_object* v_lhss_3555_, lean_object* v_b_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3562_; lean_object* v_res_3563_; 
v_subsingletonInstImplicitRhs_boxed_3562_ = lean_unbox(v_subsingletonInstImplicitRhs_3551_);
v_res_3563_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3546_, v_rhss_3547_, v_lhs_3548_, v_eqs_3549_, v_hyps_3550_, v_subsingletonInstImplicitRhs_boxed_3562_, v_f_3552_, v_info_3553_, v_kinds_3554_, v_lhss_3555_, v_b_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v_lhs_3548_);
lean_dec(v_i_3546_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3564_, lean_object* v_rhss_3565_, lean_object* v_lhs_3566_, lean_object* v_eqs_3567_, lean_object* v_hyps_3568_, uint8_t v_subsingletonInstImplicitRhs_3569_, lean_object* v_f_3570_, lean_object* v_info_3571_, lean_object* v_kinds_3572_, lean_object* v_lhss_3573_, lean_object* v_name_3574_, uint8_t v_bi_3575_, lean_object* v_type_3576_, uint8_t v_kind_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___x_3583_; lean_object* v___f_3584_; lean_object* v___x_3585_; 
v___x_3583_ = lean_box(v_subsingletonInstImplicitRhs_3569_);
v___f_3584_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3584_, 0, v_i_3564_);
lean_closure_set(v___f_3584_, 1, v_rhss_3565_);
lean_closure_set(v___f_3584_, 2, v_lhs_3566_);
lean_closure_set(v___f_3584_, 3, v_eqs_3567_);
lean_closure_set(v___f_3584_, 4, v_hyps_3568_);
lean_closure_set(v___f_3584_, 5, v___x_3583_);
lean_closure_set(v___f_3584_, 6, v_f_3570_);
lean_closure_set(v___f_3584_, 7, v_info_3571_);
lean_closure_set(v___f_3584_, 8, v_kinds_3572_);
lean_closure_set(v___f_3584_, 9, v_lhss_3573_);
v___x_3585_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3574_, v_bi_3575_, v_type_3576_, v___f_3584_, v_kind_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
v_a_3594_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3585_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3585_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3602_, lean_object* v_rhss_3603_, lean_object* v_lhss_3604_, lean_object* v_i_3605_, lean_object* v_eqs_3606_, lean_object* v_hyps_3607_, uint8_t v_subsingletonInstImplicitRhs_3608_, lean_object* v_f_3609_, lean_object* v_info_3610_, lean_object* v_kinds_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v___x_3617_; 
lean_inc(v___y_3615_);
lean_inc_ref(v___y_3614_);
lean_inc(v___y_3613_);
lean_inc_ref(v___y_3612_);
lean_inc_ref(v_lhs_3602_);
v___x_3617_ = lean_infer_type(v_lhs_3602_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___y_3625_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v___x_3617_);
v___x_3619_ = lean_array_get_size(v_rhss_3603_);
v___x_3620_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3604_);
v___x_3621_ = l_Array_toSubarray___redArg(v_lhss_3604_, v___x_3620_, v___x_3619_);
v___x_3622_ = l_Subarray_copy___redArg(v___x_3621_);
v___x_3623_ = l_Lean_Expr_replaceFVars(v_a_3618_, v___x_3622_, v_rhss_3603_);
lean_dec_ref(v___x_3622_);
lean_dec(v_a_3618_);
if (v_subsingletonInstImplicitRhs_3608_ == 0)
{
uint8_t v___x_3640_; 
v___x_3640_ = 1;
v___y_3625_ = v___x_3640_;
goto v___jp_3624_;
}
else
{
uint8_t v___x_3641_; 
v___x_3641_ = 3;
v___y_3625_ = v___x_3641_;
goto v___jp_3624_;
}
v___jp_3624_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = l_Lean_Expr_fvarId_x21(v_lhs_3602_);
lean_inc_ref(v___y_3612_);
v___x_3627_ = l_Lean_FVarId_getDecl___redArg(v___x_3626_, v___y_3612_, v___y_3614_, v___y_3615_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; lean_object* v___x_3631_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref(v___x_3627_);
v___x_3629_ = l_Lean_LocalDecl_userName(v_a_3628_);
lean_dec(v_a_3628_);
v___x_3630_ = 0;
v___x_3631_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3605_, v_rhss_3603_, v_lhs_3602_, v_eqs_3606_, v_hyps_3607_, v_subsingletonInstImplicitRhs_3608_, v_f_3609_, v_info_3610_, v_kinds_3611_, v_lhss_3604_, v___x_3629_, v___y_3625_, v___x_3623_, v___x_3630_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v___x_3631_;
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec_ref(v___x_3623_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v_kinds_3611_);
lean_dec_ref(v_info_3610_);
lean_dec_ref(v_f_3609_);
lean_dec_ref(v_hyps_3607_);
lean_dec_ref(v_eqs_3606_);
lean_dec(v_i_3605_);
lean_dec_ref(v_lhss_3604_);
lean_dec_ref(v_rhss_3603_);
lean_dec_ref(v_lhs_3602_);
v_a_3632_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3627_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3627_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v_kinds_3611_);
lean_dec_ref(v_info_3610_);
lean_dec_ref(v_f_3609_);
lean_dec_ref(v_hyps_3607_);
lean_dec_ref(v_eqs_3606_);
lean_dec(v_i_3605_);
lean_dec_ref(v_lhss_3604_);
lean_dec_ref(v_rhss_3603_);
lean_dec_ref(v_lhs_3602_);
v_a_3642_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3617_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3617_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3650_, lean_object* v_rhss_3651_, lean_object* v_lhss_3652_, lean_object* v_i_3653_, lean_object* v_eqs_3654_, lean_object* v_hyps_3655_, lean_object* v_subsingletonInstImplicitRhs_3656_, lean_object* v_f_3657_, lean_object* v_info_3658_, lean_object* v_kinds_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3665_; lean_object* v_res_3666_; 
v_subsingletonInstImplicitRhs_boxed_3665_ = lean_unbox(v_subsingletonInstImplicitRhs_3656_);
v_res_3666_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3650_, v_rhss_3651_, v_lhss_3652_, v_i_3653_, v_eqs_3654_, v_hyps_3655_, v_subsingletonInstImplicitRhs_boxed_3665_, v_f_3657_, v_info_3658_, v_kinds_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
return v_res_3666_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3668_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3669_ = lean_unsigned_to_nat(38u);
v___x_3670_ = lean_unsigned_to_nat(328u);
v___x_3671_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3672_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3673_ = l_mkPanicMessageWithDecl(v___x_3672_, v___x_3671_, v___x_3670_, v___x_3669_, v___x_3668_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3674_, lean_object* v_f_3675_, lean_object* v_info_3676_, lean_object* v_kinds_3677_, lean_object* v_lhss_3678_, lean_object* v_i_3679_, lean_object* v_rhss_3680_, lean_object* v_eqs_3681_, lean_object* v_hyps_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v___x_3688_; uint8_t v___x_3689_; 
v___x_3688_ = lean_array_get_size(v_kinds_3677_);
v___x_3689_ = lean_nat_dec_eq(v_i_3679_, v___x_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; lean_object* v_lhs_3691_; lean_object* v_hyps_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
v___x_3690_ = l_Lean_instInhabitedExpr;
v_lhs_3691_ = lean_array_get_borrowed(v___x_3690_, v_lhss_3678_, v_i_3679_);
lean_inc(v_lhs_3691_);
v_hyps_3692_ = lean_array_push(v_hyps_3682_, v_lhs_3691_);
v___x_3693_ = 0;
v___x_3694_ = lean_box(v___x_3693_);
v___x_3695_ = lean_array_get_borrowed(v___x_3694_, v_kinds_3677_, v_i_3679_);
v___x_3696_ = lean_unbox(v___x_3695_);
switch(v___x_3696_)
{
case 0:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3697_ = lean_unsigned_to_nat(1u);
v___x_3698_ = lean_nat_add(v_i_3679_, v___x_3697_);
lean_dec(v_i_3679_);
lean_inc(v_lhs_3691_);
v___x_3699_ = lean_array_push(v_rhss_3680_, v_lhs_3691_);
v___x_3700_ = lean_box(0);
v___x_3701_ = lean_array_push(v_eqs_3681_, v___x_3700_);
v_i_3679_ = v___x_3698_;
v_rhss_3680_ = v___x_3699_;
v_eqs_3681_ = v___x_3701_;
v_hyps_3682_ = v_hyps_3692_;
goto _start;
}
case 2:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_inc(v_lhs_3691_);
v___x_3703_ = l_Lean_Expr_fvarId_x21(v_lhs_3691_);
lean_inc_ref(v_a_3683_);
v___x_3704_ = l_Lean_FVarId_getDecl___redArg(v___x_3703_, v_a_3683_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref(v___x_3704_);
v___x_3706_ = l_Lean_LocalDecl_userName(v_a_3705_);
v___x_3707_ = l_Lean_LocalDecl_binderInfo(v_a_3705_);
v___x_3708_ = l_Lean_LocalDecl_type(v_a_3705_);
lean_dec(v_a_3705_);
v___x_3709_ = 0;
lean_inc(v___x_3706_);
v___x_3710_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3679_, v_rhss_3680_, v_eqs_3681_, v_hyps_3692_, v_subsingletonInstImplicitRhs_3674_, v_f_3675_, v_info_3676_, v_kinds_3677_, v_lhss_3678_, v_lhs_3691_, v___x_3706_, v___x_3706_, v___x_3707_, v___x_3708_, v___x_3709_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
return v___x_3710_;
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec_ref(v_hyps_3692_);
lean_dec(v_lhs_3691_);
lean_dec_ref(v_eqs_3681_);
lean_dec_ref(v_rhss_3680_);
lean_dec(v_i_3679_);
lean_dec_ref(v_lhss_3678_);
lean_dec_ref(v_kinds_3677_);
lean_dec_ref(v_info_3676_);
lean_dec_ref(v_f_3675_);
v_a_3711_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3704_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3704_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
case 3:
{
lean_object* v___x_3719_; 
lean_inc(v_a_3686_);
lean_inc_ref(v_a_3685_);
lean_inc(v_a_3684_);
lean_inc_ref(v_a_3683_);
lean_inc(v_lhs_3691_);
v___x_3719_ = lean_infer_type(v_lhs_3691_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v_paramInfo_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v_backDeps_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3719_);
v_paramInfo_3721_ = lean_ctor_get(v_info_3676_, 0);
v___x_3722_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_3723_ = lean_array_get_borrowed(v___x_3722_, v_paramInfo_3721_, v_i_3679_);
v_backDeps_3724_ = lean_ctor_get(v___x_3723_, 0);
v___x_3725_ = lean_array_get_size(v_rhss_3680_);
v___x_3726_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3678_);
v___x_3727_ = l_Array_toSubarray___redArg(v_lhss_3678_, v___x_3726_, v___x_3725_);
v___x_3728_ = l_Subarray_copy___redArg(v___x_3727_);
v___x_3729_ = l_Lean_Expr_replaceFVars(v_a_3720_, v___x_3728_, v_rhss_3680_);
lean_dec_ref(v___x_3728_);
lean_dec(v_a_3720_);
v___x_3730_ = l_Lean_Expr_fvarId_x21(v_lhs_3691_);
v___x_3731_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3730_, v___x_3729_, v_backDeps_3724_, v_eqs_3681_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref(v___x_3731_);
v___x_3733_ = lean_unsigned_to_nat(1u);
v___x_3734_ = lean_nat_add(v_i_3679_, v___x_3733_);
lean_dec(v_i_3679_);
v___x_3735_ = lean_array_push(v_rhss_3680_, v_a_3732_);
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_array_push(v_eqs_3681_, v___x_3736_);
v_i_3679_ = v___x_3734_;
v_rhss_3680_ = v___x_3735_;
v_eqs_3681_ = v___x_3737_;
v_hyps_3682_ = v_hyps_3692_;
goto _start;
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec_ref(v_hyps_3692_);
lean_dec_ref(v_eqs_3681_);
lean_dec_ref(v_rhss_3680_);
lean_dec(v_i_3679_);
lean_dec_ref(v_lhss_3678_);
lean_dec_ref(v_kinds_3677_);
lean_dec_ref(v_info_3676_);
lean_dec_ref(v_f_3675_);
v_a_3739_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3731_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3731_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec_ref(v_hyps_3692_);
lean_dec_ref(v_eqs_3681_);
lean_dec_ref(v_rhss_3680_);
lean_dec(v_i_3679_);
lean_dec_ref(v_lhss_3678_);
lean_dec_ref(v_kinds_3677_);
lean_dec_ref(v_info_3676_);
lean_dec_ref(v_f_3675_);
v_a_3747_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3719_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3719_);
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
case 5:
{
lean_object* v___x_3755_; lean_object* v___f_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_inc(v_lhs_3691_);
v___x_3755_ = lean_box(v_subsingletonInstImplicitRhs_3674_);
lean_inc(v_lhs_3691_);
v___f_3756_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3756_, 0, v_lhs_3691_);
lean_closure_set(v___f_3756_, 1, v_rhss_3680_);
lean_closure_set(v___f_3756_, 2, v_lhss_3678_);
lean_closure_set(v___f_3756_, 3, v_i_3679_);
lean_closure_set(v___f_3756_, 4, v_eqs_3681_);
lean_closure_set(v___f_3756_, 5, v_hyps_3692_);
lean_closure_set(v___f_3756_, 6, v___x_3755_);
lean_closure_set(v___f_3756_, 7, v_f_3675_);
lean_closure_set(v___f_3756_, 8, v_info_3676_);
lean_closure_set(v___f_3756_, 9, v_kinds_3677_);
v___x_3757_ = lean_unsigned_to_nat(1u);
v___x_3758_ = lean_mk_empty_array_with_capacity(v___x_3757_);
v___x_3759_ = lean_array_push(v___x_3758_, v_lhs_3691_);
v___x_3760_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v___x_3759_, v___f_3756_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
return v___x_3760_;
}
default: 
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
lean_dec_ref(v_hyps_3692_);
lean_dec_ref(v_eqs_3681_);
lean_dec_ref(v_rhss_3680_);
lean_dec(v_i_3679_);
lean_dec_ref(v_lhss_3678_);
lean_dec_ref(v_kinds_3677_);
lean_dec_ref(v_info_3676_);
lean_dec_ref(v_f_3675_);
v___x_3761_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3762_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v___x_3761_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
return v___x_3762_;
}
}
}
else
{
lean_object* v_lhs_3763_; lean_object* v_rhs_3764_; lean_object* v___x_3765_; 
lean_dec_ref(v_eqs_3681_);
lean_dec(v_i_3679_);
lean_dec_ref(v_info_3676_);
lean_inc_ref(v_f_3675_);
v_lhs_3763_ = l_Lean_mkAppN(v_f_3675_, v_lhss_3678_);
lean_dec_ref(v_lhss_3678_);
v_rhs_3764_ = l_Lean_mkAppN(v_f_3675_, v_rhss_3680_);
lean_dec_ref(v_rhss_3680_);
v___x_3765_ = l_Lean_Meta_mkEq(v_lhs_3763_, v_rhs_3764_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; uint8_t v___x_3767_; uint8_t v___x_3768_; lean_object* v___x_3769_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = 0;
v___x_3768_ = 1;
v___x_3769_ = l_Lean_Meta_mkForallFVars(v_hyps_3682_, v_a_3766_, v___x_3767_, v___x_3689_, v___x_3689_, v___x_3768_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
lean_dec_ref(v_hyps_3682_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref(v___x_3769_);
lean_inc_ref(v_kinds_3677_);
lean_inc(v_a_3770_);
v___x_3771_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3770_, v_kinds_3677_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3780_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3774_ = v___x_3771_;
v_isShared_3775_ = v_isSharedCheck_3780_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3771_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3780_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3776_, 0, v_a_3770_);
lean_ctor_set(v___x_3776_, 1, v_a_3772_);
lean_ctor_set(v___x_3776_, 2, v_kinds_3677_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 0, v___x_3776_);
v___x_3778_ = v___x_3774_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v_a_3770_);
lean_dec_ref(v_kinds_3677_);
v_a_3781_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3771_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3771_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec_ref(v_kinds_3677_);
v_a_3789_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3769_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3769_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_hyps_3682_);
lean_dec_ref(v_kinds_3677_);
v_a_3797_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3765_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3765_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3805_, lean_object* v_rhss_3806_, lean_object* v_b_3807_, lean_object* v_eqs_3808_, lean_object* v_hyps_3809_, uint8_t v_subsingletonInstImplicitRhs_3810_, lean_object* v_f_3811_, lean_object* v_info_3812_, lean_object* v_kinds_3813_, lean_object* v_lhss_3814_, lean_object* v_eq_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3821_ = lean_unsigned_to_nat(1u);
v___x_3822_ = lean_nat_add(v_i_3805_, v___x_3821_);
lean_inc_ref(v_b_3807_);
v___x_3823_ = lean_array_push(v_rhss_3806_, v_b_3807_);
v___x_3824_ = l_Lean_Expr_fvarId_x21(v_eq_3815_);
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
v___x_3827_ = lean_array_push(v_eqs_3808_, v___x_3826_);
v___x_3828_ = lean_array_push(v_hyps_3809_, v_b_3807_);
v___x_3829_ = lean_array_push(v___x_3828_, v_eq_3815_);
v___x_3830_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3810_, v_f_3811_, v_info_3812_, v_kinds_3813_, v_lhss_3814_, v___x_3822_, v___x_3823_, v___x_3827_, v___x_3829_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_3831_, lean_object* v_rhss_3832_, lean_object* v_b_3833_, lean_object* v_eqs_3834_, lean_object* v_hyps_3835_, lean_object* v_subsingletonInstImplicitRhs_3836_, lean_object* v_f_3837_, lean_object* v_info_3838_, lean_object* v_kinds_3839_, lean_object* v_lhss_3840_, lean_object* v_eq_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3847_; lean_object* v_res_3848_; 
v_subsingletonInstImplicitRhs_boxed_3847_ = lean_unbox(v_subsingletonInstImplicitRhs_3836_);
v_res_3848_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3831_, v_rhss_3832_, v_b_3833_, v_eqs_3834_, v_hyps_3835_, v_subsingletonInstImplicitRhs_boxed_3847_, v_f_3837_, v_info_3838_, v_kinds_3839_, v_lhss_3840_, v_eq_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v_i_3831_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(lean_object* v_lhs_3850_, lean_object* v_i_3851_, lean_object* v_rhss_3852_, lean_object* v_eqs_3853_, lean_object* v_hyps_3854_, uint8_t v_subsingletonInstImplicitRhs_3855_, lean_object* v_f_3856_, lean_object* v_info_3857_, lean_object* v_kinds_3858_, lean_object* v_lhss_3859_, lean_object* v___x_3860_, lean_object* v_b_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
lean_inc_ref(v_b_3861_);
v___x_3867_ = l_Lean_Meta_mkEq(v_lhs_3850_, v_b_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref(v___x_3867_);
v___x_3869_ = lean_box(v_subsingletonInstImplicitRhs_3855_);
v___f_3870_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3870_, 0, v_i_3851_);
lean_closure_set(v___f_3870_, 1, v_rhss_3852_);
lean_closure_set(v___f_3870_, 2, v_b_3861_);
lean_closure_set(v___f_3870_, 3, v_eqs_3853_);
lean_closure_set(v___f_3870_, 4, v_hyps_3854_);
lean_closure_set(v___f_3870_, 5, v___x_3869_);
lean_closure_set(v___f_3870_, 6, v_f_3856_);
lean_closure_set(v___f_3870_, 7, v_info_3857_);
lean_closure_set(v___f_3870_, 8, v_kinds_3858_);
lean_closure_set(v___f_3870_, 9, v_lhss_3859_);
v___x_3871_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0));
v___x_3872_ = lean_name_append_before(v___x_3860_, v___x_3871_);
v___x_3873_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3872_, v_a_3868_, v___f_3870_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
return v___x_3873_;
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_b_3861_);
lean_dec(v___x_3860_);
lean_dec_ref(v_lhss_3859_);
lean_dec_ref(v_kinds_3858_);
lean_dec_ref(v_info_3857_);
lean_dec_ref(v_f_3856_);
lean_dec_ref(v_hyps_3854_);
lean_dec_ref(v_eqs_3853_);
lean_dec_ref(v_rhss_3852_);
lean_dec(v_i_3851_);
v_a_3874_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3867_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3867_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v_lhs_3882_ = _args[0];
lean_object* v_i_3883_ = _args[1];
lean_object* v_rhss_3884_ = _args[2];
lean_object* v_eqs_3885_ = _args[3];
lean_object* v_hyps_3886_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3887_ = _args[5];
lean_object* v_f_3888_ = _args[6];
lean_object* v_info_3889_ = _args[7];
lean_object* v_kinds_3890_ = _args[8];
lean_object* v_lhss_3891_ = _args[9];
lean_object* v___x_3892_ = _args[10];
lean_object* v_b_3893_ = _args[11];
lean_object* v___y_3894_ = _args[12];
lean_object* v___y_3895_ = _args[13];
lean_object* v___y_3896_ = _args[14];
lean_object* v___y_3897_ = _args[15];
lean_object* v___y_3898_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3899_; lean_object* v_res_3900_; 
v_subsingletonInstImplicitRhs_boxed_3899_ = lean_unbox(v_subsingletonInstImplicitRhs_3887_);
v_res_3900_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(v_lhs_3882_, v_i_3883_, v_rhss_3884_, v_eqs_3885_, v_hyps_3886_, v_subsingletonInstImplicitRhs_boxed_3899_, v_f_3888_, v_info_3889_, v_kinds_3890_, v_lhss_3891_, v___x_3892_, v_b_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_3901_, lean_object* v_rhss_3902_, lean_object* v_eqs_3903_, lean_object* v_hyps_3904_, uint8_t v_subsingletonInstImplicitRhs_3905_, lean_object* v_f_3906_, lean_object* v_info_3907_, lean_object* v_kinds_3908_, lean_object* v_lhss_3909_, lean_object* v_lhs_3910_, lean_object* v___x_3911_, lean_object* v_name_3912_, uint8_t v_bi_3913_, lean_object* v_type_3914_, uint8_t v_kind_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v___x_3921_; lean_object* v___f_3922_; lean_object* v___x_3923_; 
v___x_3921_ = lean_box(v_subsingletonInstImplicitRhs_3905_);
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3922_, 0, v_lhs_3910_);
lean_closure_set(v___f_3922_, 1, v_i_3901_);
lean_closure_set(v___f_3922_, 2, v_rhss_3902_);
lean_closure_set(v___f_3922_, 3, v_eqs_3903_);
lean_closure_set(v___f_3922_, 4, v_hyps_3904_);
lean_closure_set(v___f_3922_, 5, v___x_3921_);
lean_closure_set(v___f_3922_, 6, v_f_3906_);
lean_closure_set(v___f_3922_, 7, v_info_3907_);
lean_closure_set(v___f_3922_, 8, v_kinds_3908_);
lean_closure_set(v___f_3922_, 9, v_lhss_3909_);
lean_closure_set(v___f_3922_, 10, v___x_3911_);
v___x_3923_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3912_, v_bi_3913_, v_type_3914_, v___f_3922_, v_kind_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3923_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
v_a_3932_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3923_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3923_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object** _args){
lean_object* v_i_3940_ = _args[0];
lean_object* v_rhss_3941_ = _args[1];
lean_object* v_eqs_3942_ = _args[2];
lean_object* v_hyps_3943_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3944_ = _args[4];
lean_object* v_f_3945_ = _args[5];
lean_object* v_info_3946_ = _args[6];
lean_object* v_kinds_3947_ = _args[7];
lean_object* v_lhss_3948_ = _args[8];
lean_object* v_lhs_3949_ = _args[9];
lean_object* v___x_3950_ = _args[10];
lean_object* v_name_3951_ = _args[11];
lean_object* v_bi_3952_ = _args[12];
lean_object* v_type_3953_ = _args[13];
lean_object* v_kind_3954_ = _args[14];
lean_object* v___y_3955_ = _args[15];
lean_object* v___y_3956_ = _args[16];
lean_object* v___y_3957_ = _args[17];
lean_object* v___y_3958_ = _args[18];
lean_object* v___y_3959_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3960_; uint8_t v_bi_boxed_3961_; uint8_t v_kind_boxed_3962_; lean_object* v_res_3963_; 
v_subsingletonInstImplicitRhs_boxed_3960_ = lean_unbox(v_subsingletonInstImplicitRhs_3944_);
v_bi_boxed_3961_ = lean_unbox(v_bi_3952_);
v_kind_boxed_3962_ = lean_unbox(v_kind_3954_);
v_res_3963_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3940_, v_rhss_3941_, v_eqs_3942_, v_hyps_3943_, v_subsingletonInstImplicitRhs_boxed_3960_, v_f_3945_, v_info_3946_, v_kinds_3947_, v_lhss_3948_, v_lhs_3949_, v___x_3950_, v_name_3951_, v_bi_boxed_3961_, v_type_3953_, v_kind_boxed_3962_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_3964_ = _args[0];
lean_object* v_rhss_3965_ = _args[1];
lean_object* v_lhs_3966_ = _args[2];
lean_object* v_eqs_3967_ = _args[3];
lean_object* v_hyps_3968_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3969_ = _args[5];
lean_object* v_f_3970_ = _args[6];
lean_object* v_info_3971_ = _args[7];
lean_object* v_kinds_3972_ = _args[8];
lean_object* v_lhss_3973_ = _args[9];
lean_object* v_name_3974_ = _args[10];
lean_object* v_bi_3975_ = _args[11];
lean_object* v_type_3976_ = _args[12];
lean_object* v_kind_3977_ = _args[13];
lean_object* v___y_3978_ = _args[14];
lean_object* v___y_3979_ = _args[15];
lean_object* v___y_3980_ = _args[16];
lean_object* v___y_3981_ = _args[17];
lean_object* v___y_3982_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3983_; uint8_t v_bi_boxed_3984_; uint8_t v_kind_boxed_3985_; lean_object* v_res_3986_; 
v_subsingletonInstImplicitRhs_boxed_3983_ = lean_unbox(v_subsingletonInstImplicitRhs_3969_);
v_bi_boxed_3984_ = lean_unbox(v_bi_3975_);
v_kind_boxed_3985_ = lean_unbox(v_kind_3977_);
v_res_3986_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3964_, v_rhss_3965_, v_lhs_3966_, v_eqs_3967_, v_hyps_3968_, v_subsingletonInstImplicitRhs_boxed_3983_, v_f_3970_, v_info_3971_, v_kinds_3972_, v_lhss_3973_, v_name_3974_, v_bi_boxed_3984_, v_type_3976_, v_kind_boxed_3985_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* v_subsingletonInstImplicitRhs_3987_, lean_object* v_f_3988_, lean_object* v_info_3989_, lean_object* v_kinds_3990_, lean_object* v_lhss_3991_, lean_object* v_i_3992_, lean_object* v_rhss_3993_, lean_object* v_eqs_3994_, lean_object* v_hyps_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4001_; lean_object* v_res_4002_; 
v_subsingletonInstImplicitRhs_boxed_4001_ = lean_unbox(v_subsingletonInstImplicitRhs_3987_);
v_res_4002_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_boxed_4001_, v_f_3988_, v_info_3989_, v_kinds_3990_, v_lhss_3991_, v_i_3992_, v_rhss_3993_, v_eqs_3994_, v_hyps_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* v___x_4003_, uint8_t v_subsingletonInstImplicitRhs_4004_, lean_object* v_f_4005_, lean_object* v_info_4006_, lean_object* v_kinds_4007_, lean_object* v_lhss_4008_, lean_object* v_x_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___x_4015_; uint8_t v___x_4016_; 
v___x_4015_ = lean_array_get_size(v_lhss_4008_);
v___x_4016_ = lean_nat_dec_eq(v___x_4015_, v___x_4003_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec_ref(v_lhss_4008_);
lean_dec_ref(v_kinds_4007_);
lean_dec_ref(v_info_4006_);
lean_dec_ref(v_f_4005_);
v___x_4017_ = lean_box(0);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
else
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4019_ = lean_unsigned_to_nat(0u);
v___x_4020_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_4021_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_4004_, v_f_4005_, v_info_4006_, v_kinds_4007_, v_lhss_4008_, v___x_4019_, v___x_4020_, v___x_4020_, v___x_4020_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4030_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4030_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4030_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4026_, 0, v_a_4022_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v___x_4026_);
v___x_4028_ = v___x_4024_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
v_a_4031_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4021_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4021_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* v___x_4039_, lean_object* v_subsingletonInstImplicitRhs_4040_, lean_object* v_f_4041_, lean_object* v_info_4042_, lean_object* v_kinds_4043_, lean_object* v_lhss_4044_, lean_object* v_x_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4051_; lean_object* v_res_4052_; 
v_subsingletonInstImplicitRhs_boxed_4051_ = lean_unbox(v_subsingletonInstImplicitRhs_4040_);
v_res_4052_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4039_, v_subsingletonInstImplicitRhs_boxed_4051_, v_f_4041_, v_info_4042_, v_kinds_4043_, v_lhss_4044_, v_x_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec_ref(v_x_4045_);
lean_dec(v___x_4039_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t v_subsingletonInstImplicitRhs_4053_, lean_object* v_f_4054_, lean_object* v_info_4055_, lean_object* v_kinds_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v___y_4063_; uint8_t v___y_4064_; lean_object* v_a_4069_; lean_object* v___x_4072_; 
lean_inc(v_a_4060_);
lean_inc_ref(v_a_4059_);
lean_inc(v_a_4058_);
lean_inc_ref(v_a_4057_);
lean_inc_ref(v_f_4054_);
v___x_4072_ = lean_infer_type(v_f_4054_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4087_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4087_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4087_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___f_4079_; lean_object* v___x_4081_; 
v___x_4077_ = lean_array_get_size(v_kinds_4056_);
v___x_4078_ = lean_box(v_subsingletonInstImplicitRhs_4053_);
v___f_4079_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4079_, 0, v___x_4077_);
lean_closure_set(v___f_4079_, 1, v___x_4078_);
lean_closure_set(v___f_4079_, 2, v_f_4054_);
lean_closure_set(v___f_4079_, 3, v_info_4055_);
lean_closure_set(v___f_4079_, 4, v_kinds_4056_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set_tag(v___x_4075_, 1);
lean_ctor_set(v___x_4075_, 0, v___x_4077_);
v___x_4081_ = v___x_4075_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4077_);
v___x_4081_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
uint8_t v___x_4082_; uint8_t v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = 1;
v___x_4083_ = 0;
v___x_4084_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_4073_, v___x_4081_, v___f_4079_, v___x_4082_, v___x_4083_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
if (lean_obj_tag(v___x_4084_) == 0)
{
return v___x_4084_;
}
else
{
lean_object* v_a_4085_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref(v___x_4084_);
v_a_4069_ = v_a_4085_;
goto v___jp_4068_;
}
}
}
}
else
{
lean_object* v_a_4088_; 
lean_dec_ref(v_kinds_4056_);
lean_dec_ref(v_info_4055_);
lean_dec_ref(v_f_4054_);
v_a_4088_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4088_);
lean_dec_ref(v___x_4072_);
v_a_4069_ = v_a_4088_;
goto v___jp_4068_;
}
v___jp_4062_:
{
if (v___y_4064_ == 0)
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
lean_dec_ref(v___y_4063_);
v___x_4065_ = lean_box(0);
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
return v___x_4066_;
}
else
{
lean_object* v___x_4067_; 
v___x_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___y_4063_);
return v___x_4067_;
}
}
v___jp_4068_:
{
uint8_t v___x_4070_; 
v___x_4070_ = l_Lean_Exception_isInterrupt(v_a_4069_);
if (v___x_4070_ == 0)
{
uint8_t v___x_4071_; 
lean_inc_ref(v_a_4069_);
v___x_4071_ = l_Lean_Exception_isRuntime(v_a_4069_);
v___y_4063_ = v_a_4069_;
v___y_4064_ = v___x_4071_;
goto v___jp_4062_;
}
else
{
v___y_4063_ = v_a_4069_;
v___y_4064_ = v___x_4070_;
goto v___jp_4062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* v_subsingletonInstImplicitRhs_4089_, lean_object* v_f_4090_, lean_object* v_info_4091_, lean_object* v_kinds_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4098_; lean_object* v_res_4099_; 
v_subsingletonInstImplicitRhs_boxed_4098_ = lean_unbox(v_subsingletonInstImplicitRhs_4089_);
v_res_4099_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_boxed_4098_, v_f_4090_, v_info_4091_, v_kinds_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
lean_dec(v_a_4096_);
lean_dec_ref(v_a_4095_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t v_sz_4100_, size_t v_i_4101_, lean_object* v_bs_4102_){
_start:
{
uint8_t v___x_4103_; 
v___x_4103_ = lean_usize_dec_lt(v_i_4101_, v_sz_4100_);
if (v___x_4103_ == 0)
{
return v_bs_4102_;
}
else
{
lean_object* v_v_4104_; lean_object* v___x_4105_; lean_object* v_bs_x27_4106_; uint8_t v___y_4108_; uint8_t v___x_4114_; 
v_v_4104_ = lean_array_uget(v_bs_4102_, v_i_4101_);
v___x_4105_ = lean_unsigned_to_nat(0u);
v_bs_x27_4106_ = lean_array_uset(v_bs_4102_, v_i_4101_, v___x_4105_);
v___x_4114_ = lean_unbox(v_v_4104_);
switch(v___x_4114_)
{
case 3:
{
uint8_t v___x_4115_; 
lean_dec(v_v_4104_);
v___x_4115_ = 0;
v___y_4108_ = v___x_4115_;
goto v___jp_4107_;
}
case 5:
{
uint8_t v___x_4116_; 
lean_dec(v_v_4104_);
v___x_4116_ = 0;
v___y_4108_ = v___x_4116_;
goto v___jp_4107_;
}
default: 
{
uint8_t v___x_4117_; 
v___x_4117_ = lean_unbox(v_v_4104_);
lean_dec(v_v_4104_);
v___y_4108_ = v___x_4117_;
goto v___jp_4107_;
}
}
v___jp_4107_:
{
size_t v___x_4109_; size_t v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4109_ = ((size_t)1ULL);
v___x_4110_ = lean_usize_add(v_i_4101_, v___x_4109_);
v___x_4111_ = lean_box(v___y_4108_);
v___x_4112_ = lean_array_uset(v_bs_x27_4106_, v_i_4101_, v___x_4111_);
v_i_4101_ = v___x_4110_;
v_bs_4102_ = v___x_4112_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* v_sz_4118_, lean_object* v_i_4119_, lean_object* v_bs_4120_){
_start:
{
size_t v_sz_boxed_4121_; size_t v_i_boxed_4122_; lean_object* v_res_4123_; 
v_sz_boxed_4121_ = lean_unbox_usize(v_sz_4118_);
lean_dec(v_sz_4118_);
v_i_boxed_4122_ = lean_unbox_usize(v_i_4119_);
lean_dec(v_i_4119_);
v_res_4123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_4121_, v_i_boxed_4122_, v_bs_4120_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* v_f_4124_, lean_object* v_info_4125_, lean_object* v_kinds_4126_, uint8_t v_subsingletonInstImplicitRhs_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v___x_4133_; 
lean_inc_ref(v_kinds_4126_);
lean_inc_ref(v_info_4125_);
lean_inc_ref(v_f_4124_);
v___x_4133_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4127_, v_f_4124_, v_info_4125_, v_kinds_4126_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
lean_inc(v_a_4134_);
if (lean_obj_tag(v_a_4134_) == 1)
{
lean_dec_ref(v_a_4134_);
lean_dec_ref(v_kinds_4126_);
lean_dec_ref(v_info_4125_);
lean_dec_ref(v_f_4124_);
return v___x_4133_;
}
else
{
lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v_a_4134_);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4147_ == 0)
{
lean_object* v_unused_4148_; 
v_unused_4148_ = lean_ctor_get(v___x_4133_, 0);
lean_dec(v_unused_4148_);
v___x_4136_ = v___x_4133_;
v_isShared_4137_ = v_isSharedCheck_4147_;
goto v_resetjp_4135_;
}
else
{
lean_dec(v___x_4133_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4147_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
uint8_t v___x_4138_; 
v___x_4138_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_4126_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4139_; lean_object* v___x_4141_; 
lean_dec_ref(v_kinds_4126_);
lean_dec_ref(v_info_4125_);
lean_dec_ref(v_f_4124_);
v___x_4139_ = lean_box(0);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 0, v___x_4139_);
v___x_4141_ = v___x_4136_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
else
{
size_t v_sz_4143_; size_t v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_del_object(v___x_4136_);
v_sz_4143_ = lean_array_size(v_kinds_4126_);
v___x_4144_ = ((size_t)0ULL);
v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4143_, v___x_4144_, v_kinds_4126_);
v___x_4146_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4127_, v_f_4124_, v_info_4125_, v___x_4145_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
return v___x_4146_;
}
}
}
}
else
{
lean_dec_ref(v_kinds_4126_);
lean_dec_ref(v_info_4125_);
lean_dec_ref(v_f_4124_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* v_f_4149_, lean_object* v_info_4150_, lean_object* v_kinds_4151_, lean_object* v_subsingletonInstImplicitRhs_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4158_; lean_object* v_res_4159_; 
v_subsingletonInstImplicitRhs_boxed_4158_ = lean_unbox(v_subsingletonInstImplicitRhs_4152_);
v_res_4159_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4149_, v_info_4150_, v_kinds_4151_, v_subsingletonInstImplicitRhs_boxed_4158_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
lean_dec_ref(v_a_4153_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* v_f_4160_, uint8_t v_subsingletonInstImplicitRhs_4161_, lean_object* v_maxArgs_x3f_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v___x_4168_; lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4168_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_4160_, v_a_4164_);
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref(v___x_4168_);
v___x_4170_ = l_Lean_Expr_cleanupAnnotations(v_a_4169_);
lean_inc_ref(v___x_4170_);
v___x_4171_ = l_Lean_Meta_getFunInfo(v___x_4170_, v_maxArgs_x3f_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___x_4173_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref(v___x_4171_);
lean_inc_ref(v___x_4170_);
v___x_4173_ = l_Lean_Meta_getCongrSimpKinds(v___x_4170_, v_a_4172_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4175_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref(v___x_4173_);
v___x_4175_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4170_, v_a_4172_, v_a_4174_, v_subsingletonInstImplicitRhs_4161_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
return v___x_4175_;
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec(v_a_4172_);
lean_dec_ref(v___x_4170_);
v_a_4176_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4173_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4173_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec_ref(v___x_4170_);
v_a_4184_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4171_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4171_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* v_f_4192_, lean_object* v_subsingletonInstImplicitRhs_4193_, lean_object* v_maxArgs_x3f_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4200_; lean_object* v_res_4201_; 
v_subsingletonInstImplicitRhs_boxed_4200_ = lean_unbox(v_subsingletonInstImplicitRhs_4193_);
v_res_4201_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4192_, v_subsingletonInstImplicitRhs_boxed_4200_, v_maxArgs_x3f_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_);
lean_dec(v_a_4198_);
lean_dec_ref(v_a_4197_);
lean_dec(v_a_4196_);
lean_dec_ref(v_a_4195_);
return v_res_4201_;
}
}
static lean_object* _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4207_ = lean_string_utf8_byte_size(v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4208_){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; 
v___x_4209_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4210_ = lean_string_utf8_byte_size(v_s_4208_);
v___x_4211_ = lean_obj_once(&l_Lean_Meta_isHCongrReservedNameSuffix___closed__0, &l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0);
v___x_4212_ = lean_nat_dec_le(v___x_4211_, v___x_4210_);
if (v___x_4212_ == 0)
{
lean_dec_ref(v_s_4208_);
return v___x_4212_;
}
else
{
lean_object* v___x_4213_; uint8_t v___x_4214_; 
v___x_4213_ = lean_unsigned_to_nat(0u);
v___x_4214_ = lean_string_memcmp(v_s_4208_, v___x_4209_, v___x_4213_, v___x_4213_, v___x_4211_);
if (v___x_4214_ == 0)
{
lean_dec_ref(v_s_4208_);
return v___x_4214_;
}
else
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; 
v___x_4215_ = lean_unsigned_to_nat(7u);
lean_inc_ref(v_s_4208_);
v___x_4216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4216_, 0, v_s_4208_);
lean_ctor_set(v___x_4216_, 1, v___x_4213_);
lean_ctor_set(v___x_4216_, 2, v___x_4210_);
v___x_4217_ = l_String_Slice_Pos_nextn(v___x_4216_, v___x_4213_, v___x_4215_);
lean_dec_ref(v___x_4216_);
v___x_4218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4218_, 0, v_s_4208_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
lean_ctor_set(v___x_4218_, 2, v___x_4210_);
v___x_4219_ = l_String_Slice_isNat(v___x_4218_);
lean_dec_ref(v___x_4218_);
return v___x_4219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* v_s_4220_){
_start:
{
uint8_t v_res_4221_; lean_object* v_r_4222_; 
v_res_4221_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4220_);
v_r_4222_ = lean_box(v_res_4221_);
return v_r_4222_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4272_ = lean_unsigned_to_nat(3482611248u);
v___x_4273_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4274_ = l_Lean_Name_num___override(v___x_4273_, v___x_4272_);
return v___x_4274_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4277_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4278_ = l_Lean_Name_str___override(v___x_4277_, v___x_4276_);
return v___x_4278_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4280_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4281_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4282_ = l_Lean_Name_str___override(v___x_4281_, v___x_4280_);
return v___x_4282_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4283_ = lean_unsigned_to_nat(2u);
v___x_4284_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4285_ = l_Lean_Name_num___override(v___x_4284_, v___x_4283_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4287_; uint8_t v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4287_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4288_ = 0;
v___x_4289_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4290_ = l_Lean_registerTraceClass(v___x_4287_, v___x_4288_, v___x_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4293_, lean_object* v_as_4294_, size_t v_i_4295_, size_t v_stop_4296_, lean_object* v_b_4297_){
_start:
{
lean_object* v___y_4299_; uint8_t v___x_4303_; 
v___x_4303_ = lean_usize_dec_eq(v_i_4295_, v_stop_4296_);
if (v___x_4303_ == 0)
{
lean_object* v___x_4304_; lean_object* v_fst_4305_; uint8_t v___x_4306_; 
v___x_4304_ = lean_array_uget_borrowed(v_as_4294_, v_i_4295_);
v_fst_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_fst_4305_);
lean_inc_ref(v_env_4293_);
v___x_4306_ = l_Lean_Environment_contains(v_env_4293_, v_fst_4305_, v___x_4303_);
if (v___x_4306_ == 0)
{
v___y_4299_ = v_b_4297_;
goto v___jp_4298_;
}
else
{
lean_object* v___x_4307_; 
lean_inc(v___x_4304_);
v___x_4307_ = lean_array_push(v_b_4297_, v___x_4304_);
v___y_4299_ = v___x_4307_;
goto v___jp_4298_;
}
}
else
{
lean_dec_ref(v_env_4293_);
return v_b_4297_;
}
v___jp_4298_:
{
size_t v___x_4300_; size_t v___x_4301_; 
v___x_4300_ = ((size_t)1ULL);
v___x_4301_ = lean_usize_add(v_i_4295_, v___x_4300_);
v_i_4295_ = v___x_4301_;
v_b_4297_ = v___y_4299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4308_, lean_object* v_as_4309_, lean_object* v_i_4310_, lean_object* v_stop_4311_, lean_object* v_b_4312_){
_start:
{
size_t v_i_boxed_4313_; size_t v_stop_boxed_4314_; lean_object* v_res_4315_; 
v_i_boxed_4313_ = lean_unbox_usize(v_i_4310_);
lean_dec(v_i_4310_);
v_stop_boxed_4314_ = lean_unbox_usize(v_stop_4311_);
lean_dec(v_stop_4311_);
v_res_4315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4308_, v_as_4309_, v_i_boxed_4313_, v_stop_boxed_4314_, v_b_4312_);
lean_dec_ref(v_as_4309_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4316_, lean_object* v_x_4317_){
_start:
{
if (lean_obj_tag(v_x_4317_) == 0)
{
lean_object* v_k_4318_; lean_object* v_v_4319_; lean_object* v_l_4320_; lean_object* v_r_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v_k_4318_ = lean_ctor_get(v_x_4317_, 1);
v_v_4319_ = lean_ctor_get(v_x_4317_, 2);
v_l_4320_ = lean_ctor_get(v_x_4317_, 3);
v_r_4321_ = lean_ctor_get(v_x_4317_, 4);
v___x_4322_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4316_, v_l_4320_);
lean_inc(v_v_4319_);
lean_inc(v_k_4318_);
v___x_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4323_, 0, v_k_4318_);
lean_ctor_set(v___x_4323_, 1, v_v_4319_);
v___x_4324_ = lean_array_push(v___x_4322_, v___x_4323_);
v_init_4316_ = v___x_4324_;
v_x_4317_ = v_r_4321_;
goto _start;
}
else
{
return v_init_4316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4326_, lean_object* v_x_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4326_, v_x_4327_);
lean_dec(v_x_4327_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4333_, lean_object* v_s_4334_, uint8_t v_x_4335_){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4336_ = lean_unsigned_to_nat(0u);
v___x_4337_ = ((lean_object*)(l_Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4338_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4337_, v_s_4334_);
v___x_4339_ = lean_array_get_size(v___x_4338_);
v___x_4340_ = ((lean_object*)(l_Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4341_ = lean_nat_dec_lt(v___x_4336_, v___x_4339_);
if (v___x_4341_ == 0)
{
lean_dec_ref(v___x_4338_);
lean_dec_ref(v_env_4333_);
return v___x_4340_;
}
else
{
uint8_t v___x_4342_; 
v___x_4342_ = lean_nat_dec_le(v___x_4339_, v___x_4339_);
if (v___x_4342_ == 0)
{
if (v___x_4341_ == 0)
{
lean_dec_ref(v___x_4338_);
lean_dec_ref(v_env_4333_);
return v___x_4340_;
}
else
{
size_t v___x_4343_; size_t v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = ((size_t)0ULL);
v___x_4344_ = lean_usize_of_nat(v___x_4339_);
v___x_4345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4333_, v___x_4338_, v___x_4343_, v___x_4344_, v___x_4340_);
lean_dec_ref(v___x_4338_);
return v___x_4345_;
}
}
else
{
size_t v___x_4346_; size_t v___x_4347_; lean_object* v___x_4348_; 
v___x_4346_ = ((size_t)0ULL);
v___x_4347_ = lean_usize_of_nat(v___x_4339_);
v___x_4348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4333_, v___x_4338_, v___x_4346_, v___x_4347_, v___x_4340_);
lean_dec_ref(v___x_4338_);
return v___x_4348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4349_, lean_object* v_s_4350_, lean_object* v_x_4351_){
_start:
{
uint8_t v_x_410__boxed_4352_; lean_object* v_res_4353_; 
v_x_410__boxed_4352_ = lean_unbox(v_x_4351_);
v_res_4353_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4349_, v_s_4350_, v_x_410__boxed_4352_);
lean_dec(v_s_4350_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___f_4363_ = ((lean_object*)(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4364_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4365_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4366_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4364_, v___x_4365_, v___f_4363_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4369_, lean_object* v_t_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4369_, v_t_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4372_, lean_object* v_t_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4372_, v_t_4373_);
lean_dec(v_t_4373_);
return v_res_4374_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object* v_env_4375_, lean_object* v_n_4376_){
_start:
{
if (lean_obj_tag(v_n_4376_) == 1)
{
lean_object* v_pre_4377_; lean_object* v_str_4378_; uint8_t v___y_4380_; uint8_t v___x_4382_; 
v_pre_4377_ = lean_ctor_get(v_n_4376_, 0);
lean_inc(v_pre_4377_);
v_str_4378_ = lean_ctor_get(v_n_4376_, 1);
lean_inc_ref(v_str_4378_);
lean_dec_ref(v_n_4376_);
lean_inc_ref(v_str_4378_);
v___x_4382_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4378_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4383_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4384_ = lean_string_dec_eq(v_str_4378_, v___x_4383_);
lean_dec_ref(v_str_4378_);
v___y_4380_ = v___x_4384_;
goto v___jp_4379_;
}
else
{
lean_dec_ref(v_str_4378_);
v___y_4380_ = v___x_4382_;
goto v___jp_4379_;
}
v___jp_4379_:
{
if (v___y_4380_ == 0)
{
lean_dec(v_pre_4377_);
lean_dec_ref(v_env_4375_);
return v___y_4380_;
}
else
{
uint8_t v___x_4381_; 
v___x_4381_ = l_Lean_Environment_contains(v_env_4375_, v_pre_4377_, v___y_4380_);
return v___x_4381_;
}
}
}
else
{
uint8_t v___x_4385_; 
lean_dec(v_n_4376_);
lean_dec_ref(v_env_4375_);
v___x_4385_ = 0;
return v___x_4385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_env_4386_, lean_object* v_n_4387_){
_start:
{
uint8_t v_res_4388_; lean_object* v_r_4389_; 
v_res_4388_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4386_, v_n_4387_);
v_r_4389_ = lean_box(v_res_4388_);
return v_r_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4392_; lean_object* v___x_4393_; 
v___f_4392_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_));
v___x_4393_ = l_Lean_registerReservedNamePredicate(v___f_4392_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object* v_thm_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; lean_object* v_env_4400_; lean_object* v_toConstantVal_4401_; lean_object* v_value_4402_; lean_object* v_all_4403_; uint8_t v___y_4405_; lean_object* v_type_4413_; uint8_t v___x_4414_; 
v___x_4399_ = lean_st_ref_get(v___y_4397_);
v_env_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc_ref(v_env_4400_);
lean_dec(v___x_4399_);
v_toConstantVal_4401_ = lean_ctor_get(v_thm_4396_, 0);
v_value_4402_ = lean_ctor_get(v_thm_4396_, 1);
v_all_4403_ = lean_ctor_get(v_thm_4396_, 2);
v_type_4413_ = lean_ctor_get(v_toConstantVal_4401_, 2);
lean_inc_ref(v_env_4400_);
v___x_4414_ = l_Lean_Environment_hasUnsafe(v_env_4400_, v_type_4413_);
if (v___x_4414_ == 0)
{
uint8_t v___x_4415_; 
v___x_4415_ = l_Lean_Environment_hasUnsafe(v_env_4400_, v_value_4402_);
v___y_4405_ = v___x_4415_;
goto v___jp_4404_;
}
else
{
lean_dec_ref(v_env_4400_);
v___y_4405_ = v___x_4414_;
goto v___jp_4404_;
}
v___jp_4404_:
{
if (v___y_4405_ == 0)
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4406_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4406_, 0, v_thm_4396_);
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
return v___x_4407_;
}
else
{
lean_object* v___x_4408_; uint8_t v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
lean_inc(v_all_4403_);
lean_inc_ref(v_value_4402_);
lean_inc_ref(v_toConstantVal_4401_);
lean_dec_ref(v_thm_4396_);
v___x_4408_ = lean_box(0);
v___x_4409_ = 0;
v___x_4410_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4410_, 0, v_toConstantVal_4401_);
lean_ctor_set(v___x_4410_, 1, v_value_4402_);
lean_ctor_set(v___x_4410_, 2, v___x_4408_);
lean_ctor_set(v___x_4410_, 3, v_all_4403_);
lean_ctor_set_uint8(v___x_4410_, sizeof(void*)*4, v___x_4409_);
v___x_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
return v___x_4412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_thm_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4416_, v___y_4417_);
lean_dec(v___y_4417_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_thm_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4420_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object* v_thm_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(lean_object* v_cls_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_options_4440_; uint8_t v_hasTrace_4441_; 
v_options_4440_ = lean_ctor_get(v___y_4438_, 2);
v_hasTrace_4441_ = lean_ctor_get_uint8(v_options_4440_, sizeof(void*)*1);
if (v_hasTrace_4441_ == 0)
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
lean_dec(v_cls_4437_);
v___x_4442_ = lean_box(v_hasTrace_4441_);
v___x_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4442_);
return v___x_4443_;
}
else
{
lean_object* v_inheritedTraceOptions_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; uint8_t v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v_inheritedTraceOptions_4444_ = lean_ctor_get(v___y_4438_, 13);
v___x_4445_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___closed__1));
v___x_4446_ = l_Lean_Name_append(v___x_4445_, v_cls_4437_);
v___x_4447_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4444_, v_options_4440_, v___x_4446_);
lean_dec(v___x_4446_);
v___x_4448_ = lean_box(v___x_4447_);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_cls_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v_cls_4450_, v___y_4451_);
lean_dec_ref(v___y_4451_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_cls_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v_cls_4454_, v___y_4457_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
return v_res_4467_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0(void){
_start:
{
lean_object* v___x_4468_; double v___x_4469_; 
v___x_4468_ = lean_unsigned_to_nat(0u);
v___x_4469_ = lean_float_of_nat(v___x_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(lean_object* v_cls_4473_, lean_object* v_msg_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v_ref_4480_; lean_object* v___x_4481_; lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4526_; 
v_ref_4480_ = lean_ctor_get(v___y_4477_, 5);
v___x_4481_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4526_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4526_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4486_; lean_object* v_traceState_4487_; lean_object* v_env_4488_; lean_object* v_nextMacroScope_4489_; lean_object* v_ngen_4490_; lean_object* v_auxDeclNGen_4491_; lean_object* v_cache_4492_; lean_object* v_messages_4493_; lean_object* v_infoState_4494_; lean_object* v_snapshotTasks_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4525_; 
v___x_4486_ = lean_st_ref_take(v___y_4478_);
v_traceState_4487_ = lean_ctor_get(v___x_4486_, 4);
v_env_4488_ = lean_ctor_get(v___x_4486_, 0);
v_nextMacroScope_4489_ = lean_ctor_get(v___x_4486_, 1);
v_ngen_4490_ = lean_ctor_get(v___x_4486_, 2);
v_auxDeclNGen_4491_ = lean_ctor_get(v___x_4486_, 3);
v_cache_4492_ = lean_ctor_get(v___x_4486_, 5);
v_messages_4493_ = lean_ctor_get(v___x_4486_, 6);
v_infoState_4494_ = lean_ctor_get(v___x_4486_, 7);
v_snapshotTasks_4495_ = lean_ctor_get(v___x_4486_, 8);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4497_ = v___x_4486_;
v_isShared_4498_ = v_isSharedCheck_4525_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_snapshotTasks_4495_);
lean_inc(v_infoState_4494_);
lean_inc(v_messages_4493_);
lean_inc(v_cache_4492_);
lean_inc(v_traceState_4487_);
lean_inc(v_auxDeclNGen_4491_);
lean_inc(v_ngen_4490_);
lean_inc(v_nextMacroScope_4489_);
lean_inc(v_env_4488_);
lean_dec(v___x_4486_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4525_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
uint64_t v_tid_4499_; lean_object* v_traces_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4524_; 
v_tid_4499_ = lean_ctor_get_uint64(v_traceState_4487_, sizeof(void*)*1);
v_traces_4500_ = lean_ctor_get(v_traceState_4487_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_traceState_4487_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4502_ = v_traceState_4487_;
v_isShared_4503_ = v_isSharedCheck_4524_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_traces_4500_);
lean_dec(v_traceState_4487_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4524_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; double v___x_4505_; uint8_t v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
v___x_4504_ = lean_box(0);
v___x_4505_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0);
v___x_4506_ = 0;
v___x_4507_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__1));
v___x_4508_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4508_, 0, v_cls_4473_);
lean_ctor_set(v___x_4508_, 1, v___x_4504_);
lean_ctor_set(v___x_4508_, 2, v___x_4507_);
lean_ctor_set_float(v___x_4508_, sizeof(void*)*3, v___x_4505_);
lean_ctor_set_float(v___x_4508_, sizeof(void*)*3 + 8, v___x_4505_);
lean_ctor_set_uint8(v___x_4508_, sizeof(void*)*3 + 16, v___x_4506_);
v___x_4509_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__2));
v___x_4510_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v_a_4482_);
lean_ctor_set(v___x_4510_, 2, v___x_4509_);
lean_inc(v_ref_4480_);
v___x_4511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4511_, 0, v_ref_4480_);
lean_ctor_set(v___x_4511_, 1, v___x_4510_);
v___x_4512_ = l_Lean_PersistentArray_push___redArg(v_traces_4500_, v___x_4511_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4512_);
v___x_4514_ = v___x_4502_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4512_);
lean_ctor_set_uint64(v_reuseFailAlloc_4523_, sizeof(void*)*1, v_tid_4499_);
v___x_4514_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
lean_object* v___x_4516_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 4, v___x_4514_);
v___x_4516_ = v___x_4497_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_env_4488_);
lean_ctor_set(v_reuseFailAlloc_4522_, 1, v_nextMacroScope_4489_);
lean_ctor_set(v_reuseFailAlloc_4522_, 2, v_ngen_4490_);
lean_ctor_set(v_reuseFailAlloc_4522_, 3, v_auxDeclNGen_4491_);
lean_ctor_set(v_reuseFailAlloc_4522_, 4, v___x_4514_);
lean_ctor_set(v_reuseFailAlloc_4522_, 5, v_cache_4492_);
lean_ctor_set(v_reuseFailAlloc_4522_, 6, v_messages_4493_);
lean_ctor_set(v_reuseFailAlloc_4522_, 7, v_infoState_4494_);
lean_ctor_set(v_reuseFailAlloc_4522_, 8, v_snapshotTasks_4495_);
v___x_4516_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
v___x_4517_ = lean_st_ref_set(v___y_4478_, v___x_4516_);
v___x_4518_ = lean_box(0);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4518_);
v___x_4520_ = v___x_4484_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___boxed(lean_object* v_cls_4527_, lean_object* v_msg_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(v_cls_4527_, v_msg_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
return v_res_4534_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4535_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4538_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
return v___x_4539_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4542_ = l_Lean_stringToMessageData(v___x_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4543_, uint8_t v___x_4544_, lean_object* v_name_4545_, lean_object* v_argKinds_4546_, lean_object* v___x_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___x_4593_; lean_object* v_a_4594_; lean_object* v___x_4595_; 
v___x_4593_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_4543_, v___y_4551_);
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref(v___x_4593_);
v___x_4595_ = l_Lean_addDecl(v_a_4594_, v___x_4544_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v_a_4598_; uint8_t v___x_4599_; 
lean_dec_ref(v___x_4595_);
v___x_4596_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4597_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v___x_4596_, v___y_4550_);
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4597_);
v___x_4599_ = lean_unbox(v_a_4598_);
lean_dec(v_a_4598_);
if (v___x_4599_ == 0)
{
v___y_4554_ = v___y_4549_;
v___y_4555_ = v___y_4551_;
goto v___jp_4553_;
}
else
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4600_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4545_);
v___x_4601_ = l_Lean_MessageData_ofName(v_name_4545_);
v___x_4602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4600_);
lean_ctor_set(v___x_4602_, 1, v___x_4601_);
v___x_4603_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4604_, 0, v___x_4602_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(v___x_4596_, v___x_4604_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_dec_ref(v___x_4605_);
v___y_4554_ = v___y_4549_;
v___y_4555_ = v___y_4551_;
goto v___jp_4553_;
}
else
{
lean_dec_ref(v___x_4547_);
lean_dec_ref(v_argKinds_4546_);
lean_dec(v_name_4545_);
return v___x_4605_;
}
}
}
else
{
lean_dec_ref(v___x_4547_);
lean_dec_ref(v_argKinds_4546_);
lean_dec(v_name_4545_);
return v___x_4595_;
}
v___jp_4553_:
{
lean_object* v___x_4556_; lean_object* v_env_4557_; lean_object* v_nextMacroScope_4558_; lean_object* v_ngen_4559_; lean_object* v_auxDeclNGen_4560_; lean_object* v_traceState_4561_; lean_object* v_messages_4562_; lean_object* v_infoState_4563_; lean_object* v_snapshotTasks_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4591_; 
v___x_4556_ = lean_st_ref_take(v___y_4555_);
v_env_4557_ = lean_ctor_get(v___x_4556_, 0);
v_nextMacroScope_4558_ = lean_ctor_get(v___x_4556_, 1);
v_ngen_4559_ = lean_ctor_get(v___x_4556_, 2);
v_auxDeclNGen_4560_ = lean_ctor_get(v___x_4556_, 3);
v_traceState_4561_ = lean_ctor_get(v___x_4556_, 4);
v_messages_4562_ = lean_ctor_get(v___x_4556_, 6);
v_infoState_4563_ = lean_ctor_get(v___x_4556_, 7);
v_snapshotTasks_4564_ = lean_ctor_get(v___x_4556_, 8);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4591_ == 0)
{
lean_object* v_unused_4592_; 
v_unused_4592_ = lean_ctor_get(v___x_4556_, 5);
lean_dec(v_unused_4592_);
v___x_4566_ = v___x_4556_;
v_isShared_4567_ = v_isSharedCheck_4591_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_snapshotTasks_4564_);
lean_inc(v_infoState_4563_);
lean_inc(v_messages_4562_);
lean_inc(v_traceState_4561_);
lean_inc(v_auxDeclNGen_4560_);
lean_inc(v_ngen_4559_);
lean_inc(v_nextMacroScope_4558_);
lean_inc(v_env_4557_);
lean_dec(v___x_4556_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4591_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4572_; 
v___x_4568_ = l_Lean_Meta_congrKindsExt;
v___x_4569_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4568_, v_env_4557_, v_name_4545_, v_argKinds_4546_);
v___x_4570_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 5, v___x_4570_);
lean_ctor_set(v___x_4566_, 0, v___x_4569_);
v___x_4572_ = v___x_4566_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4569_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v_nextMacroScope_4558_);
lean_ctor_set(v_reuseFailAlloc_4590_, 2, v_ngen_4559_);
lean_ctor_set(v_reuseFailAlloc_4590_, 3, v_auxDeclNGen_4560_);
lean_ctor_set(v_reuseFailAlloc_4590_, 4, v_traceState_4561_);
lean_ctor_set(v_reuseFailAlloc_4590_, 5, v___x_4570_);
lean_ctor_set(v_reuseFailAlloc_4590_, 6, v_messages_4562_);
lean_ctor_set(v_reuseFailAlloc_4590_, 7, v_infoState_4563_);
lean_ctor_set(v_reuseFailAlloc_4590_, 8, v_snapshotTasks_4564_);
v___x_4572_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v_mctx_4575_; lean_object* v_zetaDeltaFVarIds_4576_; lean_object* v_postponed_4577_; lean_object* v_diag_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4588_; 
v___x_4573_ = lean_st_ref_set(v___y_4555_, v___x_4572_);
v___x_4574_ = lean_st_ref_take(v___y_4554_);
v_mctx_4575_ = lean_ctor_get(v___x_4574_, 0);
v_zetaDeltaFVarIds_4576_ = lean_ctor_get(v___x_4574_, 2);
v_postponed_4577_ = lean_ctor_get(v___x_4574_, 3);
v_diag_4578_ = lean_ctor_get(v___x_4574_, 4);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4588_ == 0)
{
lean_object* v_unused_4589_; 
v_unused_4589_ = lean_ctor_get(v___x_4574_, 1);
lean_dec(v_unused_4589_);
v___x_4580_ = v___x_4574_;
v_isShared_4581_ = v_isSharedCheck_4588_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_diag_4578_);
lean_inc(v_postponed_4577_);
lean_inc(v_zetaDeltaFVarIds_4576_);
lean_inc(v_mctx_4575_);
lean_dec(v___x_4574_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4588_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 1, v___x_4547_);
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_mctx_4575_);
lean_ctor_set(v_reuseFailAlloc_4587_, 1, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4587_, 2, v_zetaDeltaFVarIds_4576_);
lean_ctor_set(v_reuseFailAlloc_4587_, 3, v_postponed_4577_);
lean_ctor_set(v_reuseFailAlloc_4587_, 4, v_diag_4578_);
v___x_4583_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4584_ = lean_st_ref_set(v___y_4554_, v___x_4583_);
v___x_4585_ = lean_box(0);
v___x_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
return v___x_4586_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4606_, lean_object* v___x_4607_, lean_object* v_name_4608_, lean_object* v_argKinds_4609_, lean_object* v___x_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
uint8_t v___x_14998__boxed_4616_; lean_object* v_res_4617_; 
v___x_14998__boxed_4616_ = lean_unbox(v___x_4607_);
v_res_4617_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4606_, v___x_14998__boxed_4616_, v_name_4608_, v_argKinds_4609_, v___x_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
if (lean_obj_tag(v_a_4618_) == 0)
{
lean_object* v___x_4620_; 
v___x_4620_ = l_List_reverse___redArg(v_a_4619_);
return v___x_4620_;
}
else
{
lean_object* v_head_4621_; lean_object* v_tail_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4631_; 
v_head_4621_ = lean_ctor_get(v_a_4618_, 0);
v_tail_4622_ = lean_ctor_get(v_a_4618_, 1);
v_isSharedCheck_4631_ = !lean_is_exclusive(v_a_4618_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4624_ = v_a_4618_;
v_isShared_4625_ = v_isSharedCheck_4631_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_tail_4622_);
lean_inc(v_head_4621_);
lean_dec(v_a_4618_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4631_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; lean_object* v___x_4628_; 
v___x_4626_ = l_Lean_mkLevelParam(v_head_4621_);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 1, v_a_4619_);
lean_ctor_set(v___x_4624_, 0, v___x_4626_);
v___x_4628_ = v___x_4624_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v_a_4619_);
v___x_4628_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
v_a_4618_ = v_tail_4622_;
v_a_4619_ = v___x_4628_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4632_; 
v___x_4632_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4632_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
return v___x_4634_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4635_ = lean_box(1);
v___x_4636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4637_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
lean_ctor_set(v___x_4638_, 1, v___x_4636_);
lean_ctor_set(v___x_4638_, 2, v___x_4635_);
return v___x_4638_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4641_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4642_ = lean_unsigned_to_nat(0u);
v___x_4643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
lean_ctor_set(v___x_4643_, 1, v___x_4642_);
lean_ctor_set(v___x_4643_, 2, v___x_4642_);
lean_ctor_set(v___x_4643_, 3, v___x_4641_);
lean_ctor_set(v___x_4643_, 4, v___x_4641_);
lean_ctor_set(v___x_4643_, 5, v___x_4641_);
lean_ctor_set(v___x_4643_, 6, v___x_4641_);
lean_ctor_set(v___x_4643_, 7, v___x_4641_);
lean_ctor_set(v___x_4643_, 8, v___x_4641_);
return v___x_4643_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4645_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
lean_ctor_set(v___x_4645_, 2, v___x_4644_);
lean_ctor_set(v___x_4645_, 3, v___x_4644_);
lean_ctor_set(v___x_4645_, 4, v___x_4644_);
lean_ctor_set(v___x_4645_, 5, v___x_4644_);
return v___x_4645_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
lean_ctor_set(v___x_4647_, 1, v___x_4646_);
lean_ctor_set(v___x_4647_, 2, v___x_4646_);
lean_ctor_set(v___x_4647_, 3, v___x_4646_);
lean_ctor_set(v___x_4647_, 4, v___x_4646_);
return v___x_4647_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4648_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4649_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4650_ = lean_box(1);
v___x_4651_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4652_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
lean_ctor_set(v___x_4653_, 1, v___x_4651_);
lean_ctor_set(v___x_4653_, 2, v___x_4650_);
lean_ctor_set(v___x_4653_, 3, v___x_4649_);
lean_ctor_set(v___x_4653_, 4, v___x_4648_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v_name_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
if (lean_obj_tag(v_name_4654_) == 1)
{
lean_object* v_pre_4658_; lean_object* v_str_4659_; lean_object* v___x_4660_; lean_object* v_env_4661_; uint8_t v___x_4662_; uint8_t v___x_4663_; 
v_pre_4658_ = lean_ctor_get(v_name_4654_, 0);
lean_inc(v_pre_4658_);
v_str_4659_ = lean_ctor_get(v_name_4654_, 1);
v___x_4660_ = lean_st_ref_get(v___y_4656_);
v_env_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc_ref(v_env_4661_);
lean_dec(v___x_4660_);
v___x_4662_ = 1;
lean_inc(v_pre_4658_);
v___x_4663_ = l_Lean_Environment_contains(v_env_4661_, v_pre_4658_, v___x_4662_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; lean_object* v___x_4665_; 
lean_dec(v_pre_4658_);
lean_dec_ref(v_name_4654_);
v___x_4664_ = lean_box(v___x_4663_);
v___x_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4664_);
return v___x_4665_;
}
else
{
uint8_t v___x_4666_; lean_object* v___y_4668_; uint8_t v___y_4669_; lean_object* v_a_4674_; 
lean_inc_ref(v_str_4659_);
v___x_4666_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4659_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4677_; uint8_t v___x_4678_; 
v___x_4677_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4678_ = lean_string_dec_eq(v_str_4659_, v___x_4677_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
lean_dec(v_pre_4658_);
lean_dec_ref(v_name_4654_);
v___x_4679_ = lean_box(v___x_4678_);
v___x_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4679_);
return v___x_4680_;
}
else
{
uint8_t v___x_4681_; uint8_t v___x_4682_; uint8_t v___x_4683_; lean_object* v___x_4684_; uint64_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; uint8_t v_a_4697_; lean_object* v___x_4701_; 
v___x_4681_ = 1;
v___x_4682_ = 0;
v___x_4683_ = 2;
v___x_4684_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4684_, 0, v___x_4666_);
lean_ctor_set_uint8(v___x_4684_, 1, v___x_4666_);
lean_ctor_set_uint8(v___x_4684_, 2, v___x_4666_);
lean_ctor_set_uint8(v___x_4684_, 3, v___x_4666_);
lean_ctor_set_uint8(v___x_4684_, 4, v___x_4666_);
lean_ctor_set_uint8(v___x_4684_, 5, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 6, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 7, v___x_4666_);
lean_ctor_set_uint8(v___x_4684_, 8, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 9, v___x_4681_);
lean_ctor_set_uint8(v___x_4684_, 10, v___x_4682_);
lean_ctor_set_uint8(v___x_4684_, 11, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 12, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 13, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 14, v___x_4683_);
lean_ctor_set_uint8(v___x_4684_, 15, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 16, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 17, v___x_4678_);
lean_ctor_set_uint8(v___x_4684_, 18, v___x_4678_);
v___x_4685_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4684_);
v___x_4686_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4686_, 0, v___x_4684_);
lean_ctor_set_uint64(v___x_4686_, sizeof(void*)*1, v___x_4685_);
v___x_4687_ = lean_box(1);
v___x_4688_ = lean_unsigned_to_nat(0u);
v___x_4689_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4690_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4691_ = lean_box(0);
v___x_4692_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4692_, 0, v___x_4686_);
lean_ctor_set(v___x_4692_, 1, v___x_4687_);
lean_ctor_set(v___x_4692_, 2, v___x_4689_);
lean_ctor_set(v___x_4692_, 3, v___x_4690_);
lean_ctor_set(v___x_4692_, 4, v___x_4691_);
lean_ctor_set(v___x_4692_, 5, v___x_4688_);
lean_ctor_set(v___x_4692_, 6, v___x_4691_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7, v___x_4666_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 1, v___x_4666_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 2, v___x_4666_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 3, v___x_4662_);
v___x_4693_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4694_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4695_ = lean_st_mk_ref(v___x_4694_);
lean_inc(v_pre_4658_);
v___x_4701_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4658_, v___x_4692_, v___x_4695_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref(v___x_4701_);
v___x_4703_ = l_Lean_ConstantInfo_levelParams(v_a_4702_);
lean_dec(v_a_4702_);
v___x_4704_ = lean_box(0);
lean_inc(v___x_4703_);
v___x_4705_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4703_, v___x_4704_);
lean_inc(v_pre_4658_);
v___x_4706_ = l_Lean_mkConst(v_pre_4658_, v___x_4705_);
lean_inc_ref(v___x_4706_);
v___x_4707_ = l_Lean_Meta_getFunInfo(v___x_4706_, v___x_4691_, v___x_4692_, v___x_4695_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4709_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref(v___x_4707_);
lean_inc_ref(v___x_4706_);
v___x_4709_ = l_Lean_Meta_getCongrSimpKinds(v___x_4706_, v_a_4708_, v___x_4692_, v___x_4695_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4711_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
lean_inc(v_a_4710_);
lean_dec_ref(v___x_4709_);
v___x_4711_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4706_, v_a_4708_, v_a_4710_, v___x_4662_, v___x_4692_, v___x_4695_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4712_);
lean_dec_ref(v___x_4711_);
if (lean_obj_tag(v_a_4712_) == 1)
{
lean_object* v_val_4713_; lean_object* v_type_4714_; lean_object* v_proof_4715_; lean_object* v_argKinds_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4729_; 
v_val_4713_ = lean_ctor_get(v_a_4712_, 0);
lean_inc(v_val_4713_);
lean_dec_ref(v_a_4712_);
v_type_4714_ = lean_ctor_get(v_val_4713_, 0);
v_proof_4715_ = lean_ctor_get(v_val_4713_, 1);
v_argKinds_4716_ = lean_ctor_get(v_val_4713_, 2);
v_isSharedCheck_4729_ = !lean_is_exclusive(v_val_4713_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4718_ = v_val_4713_;
v_isShared_4719_ = v_isSharedCheck_4729_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_argKinds_4716_);
lean_inc(v_proof_4715_);
lean_inc(v_type_4714_);
lean_dec(v_val_4713_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4729_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
lean_inc_ref(v_name_4654_);
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 2, v_type_4714_);
lean_ctor_set(v___x_4718_, 1, v___x_4703_);
lean_ctor_set(v___x_4718_, 0, v_name_4654_);
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_name_4654_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v___x_4703_);
lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_type_4714_);
v___x_4721_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___f_4725_; lean_object* v___x_4726_; 
lean_inc_ref(v_name_4654_);
v___x_4722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4722_, 0, v_name_4654_);
lean_ctor_set(v___x_4722_, 1, v___x_4704_);
v___x_4723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4721_);
lean_ctor_set(v___x_4723_, 1, v_proof_4715_);
lean_ctor_set(v___x_4723_, 2, v___x_4722_);
v___x_4724_ = lean_box(v___x_4666_);
lean_inc_ref(v_name_4654_);
v___f_4725_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4725_, 0, v___x_4723_);
lean_closure_set(v___f_4725_, 1, v___x_4724_);
lean_closure_set(v___f_4725_, 2, v_name_4654_);
lean_closure_set(v___f_4725_, 3, v_argKinds_4716_);
lean_closure_set(v___f_4725_, 4, v___x_4693_);
lean_inc_ref(v___y_4655_);
v___x_4726_ = l_Lean_Meta_realizeConst(v_pre_4658_, v_name_4654_, v___f_4725_, v___x_4692_, v___x_4695_, v___y_4655_, v___y_4656_);
lean_dec_ref(v___x_4692_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_dec_ref(v___x_4726_);
v_a_4697_ = v___x_4662_;
goto v___jp_4696_;
}
else
{
lean_object* v_a_4727_; 
lean_dec(v___x_4695_);
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4727_);
lean_dec_ref(v___x_4726_);
v_a_4674_ = v_a_4727_;
goto v___jp_4673_;
}
}
}
}
else
{
lean_dec(v_a_4712_);
lean_dec(v___x_4703_);
lean_dec_ref(v___x_4692_);
lean_dec(v_pre_4658_);
lean_dec_ref(v_name_4654_);
v_a_4697_ = v___x_4666_;
goto v___jp_4696_;
}
}
else
{
lean_object* v_a_4730_; 
lean_dec(v___x_4703_);
lean_dec(v___x_4695_);
lean_dec_ref(v___x_4692_);
lean_dec(v_pre_4658_);
lean_dec_ref(v_name_4654_);
v_a_4730_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4730_);
lean_dec_ref(v___x_4711_);
v_a_4674_ = v_a_4730_;
goto v___jp_4673_;
}
}
else
{
lean_object* v_a_4731_; 
lean_dec(v_a_4708_);
lean_dec_ref(v___x_4706_);
lean_dec(v___x_4703_);
lean_dec(v___x_4695_);
lean_dec_ref(v___x_4692_);
lean_dec_ref(v_name_4654_);
lean_dec(v_pre_4658_);
v_a_4731_ = lean_ctor_get(v___x_4709_, 0);
lean_inc(v_a_4731_);
lean_dec_ref(v___x_4709_);
v_a_4674_ = v_a_4731_;
goto v___jp_4673_;
}
}
else
{
lean_object* v_a_4732_; 
lean_dec_ref(v___x_4706_);
lean_dec(v___x_4703_);
lean_dec(v___x_4695_);
lean_dec_ref(v___x_4692_);
lean_dec(v_pre_4658_);
lean_dec_ref(v_name_4654_);
v_a_4732_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4732_);
lean_dec_ref(v___x_4707_);
v_a_4674_ = v_a_4732_;
goto v___jp_4673_;
}
}
else
{
lean_object* v_a_4733_; 
lean_dec(v___x_4695_);
lean_dec_ref(v___x_4692_);
lean_dec(v_pre_4658_);
lean_dec_ref(v_name_4654_);
v_a_4733_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4733_);
lean_dec_ref(v___x_4701_);
v_a_4674_ = v_a_4733_;
goto v___jp_4673_;
}
v___jp_4696_:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4698_ = lean_st_ref_get(v___x_4695_);
lean_dec(v___x_4695_);
lean_dec(v___x_4698_);
v___x_4699_ = lean_box(v_a_4697_);
v___x_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4699_);
return v___x_4700_;
}
}
}
else
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; uint8_t v___x_4739_; lean_object* v___y_4741_; uint8_t v___y_4742_; lean_object* v_a_4747_; uint8_t v___x_4750_; uint8_t v___x_4751_; uint8_t v___x_4752_; lean_object* v___x_4753_; uint64_t v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4734_ = lean_unsigned_to_nat(7u);
v___x_4735_ = lean_unsigned_to_nat(0u);
v___x_4736_ = lean_string_utf8_byte_size(v_str_4659_);
lean_inc_ref(v_str_4659_);
v___x_4737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4737_, 0, v_str_4659_);
lean_ctor_set(v___x_4737_, 1, v___x_4735_);
lean_ctor_set(v___x_4737_, 2, v___x_4736_);
v___x_4738_ = l_String_Slice_Pos_nextn(v___x_4737_, v___x_4735_, v___x_4734_);
lean_dec_ref(v___x_4737_);
v___x_4739_ = 0;
v___x_4750_ = 1;
v___x_4751_ = 0;
v___x_4752_ = 2;
v___x_4753_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4753_, 0, v___x_4739_);
lean_ctor_set_uint8(v___x_4753_, 1, v___x_4739_);
lean_ctor_set_uint8(v___x_4753_, 2, v___x_4739_);
lean_ctor_set_uint8(v___x_4753_, 3, v___x_4739_);
lean_ctor_set_uint8(v___x_4753_, 4, v___x_4739_);
lean_ctor_set_uint8(v___x_4753_, 5, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 6, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 7, v___x_4739_);
lean_ctor_set_uint8(v___x_4753_, 8, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 9, v___x_4750_);
lean_ctor_set_uint8(v___x_4753_, 10, v___x_4751_);
lean_ctor_set_uint8(v___x_4753_, 11, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 12, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 13, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 14, v___x_4752_);
lean_ctor_set_uint8(v___x_4753_, 15, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 16, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 17, v___x_4666_);
lean_ctor_set_uint8(v___x_4753_, 18, v___x_4666_);
v___x_4754_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4753_);
v___x_4755_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4755_, 0, v___x_4753_);
lean_ctor_set_uint64(v___x_4755_, sizeof(void*)*1, v___x_4754_);
v___x_4756_ = lean_box(1);
v___x_4757_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4758_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4759_ = lean_box(0);
v___x_4760_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4760_, 0, v___x_4755_);
lean_ctor_set(v___x_4760_, 1, v___x_4756_);
lean_ctor_set(v___x_4760_, 2, v___x_4757_);
lean_ctor_set(v___x_4760_, 3, v___x_4758_);
lean_ctor_set(v___x_4760_, 4, v___x_4759_);
lean_ctor_set(v___x_4760_, 5, v___x_4735_);
lean_ctor_set(v___x_4760_, 6, v___x_4759_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*7, v___x_4739_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*7 + 1, v___x_4739_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*7 + 2, v___x_4739_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*7 + 3, v___x_4662_);
v___x_4761_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4762_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4763_ = lean_st_mk_ref(v___x_4762_);
lean_inc(v_pre_4658_);
v___x_4764_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4658_, v___x_4760_, v___x_4763_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref(v___x_4764_);
lean_inc_ref(v_str_4659_);
v___x_4766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4766_, 0, v_str_4659_);
lean_ctor_set(v___x_4766_, 1, v___x_4738_);
lean_ctor_set(v___x_4766_, 2, v___x_4736_);
v___x_4767_ = l_String_Slice_toNat_x21(v___x_4766_);
lean_dec_ref(v___x_4766_);
v___x_4768_ = l_Lean_ConstantInfo_levelParams(v_a_4765_);
lean_dec(v_a_4765_);
v___x_4769_ = lean_box(0);
lean_inc(v___x_4768_);
v___x_4770_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4768_, v___x_4769_);
lean_inc(v_pre_4658_);
v___x_4771_ = l_Lean_mkConst(v_pre_4658_, v___x_4770_);
v___x_4772_ = l_Lean_Meta_mkHCongrWithArity(v___x_4771_, v___x_4767_, v___x_4760_, v___x_4763_, v___y_4655_, v___y_4656_);
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
lean_inc_ref(v_name_4654_);
if (v_isShared_4779_ == 0)
{
lean_ctor_set(v___x_4778_, 2, v_type_4774_);
lean_ctor_set(v___x_4778_, 1, v___x_4768_);
lean_ctor_set(v___x_4778_, 0, v_name_4654_);
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_name_4654_);
lean_ctor_set(v_reuseFailAlloc_4798_, 1, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_type_4774_);
v___x_4781_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___f_4785_; lean_object* v___x_4786_; 
lean_inc_ref(v_name_4654_);
v___x_4782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4782_, 0, v_name_4654_);
lean_ctor_set(v___x_4782_, 1, v___x_4769_);
v___x_4783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4781_);
lean_ctor_set(v___x_4783_, 1, v_proof_4775_);
lean_ctor_set(v___x_4783_, 2, v___x_4782_);
v___x_4784_ = lean_box(v___x_4739_);
lean_inc_ref(v_name_4654_);
v___f_4785_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4785_, 0, v___x_4783_);
lean_closure_set(v___f_4785_, 1, v___x_4784_);
lean_closure_set(v___f_4785_, 2, v_name_4654_);
lean_closure_set(v___f_4785_, 3, v_argKinds_4776_);
lean_closure_set(v___f_4785_, 4, v___x_4761_);
lean_inc_ref(v___y_4655_);
v___x_4786_ = l_Lean_Meta_realizeConst(v_pre_4658_, v_name_4654_, v___f_4785_, v___x_4760_, v___x_4763_, v___y_4655_, v___y_4656_);
lean_dec_ref(v___x_4760_);
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
v___x_4791_ = lean_box(v___x_4662_);
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
v_a_4747_ = v_a_4797_;
goto v___jp_4746_;
}
}
}
}
else
{
lean_object* v_a_4800_; 
lean_dec(v___x_4768_);
lean_dec(v___x_4763_);
lean_dec_ref(v___x_4760_);
lean_dec(v_pre_4658_);
lean_dec_ref(v_name_4654_);
v_a_4800_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_a_4800_);
lean_dec_ref(v___x_4772_);
v_a_4747_ = v_a_4800_;
goto v___jp_4746_;
}
}
else
{
lean_object* v_a_4801_; 
lean_dec(v___x_4763_);
lean_dec_ref(v___x_4760_);
lean_dec(v___x_4738_);
lean_dec(v_pre_4658_);
lean_dec_ref(v_name_4654_);
v_a_4801_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4801_);
lean_dec_ref(v___x_4764_);
v_a_4747_ = v_a_4801_;
goto v___jp_4746_;
}
v___jp_4740_:
{
if (v___y_4742_ == 0)
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
lean_dec_ref(v___y_4741_);
v___x_4743_ = lean_box(v___x_4739_);
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
else
{
lean_object* v___x_4745_; 
v___x_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4745_, 0, v___y_4741_);
return v___x_4745_;
}
}
v___jp_4746_:
{
uint8_t v___x_4748_; 
v___x_4748_ = l_Lean_Exception_isInterrupt(v_a_4747_);
if (v___x_4748_ == 0)
{
uint8_t v___x_4749_; 
lean_inc_ref(v_a_4747_);
v___x_4749_ = l_Lean_Exception_isRuntime(v_a_4747_);
v___y_4741_ = v_a_4747_;
v___y_4742_ = v___x_4749_;
goto v___jp_4740_;
}
else
{
v___y_4741_ = v_a_4747_;
v___y_4742_ = v___x_4748_;
goto v___jp_4740_;
}
}
}
v___jp_4667_:
{
if (v___y_4669_ == 0)
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
lean_dec_ref(v___y_4668_);
v___x_4670_ = lean_box(v___x_4666_);
v___x_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
return v___x_4671_;
}
else
{
lean_object* v___x_4672_; 
v___x_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4672_, 0, v___y_4668_);
return v___x_4672_;
}
}
v___jp_4673_:
{
uint8_t v___x_4675_; 
v___x_4675_ = l_Lean_Exception_isInterrupt(v_a_4674_);
if (v___x_4675_ == 0)
{
uint8_t v___x_4676_; 
lean_inc_ref(v_a_4674_);
v___x_4676_ = l_Lean_Exception_isRuntime(v_a_4674_);
v___y_4668_ = v_a_4674_;
v___y_4669_ = v___x_4676_;
goto v___jp_4667_;
}
else
{
v___y_4668_ = v_a_4674_;
v___y_4669_ = v___x_4675_;
goto v___jp_4667_;
}
}
}
}
else
{
uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
lean_dec(v_name_4654_);
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
lean_dec(v___y_4807_);
lean_dec_ref(v___y_4806_);
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
lean_object* v___f_4822_; lean_object* v___x_1829__overap_4823_; lean_object* v___x_4824_; 
v___f_4822_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1829__overap_4823_ = lean_panic_fn(v___f_4822_, v_msg_4816_);
lean_inc(v___y_4820_);
lean_inc_ref(v___y_4819_);
lean_inc(v___y_4818_);
lean_inc_ref(v___y_4817_);
v___x_4824_ = lean_apply_5(v___x_1829__overap_4823_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, lean_box(0));
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
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
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
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
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
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
lean_dec(v___y_5060_);
lean_dec_ref(v___y_5059_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
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
lean_inc(v_thmName_5101_);
v___x_5139_ = l_Lean_executeReservedNameAction(v_thmName_5101_, v_a_5073_, v_a_5074_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v___x_5140_; lean_object* v___x_5141_; 
lean_dec_ref(v___x_5139_);
v___x_5140_ = lean_box(0);
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
v___y_5095_ = v___x_5120_;
goto v___jp_5094_;
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
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
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
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
