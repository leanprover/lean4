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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_before(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "e_"};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.CongrTheorems.0.Lean.Meta.mkCongrSimpCore\?.mk\?.go"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg(lean_object* v_k_11_){
_start:
{
lean_inc(v_k_11_);
return v_k_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg___boxed(lean_object* v_k_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Meta_CongrArgKind_ctorElim___redArg(v_k_12_);
lean_dec(v_k_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, uint8_t v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_inc(v_k_18_);
return v_k_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
uint8_t v_t_boxed_24_; lean_object* v_res_25_; 
v_t_boxed_24_ = lean_unbox(v_t_21_);
v_res_25_ = l_Lean_Meta_CongrArgKind_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_boxed_24_, v_h_22_, v_k_23_);
lean_dec(v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg(lean_object* v_fixed_26_){
_start:
{
lean_inc(v_fixed_26_);
return v_fixed_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg___boxed(lean_object* v_fixed_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_CongrArgKind_fixed_elim___redArg(v_fixed_27_);
lean_dec(v_fixed_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim(lean_object* v_motive_29_, uint8_t v_t_30_, lean_object* v_h_31_, lean_object* v_fixed_32_){
_start:
{
lean_inc(v_fixed_32_);
return v_fixed_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___boxed(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_fixed_36_){
_start:
{
uint8_t v_t_boxed_37_; lean_object* v_res_38_; 
v_t_boxed_37_ = lean_unbox(v_t_34_);
v_res_38_ = l_Lean_Meta_CongrArgKind_fixed_elim(v_motive_33_, v_t_boxed_37_, v_h_35_, v_fixed_36_);
lean_dec(v_fixed_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(lean_object* v_fixedNoParam_39_){
_start:
{
lean_inc(v_fixedNoParam_39_);
return v_fixedNoParam_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg___boxed(lean_object* v_fixedNoParam_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(v_fixedNoParam_40_);
lean_dec(v_fixedNoParam_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim(lean_object* v_motive_42_, uint8_t v_t_43_, lean_object* v_h_44_, lean_object* v_fixedNoParam_45_){
_start:
{
lean_inc(v_fixedNoParam_45_);
return v_fixedNoParam_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_fixedNoParam_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_fixedNoParam_49_);
lean_dec(v_fixedNoParam_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg(lean_object* v_eq_52_){
_start:
{
lean_inc(v_eq_52_);
return v_eq_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg___boxed(lean_object* v_eq_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_CongrArgKind_eq_elim___redArg(v_eq_53_);
lean_dec(v_eq_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_eq_58_){
_start:
{
lean_inc(v_eq_58_);
return v_eq_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___boxed(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_eq_62_){
_start:
{
uint8_t v_t_boxed_63_; lean_object* v_res_64_; 
v_t_boxed_63_ = lean_unbox(v_t_60_);
v_res_64_ = l_Lean_Meta_CongrArgKind_eq_elim(v_motive_59_, v_t_boxed_63_, v_h_61_, v_eq_62_);
lean_dec(v_eq_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg(lean_object* v_cast_65_){
_start:
{
lean_inc(v_cast_65_);
return v_cast_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg___boxed(lean_object* v_cast_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_CongrArgKind_cast_elim___redArg(v_cast_66_);
lean_dec(v_cast_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim(lean_object* v_motive_68_, uint8_t v_t_69_, lean_object* v_h_70_, lean_object* v_cast_71_){
_start:
{
lean_inc(v_cast_71_);
return v_cast_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_cast_75_){
_start:
{
uint8_t v_t_boxed_76_; lean_object* v_res_77_; 
v_t_boxed_76_ = lean_unbox(v_t_73_);
v_res_77_ = l_Lean_Meta_CongrArgKind_cast_elim(v_motive_72_, v_t_boxed_76_, v_h_74_, v_cast_75_);
lean_dec(v_cast_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg(lean_object* v_heq_78_){
_start:
{
lean_inc(v_heq_78_);
return v_heq_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg___boxed(lean_object* v_heq_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Meta_CongrArgKind_heq_elim___redArg(v_heq_79_);
lean_dec(v_heq_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim(lean_object* v_motive_81_, uint8_t v_t_82_, lean_object* v_h_83_, lean_object* v_heq_84_){
_start:
{
lean_inc(v_heq_84_);
return v_heq_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___boxed(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_heq_88_){
_start:
{
uint8_t v_t_boxed_89_; lean_object* v_res_90_; 
v_t_boxed_89_ = lean_unbox(v_t_86_);
v_res_90_ = l_Lean_Meta_CongrArgKind_heq_elim(v_motive_85_, v_t_boxed_89_, v_h_87_, v_heq_88_);
lean_dec(v_heq_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(lean_object* v_subsingletonInst_91_){
_start:
{
lean_inc(v_subsingletonInst_91_);
return v_subsingletonInst_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg___boxed(lean_object* v_subsingletonInst_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(v_subsingletonInst_92_);
lean_dec(v_subsingletonInst_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim(lean_object* v_motive_94_, uint8_t v_t_95_, lean_object* v_h_96_, lean_object* v_subsingletonInst_97_){
_start:
{
lean_inc(v_subsingletonInst_97_);
return v_subsingletonInst_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___boxed(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_subsingletonInst_101_){
_start:
{
uint8_t v_t_boxed_102_; lean_object* v_res_103_; 
v_t_boxed_102_ = lean_unbox(v_t_99_);
v_res_103_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim(v_motive_98_, v_t_boxed_102_, v_h_100_, v_subsingletonInst_101_);
lean_dec(v_subsingletonInst_101_);
return v_res_103_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind_default(void){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind(void){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(2u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr(uint8_t v_x_128_, lean_object* v_prec_129_){
_start:
{
lean_object* v___y_131_; lean_object* v___y_138_; lean_object* v___y_145_; lean_object* v___y_152_; lean_object* v___y_159_; lean_object* v___y_166_; 
switch(v_x_128_)
{
case 0:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_129_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_131_ = v___x_174_;
goto v___jp_130_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_131_ = v___x_175_;
goto v___jp_130_;
}
}
case 1:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1024u);
v___x_177_ = lean_nat_dec_le(v___x_176_, v_prec_129_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_138_ = v___x_178_;
goto v___jp_137_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_138_ = v___x_179_;
goto v___jp_137_;
}
}
case 2:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1024u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v_prec_129_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_145_ = v___x_182_;
goto v___jp_144_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_145_ = v___x_183_;
goto v___jp_144_;
}
}
case 3:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1024u);
v___x_185_ = lean_nat_dec_le(v___x_184_, v_prec_129_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_152_ = v___x_186_;
goto v___jp_151_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_152_ = v___x_187_;
goto v___jp_151_;
}
}
case 4:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(1024u);
v___x_189_ = lean_nat_dec_le(v___x_188_, v_prec_129_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_159_ = v___x_190_;
goto v___jp_158_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_159_ = v___x_191_;
goto v___jp_158_;
}
}
default: 
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(1024u);
v___x_193_ = lean_nat_dec_le(v___x_192_, v_prec_129_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_166_ = v___x_194_;
goto v___jp_165_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_166_ = v___x_195_;
goto v___jp_165_;
}
}
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__1));
lean_inc(v___y_131_);
v___x_133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_133_, 0, v___y_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_134_);
v___x_136_ = l_Repr_addAppParen(v___x_135_, v_prec_129_);
return v___x_136_;
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__3));
lean_inc(v___y_138_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = l_Repr_addAppParen(v___x_142_, v_prec_129_);
return v___x_143_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_146_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__5));
lean_inc(v___y_145_);
v___x_147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_147_, 0, v___y_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = 0;
v___x_149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = l_Repr_addAppParen(v___x_149_, v_prec_129_);
return v___x_150_;
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__7));
lean_inc(v___y_152_);
v___x_154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_154_, 0, v___y_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = 0;
v___x_156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_155_);
v___x_157_ = l_Repr_addAppParen(v___x_156_, v_prec_129_);
return v___x_157_;
}
v___jp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_160_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__9));
lean_inc(v___y_159_);
v___x_161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_161_, 0, v___y_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = 0;
v___x_163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_162_);
v___x_164_ = l_Repr_addAppParen(v___x_163_, v_prec_129_);
return v___x_164_;
}
v___jp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_167_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__11));
lean_inc(v___y_166_);
v___x_168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_168_, 0, v___y_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = 0;
v___x_170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*1, v___x_169_);
v___x_171_ = l_Repr_addAppParen(v___x_170_, v_prec_129_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr___boxed(lean_object* v_x_196_, lean_object* v_prec_197_){
_start:
{
uint8_t v_x_333__boxed_198_; lean_object* v_res_199_; 
v_x_333__boxed_198_ = lean_unbox(v_x_196_);
v_res_199_ = l_Lean_Meta_instReprCongrArgKind_repr(v_x_333__boxed_198_, v_prec_197_);
lean_dec(v_prec_197_);
return v_res_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t v_x_202_, uint8_t v_y_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_x_202_);
v___x_205_ = l_Lean_Meta_CongrArgKind_ctorIdx(v_y_203_);
v___x_206_ = lean_nat_dec_eq(v___x_204_, v___x_205_);
lean_dec(v___x_205_);
lean_dec(v___x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqCongrArgKind_beq___boxed(lean_object* v_x_207_, lean_object* v_y_208_){
_start:
{
uint8_t v_x_21__boxed_209_; uint8_t v_y_22__boxed_210_; uint8_t v_res_211_; lean_object* v_r_212_; 
v_x_21__boxed_209_ = lean_unbox(v_x_207_);
v_y_22__boxed_210_ = lean_unbox(v_y_208_);
v_res_211_ = l_Lean_Meta_instBEqCongrArgKind_beq(v_x_21__boxed_209_, v_y_22__boxed_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(lean_object* v_as_216_, size_t v_sz_217_, size_t v_i_218_, lean_object* v_b_219_){
_start:
{
uint8_t v___x_220_; 
v___x_220_ = lean_usize_dec_lt(v_i_218_, v_sz_217_);
if (v___x_220_ == 0)
{
return v_b_219_;
}
else
{
lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; size_t v___x_228_; size_t v___x_229_; 
v_a_221_ = lean_array_uget_borrowed(v_as_216_, v_i_218_);
lean_inc_ref(v_b_219_);
v___x_222_ = l_Lean_LocalContext_getFVar_x21(v_b_219_, v_a_221_);
v___x_223_ = l_Lean_LocalDecl_fvarId(v___x_222_);
v___x_224_ = l_Lean_LocalDecl_userName(v___x_222_);
lean_dec_ref(v___x_222_);
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0));
v___x_226_ = lean_name_append_after(v___x_224_, v___x_225_);
v___x_227_ = l_Lean_LocalContext_setUserName(v_b_219_, v___x_223_, v___x_226_);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_218_, v___x_228_);
v_i_218_ = v___x_229_;
v_b_219_ = v___x_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(lean_object* v_as_231_, lean_object* v_sz_232_, lean_object* v_i_233_, lean_object* v_b_234_){
_start:
{
size_t v_sz_boxed_235_; size_t v_i_boxed_236_; lean_object* v_res_237_; 
v_sz_boxed_235_ = lean_unbox_usize(v_sz_232_);
lean_dec(v_sz_232_);
v_i_boxed_236_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_as_231_, v_sz_boxed_235_, v_i_boxed_236_, v_b_234_);
lean_dec_ref(v_as_231_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(lean_object* v_ys_238_, lean_object* v_lctx_239_){
_start:
{
size_t v_sz_240_; size_t v___x_241_; lean_object* v___x_242_; 
v_sz_240_ = lean_array_size(v_ys_238_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_ys_238_, v_sz_240_, v___x_241_, v_lctx_239_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(lean_object* v_ys_243_, lean_object* v_lctx_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_243_, v_lctx_244_);
lean_dec_ref(v_ys_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(lean_object* v_as_246_, size_t v_sz_247_, size_t v_i_248_, lean_object* v_b_249_){
_start:
{
uint8_t v___x_250_; 
v___x_250_ = lean_usize_dec_lt(v_i_248_, v_sz_247_);
if (v___x_250_ == 0)
{
return v_b_249_;
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; size_t v___x_256_; size_t v___x_257_; 
v_a_251_ = lean_array_uget_borrowed(v_as_246_, v_i_248_);
lean_inc_ref(v_b_249_);
v___x_252_ = l_Lean_LocalContext_getFVar_x21(v_b_249_, v_a_251_);
v___x_253_ = l_Lean_LocalDecl_fvarId(v___x_252_);
lean_dec_ref(v___x_252_);
v___x_254_ = 0;
v___x_255_ = l_Lean_LocalContext_setBinderInfo(v_b_249_, v___x_253_, v___x_254_);
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_add(v_i_248_, v___x_256_);
v_i_248_ = v___x_257_;
v_b_249_ = v___x_255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(lean_object* v_as_259_, lean_object* v_sz_260_, lean_object* v_i_261_, lean_object* v_b_262_){
_start:
{
size_t v_sz_boxed_263_; size_t v_i_boxed_264_; lean_object* v_res_265_; 
v_sz_boxed_263_ = lean_unbox_usize(v_sz_260_);
lean_dec(v_sz_260_);
v_i_boxed_264_ = lean_unbox_usize(v_i_261_);
lean_dec(v_i_261_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_as_259_, v_sz_boxed_263_, v_i_boxed_264_, v_b_262_);
lean_dec_ref(v_as_259_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(lean_object* v_ys_266_, lean_object* v_lctx_267_){
_start:
{
size_t v_sz_268_; size_t v___x_269_; lean_object* v___x_270_; 
v_sz_268_ = lean_array_size(v_ys_266_);
v___x_269_ = ((size_t)0ULL);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_ys_266_, v_sz_268_, v___x_269_, v_lctx_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(lean_object* v_ys_271_, lean_object* v_lctx_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_271_, v_lctx_272_);
lean_dec_ref(v_ys_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_274_, lean_object* v_b_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; 
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
v___x_281_ = lean_apply_6(v_k_274_, v_b_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, lean_box(0));
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_282_, lean_object* v_b_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_282_, v_b_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(lean_object* v_name_290_, uint8_t v_bi_291_, lean_object* v_type_292_, lean_object* v_k_293_, uint8_t v_kind_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; 
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_300_, 0, v_k_293_);
v___x_301_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_290_, v_bi_291_, v_type_292_, v___f_300_, v_kind_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_310_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_301_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_301_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_318_, lean_object* v_bi_319_, lean_object* v_type_320_, lean_object* v_k_321_, lean_object* v_kind_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v_bi_boxed_328_; uint8_t v_kind_boxed_329_; lean_object* v_res_330_; 
v_bi_boxed_328_ = lean_unbox(v_bi_319_);
v_kind_boxed_329_ = lean_unbox(v_kind_322_);
v_res_330_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_318_, v_bi_boxed_328_, v_type_320_, v_k_321_, v_kind_boxed_329_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(lean_object* v_name_331_, lean_object* v_type_332_, lean_object* v_k_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
uint8_t v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; 
v___x_339_ = 0;
v___x_340_ = 0;
v___x_341_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_331_, v___x_339_, v_type_332_, v_k_333_, v___x_340_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg___boxed(lean_object* v_name_342_, lean_object* v_type_343_, lean_object* v_k_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_342_, v_type_343_, v_k_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_eqs_354_, lean_object* v_kinds_355_, lean_object* v_xs_356_, lean_object* v_ys_357_, lean_object* v_k_358_, lean_object* v___x_359_, lean_object* v_h_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(v_eqs_354_, v_kinds_355_, v_xs_356_, v_ys_357_, v_k_358_, v___x_359_, v_h_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___x_359_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(lean_object* v_eqs_367_, lean_object* v_kinds_368_, lean_object* v_xs_369_, lean_object* v_ys_370_, lean_object* v_k_371_, lean_object* v___x_372_, lean_object* v_h_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_379_ = lean_array_push(v_eqs_367_, v_h_373_);
v___x_380_ = 2;
v___x_381_ = lean_box(v___x_380_);
v___x_382_ = lean_array_push(v_kinds_368_, v___x_381_);
v___x_383_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_369_, v_ys_370_, v_k_371_, v___x_372_, v___x_379_, v___x_382_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(lean_object* v_eqs_384_, lean_object* v_kinds_385_, lean_object* v_xs_386_, lean_object* v_ys_387_, lean_object* v_k_388_, lean_object* v___x_389_, lean_object* v_h_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(v_eqs_384_, v_kinds_385_, v_xs_386_, v_ys_387_, v_k_388_, v___x_389_, v_h_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___x_389_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(lean_object* v_xs_397_, lean_object* v_ys_398_, lean_object* v_k_399_, lean_object* v_i_400_, lean_object* v_eqs_401_, lean_object* v_kinds_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_array_get_size(v_xs_397_);
v___x_409_ = lean_nat_dec_lt(v_i_400_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
lean_dec_ref(v_ys_398_);
lean_dec_ref(v_xs_397_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
lean_inc(v_a_404_);
lean_inc_ref(v_a_403_);
v___x_410_ = lean_apply_7(v_k_399_, v_eqs_401_, v_kinds_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, lean_box(0));
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v_x_412_; lean_object* v___x_413_; 
v___x_411_ = l_Lean_instInhabitedExpr;
v_x_412_ = lean_array_get_borrowed(v___x_411_, v_xs_397_, v_i_400_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
lean_inc(v_a_404_);
lean_inc_ref(v_a_403_);
lean_inc(v_x_412_);
v___x_413_ = lean_infer_type(v_x_412_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v_y_415_; lean_object* v___x_416_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v_y_415_ = lean_array_get_borrowed(v___x_411_, v_ys_398_, v_i_400_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
lean_inc(v_a_404_);
lean_inc_ref(v_a_403_);
lean_inc(v_y_415_);
v___x_416_ = lean_infer_type(v_y_415_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = l_Lean_Expr_cleanupAnnotations(v_a_414_);
v___x_419_ = l_Lean_Expr_cleanupAnnotations(v_a_417_);
v___x_420_ = lean_expr_eqv(v___x_418_, v___x_419_);
lean_dec_ref(v___x_419_);
lean_dec_ref(v___x_418_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_inc(v_y_415_);
lean_inc(v_x_412_);
v___x_421_ = l_Lean_Meta_mkHEq(v_x_412_, v_y_415_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_421_, 1);
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1));
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_add(v_i_400_, v___x_424_);
lean_inc(v___x_425_);
v___f_426_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_426_, 0, v_eqs_401_);
lean_closure_set(v___f_426_, 1, v_kinds_402_);
lean_closure_set(v___f_426_, 2, v_xs_397_);
lean_closure_set(v___f_426_, 3, v_ys_398_);
lean_closure_set(v___f_426_, 4, v_k_399_);
lean_closure_set(v___f_426_, 5, v___x_425_);
v___x_427_ = lean_name_append_index_after(v___x_423_, v___x_425_);
v___x_428_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_427_, v_a_422_, v___f_426_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
return v___x_428_;
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_kinds_402_);
lean_dec_ref(v_eqs_401_);
lean_dec_ref(v_k_399_);
lean_dec_ref(v_ys_398_);
lean_dec_ref(v_xs_397_);
v_a_429_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_421_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_421_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v___x_437_; 
lean_inc(v_y_415_);
lean_inc(v_x_412_);
v___x_437_ = l_Lean_Meta_mkEq(v_x_412_, v_y_415_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1));
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_i_400_, v___x_440_);
lean_inc(v___x_441_);
v___f_442_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_442_, 0, v_eqs_401_);
lean_closure_set(v___f_442_, 1, v_kinds_402_);
lean_closure_set(v___f_442_, 2, v_xs_397_);
lean_closure_set(v___f_442_, 3, v_ys_398_);
lean_closure_set(v___f_442_, 4, v_k_399_);
lean_closure_set(v___f_442_, 5, v___x_441_);
v___x_443_ = lean_name_append_index_after(v___x_439_, v___x_441_);
v___x_444_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_443_, v_a_438_, v___f_442_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
return v___x_444_;
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v_kinds_402_);
lean_dec_ref(v_eqs_401_);
lean_dec_ref(v_k_399_);
lean_dec_ref(v_ys_398_);
lean_dec_ref(v_xs_397_);
v_a_445_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_437_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_437_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_a_414_);
lean_dec_ref(v_kinds_402_);
lean_dec_ref(v_eqs_401_);
lean_dec_ref(v_k_399_);
lean_dec_ref(v_ys_398_);
lean_dec_ref(v_xs_397_);
v_a_453_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_416_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_416_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_kinds_402_);
lean_dec_ref(v_eqs_401_);
lean_dec_ref(v_k_399_);
lean_dec_ref(v_ys_398_);
lean_dec_ref(v_xs_397_);
v_a_461_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_413_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_413_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(lean_object* v_eqs_469_, lean_object* v_kinds_470_, lean_object* v_xs_471_, lean_object* v_ys_472_, lean_object* v_k_473_, lean_object* v___x_474_, lean_object* v_h_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_481_ = lean_array_push(v_eqs_469_, v_h_475_);
v___x_482_ = 4;
v___x_483_ = lean_box(v___x_482_);
v___x_484_ = lean_array_push(v_kinds_470_, v___x_483_);
v___x_485_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_471_, v_ys_472_, v_k_473_, v___x_474_, v___x_481_, v___x_484_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(lean_object* v_xs_486_, lean_object* v_ys_487_, lean_object* v_k_488_, lean_object* v_i_489_, lean_object* v_eqs_490_, lean_object* v_kinds_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_486_, v_ys_487_, v_k_488_, v_i_489_, v_eqs_490_, v_kinds_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_i_489_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_object* v_00_u03b1_498_, lean_object* v_xs_499_, lean_object* v_ys_500_, lean_object* v_k_501_, lean_object* v_i_502_, lean_object* v_eqs_503_, lean_object* v_kinds_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_499_, v_ys_500_, v_k_501_, v_i_502_, v_eqs_503_, v_kinds_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(lean_object* v_00_u03b1_511_, lean_object* v_xs_512_, lean_object* v_ys_513_, lean_object* v_k_514_, lean_object* v_i_515_, lean_object* v_eqs_516_, lean_object* v_kinds_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(v_00_u03b1_511_, v_xs_512_, v_ys_513_, v_k_514_, v_i_515_, v_eqs_516_, v_kinds_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_i_515_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(lean_object* v_00_u03b1_524_, lean_object* v_name_525_, uint8_t v_bi_526_, lean_object* v_type_527_, lean_object* v_k_528_, uint8_t v_kind_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_525_, v_bi_526_, v_type_527_, v_k_528_, v_kind_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_536_, lean_object* v_name_537_, lean_object* v_bi_538_, lean_object* v_type_539_, lean_object* v_k_540_, lean_object* v_kind_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
uint8_t v_bi_boxed_547_; uint8_t v_kind_boxed_548_; lean_object* v_res_549_; 
v_bi_boxed_547_ = lean_unbox(v_bi_538_);
v_kind_boxed_548_ = lean_unbox(v_kind_541_);
v_res_549_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_536_, v_name_537_, v_bi_boxed_547_, v_type_539_, v_k_540_, v_kind_boxed_548_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(lean_object* v_00_u03b1_550_, lean_object* v_name_551_, lean_object* v_type_552_, lean_object* v_k_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_551_, v_type_552_, v_k_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___boxed(lean_object* v_00_u03b1_560_, lean_object* v_name_561_, lean_object* v_type_562_, lean_object* v_k_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(v_00_u03b1_560_, v_name_561_, v_type_562_, v_k_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(lean_object* v_xs_572_, lean_object* v_ys_573_, lean_object* v_k_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_582_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_572_, v_ys_573_, v_k_574_, v___x_580_, v___x_581_, v___x_581_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___boxed(lean_object* v_xs_583_, lean_object* v_ys_584_, lean_object* v_k_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_583_, v_ys_584_, v_k_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(lean_object* v_00_u03b1_592_, lean_object* v_xs_593_, lean_object* v_ys_594_, lean_object* v_k_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_593_, v_ys_594_, v_k_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed(lean_object* v_00_u03b1_602_, lean_object* v_xs_603_, lean_object* v_ys_604_, lean_object* v_k_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(v_00_u03b1_602_, v_xs_603_, v_ys_604_, v_k_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(lean_object* v_k_612_, lean_object* v_b_613_, lean_object* v_c_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; 
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
v___x_620_ = lean_apply_7(v_k_612_, v_b_613_, v_c_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, lean_box(0));
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed(lean_object* v_k_621_, lean_object* v_b_622_, lean_object* v_c_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(v_k_621_, v_b_622_, v_c_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(lean_object* v_type_630_, lean_object* v_maxFVars_x3f_631_, lean_object* v_k_632_, uint8_t v_cleanupAnnotations_633_, uint8_t v_whnfType_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___f_640_; lean_object* v___x_641_; 
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_640_, 0, v_k_632_);
v___x_641_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_630_, v_maxFVars_x3f_631_, v___f_640_, v_cleanupAnnotations_633_, v_whnfType_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_a_650_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_641_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_641_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___boxed(lean_object* v_type_658_, lean_object* v_maxFVars_x3f_659_, lean_object* v_k_660_, lean_object* v_cleanupAnnotations_661_, lean_object* v_whnfType_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_668_; uint8_t v_whnfType_boxed_669_; lean_object* v_res_670_; 
v_cleanupAnnotations_boxed_668_ = lean_unbox(v_cleanupAnnotations_661_);
v_whnfType_boxed_669_ = lean_unbox(v_whnfType_662_);
v_res_670_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_658_, v_maxFVars_x3f_659_, v_k_660_, v_cleanupAnnotations_boxed_668_, v_whnfType_boxed_669_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(lean_object* v_00_u03b1_671_, lean_object* v_type_672_, lean_object* v_maxFVars_x3f_673_, lean_object* v_k_674_, uint8_t v_cleanupAnnotations_675_, uint8_t v_whnfType_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_672_, v_maxFVars_x3f_673_, v_k_674_, v_cleanupAnnotations_675_, v_whnfType_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___boxed(lean_object* v_00_u03b1_683_, lean_object* v_type_684_, lean_object* v_maxFVars_x3f_685_, lean_object* v_k_686_, lean_object* v_cleanupAnnotations_687_, lean_object* v_whnfType_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_694_; uint8_t v_whnfType_boxed_695_; lean_object* v_res_696_; 
v_cleanupAnnotations_boxed_694_ = lean_unbox(v_cleanupAnnotations_687_);
v_whnfType_boxed_695_ = lean_unbox(v_whnfType_688_);
v_res_696_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(v_00_u03b1_683_, v_type_684_, v_maxFVars_x3f_685_, v_k_686_, v_cleanupAnnotations_boxed_694_, v_whnfType_boxed_695_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v_a_710_, lean_object* v_type_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
uint8_t v___x_1901__boxed_717_; lean_object* v_res_718_; 
v___x_1901__boxed_717_ = lean_unbox(v___x_707_);
v_res_718_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(v___x_705_, v___x_706_, v___x_1901__boxed_717_, v___x_708_, v___x_709_, v_a_710_, v_type_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v_a_710_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(lean_object* v_type_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_726_ = lean_unsigned_to_nat(3u);
v___x_727_ = l_Lean_Expr_isAppOfArity(v_type_719_, v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3));
v___x_729_ = lean_unsigned_to_nat(4u);
v___x_730_ = l_Lean_Expr_isAppOfArity(v_type_719_, v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___f_735_; uint8_t v___x_736_; lean_object* v___x_737_; 
v___x_731_ = l_Lean_instInhabitedExpr;
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_734_ = lean_box(v___x_730_);
v___f_735_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed), 12, 5);
lean_closure_set(v___f_735_, 0, v___x_731_);
lean_closure_set(v___f_735_, 1, v___x_732_);
lean_closure_set(v___f_735_, 2, v___x_734_);
lean_closure_set(v___f_735_, 3, v___x_726_);
lean_closure_set(v___f_735_, 4, v___x_733_);
v___x_736_ = 1;
v___x_737_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_719_, v___x_733_, v___f_735_, v___x_736_, v___x_730_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_738_ = l_Lean_Expr_appFn_x21(v_type_719_);
lean_dec_ref(v_type_719_);
v___x_739_ = l_Lean_Expr_appFn_x21(v___x_738_);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Lean_Expr_appArg_x21(v___x_739_);
lean_dec_ref(v___x_739_);
v___x_741_ = l_Lean_Meta_mkHEqRefl(v___x_740_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_741_;
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = l_Lean_Expr_appFn_x21(v_type_719_);
lean_dec_ref(v_type_719_);
v___x_743_ = l_Lean_Expr_appArg_x21(v___x_742_);
lean_dec_ref(v___x_742_);
v___x_744_ = l_Lean_Meta_mkEqRefl(v___x_743_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(lean_object* v_type_745_, lean_object* v_motive_746_, lean_object* v___x_747_, lean_object* v_b_748_, uint8_t v___x_749_, lean_object* v___x_750_, lean_object* v_a_751_, lean_object* v_eqPr_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_type_758_; lean_object* v___x_759_; 
v_type_758_ = l_Lean_Expr_bindingBody_x21(v_type_745_);
v___x_759_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_758_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc_ref(v_eqPr_752_);
v___x_761_ = lean_infer_type(v_eqPr_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
v___x_763_ = lean_whnf(v_a_762_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v_motive_765_; lean_object* v_major_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; uint8_t v___x_785_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v_motive_765_ = l_Lean_Expr_bindingBody_x21(v_motive_746_);
v___x_785_ = l_Lean_Expr_isHEq(v_a_764_);
lean_dec(v_a_764_);
if (v___x_785_ == 0)
{
lean_inc_ref(v_eqPr_752_);
v_major_767_ = v_eqPr_752_;
v___y_768_ = v___y_753_;
v___y_769_ = v___y_754_;
v___y_770_ = v___y_755_;
v___y_771_ = v___y_756_;
goto v___jp_766_;
}
else
{
lean_object* v___x_786_; 
lean_inc_ref(v_eqPr_752_);
v___x_786_ = l_Lean_Meta_mkEqOfHEq(v_eqPr_752_, v___x_785_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v_major_767_ = v_a_787_;
v___y_768_ = v___y_753_;
v___y_769_ = v___y_754_;
v___y_770_ = v___y_755_;
v___y_771_ = v___y_756_;
goto v___jp_766_;
}
else
{
lean_dec_ref(v_motive_765_);
lean_dec(v_a_760_);
lean_dec_ref(v_eqPr_752_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_b_748_);
return v___x_786_;
}
}
v___jp_766_:
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; 
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_747_);
lean_inc_ref(v_b_748_);
v___x_773_ = lean_array_push(v___x_772_, v_b_748_);
v___x_774_ = 1;
v___x_775_ = 1;
v___x_776_ = l_Lean_Meta_mkLambdaFVars(v___x_773_, v_motive_765_, v___x_749_, v___x_774_, v___x_749_, v___x_774_, v___x_775_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec_ref(v___x_773_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = l_Lean_Meta_mkEqNDRec(v_a_777_, v_a_760_, v_major_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = lean_mk_empty_array_with_capacity(v___x_750_);
v___x_781_ = lean_array_push(v___x_780_, v_a_751_);
v___x_782_ = lean_array_push(v___x_781_, v_b_748_);
v___x_783_ = lean_array_push(v___x_782_, v_eqPr_752_);
v___x_784_ = l_Lean_Meta_mkLambdaFVars(v___x_783_, v_a_779_, v___x_749_, v___x_774_, v___x_749_, v___x_774_, v___x_775_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec_ref(v___x_783_);
return v___x_784_;
}
else
{
lean_dec_ref(v_eqPr_752_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_b_748_);
return v___x_778_;
}
}
else
{
lean_dec_ref(v_major_767_);
lean_dec(v_a_760_);
lean_dec_ref(v_eqPr_752_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_b_748_);
return v___x_776_;
}
}
}
else
{
lean_dec(v_a_760_);
lean_dec_ref(v_eqPr_752_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_b_748_);
return v___x_763_;
}
}
else
{
lean_dec(v_a_760_);
lean_dec_ref(v_eqPr_752_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_b_748_);
return v___x_761_;
}
}
else
{
lean_dec_ref(v_eqPr_752_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_b_748_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(lean_object* v_type_788_, lean_object* v_motive_789_, lean_object* v___x_790_, lean_object* v_b_791_, lean_object* v___x_792_, lean_object* v___x_793_, lean_object* v_a_794_, lean_object* v_eqPr_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
uint8_t v___x_1957__boxed_801_; lean_object* v_res_802_; 
v___x_1957__boxed_801_ = lean_unbox(v___x_792_);
v_res_802_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(v_type_788_, v_motive_789_, v___x_790_, v_b_791_, v___x_1957__boxed_801_, v___x_793_, v_a_794_, v_eqPr_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___x_793_);
lean_dec(v___x_790_);
lean_dec_ref(v_motive_789_);
lean_dec_ref(v_type_788_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(lean_object* v___x_803_, lean_object* v___x_804_, lean_object* v_type_805_, lean_object* v_a_806_, lean_object* v___x_807_, uint8_t v___x_808_, lean_object* v___x_809_, lean_object* v_b_810_, lean_object* v_motive_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_b_817_; lean_object* v___x_818_; lean_object* v_type_819_; lean_object* v___x_820_; lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_b_817_ = lean_array_get_borrowed(v___x_803_, v_b_810_, v___x_804_);
v___x_818_ = l_Lean_Expr_bindingBody_x21(v_type_805_);
v_type_819_ = lean_expr_instantiate1(v___x_818_, v_a_806_);
lean_dec_ref(v___x_818_);
v___x_820_ = lean_box(v___x_808_);
lean_inc(v_b_817_);
lean_inc_ref(v_motive_811_);
v___f_821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed), 13, 7);
lean_closure_set(v___f_821_, 0, v_type_819_);
lean_closure_set(v___f_821_, 1, v_motive_811_);
lean_closure_set(v___f_821_, 2, v___x_807_);
lean_closure_set(v___f_821_, 3, v_b_817_);
lean_closure_set(v___f_821_, 4, v___x_820_);
lean_closure_set(v___f_821_, 5, v___x_809_);
lean_closure_set(v___f_821_, 6, v_a_806_);
v___x_822_ = l_Lean_Expr_bindingName_x21(v_motive_811_);
v___x_823_ = l_Lean_Expr_bindingDomain_x21(v_motive_811_);
lean_dec_ref(v_motive_811_);
v___x_824_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_822_, v___x_823_, v___f_821_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(lean_object* v___x_825_, lean_object* v___x_826_, lean_object* v_type_827_, lean_object* v_a_828_, lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v_b_832_, lean_object* v_motive_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_1916__boxed_839_; lean_object* v_res_840_; 
v___x_1916__boxed_839_ = lean_unbox(v___x_830_);
v_res_840_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(v___x_825_, v___x_826_, v_type_827_, v_a_828_, v___x_829_, v___x_1916__boxed_839_, v___x_831_, v_b_832_, v_motive_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v_b_832_);
lean_dec_ref(v_type_827_);
lean_dec(v___x_826_);
lean_dec_ref(v___x_825_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object* v___x_841_, lean_object* v___x_842_, uint8_t v___x_843_, lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v_a_846_, lean_object* v_type_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v___f_856_; uint8_t v___x_857_; lean_object* v___x_858_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v_a_854_ = lean_array_get(v___x_841_, v_a_846_, v___x_853_);
v___x_855_ = lean_box(v___x_843_);
lean_inc_ref(v_type_847_);
v___f_856_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed), 14, 7);
lean_closure_set(v___f_856_, 0, v___x_841_);
lean_closure_set(v___f_856_, 1, v___x_853_);
lean_closure_set(v___f_856_, 2, v_type_847_);
lean_closure_set(v___f_856_, 3, v_a_854_);
lean_closure_set(v___f_856_, 4, v___x_842_);
lean_closure_set(v___f_856_, 5, v___x_855_);
lean_closure_set(v___f_856_, 6, v___x_844_);
v___x_857_ = 1;
v___x_858_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_847_, v___x_845_, v___f_856_, v___x_857_, v___x_843_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___boxed(lean_object* v_type_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(lean_object* v_lctx_866_, lean_object* v_localInsts_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_866_, v_localInsts_867_, v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_874_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_874_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(lean_object* v_lctx_891_, lean_object* v_localInsts_892_, lean_object* v_x_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_891_, v_localInsts_892_, v_x_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_object* v_00_u03b1_900_, lean_object* v_lctx_901_, lean_object* v_localInsts_902_, lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_901_, v_localInsts_902_, v_x_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(lean_object* v_00_u03b1_910_, lean_object* v_lctx_911_, lean_object* v_localInsts_912_, lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(v_00_u03b1_910_, v_lctx_911_, v_localInsts_912_, v_x_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(lean_object* v_as_920_, size_t v_sz_921_, size_t v_i_922_, lean_object* v_b_923_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_lt(v_i_922_, v_sz_921_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v_b_923_);
return v___x_926_;
}
else
{
lean_object* v_snd_927_; lean_object* v_snd_928_; lean_object* v_fst_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_999_; 
v_snd_927_ = lean_ctor_get(v_b_923_, 1);
lean_inc(v_snd_927_);
v_snd_928_ = lean_ctor_get(v_snd_927_, 1);
lean_inc(v_snd_928_);
v_fst_929_ = lean_ctor_get(v_b_923_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_b_923_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v_b_923_, 1);
lean_dec(v_unused_1000_);
v___x_931_ = v_b_923_;
v_isShared_932_ = v_isSharedCheck_999_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_fst_929_);
lean_dec(v_b_923_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_999_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_fst_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_997_; 
v_fst_933_ = lean_ctor_get(v_snd_927_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_snd_927_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_snd_927_, 1);
lean_dec(v_unused_998_);
v___x_935_ = v_snd_927_;
v_isShared_936_ = v_isSharedCheck_997_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_fst_933_);
lean_dec(v_snd_927_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_997_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_array_937_; lean_object* v_start_938_; lean_object* v_stop_939_; uint8_t v___x_940_; 
v_array_937_ = lean_ctor_get(v_snd_928_, 0);
v_start_938_ = lean_ctor_get(v_snd_928_, 1);
v_stop_939_ = lean_ctor_get(v_snd_928_, 2);
v___x_940_ = lean_nat_dec_lt(v_start_938_, v_stop_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_942_; 
if (v_isShared_936_ == 0)
{
v___x_942_ = v___x_935_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_933_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_928_);
v___x_942_ = v_reuseFailAlloc_947_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_942_);
v___x_944_ = v___x_931_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_fst_929_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_942_);
v___x_944_ = v_reuseFailAlloc_946_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
}
else
{
lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_993_; 
lean_inc(v_stop_939_);
lean_inc(v_start_938_);
lean_inc_ref(v_array_937_);
v_isSharedCheck_993_ = !lean_is_exclusive(v_snd_928_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; lean_object* v_unused_995_; lean_object* v_unused_996_; 
v_unused_994_ = lean_ctor_get(v_snd_928_, 2);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_snd_928_, 1);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_snd_928_, 0);
lean_dec(v_unused_996_);
v___x_949_ = v_snd_928_;
v_isShared_950_ = v_isSharedCheck_993_;
goto v_resetjp_948_;
}
else
{
lean_dec(v_snd_928_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_993_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_array_951_; lean_object* v_start_952_; lean_object* v_stop_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v_array_951_ = lean_ctor_get(v_fst_933_, 0);
v_start_952_ = lean_ctor_get(v_fst_933_, 1);
v_stop_953_ = lean_ctor_get(v_fst_933_, 2);
v___x_954_ = lean_array_fget(v_array_937_, v_start_938_);
v___x_955_ = lean_unsigned_to_nat(1u);
v___x_956_ = lean_nat_add(v_start_938_, v___x_955_);
lean_dec(v_start_938_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___x_956_);
v___x_958_ = v___x_949_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_array_937_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_stop_939_);
v___x_958_ = v_reuseFailAlloc_992_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_lt(v_start_952_, v_stop_953_);
if (v___x_959_ == 0)
{
lean_object* v___x_961_; 
lean_dec(v___x_954_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v___x_958_);
v___x_961_ = v___x_935_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_fst_933_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_958_);
v___x_961_ = v_reuseFailAlloc_966_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_961_);
v___x_963_ = v___x_931_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_fst_929_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; 
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
else
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_988_; 
lean_inc(v_stop_953_);
lean_inc(v_start_952_);
lean_inc_ref(v_array_951_);
v_isSharedCheck_988_ = !lean_is_exclusive(v_fst_933_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; 
v_unused_989_ = lean_ctor_get(v_fst_933_, 2);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_fst_933_, 1);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_fst_933_, 0);
lean_dec(v_unused_991_);
v___x_968_ = v_fst_933_;
v_isShared_969_ = v_isSharedCheck_988_;
goto v_resetjp_967_;
}
else
{
lean_dec(v_fst_933_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_988_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v_a_970_ = lean_array_uget_borrowed(v_as_920_, v_i_922_);
v___x_971_ = lean_array_fget(v_array_951_, v_start_952_);
v___x_972_ = lean_nat_add(v_start_952_, v___x_955_);
lean_dec(v_start_952_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v___x_972_);
v___x_974_ = v___x_968_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_array_951_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_stop_953_);
v___x_974_ = v_reuseFailAlloc_987_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
lean_inc(v_a_970_);
v___x_975_ = lean_array_push(v_fst_929_, v_a_970_);
v___x_976_ = lean_array_push(v___x_975_, v___x_971_);
v___x_977_ = lean_array_push(v___x_976_, v___x_954_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v___x_958_);
lean_ctor_set(v___x_935_, 0, v___x_974_);
v___x_979_ = v___x_935_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_958_);
v___x_979_ = v_reuseFailAlloc_986_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_981_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_979_);
lean_ctor_set(v___x_931_, 0, v___x_977_);
v___x_981_ = v___x_931_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
size_t v___x_982_; size_t v___x_983_; 
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_922_, v___x_982_);
v_i_922_ = v___x_983_;
v_b_923_ = v___x_981_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(lean_object* v_as_1001_, lean_object* v_sz_1002_, lean_object* v_i_1003_, lean_object* v_b_1004_, lean_object* v___y_1005_){
_start:
{
size_t v_sz_boxed_1006_; size_t v_i_boxed_1007_; lean_object* v_res_1008_; 
v_sz_boxed_1006_ = lean_unbox_usize(v_sz_1002_);
lean_dec(v_sz_1002_);
v_i_boxed_1007_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_res_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_1001_, v_sz_boxed_1006_, v_i_boxed_1007_, v_b_1004_);
lean_dec_ref(v_as_1001_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object* v_ys_1009_, lean_object* v_xs_1010_, lean_object* v_f_1011_, uint8_t v___x_1012_, uint8_t v___x_1013_, lean_object* v_eqs_1014_, lean_object* v_argKinds_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; size_t v_sz_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_1023_ = lean_array_get_size(v_ys_1009_);
lean_inc_ref(v_ys_1009_);
v___x_1024_ = l_Array_toSubarray___redArg(v_ys_1009_, v___x_1021_, v___x_1023_);
v___x_1025_ = lean_array_get_size(v_eqs_1014_);
v___x_1026_ = l_Array_toSubarray___redArg(v_eqs_1014_, v___x_1021_, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1024_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1022_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v_sz_1029_ = lean_array_size(v_xs_1010_);
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_xs_1010_, v_sz_1029_, v___x_1030_, v___x_1028_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
lean_inc_ref(v_f_1011_);
v___x_1033_ = l_Lean_mkAppN(v_f_1011_, v_xs_1010_);
v___x_1034_ = l_Lean_mkAppN(v_f_1011_, v_ys_1009_);
lean_dec_ref(v_ys_1009_);
v___x_1035_ = l_Lean_Meta_mkHEq(v___x_1033_, v___x_1034_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v_fst_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v_fst_1037_ = lean_ctor_get(v_a_1032_, 0);
lean_inc(v_fst_1037_);
lean_dec(v_a_1032_);
v___x_1038_ = 1;
v___x_1039_ = l_Lean_Meta_mkForallFVars(v_fst_1037_, v_a_1036_, v___x_1012_, v___x_1013_, v___x_1013_, v___x_1038_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v_fst_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc_n(v_a_1040_, 2);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_a_1040_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1050_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1046_, 0, v_a_1040_);
lean_ctor_set(v___x_1046_, 1, v_a_1042_);
lean_ctor_set(v___x_1046_, 2, v_argKinds_1015_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1040_);
lean_dec_ref(v_argKinds_1015_);
v_a_1051_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1041_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1041_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_argKinds_1015_);
v_a_1059_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1039_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1039_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_1032_);
lean_dec_ref(v_argKinds_1015_);
v_a_1067_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1035_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1035_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref(v_argKinds_1015_);
lean_dec_ref(v_f_1011_);
lean_dec_ref(v_ys_1009_);
v_a_1075_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1031_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1031_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object* v_ys_1083_, lean_object* v_xs_1084_, lean_object* v_f_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v_eqs_1088_, lean_object* v_argKinds_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v___x_4530__boxed_1095_; uint8_t v___x_4531__boxed_1096_; lean_object* v_res_1097_; 
v___x_4530__boxed_1095_ = lean_unbox(v___x_1086_);
v___x_4531__boxed_1096_ = lean_unbox(v___x_1087_);
v_res_1097_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1083_, v_xs_1084_, v_f_1085_, v___x_4530__boxed_1095_, v___x_4531__boxed_1096_, v_eqs_1088_, v_argKinds_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v_xs_1084_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(lean_object* v_msgData_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v_env_1105_; lean_object* v___x_1106_; lean_object* v_toCold_1107_; lean_object* v_mctx_1108_; lean_object* v_lctx_1109_; lean_object* v_options_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1104_ = lean_st_ref_get(v___y_1102_);
v_env_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_env_1105_);
lean_dec(v___x_1104_);
v___x_1106_ = lean_st_ref_get(v___y_1100_);
v_toCold_1107_ = lean_ctor_get(v___y_1101_, 0);
v_mctx_1108_ = lean_ctor_get(v___x_1106_, 0);
lean_inc_ref(v_mctx_1108_);
lean_dec(v___x_1106_);
v_lctx_1109_ = lean_ctor_get(v___y_1099_, 2);
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
lean_ctor_set(v___x_1112_, 1, v_msgData_1098_);
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
uint8_t v___x_5199__boxed_1705_; lean_object* v_res_1706_; 
v___x_5199__boxed_1705_ = lean_unbox(v___x_1698_);
v_res_1706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1693_, v_val_1694_, v_xs_1695_, v___x_1696_, v___x_1697_, v___x_5199__boxed_1705_, v_a_1699_, v_b_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
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
uint8_t v___x_5286__boxed_1752_; lean_object* v_res_1753_; 
v___x_5286__boxed_1752_ = lean_unbox(v___x_1744_);
v_res_1753_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1742_, v_induct_1743_, v___x_5286__boxed_1752_, v_xs_1745_, v_x_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
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
v___x_1754_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
lean_ctor_set(v___x_1759_, 2, v___x_1758_);
lean_ctor_set(v___x_1759_, 3, v___x_1758_);
lean_ctor_set(v___x_1759_, 4, v___x_1757_);
lean_ctor_set(v___x_1759_, 5, v___x_1757_);
lean_ctor_set(v___x_1759_, 6, v___x_1757_);
lean_ctor_set(v___x_1759_, 7, v___x_1757_);
lean_ctor_set(v___x_1759_, 8, v___x_1757_);
lean_ctor_set(v___x_1759_, 9, v___x_1757_);
lean_ctor_set(v___x_1759_, 10, v___x_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_unsigned_to_nat(32u);
v___x_1761_ = lean_mk_empty_array_with_capacity(v___x_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1763_ = ((size_t)5ULL);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_unsigned_to_nat(32u);
v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___x_1767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1768_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___x_1766_);
lean_ctor_set(v___x_1768_, 2, v___x_1764_);
lean_ctor_set(v___x_1768_, 3, v___x_1764_);
lean_ctor_set_usize(v___x_1768_, 4, v___x_1763_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = lean_box(1);
v___x_1770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1770_);
lean_ctor_set(v___x_1772_, 2, v___x_1769_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1790_ = l_Lean_stringToMessageData(v___x_1789_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1793_ = l_Lean_stringToMessageData(v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1794_, lean_object* v_declHint_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v_env_1799_; uint8_t v___x_1800_; 
v___x_1798_ = lean_st_ref_get(v___y_1796_);
v_env_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc_ref(v_env_1799_);
lean_dec(v___x_1798_);
v___x_1800_ = l_Lean_Name_isAnonymous(v_declHint_1795_);
if (v___x_1800_ == 0)
{
uint8_t v_isExporting_1801_; 
v_isExporting_1801_ = lean_ctor_get_uint8(v_env_1799_, sizeof(void*)*8);
if (v_isExporting_1801_ == 0)
{
lean_object* v___x_1802_; 
lean_dec_ref(v_env_1799_);
lean_dec(v_declHint_1795_);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_msg_1794_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
lean_inc_ref(v_env_1799_);
v___x_1803_ = l_Lean_Environment_setExporting(v_env_1799_, v___x_1800_);
lean_inc(v_declHint_1795_);
lean_inc_ref(v___x_1803_);
v___x_1804_ = l_Lean_Environment_contains(v___x_1803_, v_declHint_1795_, v_isExporting_1801_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_dec_ref(v___x_1803_);
lean_dec_ref(v_env_1799_);
lean_dec(v_declHint_1795_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_msg_1794_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v_c_1811_; lean_object* v___x_1812_; 
v___x_1806_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1807_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1808_ = l_Lean_Options_empty;
v___x_1809_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1803_);
lean_ctor_set(v___x_1809_, 1, v___x_1806_);
lean_ctor_set(v___x_1809_, 2, v___x_1807_);
lean_ctor_set(v___x_1809_, 3, v___x_1808_);
lean_inc(v_declHint_1795_);
v___x_1810_ = l_Lean_MessageData_ofConstName(v_declHint_1795_, v___x_1800_);
v_c_1811_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1811_, 0, v___x_1809_);
lean_ctor_set(v_c_1811_, 1, v___x_1810_);
v___x_1812_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1799_, v_declHint_1795_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec_ref(v_env_1799_);
lean_dec(v_declHint_1795_);
v___x_1813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v_c_1811_);
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_MessageData_note(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_msg_1794_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1855_; 
v_val_1820_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1822_ = v___x_1812_;
v_isShared_1823_ = v_isSharedCheck_1855_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_val_1820_);
lean_dec(v___x_1812_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1855_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v_mod_1827_; uint8_t v___x_1828_; 
v___x_1824_ = lean_box(0);
v___x_1825_ = l_Lean_Environment_header(v_env_1799_);
lean_dec_ref(v_env_1799_);
v___x_1826_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1825_);
v_mod_1827_ = lean_array_get(v___x_1824_, v___x_1826_, v_val_1820_);
lean_dec(v_val_1820_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = l_Lean_isPrivateName(v_declHint_1795_);
lean_dec(v_declHint_1795_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v_c_1811_);
v___x_1831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = l_Lean_MessageData_ofName(v_mod_1827_);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = l_Lean_MessageData_note(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_msg_1794_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1838_);
v___x_1840_ = v___x_1822_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v_c_1811_);
v___x_1844_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = l_Lean_MessageData_ofName(v_mod_1827_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_MessageData_note(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v_msg_1794_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1851_);
v___x_1853_ = v___x_1822_;
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
}
}
}
}
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v_env_1799_);
lean_dec(v_declHint_1795_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_msg_1794_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1857_, lean_object* v_declHint_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1857_, v_declHint_1858_, v___y_1859_);
lean_dec(v___y_1859_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msg_1862_, lean_object* v_declHint_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1879_; 
v___x_1869_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1862_, v_declHint_1863_, v___y_1867_);
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1874_ = l_Lean_unknownIdentifierMessageTag;
v___x_1875_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_a_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1875_);
v___x_1877_ = v___x_1872_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1880_, lean_object* v_declHint_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1880_, v_declHint_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1888_, lean_object* v_msg_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_toCold_1895_; lean_object* v_currRecDepth_1896_; lean_object* v_ref_1897_; uint8_t v_diag_1898_; uint8_t v_suppressElabErrors_1899_; lean_object* v_ref_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v_toCold_1895_ = lean_ctor_get(v___y_1892_, 0);
v_currRecDepth_1896_ = lean_ctor_get(v___y_1892_, 1);
v_ref_1897_ = lean_ctor_get(v___y_1892_, 2);
v_diag_1898_ = lean_ctor_get_uint8(v___y_1892_, sizeof(void*)*3);
v_suppressElabErrors_1899_ = lean_ctor_get_uint8(v___y_1892_, sizeof(void*)*3 + 1);
v_ref_1900_ = l_Lean_replaceRef(v_ref_1888_, v_ref_1897_);
lean_inc(v_currRecDepth_1896_);
lean_inc_ref(v_toCold_1895_);
v___x_1901_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1901_, 0, v_toCold_1895_);
lean_ctor_set(v___x_1901_, 1, v_currRecDepth_1896_);
lean_ctor_set(v___x_1901_, 2, v_ref_1900_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3, v_diag_1898_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 1, v_suppressElabErrors_1899_);
v___x_1902_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1889_, v___y_1890_, v___y_1891_, v___x_1901_, v___y_1893_);
lean_dec_ref_known(v___x_1901_, 3);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1903_, lean_object* v_msg_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1903_, v_msg_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v_ref_1903_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1911_, lean_object* v_msg_1912_, lean_object* v_declHint_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1921_; 
v___x_1919_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1912_, v_declHint_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1911_, v_a_1920_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1922_, lean_object* v_msg_1923_, lean_object* v_declHint_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1922_, v_msg_1923_, v_declHint_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v_ref_1922_);
return v_res_1930_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1933_ = l_Lean_stringToMessageData(v___x_1932_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1936_ = l_Lean_stringToMessageData(v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1937_, lean_object* v_constName_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1944_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1945_ = 0;
lean_inc(v_constName_1938_);
v___x_1946_ = l_Lean_MessageData_ofConstName(v_constName_1938_, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1944_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1937_, v___x_1949_, v_constName_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1951_, lean_object* v_constName_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1951_, v_constName_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v_ref_1951_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_ref_1965_; lean_object* v___x_1966_; 
v_ref_1965_ = lean_ctor_get(v___y_1962_, 2);
v___x_1966_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1965_, v_constName_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v_env_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1980_ = lean_st_ref_get(v___y_1978_);
v_env_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc_ref(v_env_1981_);
lean_dec(v___x_1980_);
v___x_1982_ = 0;
lean_inc(v_constName_1974_);
v___x_1983_ = l_Lean_Environment_find_x3f(v_env_1981_, v_constName_1974_, v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v___x_1984_;
}
else
{
lean_object* v_val_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_constName_1974_);
v_val_1985_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1983_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_val_1985_);
lean_dec(v___x_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 0);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_val_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
if (lean_obj_tag(v_f_2000_) == 4)
{
lean_object* v_declName_2006_; lean_object* v___x_2007_; 
v_declName_2006_ = lean_ctor_get(v_f_2000_, 0);
lean_inc(v_declName_2006_);
lean_dec_ref_known(v_f_2000_, 2);
v___x_2007_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2006_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2031_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2031_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2031_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
if (lean_obj_tag(v_a_2008_) == 6)
{
lean_object* v_val_2012_; lean_object* v___x_2013_; lean_object* v_env_2014_; lean_object* v_toConstantVal_2015_; lean_object* v_induct_2016_; uint8_t v___x_2017_; 
v_val_2012_ = lean_ctor_get(v_a_2008_, 0);
lean_inc_ref(v_val_2012_);
lean_dec_ref_known(v_a_2008_, 1);
v___x_2013_ = lean_st_ref_get(v_a_2004_);
v_env_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_ref(v_env_2014_);
lean_dec(v___x_2013_);
v_toConstantVal_2015_ = lean_ctor_get(v_val_2012_, 0);
v_induct_2016_ = lean_ctor_get(v_val_2012_, 1);
lean_inc(v_induct_2016_);
v___x_2017_ = l_Lean_isClass(v_env_2014_, v_induct_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
lean_dec(v_induct_2016_);
lean_dec_ref(v_val_2012_);
v___x_2018_ = lean_box(0);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2018_);
v___x_2020_ = v___x_2010_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
else
{
lean_object* v_type_2022_; lean_object* v___x_2023_; lean_object* v___f_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; 
lean_del_object(v___x_2010_);
v_type_2022_ = lean_ctor_get(v_toConstantVal_2015_, 2);
lean_inc_ref(v_type_2022_);
v___x_2023_ = lean_box(v___x_2017_);
v___f_2024_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2024_, 0, v_val_2012_);
lean_closure_set(v___f_2024_, 1, v_induct_2016_);
lean_closure_set(v___f_2024_, 2, v___x_2023_);
v___x_2025_ = 0;
v___x_2026_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2022_, v___f_2024_, v___x_2017_, v___x_2025_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2026_;
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
lean_dec(v_a_2008_);
v___x_2027_ = lean_box(0);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2027_);
v___x_2029_ = v___x_2010_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_a_2032_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2007_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2007_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_dec_ref(v_f_2000_);
v___x_2040_ = lean_box(0);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2049_, lean_object* v_val_2050_, lean_object* v_xs_2051_, lean_object* v___x_2052_, lean_object* v___x_2053_, uint8_t v___x_2054_, lean_object* v_inst_2055_, lean_object* v_R_2056_, lean_object* v_a_2057_, lean_object* v_b_2058_, lean_object* v_c_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2049_, v_val_2050_, v_xs_2051_, v___x_2052_, v___x_2053_, v___x_2054_, v_a_2057_, v_b_2058_, v___y_2060_, v___y_2062_, v___y_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2066_, lean_object* v_val_2067_, lean_object* v_xs_2068_, lean_object* v___x_2069_, lean_object* v___x_2070_, lean_object* v___x_2071_, lean_object* v_inst_2072_, lean_object* v_R_2073_, lean_object* v_a_2074_, lean_object* v_b_2075_, lean_object* v_c_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v___x_5868__boxed_2082_; lean_object* v_res_2083_; 
v___x_5868__boxed_2082_ = lean_unbox(v___x_2071_);
v_res_2083_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2066_, v_val_2067_, v_xs_2068_, v___x_2069_, v___x_2070_, v___x_5868__boxed_2082_, v_inst_2072_, v_R_2073_, v_a_2074_, v_b_2075_, v_c_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v_xs_2068_);
lean_dec_ref(v_val_2067_);
lean_dec(v_upperBound_2066_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2084_, lean_object* v_constName_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2092_, lean_object* v_constName_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2092_, v_constName_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2100_, lean_object* v_ref_2101_, lean_object* v_constName_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2101_, v_constName_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2109_, lean_object* v_ref_2110_, lean_object* v_constName_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2109_, v_ref_2110_, v_constName_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v_ref_2110_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2118_, lean_object* v_ref_2119_, lean_object* v_msg_2120_, lean_object* v_declHint_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2119_, v_msg_2120_, v_declHint_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_ref_2129_, lean_object* v_msg_2130_, lean_object* v_declHint_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2128_, v_ref_2129_, v_msg_2130_, v_declHint_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_ref_2129_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2138_, lean_object* v_declHint_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2138_, v_declHint_2139_, v___y_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2146_, lean_object* v_declHint_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2146_, v_declHint_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2154_, lean_object* v_ref_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2155_, v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_ref_2164_, lean_object* v_msg_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2163_, v_ref_2164_, v_msg_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v_ref_2164_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2172_, lean_object* v_a_2173_, lean_object* v_____r_2174_, lean_object* v_result_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
uint8_t v___x_2181_; 
v___x_2181_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2172_, v_result_2175_, v_a_2173_);
if (v___x_2181_ == 0)
{
uint8_t v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2182_ = 0;
v___x_2183_ = lean_box(v___x_2182_);
v___x_2184_ = lean_array_push(v_result_2175_, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
else
{
uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2187_ = 5;
v___x_2188_ = lean_box(v___x_2187_);
v___x_2189_ = lean_array_push(v_result_2175_, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2192_, lean_object* v_a_2193_, lean_object* v_____r_2194_, lean_object* v_result_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2192_, v_a_2193_, v_____r_2194_, v_result_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v_a_2193_);
lean_dec_ref(v_info_2192_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2202_, lean_object* v_upperBound_2203_, lean_object* v___x_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_b_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_a_2214_; lean_object* v___y_2219_; uint8_t v___x_2238_; 
v___x_2238_ = lean_nat_dec_lt(v_a_2206_, v_upperBound_2203_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
lean_dec(v_a_2206_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_b_2207_);
return v___x_2239_;
}
else
{
lean_object* v_resultDeps_2240_; uint8_t v___x_2241_; 
v_resultDeps_2240_ = lean_ctor_get(v_info_2202_, 1);
v___x_2241_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2240_, v_a_2206_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; uint8_t v_isProp_2243_; 
v___x_2242_ = lean_array_fget_borrowed(v___x_2204_, v_a_2206_);
v_isProp_2243_ = lean_ctor_get_uint8(v___x_2242_, sizeof(void*)*1 + 2);
if (v_isProp_2243_ == 0)
{
uint8_t v_isInstance_2244_; 
v_isInstance_2244_ = lean_ctor_get_uint8(v___x_2242_, sizeof(void*)*1 + 4);
if (v_isInstance_2244_ == 0)
{
uint8_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = 2;
v___x_2246_ = lean_box(v___x_2245_);
v___x_2247_ = lean_array_push(v_b_2207_, v___x_2246_);
v_a_2214_ = v___x_2247_;
goto v___jp_2213_;
}
else
{
if (lean_obj_tag(v_a_2205_) == 1)
{
lean_object* v_val_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v_val_2248_ = lean_ctor_get(v_a_2205_, 0);
v___x_2249_ = lean_array_get_size(v_val_2248_);
v___x_2250_ = lean_nat_dec_lt(v_a_2206_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_box(0);
v___x_2252_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2202_, v_a_2206_, v___x_2251_, v_b_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
v___y_2219_ = v___x_2252_;
goto v___jp_2218_;
}
else
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_array_fget_borrowed(v_val_2248_, v_a_2206_);
v___x_2254_ = lean_unbox(v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2202_, v_a_2206_, v___x_2255_, v_b_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
v___y_2219_ = v___x_2256_;
goto v___jp_2218_;
}
else
{
uint8_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = 2;
v___x_2258_ = lean_box(v___x_2257_);
v___x_2259_ = lean_array_push(v_b_2207_, v___x_2258_);
v_a_2214_ = v___x_2259_;
goto v___jp_2213_;
}
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_box(0);
v___x_2261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2202_, v_a_2206_, v___x_2260_, v_b_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
v___y_2219_ = v___x_2261_;
goto v___jp_2218_;
}
}
}
else
{
uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = 3;
v___x_2263_ = lean_box(v___x_2262_);
v___x_2264_ = lean_array_push(v_b_2207_, v___x_2263_);
v_a_2214_ = v___x_2264_;
goto v___jp_2213_;
}
}
else
{
uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = 0;
v___x_2266_ = lean_box(v___x_2265_);
v___x_2267_ = lean_array_push(v_b_2207_, v___x_2266_);
v_a_2214_ = v___x_2267_;
goto v___jp_2213_;
}
}
v___jp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_unsigned_to_nat(1u);
v___x_2216_ = lean_nat_add(v_a_2206_, v___x_2215_);
lean_dec(v_a_2206_);
v_a_2206_ = v___x_2216_;
v_b_2207_ = v_a_2214_;
goto _start;
}
v___jp_2218_:
{
if (lean_obj_tag(v___y_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2229_; 
v_a_2220_ = lean_ctor_get(v___y_2219_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___y_2219_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2222_ = v___y_2219_;
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___y_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
if (lean_obj_tag(v_a_2220_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2226_; 
lean_dec(v_a_2206_);
v_a_2224_ = lean_ctor_get(v_a_2220_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v_a_2220_, 1);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v_a_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
else
{
lean_object* v_a_2228_; 
lean_del_object(v___x_2222_);
v_a_2228_ = lean_ctor_get(v_a_2220_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v_a_2220_, 1);
v_a_2214_ = v_a_2228_;
goto v___jp_2213_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_a_2206_);
v_a_2230_ = lean_ctor_get(v___y_2219_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___y_2219_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___y_2219_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___y_2219_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2268_, lean_object* v_upperBound_2269_, lean_object* v___x_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2268_, v_upperBound_2269_, v___x_2270_, v_a_2271_, v_a_2272_, v_b_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v_a_2271_);
lean_dec_ref(v___x_2270_);
lean_dec(v_upperBound_2269_);
lean_dec_ref(v_info_2268_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2282_, lean_object* v_info_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2282_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v_paramInfo_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v_result_2294_; lean_object* v___x_2295_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v_paramInfo_2291_ = lean_ctor_get(v_info_2283_, 0);
v___x_2292_ = lean_array_get_size(v_paramInfo_2291_);
v___x_2293_ = lean_unsigned_to_nat(0u);
v_result_2294_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2295_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2283_, v___x_2292_, v_paramInfo_2291_, v_a_2290_, v___x_2293_, v_result_2294_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v_a_2290_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2304_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2283_, v_a_2296_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
return v___x_2295_;
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
v_a_2305_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2289_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2289_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2313_, lean_object* v_info_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Meta_getCongrSimpKinds(v_f_2313_, v_info_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec_ref(v_info_2314_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2321_, lean_object* v_upperBound_2322_, lean_object* v___x_2323_, lean_object* v_a_2324_, lean_object* v_inst_2325_, lean_object* v_R_2326_, lean_object* v_a_2327_, lean_object* v_b_2328_, lean_object* v_c_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2321_, v_upperBound_2322_, v___x_2323_, v_a_2324_, v_a_2327_, v_b_2328_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2336_, lean_object* v_upperBound_2337_, lean_object* v___x_2338_, lean_object* v_a_2339_, lean_object* v_inst_2340_, lean_object* v_R_2341_, lean_object* v_a_2342_, lean_object* v_b_2343_, lean_object* v_c_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2336_, v_upperBound_2337_, v___x_2338_, v_a_2339_, v_inst_2340_, v_R_2341_, v_a_2342_, v_b_2343_, v_c_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v_a_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_upperBound_2337_);
lean_dec_ref(v_info_2336_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2351_, lean_object* v_info_2352_, lean_object* v___x_2353_, lean_object* v_a_2354_, lean_object* v_b_2355_){
_start:
{
lean_object* v_a_2358_; uint8_t v___x_2362_; 
v___x_2362_ = lean_nat_dec_lt(v_a_2354_, v_upperBound_2351_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; 
lean_dec(v_a_2354_);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_b_2355_);
return v___x_2363_;
}
else
{
lean_object* v_resultDeps_2364_; uint8_t v___x_2365_; 
v_resultDeps_2364_ = lean_ctor_get(v_info_2352_, 1);
v___x_2365_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2364_, v_a_2354_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_nat_dec_eq(v_a_2354_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; uint8_t v_isProp_2369_; 
v___x_2368_ = lean_array_fget_borrowed(v___x_2353_, v_a_2354_);
v_isProp_2369_ = lean_ctor_get_uint8(v___x_2368_, sizeof(void*)*1 + 2);
if (v_isProp_2369_ == 0)
{
uint8_t v_isInstance_2370_; 
v_isInstance_2370_ = lean_ctor_get_uint8(v___x_2368_, sizeof(void*)*1 + 4);
if (v_isInstance_2370_ == 0)
{
uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = 0;
v___x_2372_ = lean_box(v___x_2371_);
v___x_2373_ = lean_array_push(v_b_2355_, v___x_2372_);
v_a_2358_ = v___x_2373_;
goto v___jp_2357_;
}
else
{
uint8_t v___x_2374_; 
v___x_2374_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2352_, v_b_2355_, v_a_2354_);
if (v___x_2374_ == 0)
{
uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = 0;
v___x_2376_ = lean_box(v___x_2375_);
v___x_2377_ = lean_array_push(v_b_2355_, v___x_2376_);
v_a_2358_ = v___x_2377_;
goto v___jp_2357_;
}
else
{
uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = 5;
v___x_2379_ = lean_box(v___x_2378_);
v___x_2380_ = lean_array_push(v_b_2355_, v___x_2379_);
v_a_2358_ = v___x_2380_;
goto v___jp_2357_;
}
}
}
else
{
uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = 3;
v___x_2382_ = lean_box(v___x_2381_);
v___x_2383_ = lean_array_push(v_b_2355_, v___x_2382_);
v_a_2358_ = v___x_2383_;
goto v___jp_2357_;
}
}
else
{
uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = 2;
v___x_2385_ = lean_box(v___x_2384_);
v___x_2386_ = lean_array_push(v_b_2355_, v___x_2385_);
v_a_2358_ = v___x_2386_;
goto v___jp_2357_;
}
}
else
{
uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = 0;
v___x_2388_ = lean_box(v___x_2387_);
v___x_2389_ = lean_array_push(v_b_2355_, v___x_2388_);
v_a_2358_ = v___x_2389_;
goto v___jp_2357_;
}
}
v___jp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_nat_add(v_a_2354_, v___x_2359_);
lean_dec(v_a_2354_);
v_a_2354_ = v___x_2360_;
v_b_2355_ = v_a_2358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2390_, lean_object* v_info_2391_, lean_object* v___x_2392_, lean_object* v_a_2393_, lean_object* v_b_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2390_, v_info_2391_, v___x_2392_, v_a_2393_, v_b_2394_);
lean_dec_ref(v___x_2392_);
lean_dec_ref(v_info_2391_);
lean_dec(v_upperBound_2390_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_paramInfo_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v_result_2406_; lean_object* v___x_2407_; 
v_paramInfo_2403_ = lean_ctor_get(v_info_2397_, 0);
v___x_2404_ = lean_array_get_size(v_paramInfo_2403_);
v___x_2405_ = lean_unsigned_to_nat(0u);
v_result_2406_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2407_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2404_, v_info_2397_, v_paramInfo_2403_, v___x_2405_, v_result_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2416_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2416_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2416_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2397_, v_a_2408_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
else
{
return v___x_2407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_info_2417_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2424_, lean_object* v_info_2425_, lean_object* v___x_2426_, lean_object* v_inst_2427_, lean_object* v_R_2428_, lean_object* v_a_2429_, lean_object* v_b_2430_, lean_object* v_c_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2424_, v_info_2425_, v___x_2426_, v_a_2429_, v_b_2430_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2438_, lean_object* v_info_2439_, lean_object* v___x_2440_, lean_object* v_inst_2441_, lean_object* v_R_2442_, lean_object* v_a_2443_, lean_object* v_b_2444_, lean_object* v_c_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2438_, v_info_2439_, v___x_2440_, v_inst_2441_, v_R_2442_, v_a_2443_, v_b_2444_, v_c_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec_ref(v___x_2440_);
lean_dec_ref(v_info_2439_);
lean_dec(v_upperBound_2438_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 0)
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_unsigned_to_nat(0u);
return v___x_2453_;
}
else
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_unsigned_to_nat(1u);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___boxed(lean_object* v_x_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(v_x_2455_);
lean_dec_ref(v_x_2455_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2457_, lean_object* v_k_2458_){
_start:
{
if (lean_obj_tag(v_t_2457_) == 0)
{
lean_object* v_fvarId_2459_; lean_object* v___x_2460_; 
v_fvarId_2459_ = lean_ctor_get(v_t_2457_, 0);
lean_inc(v_fvarId_2459_);
lean_dec_ref_known(v_t_2457_, 1);
v___x_2460_ = lean_apply_1(v_k_2458_, v_fvarId_2459_);
return v___x_2460_;
}
else
{
lean_object* v_lhs_2461_; lean_object* v_rhs_2462_; lean_object* v___x_2463_; 
v_lhs_2461_ = lean_ctor_get(v_t_2457_, 0);
lean_inc(v_lhs_2461_);
v_rhs_2462_ = lean_ctor_get(v_t_2457_, 1);
lean_inc(v_rhs_2462_);
lean_dec_ref_known(v_t_2457_, 2);
v___x_2463_ = lean_apply_2(v_k_2458_, v_lhs_2461_, v_rhs_2462_);
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2464_, lean_object* v_ctorIdx_2465_, lean_object* v_t_2466_, lean_object* v_h_2467_, lean_object* v_k_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2466_, v_k_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2470_, lean_object* v_ctorIdx_2471_, lean_object* v_t_2472_, lean_object* v_h_2473_, lean_object* v_k_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2470_, v_ctorIdx_2471_, v_t_2472_, v_h_2473_, v_k_2474_);
lean_dec(v_ctorIdx_2471_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2476_, lean_object* v_hyp_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2476_, v_hyp_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2479_, lean_object* v_t_2480_, lean_object* v_h_2481_, lean_object* v_hyp_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2480_, v_hyp_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2484_, lean_object* v_decSubsingleton_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2484_, v_decSubsingleton_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2487_, lean_object* v_t_2488_, lean_object* v_h_2489_, lean_object* v_decSubsingleton_2490_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2488_, v_decSubsingleton_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2492_, lean_object* v_fvarId_2493_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2492_, v_fvarId_2493_);
if (lean_obj_tag(v___x_2494_) == 1)
{
lean_object* v_val_2495_; lean_object* v___x_2496_; 
v_val_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = l_Lean_Expr_fvarId_x21(v_val_2495_);
lean_dec(v_val_2495_);
return v___x_2496_;
}
else
{
lean_dec(v___x_2494_);
lean_inc(v_fvarId_2493_);
return v_fvarId_2493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2497_, lean_object* v_fvarId_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2497_, v_fvarId_2498_);
lean_dec(v_fvarId_2498_);
lean_dec(v_s_2497_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2500_, lean_object* v_x_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2500_, v_x_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_a_2516_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2507_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2507_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2524_, lean_object* v_x_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2524_, v_x_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2532_, lean_object* v_mvarId_2533_, lean_object* v_x_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2533_, v_x_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2541_, lean_object* v_mvarId_2542_, lean_object* v_x_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2541_, v_mvarId_2542_, v_x_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2550_, lean_object* v___y_2551_){
_start:
{
uint8_t v___x_2553_; 
v___x_2553_ = l_Lean_Expr_hasMVar(v_e_2550_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_e_2550_);
return v___x_2554_;
}
else
{
lean_object* v___x_2555_; lean_object* v_mctx_2556_; lean_object* v___x_2557_; lean_object* v_fst_2558_; lean_object* v_snd_2559_; lean_object* v___x_2560_; lean_object* v_cache_2561_; lean_object* v_zetaDeltaFVarIds_2562_; lean_object* v_postponed_2563_; lean_object* v_diag_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2573_; 
v___x_2555_ = lean_st_ref_get(v___y_2551_);
v_mctx_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_mctx_2556_);
lean_dec(v___x_2555_);
v___x_2557_ = l_Lean_instantiateMVarsCore(v_mctx_2556_, v_e_2550_);
v_fst_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_fst_2558_);
v_snd_2559_ = lean_ctor_get(v___x_2557_, 1);
lean_inc(v_snd_2559_);
lean_dec_ref(v___x_2557_);
v___x_2560_ = lean_st_ref_take(v___y_2551_);
v_cache_2561_ = lean_ctor_get(v___x_2560_, 1);
v_zetaDeltaFVarIds_2562_ = lean_ctor_get(v___x_2560_, 2);
v_postponed_2563_ = lean_ctor_get(v___x_2560_, 3);
v_diag_2564_ = lean_ctor_get(v___x_2560_, 4);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v___x_2560_, 0);
lean_dec(v_unused_2574_);
v___x_2566_ = v___x_2560_;
v_isShared_2567_ = v_isSharedCheck_2573_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_diag_2564_);
lean_inc(v_postponed_2563_);
lean_inc(v_zetaDeltaFVarIds_2562_);
lean_inc(v_cache_2561_);
lean_dec(v___x_2560_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2573_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v_snd_2559_);
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_snd_2559_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_cache_2561_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_zetaDeltaFVarIds_2562_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_postponed_2563_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_diag_2564_);
v___x_2569_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_st_ref_put(v___y_2551_, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_fst_2558_);
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2575_, v___y_2576_);
lean_dec(v___y_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2579_, v___y_2581_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_){
_start:
{
lean_object* v_ks_2597_; lean_object* v_vs_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2622_; 
v_ks_2597_ = lean_ctor_get(v_x_2593_, 0);
v_vs_2598_ = lean_ctor_get(v_x_2593_, 1);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_x_2593_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2600_ = v_x_2593_;
v_isShared_2601_ = v_isSharedCheck_2622_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_vs_2598_);
lean_inc(v_ks_2597_);
lean_dec(v_x_2593_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2622_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = lean_array_get_size(v_ks_2597_);
v___x_2603_ = lean_nat_dec_lt(v_x_2594_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
lean_dec(v_x_2594_);
v___x_2604_ = lean_array_push(v_ks_2597_, v_x_2595_);
v___x_2605_ = lean_array_push(v_vs_2598_, v_x_2596_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 1, v___x_2605_);
lean_ctor_set(v___x_2600_, 0, v___x_2604_);
v___x_2607_ = v___x_2600_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
else
{
lean_object* v_k_x27_2609_; uint8_t v___x_2610_; 
v_k_x27_2609_ = lean_array_fget_borrowed(v_ks_2597_, v_x_2594_);
v___x_2610_ = l_Lean_instBEqMVarId_beq(v_x_2595_, v_k_x27_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2612_; 
if (v_isShared_2601_ == 0)
{
v___x_2612_ = v___x_2600_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_ks_2597_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_vs_2598_);
v___x_2612_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_unsigned_to_nat(1u);
v___x_2614_ = lean_nat_add(v_x_2594_, v___x_2613_);
lean_dec(v_x_2594_);
v_x_2593_ = v___x_2612_;
v_x_2594_ = v___x_2614_;
goto _start;
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2617_ = lean_array_fset(v_ks_2597_, v_x_2594_, v_x_2595_);
v___x_2618_ = lean_array_fset(v_vs_2598_, v_x_2594_, v_x_2596_);
lean_dec(v_x_2594_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 1, v___x_2618_);
lean_ctor_set(v___x_2600_, 0, v___x_2617_);
v___x_2620_ = v___x_2600_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2623_, lean_object* v_k_2624_, lean_object* v_v_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2623_, v___x_2626_, v_k_2624_, v_v_2625_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2629_, size_t v_x_2630_, size_t v_x_2631_, lean_object* v_x_2632_, lean_object* v_x_2633_){
_start:
{
if (lean_obj_tag(v_x_2629_) == 0)
{
lean_object* v_es_2634_; size_t v___x_2635_; size_t v___x_2636_; lean_object* v_j_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v_es_2634_ = lean_ctor_get(v_x_2629_, 0);
v___x_2635_ = ((size_t)31ULL);
v___x_2636_ = lean_usize_land(v_x_2630_, v___x_2635_);
v_j_2637_ = lean_usize_to_nat(v___x_2636_);
v___x_2638_ = lean_array_get_size(v_es_2634_);
v___x_2639_ = lean_nat_dec_lt(v_j_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_dec(v_j_2637_);
lean_dec(v_x_2633_);
lean_dec(v_x_2632_);
return v_x_2629_;
}
else
{
lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2678_; 
lean_inc_ref(v_es_2634_);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_x_2629_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v_x_2629_, 0);
lean_dec(v_unused_2679_);
v___x_2641_ = v_x_2629_;
v_isShared_2642_ = v_isSharedCheck_2678_;
goto v_resetjp_2640_;
}
else
{
lean_dec(v_x_2629_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2678_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_v_2643_; lean_object* v___x_2644_; lean_object* v_xs_x27_2645_; lean_object* v___y_2647_; 
v_v_2643_ = lean_array_fget(v_es_2634_, v_j_2637_);
v___x_2644_ = lean_box(0);
v_xs_x27_2645_ = lean_array_fset(v_es_2634_, v_j_2637_, v___x_2644_);
switch(lean_obj_tag(v_v_2643_))
{
case 0:
{
lean_object* v_key_2652_; lean_object* v_val_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2663_; 
v_key_2652_ = lean_ctor_get(v_v_2643_, 0);
v_val_2653_ = lean_ctor_get(v_v_2643_, 1);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_v_2643_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2655_ = v_v_2643_;
v_isShared_2656_ = v_isSharedCheck_2663_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_val_2653_);
lean_inc(v_key_2652_);
lean_dec(v_v_2643_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2663_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
uint8_t v___x_2657_; 
v___x_2657_ = l_Lean_instBEqMVarId_beq(v_x_2632_, v_key_2652_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_del_object(v___x_2655_);
v___x_2658_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2652_, v_val_2653_, v_x_2632_, v_x_2633_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
v___y_2647_ = v___x_2659_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2661_; 
lean_dec(v_val_2653_);
lean_dec(v_key_2652_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v_x_2633_);
lean_ctor_set(v___x_2655_, 0, v_x_2632_);
v___x_2661_ = v___x_2655_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_x_2632_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_x_2633_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
v___y_2647_ = v___x_2661_;
goto v___jp_2646_;
}
}
}
}
case 1:
{
lean_object* v_node_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2676_; 
v_node_2664_ = lean_ctor_get(v_v_2643_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_v_2643_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2666_ = v_v_2643_;
v_isShared_2667_ = v_isSharedCheck_2676_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_node_2664_);
lean_dec(v_v_2643_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2676_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
size_t v___x_2668_; size_t v___x_2669_; size_t v___x_2670_; size_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2668_ = ((size_t)5ULL);
v___x_2669_ = lean_usize_shift_right(v_x_2630_, v___x_2668_);
v___x_2670_ = ((size_t)1ULL);
v___x_2671_ = lean_usize_add(v_x_2631_, v___x_2670_);
v___x_2672_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2664_, v___x_2669_, v___x_2671_, v_x_2632_, v_x_2633_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2672_);
v___x_2674_ = v___x_2666_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
v___y_2647_ = v___x_2674_;
goto v___jp_2646_;
}
}
}
default: 
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v_x_2632_);
lean_ctor_set(v___x_2677_, 1, v_x_2633_);
v___y_2647_ = v___x_2677_;
goto v___jp_2646_;
}
}
v___jp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2648_ = lean_array_fset(v_xs_x27_2645_, v_j_2637_, v___y_2647_);
lean_dec(v_j_2637_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2648_);
v___x_2650_ = v___x_2641_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
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
else
{
lean_object* v_ks_2680_; lean_object* v_vs_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2699_; 
v_ks_2680_ = lean_ctor_get(v_x_2629_, 0);
v_vs_2681_ = lean_ctor_get(v_x_2629_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_x_2629_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2683_ = v_x_2629_;
v_isShared_2684_ = v_isSharedCheck_2699_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_vs_2681_);
lean_inc(v_ks_2680_);
lean_dec(v_x_2629_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2699_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_ks_2680_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_vs_2681_);
v___x_2686_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v_newNode_2687_; size_t v___x_2688_; uint8_t v___x_2689_; 
v_newNode_2687_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2686_, v_x_2632_, v_x_2633_);
v___x_2688_ = ((size_t)7ULL);
v___x_2689_ = lean_usize_dec_le(v___x_2688_, v_x_2631_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2690_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2687_);
v___x_2691_ = lean_unsigned_to_nat(4u);
v___x_2692_ = lean_nat_dec_lt(v___x_2690_, v___x_2691_);
lean_dec(v___x_2690_);
if (v___x_2692_ == 0)
{
lean_object* v_ks_2693_; lean_object* v_vs_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v_ks_2693_ = lean_ctor_get(v_newNode_2687_, 0);
lean_inc_ref(v_ks_2693_);
v_vs_2694_ = lean_ctor_get(v_newNode_2687_, 1);
lean_inc_ref(v_vs_2694_);
lean_dec_ref(v_newNode_2687_);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2697_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2631_, v_ks_2693_, v_vs_2694_, v___x_2695_, v___x_2696_);
lean_dec_ref(v_vs_2694_);
lean_dec_ref(v_ks_2693_);
return v___x_2697_;
}
else
{
return v_newNode_2687_;
}
}
else
{
return v_newNode_2687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_2700_, lean_object* v_keys_2701_, lean_object* v_vals_2702_, lean_object* v_i_2703_, lean_object* v_entries_2704_){
_start:
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = lean_array_get_size(v_keys_2701_);
v___x_2706_ = lean_nat_dec_lt(v_i_2703_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_dec(v_i_2703_);
return v_entries_2704_;
}
else
{
lean_object* v_k_2707_; lean_object* v_v_2708_; uint64_t v___x_2709_; size_t v_h_2710_; size_t v___x_2711_; lean_object* v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v_h_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_k_2707_ = lean_array_fget_borrowed(v_keys_2701_, v_i_2703_);
v_v_2708_ = lean_array_fget_borrowed(v_vals_2702_, v_i_2703_);
v___x_2709_ = l_Lean_instHashableMVarId_hash(v_k_2707_);
v_h_2710_ = lean_uint64_to_usize(v___x_2709_);
v___x_2711_ = ((size_t)5ULL);
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = ((size_t)1ULL);
v___x_2714_ = lean_usize_sub(v_depth_2700_, v___x_2713_);
v___x_2715_ = lean_usize_mul(v___x_2711_, v___x_2714_);
v_h_2716_ = lean_usize_shift_right(v_h_2710_, v___x_2715_);
v___x_2717_ = lean_nat_add(v_i_2703_, v___x_2712_);
lean_dec(v_i_2703_);
lean_inc(v_v_2708_);
lean_inc(v_k_2707_);
v___x_2718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_2704_, v_h_2716_, v_depth_2700_, v_k_2707_, v_v_2708_);
v_i_2703_ = v___x_2717_;
v_entries_2704_ = v___x_2718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2720_, lean_object* v_keys_2721_, lean_object* v_vals_2722_, lean_object* v_i_2723_, lean_object* v_entries_2724_){
_start:
{
size_t v_depth_boxed_2725_; lean_object* v_res_2726_; 
v_depth_boxed_2725_ = lean_unbox_usize(v_depth_2720_);
lean_dec(v_depth_2720_);
v_res_2726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_2725_, v_keys_2721_, v_vals_2722_, v_i_2723_, v_entries_2724_);
lean_dec_ref(v_vals_2722_);
lean_dec_ref(v_keys_2721_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_){
_start:
{
size_t v_x_3878__boxed_2732_; size_t v_x_3879__boxed_2733_; lean_object* v_res_2734_; 
v_x_3878__boxed_2732_ = lean_unbox_usize(v_x_2728_);
lean_dec(v_x_2728_);
v_x_3879__boxed_2733_ = lean_unbox_usize(v_x_2729_);
lean_dec(v_x_2729_);
v_res_2734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2727_, v_x_3878__boxed_2732_, v_x_3879__boxed_2733_, v_x_2730_, v_x_2731_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object* v_x_2735_, lean_object* v_x_2736_, lean_object* v_x_2737_){
_start:
{
uint64_t v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v___x_2738_ = l_Lean_instHashableMVarId_hash(v_x_2736_);
v___x_2739_ = lean_uint64_to_usize(v___x_2738_);
v___x_2740_ = ((size_t)1ULL);
v___x_2741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2735_, v___x_2739_, v___x_2740_, v_x_2736_, v_x_2737_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object* v_mvarId_2742_, lean_object* v_val_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; lean_object* v_mctx_2747_; lean_object* v_cache_2748_; lean_object* v_zetaDeltaFVarIds_2749_; lean_object* v_postponed_2750_; lean_object* v_diag_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2780_; 
v___x_2746_ = lean_st_ref_take(v___y_2744_);
v_mctx_2747_ = lean_ctor_get(v___x_2746_, 0);
v_cache_2748_ = lean_ctor_get(v___x_2746_, 1);
v_zetaDeltaFVarIds_2749_ = lean_ctor_get(v___x_2746_, 2);
v_postponed_2750_ = lean_ctor_get(v___x_2746_, 3);
v_diag_2751_ = lean_ctor_get(v___x_2746_, 4);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2753_ = v___x_2746_;
v_isShared_2754_ = v_isSharedCheck_2780_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_diag_2751_);
lean_inc(v_postponed_2750_);
lean_inc(v_zetaDeltaFVarIds_2749_);
lean_inc(v_cache_2748_);
lean_inc(v_mctx_2747_);
lean_dec(v___x_2746_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2780_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v_depth_2755_; lean_object* v_levelAssignDepth_2756_; lean_object* v_lmvarCounter_2757_; lean_object* v_mvarCounter_2758_; lean_object* v_lDecls_2759_; lean_object* v_decls_2760_; lean_object* v_userNames_2761_; lean_object* v_lAssignment_2762_; lean_object* v_eAssignment_2763_; lean_object* v_dAssignment_2764_; lean_object* v_instanceTypedMVars_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2779_; 
v_depth_2755_ = lean_ctor_get(v_mctx_2747_, 0);
v_levelAssignDepth_2756_ = lean_ctor_get(v_mctx_2747_, 1);
v_lmvarCounter_2757_ = lean_ctor_get(v_mctx_2747_, 2);
v_mvarCounter_2758_ = lean_ctor_get(v_mctx_2747_, 3);
v_lDecls_2759_ = lean_ctor_get(v_mctx_2747_, 4);
v_decls_2760_ = lean_ctor_get(v_mctx_2747_, 5);
v_userNames_2761_ = lean_ctor_get(v_mctx_2747_, 6);
v_lAssignment_2762_ = lean_ctor_get(v_mctx_2747_, 7);
v_eAssignment_2763_ = lean_ctor_get(v_mctx_2747_, 8);
v_dAssignment_2764_ = lean_ctor_get(v_mctx_2747_, 9);
v_instanceTypedMVars_2765_ = lean_ctor_get(v_mctx_2747_, 10);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_mctx_2747_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2767_ = v_mctx_2747_;
v_isShared_2768_ = v_isSharedCheck_2779_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_instanceTypedMVars_2765_);
lean_inc(v_dAssignment_2764_);
lean_inc(v_eAssignment_2763_);
lean_inc(v_lAssignment_2762_);
lean_inc(v_userNames_2761_);
lean_inc(v_decls_2760_);
lean_inc(v_lDecls_2759_);
lean_inc(v_mvarCounter_2758_);
lean_inc(v_lmvarCounter_2757_);
lean_inc(v_levelAssignDepth_2756_);
lean_inc(v_depth_2755_);
lean_dec(v_mctx_2747_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2779_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2769_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2763_, v_mvarId_2742_, v_val_2743_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 8, v___x_2769_);
v___x_2771_ = v___x_2767_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_depth_2755_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_levelAssignDepth_2756_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_lmvarCounter_2757_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_mvarCounter_2758_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v_lDecls_2759_);
lean_ctor_set(v_reuseFailAlloc_2778_, 5, v_decls_2760_);
lean_ctor_set(v_reuseFailAlloc_2778_, 6, v_userNames_2761_);
lean_ctor_set(v_reuseFailAlloc_2778_, 7, v_lAssignment_2762_);
lean_ctor_set(v_reuseFailAlloc_2778_, 8, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2778_, 9, v_dAssignment_2764_);
lean_ctor_set(v_reuseFailAlloc_2778_, 10, v_instanceTypedMVars_2765_);
v___x_2771_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2773_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2771_);
v___x_2773_ = v___x_2753_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_cache_2748_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v_zetaDeltaFVarIds_2749_);
lean_ctor_set(v_reuseFailAlloc_2777_, 3, v_postponed_2750_);
lean_ctor_set(v_reuseFailAlloc_2777_, 4, v_diag_2751_);
v___x_2773_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = lean_st_ref_put(v___y_2744_, v___x_2773_);
v___x_2775_ = lean_box(0);
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
return v___x_2776_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2781_, lean_object* v_val_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2781_, v_val_2782_, v___y_2783_);
lean_dec(v___y_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2794_, lean_object* v_as_2795_, size_t v_sz_2796_, size_t v_i_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_a_2805_; uint8_t v___x_2809_; 
v___x_2809_ = lean_usize_dec_lt(v_i_2797_, v_sz_2796_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_b_2798_);
return v___x_2810_;
}
else
{
lean_object* v_fst_2811_; lean_object* v_snd_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; lean_object* v_a_2815_; 
v_fst_2811_ = lean_ctor_get(v_b_2798_, 0);
lean_inc(v_fst_2811_);
v_snd_2812_ = lean_ctor_get(v_b_2798_, 1);
lean_inc(v_snd_2812_);
lean_dec_ref(v_b_2798_);
v___x_2813_ = lean_unsigned_to_nat(0u);
v___x_2814_ = lean_nat_dec_eq(v___x_2794_, v___x_2813_);
v_a_2815_ = lean_array_uget_borrowed(v_as_2795_, v_i_2797_);
if (lean_obj_tag(v_a_2815_) == 0)
{
lean_object* v_fvarId_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_fvarId_2816_ = lean_ctor_get(v_a_2815_, 0);
v___x_2817_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2812_, v_fvarId_2816_);
v___x_2818_ = l_Lean_Meta_substCore(v_fst_2811_, v___x_2817_, v___x_2809_, v_snd_2812_, v___x_2809_, v___x_2814_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v_fst_2820_; lean_object* v_snd_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v_fst_2820_ = lean_ctor_get(v_a_2819_, 0);
v_snd_2821_ = lean_ctor_get(v_a_2819_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v_a_2819_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snd_2821_);
lean_inc(v_fst_2820_);
lean_dec(v_a_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_fst_2820_);
lean_ctor_set(v___x_2823_, 0, v_snd_2821_);
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_snd_2821_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_fst_2820_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
v_a_2805_ = v___x_2826_;
goto v___jp_2804_;
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
v_a_2829_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2818_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2818_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_lhs_2837_; lean_object* v_rhs_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v_lhs_2837_ = lean_ctor_get(v_a_2815_, 0);
v_rhs_2838_ = lean_ctor_get(v_a_2815_, 1);
v___x_2839_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2812_, v_lhs_2837_);
v___x_2840_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2812_, v_rhs_2838_);
v___x_2841_ = l_Lean_mkFVar(v___x_2839_);
v___x_2842_ = l_Lean_mkFVar(v___x_2840_);
lean_inc_ref(v___x_2842_);
lean_inc_ref(v___x_2841_);
v___x_2843_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2843_, 0, v___x_2841_);
lean_closure_set(v___x_2843_, 1, v___x_2842_);
lean_inc(v_fst_2811_);
v___x_2844_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2811_, v___x_2843_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2847_ = lean_unsigned_to_nat(2u);
v___x_2848_ = lean_mk_empty_array_with_capacity(v___x_2847_);
v___x_2849_ = lean_array_push(v___x_2848_, v___x_2841_);
v___x_2850_ = lean_array_push(v___x_2849_, v___x_2842_);
v___x_2851_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2851_, 0, v___x_2846_);
lean_closure_set(v___x_2851_, 1, v___x_2850_);
lean_inc(v_fst_2811_);
v___x_2852_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2811_, v___x_2851_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
v___x_2855_ = l_Lean_MVarId_assert(v_fst_2811_, v___x_2854_, v_a_2845_, v_a_2853_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = l_Lean_Meta_intro1Core(v_a_2856_, v___x_2814_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v_fst_2859_; lean_object* v_snd_2860_; lean_object* v___x_2861_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v_fst_2859_ = lean_ctor_get(v_a_2858_, 0);
lean_inc(v_fst_2859_);
v_snd_2860_ = lean_ctor_get(v_a_2858_, 1);
lean_inc(v_snd_2860_);
lean_dec(v_a_2858_);
v___x_2861_ = l_Lean_Meta_substCore(v_snd_2860_, v_fst_2859_, v___x_2809_, v_snd_2812_, v___x_2809_, v___x_2814_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v_fst_2863_; lean_object* v_snd_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v_fst_2863_ = lean_ctor_get(v_a_2862_, 0);
v_snd_2864_ = lean_ctor_get(v_a_2862_, 1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v_a_2862_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_snd_2864_);
lean_inc(v_fst_2863_);
lean_dec(v_a_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 1, v_fst_2863_);
lean_ctor_set(v___x_2866_, 0, v_snd_2864_);
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_snd_2864_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_fst_2863_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
v_a_2805_ = v___x_2869_;
goto v___jp_2804_;
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v_a_2872_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2861_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2861_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_snd_2812_);
v_a_2880_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2857_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2857_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_snd_2812_);
v_a_2888_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2855_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2855_);
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
lean_dec(v_a_2845_);
lean_dec(v_snd_2812_);
lean_dec(v_fst_2811_);
v_a_2896_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2852_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2852_);
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
lean_dec_ref(v___x_2842_);
lean_dec_ref(v___x_2841_);
lean_dec(v_snd_2812_);
lean_dec(v_fst_2811_);
v_a_2904_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2844_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2844_);
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
}
v___jp_2804_:
{
size_t v___x_2806_; size_t v___x_2807_; 
v___x_2806_ = ((size_t)1ULL);
v___x_2807_ = lean_usize_add(v_i_2797_, v___x_2806_);
v_i_2797_ = v___x_2807_;
v_b_2798_ = v_a_2805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_2912_, lean_object* v_as_2913_, lean_object* v_sz_2914_, lean_object* v_i_2915_, lean_object* v_b_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
size_t v_sz_boxed_2922_; size_t v_i_boxed_2923_; lean_object* v_res_2924_; 
v_sz_boxed_2922_ = lean_unbox_usize(v_sz_2914_);
lean_dec(v_sz_2914_);
v_i_boxed_2923_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2912_, v_as_2913_, v_sz_boxed_2922_, v_i_boxed_2923_, v_b_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v_as_2913_);
lean_dec(v___x_2912_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_2925_, lean_object* v_as_2926_, size_t v_i_2927_, size_t v_stop_2928_, lean_object* v_b_2929_){
_start:
{
lean_object* v___y_2931_; uint8_t v___x_2935_; 
v___x_2935_ = lean_usize_dec_eq(v_i_2927_, v_stop_2928_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_box(0);
v___x_2937_ = lean_array_uget_borrowed(v_as_2926_, v_i_2927_);
v___x_2938_ = lean_array_get_borrowed(v___x_2936_, v_eqs_2925_, v___x_2937_);
if (lean_obj_tag(v___x_2938_) == 0)
{
v___y_2931_ = v_b_2929_;
goto v___jp_2930_;
}
else
{
lean_object* v_val_2939_; lean_object* v___x_2940_; 
v_val_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_val_2939_);
v___x_2940_ = lean_array_push(v_b_2929_, v_val_2939_);
v___y_2931_ = v___x_2940_;
goto v___jp_2930_;
}
}
else
{
return v_b_2929_;
}
v___jp_2930_:
{
size_t v___x_2932_; size_t v___x_2933_; 
v___x_2932_ = ((size_t)1ULL);
v___x_2933_ = lean_usize_add(v_i_2927_, v___x_2932_);
v_i_2927_ = v___x_2933_;
v_b_2929_ = v___y_2931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_2941_, lean_object* v_as_2942_, lean_object* v_i_2943_, lean_object* v_stop_2944_, lean_object* v_b_2945_){
_start:
{
size_t v_i_boxed_2946_; size_t v_stop_boxed_2947_; lean_object* v_res_2948_; 
v_i_boxed_2946_ = lean_unbox_usize(v_i_2943_);
lean_dec(v_i_2943_);
v_stop_boxed_2947_ = lean_unbox_usize(v_stop_2944_);
lean_dec(v_stop_2944_);
v_res_2948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2941_, v_as_2942_, v_i_boxed_2946_, v_stop_boxed_2947_, v_b_2945_);
lean_dec_ref(v_as_2942_);
lean_dec_ref(v_eqs_2941_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_2951_, lean_object* v_as_2952_, lean_object* v_start_2953_, lean_object* v_stop_2954_){
_start:
{
lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_2956_ = lean_nat_dec_lt(v_start_2953_, v_stop_2954_);
if (v___x_2956_ == 0)
{
return v___x_2955_;
}
else
{
lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2957_ = lean_array_get_size(v_as_2952_);
v___x_2958_ = lean_nat_dec_le(v_stop_2954_, v___x_2957_);
if (v___x_2958_ == 0)
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_nat_dec_lt(v_start_2953_, v___x_2957_);
if (v___x_2959_ == 0)
{
return v___x_2955_;
}
else
{
size_t v___x_2960_; size_t v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_usize_of_nat(v_start_2953_);
v___x_2961_ = lean_usize_of_nat(v___x_2957_);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2951_, v_as_2952_, v___x_2960_, v___x_2961_, v___x_2955_);
return v___x_2962_;
}
}
else
{
size_t v___x_2963_; size_t v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_usize_of_nat(v_start_2953_);
v___x_2964_ = lean_usize_of_nat(v_stop_2954_);
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2951_, v_as_2952_, v___x_2963_, v___x_2964_, v___x_2955_);
return v___x_2965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_2966_, lean_object* v_as_2967_, lean_object* v_start_2968_, lean_object* v_stop_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2966_, v_as_2967_, v_start_2968_, v_stop_2969_);
lean_dec(v_stop_2969_);
lean_dec(v_start_2968_);
lean_dec_ref(v_as_2967_);
lean_dec_ref(v_eqs_2966_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_2971_, lean_object* v_type_2972_, lean_object* v_deps_2973_, lean_object* v_eqs_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_eqs_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2980_ = lean_unsigned_to_nat(0u);
v___x_2981_ = lean_array_get_size(v_deps_2973_);
v_eqs_2982_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2974_, v_deps_2973_, v___x_2980_, v___x_2981_);
v___x_2983_ = lean_array_get_size(v_eqs_2982_);
v___x_2984_ = lean_nat_dec_eq(v___x_2983_, v___x_2980_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_type_2972_);
v___x_2986_ = 0;
v___x_2987_ = lean_box(0);
v___x_2988_ = l_Lean_Meta_mkFreshExprMVar(v___x_2985_, v___x_2986_, v___x_2987_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; size_t v_sz_2993_; size_t v___x_2994_; lean_object* v___x_2995_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v___x_2990_ = l_Lean_Expr_mvarId_x21(v_a_2989_);
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v_sz_2993_ = lean_array_size(v_eqs_2982_);
v___x_2994_ = ((size_t)0ULL);
v___x_2995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2983_, v_eqs_2982_, v_sz_2993_, v___x_2994_, v___x_2992_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
lean_dec_ref(v_eqs_2982_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v_fst_2997_; lean_object* v_snd_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v_fst_2997_ = lean_ctor_get(v_a_2996_, 0);
lean_inc(v_fst_2997_);
v_snd_2998_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_snd_2998_);
lean_dec(v_a_2996_);
v___x_2999_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2998_, v_fvarId_2971_);
lean_dec(v_fvarId_2971_);
lean_dec(v_snd_2998_);
v___x_3000_ = l_Lean_mkFVar(v___x_2999_);
v___x_3001_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_2997_, v___x_3000_, v_a_2976_);
lean_dec_ref(v___x_3001_);
v___x_3002_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_2989_, v_a_2976_);
return v___x_3002_;
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2989_);
lean_dec(v_fvarId_2971_);
v_a_3003_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2995_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2995_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_dec_ref(v_eqs_2982_);
lean_dec(v_fvarId_2971_);
return v___x_2988_;
}
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v_eqs_2982_);
lean_dec_ref(v_type_2972_);
v___x_3011_ = l_Lean_mkFVar(v_fvarId_2971_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3013_, lean_object* v_type_3014_, lean_object* v_deps_3015_, lean_object* v_eqs_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3013_, v_type_3014_, v_deps_3015_, v_eqs_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec_ref(v_eqs_3016_);
lean_dec_ref(v_deps_3015_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3023_, lean_object* v_val_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3023_, v_val_3024_, v___y_3026_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3031_, lean_object* v_val_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3031_, v_val_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_, lean_object* v_x_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3040_, v_x_3041_, v_x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3044_, lean_object* v_x_3045_, size_t v_x_3046_, size_t v_x_3047_, lean_object* v_x_3048_, lean_object* v_x_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3045_, v_x_3046_, v_x_3047_, v_x_3048_, v_x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_, lean_object* v_x_3054_, lean_object* v_x_3055_, lean_object* v_x_3056_){
_start:
{
size_t v_x_4479__boxed_3057_; size_t v_x_4480__boxed_3058_; lean_object* v_res_3059_; 
v_x_4479__boxed_3057_ = lean_unbox_usize(v_x_3053_);
lean_dec(v_x_3053_);
v_x_4480__boxed_3058_ = lean_unbox_usize(v_x_3054_);
lean_dec(v_x_3054_);
v_res_3059_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3051_, v_x_3052_, v_x_4479__boxed_3057_, v_x_4480__boxed_3058_, v_x_3055_, v_x_3056_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3060_, lean_object* v_n_3061_, lean_object* v_k_3062_, lean_object* v_v_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3061_, v_k_3062_, v_v_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3065_, size_t v_depth_3066_, lean_object* v_keys_3067_, lean_object* v_vals_3068_, lean_object* v_heq_3069_, lean_object* v_i_3070_, lean_object* v_entries_3071_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3066_, v_keys_3067_, v_vals_3068_, v_i_3070_, v_entries_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3073_, lean_object* v_depth_3074_, lean_object* v_keys_3075_, lean_object* v_vals_3076_, lean_object* v_heq_3077_, lean_object* v_i_3078_, lean_object* v_entries_3079_){
_start:
{
size_t v_depth_boxed_3080_; lean_object* v_res_3081_; 
v_depth_boxed_3080_ = lean_unbox_usize(v_depth_3074_);
lean_dec(v_depth_3074_);
v_res_3081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3073_, v_depth_boxed_3080_, v_keys_3075_, v_vals_3076_, v_heq_3077_, v_i_3078_, v_entries_3079_);
lean_dec_ref(v_vals_3076_);
lean_dec_ref(v_keys_3075_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3082_, lean_object* v_x_3083_, lean_object* v_x_3084_, lean_object* v_x_3085_, lean_object* v_x_3086_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3083_, v_x_3084_, v_x_3085_, v_x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___f_3095_; lean_object* v___x_1366__overap_3096_; lean_object* v___x_3097_; 
v___f_3095_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1366__overap_3096_ = lean_panic_fn_borrowed(v___f_3095_, v_msg_3089_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
lean_inc(v___y_3091_);
lean_inc_ref(v___y_3090_);
v___x_3097_ = lean_apply_5(v___x_1366__overap_3096_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, lean_box(0));
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
return v_res_3104_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3108_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3109_ = lean_unsigned_to_nat(34u);
v___x_3110_ = lean_unsigned_to_nat(360u);
v___x_3111_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3112_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3113_ = l_mkPanicMessageWithDecl(v___x_3112_, v___x_3111_, v___x_3110_, v___x_3109_, v___x_3108_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3114_, lean_object* v___x_3115_, lean_object* v___x_3116_, lean_object* v_i_3117_, lean_object* v_kinds_3118_, lean_object* v___x_3119_, lean_object* v_lhs_3120_, lean_object* v_rhs_3121_, lean_object* v_type_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
uint8_t v___x_1556__boxed_3128_; uint8_t v___x_1557__boxed_3129_; lean_object* v_res_3130_; 
v___x_1556__boxed_3128_ = lean_unbox(v___x_3115_);
v___x_1557__boxed_3129_ = lean_unbox(v___x_3116_);
v_res_3130_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3114_, v___x_1556__boxed_3128_, v___x_1557__boxed_3129_, v_i_3117_, v_kinds_3118_, v___x_3119_, v_lhs_3120_, v_rhs_3121_, v_type_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3131_, uint8_t v___x_3132_, uint8_t v___x_3133_, lean_object* v_i_3134_, lean_object* v___x_3135_, lean_object* v_kinds_3136_, lean_object* v_typeSub_3137_, lean_object* v_lhs_3138_, lean_object* v_rhs_3139_, lean_object* v_type_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___x_3146_; uint8_t v___x_3147_; lean_object* v___x_3148_; 
lean_inc_ref(v_rhs_3139_);
v___x_3146_ = lean_array_push(v___x_3131_, v_rhs_3139_);
v___x_3147_ = 1;
v___x_3148_ = l_Lean_Meta_mkLambdaFVars(v___x_3146_, v_type_3140_, v___x_3132_, v___x_3133_, v___x_3132_, v___x_3133_, v___x_3147_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec_ref(v___x_3146_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v___x_3150_ = lean_nat_add(v_i_3134_, v___x_3135_);
v___x_3151_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3136_, v___x_3150_, v_typeSub_3137_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v___x_3153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3154_ = lean_unsigned_to_nat(2u);
v___x_3155_ = lean_mk_empty_array_with_capacity(v___x_3154_);
v___x_3156_ = lean_array_push(v___x_3155_, v_lhs_3138_);
v___x_3157_ = lean_array_push(v___x_3156_, v_rhs_3139_);
lean_inc_ref(v___x_3157_);
v___x_3158_ = l_Lean_Meta_mkAppM(v___x_3153_, v___x_3157_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = l_Lean_Meta_mkEqNDRec(v_a_3149_, v_a_3152_, v_a_3159_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3162_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v___x_3162_ = l_Lean_Meta_mkLambdaFVars(v___x_3157_, v_a_3161_, v___x_3132_, v___x_3133_, v___x_3132_, v___x_3133_, v___x_3147_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec_ref(v___x_3157_);
return v___x_3162_;
}
else
{
lean_dec_ref(v___x_3157_);
return v___x_3160_;
}
}
else
{
lean_dec_ref(v___x_3157_);
lean_dec(v_a_3152_);
lean_dec(v_a_3149_);
return v___x_3158_;
}
}
else
{
lean_dec(v_a_3149_);
lean_dec_ref(v_rhs_3139_);
lean_dec_ref(v_lhs_3138_);
return v___x_3151_;
}
}
else
{
lean_dec_ref(v_rhs_3139_);
lean_dec_ref(v_lhs_3138_);
lean_dec_ref(v_typeSub_3137_);
lean_dec_ref(v_kinds_3136_);
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3163_, lean_object* v___x_3164_, lean_object* v___x_3165_, lean_object* v_i_3166_, lean_object* v___x_3167_, lean_object* v_kinds_3168_, lean_object* v_typeSub_3169_, lean_object* v_lhs_3170_, lean_object* v_rhs_3171_, lean_object* v_type_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v___x_1620__boxed_3178_; uint8_t v___x_1621__boxed_3179_; lean_object* v_res_3180_; 
v___x_1620__boxed_3178_ = lean_unbox(v___x_3164_);
v___x_1621__boxed_3179_ = lean_unbox(v___x_3165_);
v_res_3180_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3163_, v___x_1620__boxed_3178_, v___x_1621__boxed_3179_, v_i_3166_, v___x_3167_, v_kinds_3168_, v_typeSub_3169_, v_lhs_3170_, v_rhs_3171_, v_type_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___x_3167_);
lean_dec(v_i_3166_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(uint8_t v___x_3181_, lean_object* v_kinds_3182_, lean_object* v_i_3183_, uint8_t v___x_3184_, uint8_t v___x_3185_, lean_object* v_lhs_3186_, lean_object* v_type_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3196_ = lean_box(v___x_3181_);
v___x_3197_ = lean_array_get(v___x_3196_, v_kinds_3182_, v_i_3183_);
lean_dec(v___x_3196_);
v___x_3198_ = lean_unbox(v___x_3197_);
lean_dec(v___x_3197_);
switch(v___x_3198_)
{
case 1:
{
lean_dec_ref(v_type_3187_);
lean_dec_ref(v_lhs_3186_);
lean_dec(v_i_3183_);
lean_dec_ref(v_kinds_3182_);
goto v___jp_3193_;
}
case 2:
{
lean_object* v___x_3199_; 
lean_inc_ref(v_lhs_3186_);
v___x_3199_ = l_Lean_Meta_mkEqRefl(v_lhs_3186_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___f_3210_; lean_object* v___x_3211_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = l_Lean_Expr_bindingBody_x21(v_type_3187_);
v___x_3202_ = l_Lean_Expr_bindingBody_x21(v___x_3201_);
lean_dec_ref(v___x_3201_);
v___x_3203_ = lean_unsigned_to_nat(2u);
v___x_3204_ = lean_mk_empty_array_with_capacity(v___x_3203_);
lean_inc_ref(v___x_3204_);
v___x_3205_ = lean_array_push(v___x_3204_, v_a_3200_);
lean_inc_ref(v_lhs_3186_);
v___x_3206_ = lean_array_push(v___x_3205_, v_lhs_3186_);
v___x_3207_ = lean_expr_instantiate(v___x_3202_, v___x_3206_);
lean_dec_ref(v___x_3206_);
lean_dec_ref(v___x_3202_);
v___x_3208_ = lean_box(v___x_3184_);
v___x_3209_ = lean_box(v___x_3185_);
v___f_3210_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3210_, 0, v___x_3204_);
lean_closure_set(v___f_3210_, 1, v___x_3208_);
lean_closure_set(v___f_3210_, 2, v___x_3209_);
lean_closure_set(v___f_3210_, 3, v_i_3183_);
lean_closure_set(v___f_3210_, 4, v_kinds_3182_);
lean_closure_set(v___f_3210_, 5, v___x_3207_);
lean_closure_set(v___f_3210_, 6, v_lhs_3186_);
v___x_3211_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3187_, v___f_3210_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3211_;
}
else
{
lean_dec_ref(v_type_3187_);
lean_dec_ref(v_lhs_3186_);
lean_dec(v_i_3183_);
lean_dec_ref(v_kinds_3182_);
return v___x_3199_;
}
}
case 4:
{
lean_dec_ref(v_type_3187_);
lean_dec_ref(v_lhs_3186_);
lean_dec(v_i_3183_);
lean_dec_ref(v_kinds_3182_);
goto v___jp_3193_;
}
case 5:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v_typeSub_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; 
v___x_3212_ = l_Lean_Expr_bindingBody_x21(v_type_3187_);
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_mk_empty_array_with_capacity(v___x_3213_);
lean_inc_ref(v_lhs_3186_);
lean_inc_ref(v___x_3214_);
v___x_3215_ = lean_array_push(v___x_3214_, v_lhs_3186_);
v_typeSub_3216_ = lean_expr_instantiate(v___x_3212_, v___x_3215_);
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3212_);
v___x_3217_ = lean_box(v___x_3184_);
v___x_3218_ = lean_box(v___x_3185_);
v___f_3219_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3219_, 0, v___x_3214_);
lean_closure_set(v___f_3219_, 1, v___x_3217_);
lean_closure_set(v___f_3219_, 2, v___x_3218_);
lean_closure_set(v___f_3219_, 3, v_i_3183_);
lean_closure_set(v___f_3219_, 4, v___x_3213_);
lean_closure_set(v___f_3219_, 5, v_kinds_3182_);
lean_closure_set(v___f_3219_, 6, v_typeSub_3216_);
lean_closure_set(v___f_3219_, 7, v_lhs_3186_);
v___x_3220_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3187_, v___f_3219_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3220_;
}
default: 
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = lean_unsigned_to_nat(1u);
v___x_3222_ = lean_nat_add(v_i_3183_, v___x_3221_);
lean_dec(v_i_3183_);
v___x_3223_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3182_, v___x_3222_, v_type_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; lean_object* v___x_3228_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v___x_3225_ = lean_mk_empty_array_with_capacity(v___x_3221_);
v___x_3226_ = lean_array_push(v___x_3225_, v_lhs_3186_);
v___x_3227_ = 1;
v___x_3228_ = l_Lean_Meta_mkLambdaFVars(v___x_3226_, v_a_3224_, v___x_3184_, v___x_3185_, v___x_3184_, v___x_3185_, v___x_3227_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec_ref(v___x_3226_);
return v___x_3228_;
}
else
{
lean_dec_ref(v_lhs_3186_);
return v___x_3223_;
}
}
}
v___jp_3193_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3195_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3194_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v___x_3229_, lean_object* v_kinds_3230_, lean_object* v_i_3231_, lean_object* v___x_3232_, lean_object* v___x_3233_, lean_object* v_lhs_3234_, lean_object* v_type_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
uint8_t v___x_1657__boxed_3241_; uint8_t v___x_1658__boxed_3242_; uint8_t v___x_1659__boxed_3243_; lean_object* v_res_3244_; 
v___x_1657__boxed_3241_ = lean_unbox(v___x_3229_);
v___x_1658__boxed_3242_ = lean_unbox(v___x_3232_);
v___x_1659__boxed_3243_ = lean_unbox(v___x_3233_);
v_res_3244_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v___x_1657__boxed_3241_, v_kinds_3230_, v_i_3231_, v___x_1658__boxed_3242_, v___x_1659__boxed_3243_, v_lhs_3234_, v_type_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
return v_res_3244_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3245_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3246_ = lean_unsigned_to_nat(43u);
v___x_3247_ = lean_unsigned_to_nat(355u);
v___x_3248_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3249_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3250_ = l_mkPanicMessageWithDecl(v___x_3249_, v___x_3248_, v___x_3247_, v___x_3246_, v___x_3245_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3251_, lean_object* v_i_3252_, lean_object* v_type_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = lean_array_get_size(v_kinds_3251_);
v___x_3260_ = lean_nat_dec_eq(v_i_3252_, v___x_3259_);
if (v___x_3260_ == 0)
{
uint8_t v___x_3261_; uint8_t v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___f_3266_; lean_object* v___x_3267_; 
v___x_3261_ = 0;
v___x_3262_ = 1;
v___x_3263_ = lean_box(v___x_3261_);
v___x_3264_ = lean_box(v___x_3260_);
v___x_3265_ = lean_box(v___x_3262_);
v___f_3266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 12, 5);
lean_closure_set(v___f_3266_, 0, v___x_3263_);
lean_closure_set(v___f_3266_, 1, v_kinds_3251_);
lean_closure_set(v___f_3266_, 2, v_i_3252_);
lean_closure_set(v___f_3266_, 3, v___x_3264_);
lean_closure_set(v___f_3266_, 4, v___x_3265_);
v___x_3267_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3253_, v___f_3266_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
lean_dec(v_i_3252_);
lean_dec_ref(v_kinds_3251_);
v___x_3268_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3269_ = lean_unsigned_to_nat(3u);
v___x_3270_ = l_Lean_Expr_isAppOfArity(v_type_3253_, v___x_3268_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec_ref(v_type_3253_);
v___x_3271_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3272_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3271_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3272_;
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = l_Lean_Expr_appFn_x21(v_type_3253_);
lean_dec_ref(v_type_3253_);
v___x_3274_ = l_Lean_Expr_appArg_x21(v___x_3273_);
lean_dec_ref(v___x_3273_);
v___x_3275_ = l_Lean_Meta_mkEqRefl(v___x_3274_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* v___x_3276_, lean_object* v_rhs_3277_, uint8_t v___x_3278_, uint8_t v___x_3279_, lean_object* v_i_3280_, lean_object* v_kinds_3281_, lean_object* v___x_3282_, lean_object* v_lhs_3283_, lean_object* v_heq_3284_, lean_object* v_type_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; 
lean_inc_ref(v_rhs_3277_);
v___x_3291_ = lean_array_push(v___x_3276_, v_rhs_3277_);
lean_inc_ref(v_heq_3284_);
v___x_3292_ = lean_array_push(v___x_3291_, v_heq_3284_);
v___x_3293_ = 1;
v___x_3294_ = l_Lean_Meta_mkLambdaFVars(v___x_3292_, v_type_3285_, v___x_3278_, v___x_3279_, v___x_3278_, v___x_3279_, v___x_3293_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec_ref(v___x_3292_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v___x_3296_ = lean_unsigned_to_nat(1u);
v___x_3297_ = lean_nat_add(v_i_3280_, v___x_3296_);
v___x_3298_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3281_, v___x_3297_, v___x_3282_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3298_, 1);
lean_inc_ref(v_heq_3284_);
v___x_3300_ = l_Lean_Meta_mkEqRec(v_a_3295_, v_a_3299_, v_heq_3284_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3300_, 1);
v___x_3302_ = lean_unsigned_to_nat(3u);
v___x_3303_ = lean_mk_empty_array_with_capacity(v___x_3302_);
v___x_3304_ = lean_array_push(v___x_3303_, v_lhs_3283_);
v___x_3305_ = lean_array_push(v___x_3304_, v_rhs_3277_);
v___x_3306_ = lean_array_push(v___x_3305_, v_heq_3284_);
v___x_3307_ = l_Lean_Meta_mkLambdaFVars(v___x_3306_, v_a_3301_, v___x_3278_, v___x_3279_, v___x_3278_, v___x_3279_, v___x_3293_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec_ref(v___x_3306_);
return v___x_3307_;
}
else
{
lean_dec_ref(v_heq_3284_);
lean_dec_ref(v_lhs_3283_);
lean_dec_ref(v_rhs_3277_);
return v___x_3300_;
}
}
else
{
lean_dec(v_a_3295_);
lean_dec_ref(v_heq_3284_);
lean_dec_ref(v_lhs_3283_);
lean_dec_ref(v_rhs_3277_);
return v___x_3298_;
}
}
else
{
lean_dec_ref(v_heq_3284_);
lean_dec_ref(v_lhs_3283_);
lean_dec_ref(v___x_3282_);
lean_dec_ref(v_kinds_3281_);
lean_dec_ref(v_rhs_3277_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* v___x_3308_, lean_object* v_rhs_3309_, lean_object* v___x_3310_, lean_object* v___x_3311_, lean_object* v_i_3312_, lean_object* v_kinds_3313_, lean_object* v___x_3314_, lean_object* v_lhs_3315_, lean_object* v_heq_3316_, lean_object* v_type_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
uint8_t v___x_1567__boxed_3323_; uint8_t v___x_1568__boxed_3324_; lean_object* v_res_3325_; 
v___x_1567__boxed_3323_ = lean_unbox(v___x_3310_);
v___x_1568__boxed_3324_ = lean_unbox(v___x_3311_);
v_res_3325_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3308_, v_rhs_3309_, v___x_1567__boxed_3323_, v___x_1568__boxed_3324_, v_i_3312_, v_kinds_3313_, v___x_3314_, v_lhs_3315_, v_heq_3316_, v_type_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v_i_3312_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* v___x_3326_, uint8_t v___x_3327_, uint8_t v___x_3328_, lean_object* v_i_3329_, lean_object* v_kinds_3330_, lean_object* v___x_3331_, lean_object* v_lhs_3332_, lean_object* v_rhs_3333_, lean_object* v_type_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___f_3342_; lean_object* v___x_3343_; 
v___x_3340_ = lean_box(v___x_3327_);
v___x_3341_ = lean_box(v___x_3328_);
v___f_3342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3342_, 0, v___x_3326_);
lean_closure_set(v___f_3342_, 1, v_rhs_3333_);
lean_closure_set(v___f_3342_, 2, v___x_3340_);
lean_closure_set(v___f_3342_, 3, v___x_3341_);
lean_closure_set(v___f_3342_, 4, v_i_3329_);
lean_closure_set(v___f_3342_, 5, v_kinds_3330_);
lean_closure_set(v___f_3342_, 6, v___x_3331_);
lean_closure_set(v___f_3342_, 7, v_lhs_3332_);
v___x_3343_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3334_, v___f_3342_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object* v_kinds_3344_, lean_object* v_i_3345_, lean_object* v_type_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3344_, v_i_3345_, v_type_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* v_type_3353_, lean_object* v_kinds_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3354_, v___x_3360_, v_type_3353_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object* v_type_3362_, lean_object* v_kinds_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3362_, v_kinds_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_msg_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v___f_3376_; lean_object* v___x_1569__overap_3377_; lean_object* v___x_3378_; 
v___f_3376_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1569__overap_3377_ = lean_panic_fn_borrowed(v___f_3376_, v_msg_3370_);
lean_inc(v___y_3374_);
lean_inc_ref(v___y_3373_);
lean_inc(v___y_3372_);
lean_inc_ref(v___y_3371_);
v___x_3378_ = lean_apply_5(v___x_1569__overap_3377_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, lean_box(0));
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_msg_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_msg_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(lean_object* v_bs_3386_, lean_object* v_k_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___x_3393_; 
v___x_3393_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3386_, v_k_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
v_a_3402_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3393_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3393_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg___boxed(lean_object* v_bs_3410_, lean_object* v_k_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3410_, v_k_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec_ref(v_bs_3410_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(lean_object* v_00_u03b1_3418_, lean_object* v_bs_3419_, lean_object* v_k_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3419_, v_k_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3427_, lean_object* v_bs_3428_, lean_object* v_k_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(v_00_u03b1_3427_, v_bs_3428_, v_k_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec_ref(v_bs_3428_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(size_t v_sz_3436_, size_t v_i_3437_, lean_object* v_bs_3438_){
_start:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_usize_dec_lt(v_i_3437_, v_sz_3436_);
if (v___x_3439_ == 0)
{
return v_bs_3438_;
}
else
{
lean_object* v_v_3440_; lean_object* v___x_3441_; lean_object* v_bs_x27_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; size_t v___x_3447_; size_t v___x_3448_; lean_object* v___x_3449_; 
v_v_3440_ = lean_array_uget(v_bs_3438_, v_i_3437_);
v___x_3441_ = lean_unsigned_to_nat(0u);
v_bs_x27_3442_ = lean_array_uset(v_bs_3438_, v_i_3437_, v___x_3441_);
v___x_3443_ = l_Lean_Expr_fvarId_x21(v_v_3440_);
lean_dec(v_v_3440_);
v___x_3444_ = 1;
v___x_3445_ = lean_box(v___x_3444_);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3443_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = ((size_t)1ULL);
v___x_3448_ = lean_usize_add(v_i_3437_, v___x_3447_);
v___x_3449_ = lean_array_uset(v_bs_x27_3442_, v_i_3437_, v___x_3446_);
v_i_3437_ = v___x_3448_;
v_bs_3438_ = v___x_3449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0___boxed(lean_object* v_sz_3451_, lean_object* v_i_3452_, lean_object* v_bs_3453_){
_start:
{
size_t v_sz_boxed_3454_; size_t v_i_boxed_3455_; lean_object* v_res_3456_; 
v_sz_boxed_3454_ = lean_unbox_usize(v_sz_3451_);
lean_dec(v_sz_3451_);
v_i_boxed_3455_ = lean_unbox_usize(v_i_3452_);
lean_dec(v_i_3452_);
v_res_3456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_boxed_3454_, v_i_boxed_3455_, v_bs_3453_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(lean_object* v_bs_3457_, lean_object* v_k_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
size_t v_sz_3464_; size_t v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_sz_3464_ = lean_array_size(v_bs_3457_);
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_3464_, v___x_3465_, v_bs_3457_);
v___x_3467_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v___x_3466_, v_k_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
lean_dec_ref(v___x_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg___boxed(lean_object* v_bs_3468_, lean_object* v_k_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3468_, v_k_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_00_u03b1_3476_, lean_object* v_bs_3477_, lean_object* v_k_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3477_, v_k_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3485_, lean_object* v_bs_3486_, lean_object* v_k_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_00_u03b1_3485_, v_bs_3486_, v_k_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3494_, lean_object* v_rhss_3495_, lean_object* v_b_3496_, lean_object* v_eqs_3497_, lean_object* v_hyps_3498_, uint8_t v_subsingletonInstImplicitRhs_3499_, lean_object* v_f_3500_, lean_object* v_info_3501_, lean_object* v_kinds_3502_, lean_object* v_lhss_3503_, lean_object* v_eq_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3510_ = lean_unsigned_to_nat(1u);
v___x_3511_ = lean_nat_add(v_i_3494_, v___x_3510_);
lean_inc_ref(v_b_3496_);
v___x_3512_ = lean_array_push(v_rhss_3495_, v_b_3496_);
v___x_3513_ = l_Lean_Expr_fvarId_x21(v_eq_3504_);
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
v___x_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
v___x_3516_ = lean_array_push(v_eqs_3497_, v___x_3515_);
v___x_3517_ = lean_array_push(v_hyps_3498_, v_b_3496_);
v___x_3518_ = lean_array_push(v___x_3517_, v_eq_3504_);
v___x_3519_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3499_, v_f_3500_, v_info_3501_, v_kinds_3502_, v_lhss_3503_, v___x_3511_, v___x_3512_, v___x_3516_, v___x_3518_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3520_, lean_object* v_rhss_3521_, lean_object* v_b_3522_, lean_object* v_eqs_3523_, lean_object* v_hyps_3524_, lean_object* v_subsingletonInstImplicitRhs_3525_, lean_object* v_f_3526_, lean_object* v_info_3527_, lean_object* v_kinds_3528_, lean_object* v_lhss_3529_, lean_object* v_eq_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3536_; lean_object* v_res_3537_; 
v_subsingletonInstImplicitRhs_boxed_3536_ = lean_unbox(v_subsingletonInstImplicitRhs_3525_);
v_res_3537_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3520_, v_rhss_3521_, v_b_3522_, v_eqs_3523_, v_hyps_3524_, v_subsingletonInstImplicitRhs_boxed_3536_, v_f_3526_, v_info_3527_, v_kinds_3528_, v_lhss_3529_, v_eq_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v_i_3520_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(lean_object* v_lhs_3539_, lean_object* v_i_3540_, lean_object* v_rhss_3541_, lean_object* v_eqs_3542_, lean_object* v_hyps_3543_, uint8_t v_subsingletonInstImplicitRhs_3544_, lean_object* v_f_3545_, lean_object* v_info_3546_, lean_object* v_kinds_3547_, lean_object* v_lhss_3548_, lean_object* v___x_3549_, lean_object* v_b_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; 
lean_inc_ref(v_b_3550_);
v___x_3556_ = l_Lean_Meta_mkEq(v_lhs_3539_, v_b_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v___x_3558_ = lean_box(v_subsingletonInstImplicitRhs_3544_);
v___f_3559_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3559_, 0, v_i_3540_);
lean_closure_set(v___f_3559_, 1, v_rhss_3541_);
lean_closure_set(v___f_3559_, 2, v_b_3550_);
lean_closure_set(v___f_3559_, 3, v_eqs_3542_);
lean_closure_set(v___f_3559_, 4, v_hyps_3543_);
lean_closure_set(v___f_3559_, 5, v___x_3558_);
lean_closure_set(v___f_3559_, 6, v_f_3545_);
lean_closure_set(v___f_3559_, 7, v_info_3546_);
lean_closure_set(v___f_3559_, 8, v_kinds_3547_);
lean_closure_set(v___f_3559_, 9, v_lhss_3548_);
v___x_3560_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0));
v___x_3561_ = lean_name_append_before(v___x_3549_, v___x_3560_);
v___x_3562_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3561_, v_a_3557_, v___f_3559_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3562_;
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec_ref(v_b_3550_);
lean_dec(v___x_3549_);
lean_dec_ref(v_lhss_3548_);
lean_dec_ref(v_kinds_3547_);
lean_dec_ref(v_info_3546_);
lean_dec_ref(v_f_3545_);
lean_dec_ref(v_hyps_3543_);
lean_dec_ref(v_eqs_3542_);
lean_dec_ref(v_rhss_3541_);
lean_dec(v_i_3540_);
v_a_3563_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3556_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3556_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed(lean_object** _args){
lean_object* v_lhs_3571_ = _args[0];
lean_object* v_i_3572_ = _args[1];
lean_object* v_rhss_3573_ = _args[2];
lean_object* v_eqs_3574_ = _args[3];
lean_object* v_hyps_3575_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3576_ = _args[5];
lean_object* v_f_3577_ = _args[6];
lean_object* v_info_3578_ = _args[7];
lean_object* v_kinds_3579_ = _args[8];
lean_object* v_lhss_3580_ = _args[9];
lean_object* v___x_3581_ = _args[10];
lean_object* v_b_3582_ = _args[11];
lean_object* v___y_3583_ = _args[12];
lean_object* v___y_3584_ = _args[13];
lean_object* v___y_3585_ = _args[14];
lean_object* v___y_3586_ = _args[15];
lean_object* v___y_3587_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3588_; lean_object* v_res_3589_; 
v_subsingletonInstImplicitRhs_boxed_3588_ = lean_unbox(v_subsingletonInstImplicitRhs_3576_);
v_res_3589_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(v_lhs_3571_, v_i_3572_, v_rhss_3573_, v_eqs_3574_, v_hyps_3575_, v_subsingletonInstImplicitRhs_boxed_3588_, v_f_3577_, v_info_3578_, v_kinds_3579_, v_lhss_3580_, v___x_3581_, v_b_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3590_, lean_object* v_rhss_3591_, lean_object* v_eqs_3592_, lean_object* v_hyps_3593_, uint8_t v_subsingletonInstImplicitRhs_3594_, lean_object* v_f_3595_, lean_object* v_info_3596_, lean_object* v_kinds_3597_, lean_object* v_lhss_3598_, lean_object* v_lhs_3599_, lean_object* v___x_3600_, lean_object* v_name_3601_, uint8_t v_bi_3602_, lean_object* v_type_3603_, uint8_t v_kind_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; 
v___x_3610_ = lean_box(v_subsingletonInstImplicitRhs_3594_);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3611_, 0, v_lhs_3599_);
lean_closure_set(v___f_3611_, 1, v_i_3590_);
lean_closure_set(v___f_3611_, 2, v_rhss_3591_);
lean_closure_set(v___f_3611_, 3, v_eqs_3592_);
lean_closure_set(v___f_3611_, 4, v_hyps_3593_);
lean_closure_set(v___f_3611_, 5, v___x_3610_);
lean_closure_set(v___f_3611_, 6, v_f_3595_);
lean_closure_set(v___f_3611_, 7, v_info_3596_);
lean_closure_set(v___f_3611_, 8, v_kinds_3597_);
lean_closure_set(v___f_3611_, 9, v_lhss_3598_);
lean_closure_set(v___f_3611_, 10, v___x_3600_);
v___x_3612_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3601_, v_bi_3602_, v_type_3603_, v___f_3611_, v_kind_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3612_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3612_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
v_a_3621_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3612_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3612_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3629_, lean_object* v_rhss_3630_, lean_object* v_lhss_3631_, lean_object* v_i_3632_, lean_object* v_eqs_3633_, lean_object* v_hyps_3634_, uint8_t v_subsingletonInstImplicitRhs_3635_, lean_object* v_f_3636_, lean_object* v_info_3637_, lean_object* v_kinds_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v___x_3644_; 
lean_inc(v___y_3642_);
lean_inc_ref(v___y_3641_);
lean_inc(v___y_3640_);
lean_inc_ref(v___y_3639_);
lean_inc_ref(v_lhs_3629_);
v___x_3644_ = lean_infer_type(v_lhs_3629_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; uint8_t v___y_3652_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v___x_3646_ = lean_array_get_size(v_rhss_3630_);
v___x_3647_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3631_);
v___x_3648_ = l_Array_toSubarray___redArg(v_lhss_3631_, v___x_3647_, v___x_3646_);
v___x_3649_ = l_Subarray_copy___redArg(v___x_3648_);
v___x_3650_ = l_Lean_Expr_replaceFVars(v_a_3645_, v___x_3649_, v_rhss_3630_);
lean_dec_ref(v___x_3649_);
lean_dec(v_a_3645_);
if (v_subsingletonInstImplicitRhs_3635_ == 0)
{
uint8_t v___x_3667_; 
v___x_3667_ = 1;
v___y_3652_ = v___x_3667_;
goto v___jp_3651_;
}
else
{
uint8_t v___x_3668_; 
v___x_3668_ = 3;
v___y_3652_ = v___x_3668_;
goto v___jp_3651_;
}
v___jp_3651_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = l_Lean_Expr_fvarId_x21(v_lhs_3629_);
v___x_3654_ = l_Lean_FVarId_getDecl___redArg(v___x_3653_, v___y_3639_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3654_, 1);
v___x_3656_ = l_Lean_LocalDecl_userName(v_a_3655_);
lean_dec(v_a_3655_);
v___x_3657_ = 0;
v___x_3658_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3632_, v_rhss_3630_, v_lhs_3629_, v_eqs_3633_, v_hyps_3634_, v_subsingletonInstImplicitRhs_3635_, v_f_3636_, v_info_3637_, v_kinds_3638_, v_lhss_3631_, v___x_3656_, v___y_3652_, v___x_3650_, v___x_3657_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
return v___x_3658_;
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec_ref(v___x_3650_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v_kinds_3638_);
lean_dec_ref(v_info_3637_);
lean_dec_ref(v_f_3636_);
lean_dec_ref(v_hyps_3634_);
lean_dec_ref(v_eqs_3633_);
lean_dec(v_i_3632_);
lean_dec_ref(v_lhss_3631_);
lean_dec_ref(v_rhss_3630_);
lean_dec_ref(v_lhs_3629_);
v_a_3659_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3654_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3654_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v_kinds_3638_);
lean_dec_ref(v_info_3637_);
lean_dec_ref(v_f_3636_);
lean_dec_ref(v_hyps_3634_);
lean_dec_ref(v_eqs_3633_);
lean_dec(v_i_3632_);
lean_dec_ref(v_lhss_3631_);
lean_dec_ref(v_rhss_3630_);
lean_dec_ref(v_lhs_3629_);
v_a_3669_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3644_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3644_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3677_, lean_object* v_rhss_3678_, lean_object* v_lhss_3679_, lean_object* v_i_3680_, lean_object* v_eqs_3681_, lean_object* v_hyps_3682_, lean_object* v_subsingletonInstImplicitRhs_3683_, lean_object* v_f_3684_, lean_object* v_info_3685_, lean_object* v_kinds_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3692_; lean_object* v_res_3693_; 
v_subsingletonInstImplicitRhs_boxed_3692_ = lean_unbox(v_subsingletonInstImplicitRhs_3683_);
v_res_3693_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3677_, v_rhss_3678_, v_lhss_3679_, v_i_3680_, v_eqs_3681_, v_hyps_3682_, v_subsingletonInstImplicitRhs_boxed_3692_, v_f_3684_, v_info_3685_, v_kinds_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v_res_3693_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3695_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3696_ = lean_unsigned_to_nat(38u);
v___x_3697_ = lean_unsigned_to_nat(328u);
v___x_3698_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3699_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3700_ = l_mkPanicMessageWithDecl(v___x_3699_, v___x_3698_, v___x_3697_, v___x_3696_, v___x_3695_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3701_, lean_object* v_f_3702_, lean_object* v_info_3703_, lean_object* v_kinds_3704_, lean_object* v_lhss_3705_, lean_object* v_i_3706_, lean_object* v_rhss_3707_, lean_object* v_eqs_3708_, lean_object* v_hyps_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3715_ = lean_array_get_size(v_kinds_3704_);
v___x_3716_ = lean_nat_dec_eq(v_i_3706_, v___x_3715_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; uint8_t v___x_3718_; lean_object* v_lhs_3719_; lean_object* v_hyps_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3717_ = l_Lean_instInhabitedExpr;
v___x_3718_ = 0;
v_lhs_3719_ = lean_array_get_borrowed(v___x_3717_, v_lhss_3705_, v_i_3706_);
lean_inc(v_lhs_3719_);
v_hyps_3720_ = lean_array_push(v_hyps_3709_, v_lhs_3719_);
v___x_3721_ = lean_box(v___x_3718_);
v___x_3722_ = lean_array_get(v___x_3721_, v_kinds_3704_, v_i_3706_);
lean_dec(v___x_3721_);
v___x_3723_ = lean_unbox(v___x_3722_);
lean_dec(v___x_3722_);
switch(v___x_3723_)
{
case 0:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3724_ = lean_unsigned_to_nat(1u);
v___x_3725_ = lean_nat_add(v_i_3706_, v___x_3724_);
lean_dec(v_i_3706_);
lean_inc(v_lhs_3719_);
v___x_3726_ = lean_array_push(v_rhss_3707_, v_lhs_3719_);
v___x_3727_ = lean_box(0);
v___x_3728_ = lean_array_push(v_eqs_3708_, v___x_3727_);
v_i_3706_ = v___x_3725_;
v_rhss_3707_ = v___x_3726_;
v_eqs_3708_ = v___x_3728_;
v_hyps_3709_ = v_hyps_3720_;
goto _start;
}
case 2:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
lean_inc(v_lhs_3719_);
v___x_3730_ = l_Lean_Expr_fvarId_x21(v_lhs_3719_);
v___x_3731_ = l_Lean_FVarId_getDecl___redArg(v___x_3730_, v_a_3710_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; lean_object* v___x_3735_; uint8_t v___x_3736_; lean_object* v___x_3737_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v___x_3733_ = l_Lean_LocalDecl_userName(v_a_3732_);
v___x_3734_ = l_Lean_LocalDecl_binderInfo(v_a_3732_);
v___x_3735_ = l_Lean_LocalDecl_type(v_a_3732_);
lean_dec(v_a_3732_);
v___x_3736_ = 0;
lean_inc(v___x_3733_);
v___x_3737_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3706_, v_rhss_3707_, v_eqs_3708_, v_hyps_3720_, v_subsingletonInstImplicitRhs_3701_, v_f_3702_, v_info_3703_, v_kinds_3704_, v_lhss_3705_, v_lhs_3719_, v___x_3733_, v___x_3733_, v___x_3734_, v___x_3735_, v___x_3736_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
return v___x_3737_;
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec_ref(v_hyps_3720_);
lean_dec(v_lhs_3719_);
lean_dec_ref(v_eqs_3708_);
lean_dec_ref(v_rhss_3707_);
lean_dec(v_i_3706_);
lean_dec_ref(v_lhss_3705_);
lean_dec_ref(v_kinds_3704_);
lean_dec_ref(v_info_3703_);
lean_dec_ref(v_f_3702_);
v_a_3738_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3731_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3731_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
case 3:
{
lean_object* v___x_3746_; 
lean_inc(v_a_3713_);
lean_inc_ref(v_a_3712_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
lean_inc(v_lhs_3719_);
v___x_3746_ = lean_infer_type(v_lhs_3719_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v_paramInfo_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v_backDeps_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
v_paramInfo_3748_ = lean_ctor_get(v_info_3703_, 0);
v___x_3749_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_3750_ = lean_array_get_borrowed(v___x_3749_, v_paramInfo_3748_, v_i_3706_);
v_backDeps_3751_ = lean_ctor_get(v___x_3750_, 0);
v___x_3752_ = lean_array_get_size(v_rhss_3707_);
v___x_3753_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3705_);
v___x_3754_ = l_Array_toSubarray___redArg(v_lhss_3705_, v___x_3753_, v___x_3752_);
v___x_3755_ = l_Subarray_copy___redArg(v___x_3754_);
v___x_3756_ = l_Lean_Expr_replaceFVars(v_a_3747_, v___x_3755_, v_rhss_3707_);
lean_dec_ref(v___x_3755_);
lean_dec(v_a_3747_);
v___x_3757_ = l_Lean_Expr_fvarId_x21(v_lhs_3719_);
v___x_3758_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3757_, v___x_3756_, v_backDeps_3751_, v_eqs_3708_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3758_, 1);
v___x_3760_ = lean_unsigned_to_nat(1u);
v___x_3761_ = lean_nat_add(v_i_3706_, v___x_3760_);
lean_dec(v_i_3706_);
v___x_3762_ = lean_array_push(v_rhss_3707_, v_a_3759_);
v___x_3763_ = lean_box(0);
v___x_3764_ = lean_array_push(v_eqs_3708_, v___x_3763_);
v_i_3706_ = v___x_3761_;
v_rhss_3707_ = v___x_3762_;
v_eqs_3708_ = v___x_3764_;
v_hyps_3709_ = v_hyps_3720_;
goto _start;
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec_ref(v_hyps_3720_);
lean_dec_ref(v_eqs_3708_);
lean_dec_ref(v_rhss_3707_);
lean_dec(v_i_3706_);
lean_dec_ref(v_lhss_3705_);
lean_dec_ref(v_kinds_3704_);
lean_dec_ref(v_info_3703_);
lean_dec_ref(v_f_3702_);
v_a_3766_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3758_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3758_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_dec_ref(v_hyps_3720_);
lean_dec_ref(v_eqs_3708_);
lean_dec_ref(v_rhss_3707_);
lean_dec(v_i_3706_);
lean_dec_ref(v_lhss_3705_);
lean_dec_ref(v_kinds_3704_);
lean_dec_ref(v_info_3703_);
lean_dec_ref(v_f_3702_);
v_a_3774_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3746_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3746_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
case 5:
{
lean_object* v___x_3782_; lean_object* v___f_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_inc_n(v_lhs_3719_, 2);
v___x_3782_ = lean_box(v_subsingletonInstImplicitRhs_3701_);
v___f_3783_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3783_, 0, v_lhs_3719_);
lean_closure_set(v___f_3783_, 1, v_rhss_3707_);
lean_closure_set(v___f_3783_, 2, v_lhss_3705_);
lean_closure_set(v___f_3783_, 3, v_i_3706_);
lean_closure_set(v___f_3783_, 4, v_eqs_3708_);
lean_closure_set(v___f_3783_, 5, v_hyps_3720_);
lean_closure_set(v___f_3783_, 6, v___x_3782_);
lean_closure_set(v___f_3783_, 7, v_f_3702_);
lean_closure_set(v___f_3783_, 8, v_info_3703_);
lean_closure_set(v___f_3783_, 9, v_kinds_3704_);
v___x_3784_ = lean_unsigned_to_nat(1u);
v___x_3785_ = lean_mk_empty_array_with_capacity(v___x_3784_);
v___x_3786_ = lean_array_push(v___x_3785_, v_lhs_3719_);
v___x_3787_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v___x_3786_, v___f_3783_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
return v___x_3787_;
}
default: 
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
lean_dec_ref(v_hyps_3720_);
lean_dec_ref(v_eqs_3708_);
lean_dec_ref(v_rhss_3707_);
lean_dec(v_i_3706_);
lean_dec_ref(v_lhss_3705_);
lean_dec_ref(v_kinds_3704_);
lean_dec_ref(v_info_3703_);
lean_dec_ref(v_f_3702_);
v___x_3788_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3789_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v___x_3788_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
return v___x_3789_;
}
}
}
else
{
lean_object* v_lhs_3790_; lean_object* v_rhs_3791_; lean_object* v___x_3792_; 
lean_dec_ref(v_eqs_3708_);
lean_dec(v_i_3706_);
lean_dec_ref(v_info_3703_);
lean_inc_ref(v_f_3702_);
v_lhs_3790_ = l_Lean_mkAppN(v_f_3702_, v_lhss_3705_);
lean_dec_ref(v_lhss_3705_);
v_rhs_3791_ = l_Lean_mkAppN(v_f_3702_, v_rhss_3707_);
lean_dec_ref(v_rhss_3707_);
v___x_3792_ = l_Lean_Meta_mkEq(v_lhs_3790_, v_rhs_3791_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; uint8_t v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___x_3794_ = 0;
v___x_3795_ = 1;
v___x_3796_ = l_Lean_Meta_mkForallFVars(v_hyps_3709_, v_a_3793_, v___x_3794_, v___x_3716_, v___x_3716_, v___x_3795_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
lean_dec_ref(v_hyps_3709_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc_n(v_a_3797_, 2);
lean_dec_ref_known(v___x_3796_, 1);
lean_inc_ref(v_kinds_3704_);
v___x_3798_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3797_, v_kinds_3704_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3807_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3803_, 0, v_a_3797_);
lean_ctor_set(v___x_3803_, 1, v_a_3799_);
lean_ctor_set(v___x_3803_, 2, v_kinds_3704_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_a_3797_);
lean_dec_ref(v_kinds_3704_);
v_a_3808_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3798_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3798_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec_ref(v_kinds_3704_);
v_a_3816_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3796_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3796_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v_hyps_3709_);
lean_dec_ref(v_kinds_3704_);
v_a_3824_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3792_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3792_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3832_, lean_object* v_rhss_3833_, lean_object* v_lhs_3834_, lean_object* v_eqs_3835_, lean_object* v_hyps_3836_, uint8_t v_subsingletonInstImplicitRhs_3837_, lean_object* v_f_3838_, lean_object* v_info_3839_, lean_object* v_kinds_3840_, lean_object* v_lhss_3841_, lean_object* v_b_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3848_ = lean_unsigned_to_nat(1u);
v___x_3849_ = lean_nat_add(v_i_3832_, v___x_3848_);
lean_inc_ref(v_b_3842_);
v___x_3850_ = lean_array_push(v_rhss_3833_, v_b_3842_);
v___x_3851_ = l_Lean_Expr_fvarId_x21(v_lhs_3834_);
v___x_3852_ = l_Lean_Expr_fvarId_x21(v_b_3842_);
v___x_3853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
v___x_3855_ = lean_array_push(v_eqs_3835_, v___x_3854_);
v___x_3856_ = lean_array_push(v_hyps_3836_, v_b_3842_);
v___x_3857_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3837_, v_f_3838_, v_info_3839_, v_kinds_3840_, v_lhss_3841_, v___x_3849_, v___x_3850_, v___x_3855_, v___x_3856_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_3858_, lean_object* v_rhss_3859_, lean_object* v_lhs_3860_, lean_object* v_eqs_3861_, lean_object* v_hyps_3862_, lean_object* v_subsingletonInstImplicitRhs_3863_, lean_object* v_f_3864_, lean_object* v_info_3865_, lean_object* v_kinds_3866_, lean_object* v_lhss_3867_, lean_object* v_b_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3874_; lean_object* v_res_3875_; 
v_subsingletonInstImplicitRhs_boxed_3874_ = lean_unbox(v_subsingletonInstImplicitRhs_3863_);
v_res_3875_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3858_, v_rhss_3859_, v_lhs_3860_, v_eqs_3861_, v_hyps_3862_, v_subsingletonInstImplicitRhs_boxed_3874_, v_f_3864_, v_info_3865_, v_kinds_3866_, v_lhss_3867_, v_b_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec_ref(v_lhs_3860_);
lean_dec(v_i_3858_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_3876_, lean_object* v_rhss_3877_, lean_object* v_lhs_3878_, lean_object* v_eqs_3879_, lean_object* v_hyps_3880_, uint8_t v_subsingletonInstImplicitRhs_3881_, lean_object* v_f_3882_, lean_object* v_info_3883_, lean_object* v_kinds_3884_, lean_object* v_lhss_3885_, lean_object* v_name_3886_, uint8_t v_bi_3887_, lean_object* v_type_3888_, uint8_t v_kind_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___x_3895_; lean_object* v___f_3896_; lean_object* v___x_3897_; 
v___x_3895_ = lean_box(v_subsingletonInstImplicitRhs_3881_);
v___f_3896_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3896_, 0, v_i_3876_);
lean_closure_set(v___f_3896_, 1, v_rhss_3877_);
lean_closure_set(v___f_3896_, 2, v_lhs_3878_);
lean_closure_set(v___f_3896_, 3, v_eqs_3879_);
lean_closure_set(v___f_3896_, 4, v_hyps_3880_);
lean_closure_set(v___f_3896_, 5, v___x_3895_);
lean_closure_set(v___f_3896_, 6, v_f_3882_);
lean_closure_set(v___f_3896_, 7, v_info_3883_);
lean_closure_set(v___f_3896_, 8, v_kinds_3884_);
lean_closure_set(v___f_3896_, 9, v_lhss_3885_);
v___x_3897_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3886_, v_bi_3887_, v_type_3888_, v___f_3896_, v_kind_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
v_a_3906_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3897_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3897_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object** _args){
lean_object* v_i_3914_ = _args[0];
lean_object* v_rhss_3915_ = _args[1];
lean_object* v_lhs_3916_ = _args[2];
lean_object* v_eqs_3917_ = _args[3];
lean_object* v_hyps_3918_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3919_ = _args[5];
lean_object* v_f_3920_ = _args[6];
lean_object* v_info_3921_ = _args[7];
lean_object* v_kinds_3922_ = _args[8];
lean_object* v_lhss_3923_ = _args[9];
lean_object* v_name_3924_ = _args[10];
lean_object* v_bi_3925_ = _args[11];
lean_object* v_type_3926_ = _args[12];
lean_object* v_kind_3927_ = _args[13];
lean_object* v___y_3928_ = _args[14];
lean_object* v___y_3929_ = _args[15];
lean_object* v___y_3930_ = _args[16];
lean_object* v___y_3931_ = _args[17];
lean_object* v___y_3932_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3933_; uint8_t v_bi_boxed_3934_; uint8_t v_kind_boxed_3935_; lean_object* v_res_3936_; 
v_subsingletonInstImplicitRhs_boxed_3933_ = lean_unbox(v_subsingletonInstImplicitRhs_3919_);
v_bi_boxed_3934_ = lean_unbox(v_bi_3925_);
v_kind_boxed_3935_ = lean_unbox(v_kind_3927_);
v_res_3936_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3914_, v_rhss_3915_, v_lhs_3916_, v_eqs_3917_, v_hyps_3918_, v_subsingletonInstImplicitRhs_boxed_3933_, v_f_3920_, v_info_3921_, v_kinds_3922_, v_lhss_3923_, v_name_3924_, v_bi_boxed_3934_, v_type_3926_, v_kind_boxed_3935_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_3937_ = _args[0];
lean_object* v_rhss_3938_ = _args[1];
lean_object* v_eqs_3939_ = _args[2];
lean_object* v_hyps_3940_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3941_ = _args[4];
lean_object* v_f_3942_ = _args[5];
lean_object* v_info_3943_ = _args[6];
lean_object* v_kinds_3944_ = _args[7];
lean_object* v_lhss_3945_ = _args[8];
lean_object* v_lhs_3946_ = _args[9];
lean_object* v___x_3947_ = _args[10];
lean_object* v_name_3948_ = _args[11];
lean_object* v_bi_3949_ = _args[12];
lean_object* v_type_3950_ = _args[13];
lean_object* v_kind_3951_ = _args[14];
lean_object* v___y_3952_ = _args[15];
lean_object* v___y_3953_ = _args[16];
lean_object* v___y_3954_ = _args[17];
lean_object* v___y_3955_ = _args[18];
lean_object* v___y_3956_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3957_; uint8_t v_bi_boxed_3958_; uint8_t v_kind_boxed_3959_; lean_object* v_res_3960_; 
v_subsingletonInstImplicitRhs_boxed_3957_ = lean_unbox(v_subsingletonInstImplicitRhs_3941_);
v_bi_boxed_3958_ = lean_unbox(v_bi_3949_);
v_kind_boxed_3959_ = lean_unbox(v_kind_3951_);
v_res_3960_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3937_, v_rhss_3938_, v_eqs_3939_, v_hyps_3940_, v_subsingletonInstImplicitRhs_boxed_3957_, v_f_3942_, v_info_3943_, v_kinds_3944_, v_lhss_3945_, v_lhs_3946_, v___x_3947_, v_name_3948_, v_bi_boxed_3958_, v_type_3950_, v_kind_boxed_3959_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* v_subsingletonInstImplicitRhs_3961_, lean_object* v_f_3962_, lean_object* v_info_3963_, lean_object* v_kinds_3964_, lean_object* v_lhss_3965_, lean_object* v_i_3966_, lean_object* v_rhss_3967_, lean_object* v_eqs_3968_, lean_object* v_hyps_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3975_; lean_object* v_res_3976_; 
v_subsingletonInstImplicitRhs_boxed_3975_ = lean_unbox(v_subsingletonInstImplicitRhs_3961_);
v_res_3976_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_boxed_3975_, v_f_3962_, v_info_3963_, v_kinds_3964_, v_lhss_3965_, v_i_3966_, v_rhss_3967_, v_eqs_3968_, v_hyps_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* v___x_3977_, uint8_t v_subsingletonInstImplicitRhs_3978_, lean_object* v_f_3979_, lean_object* v_info_3980_, lean_object* v_kinds_3981_, lean_object* v_lhss_3982_, lean_object* v_x_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; uint8_t v___x_3990_; 
v___x_3989_ = lean_array_get_size(v_lhss_3982_);
v___x_3990_ = lean_nat_dec_eq(v___x_3989_, v___x_3977_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
lean_dec_ref(v_lhss_3982_);
lean_dec_ref(v_kinds_3981_);
lean_dec_ref(v_info_3980_);
lean_dec_ref(v_f_3979_);
v___x_3991_ = lean_box(0);
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
return v___x_3992_;
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = lean_unsigned_to_nat(0u);
v___x_3994_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_3995_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3978_, v_f_3979_, v_info_3980_, v_kinds_3981_, v_lhss_3982_, v___x_3993_, v___x_3994_, v___x_3994_, v___x_3994_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4004_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3998_ = v___x_3995_;
v_isShared_3999_ = v_isSharedCheck_4004_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3995_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4004_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_a_3996_);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 0, v___x_4000_);
v___x_4002_ = v___x_3998_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3995_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3995_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* v___x_4013_, lean_object* v_subsingletonInstImplicitRhs_4014_, lean_object* v_f_4015_, lean_object* v_info_4016_, lean_object* v_kinds_4017_, lean_object* v_lhss_4018_, lean_object* v_x_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4025_; lean_object* v_res_4026_; 
v_subsingletonInstImplicitRhs_boxed_4025_ = lean_unbox(v_subsingletonInstImplicitRhs_4014_);
v_res_4026_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4013_, v_subsingletonInstImplicitRhs_boxed_4025_, v_f_4015_, v_info_4016_, v_kinds_4017_, v_lhss_4018_, v_x_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec_ref(v_x_4019_);
lean_dec(v___x_4013_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t v_subsingletonInstImplicitRhs_4027_, lean_object* v_f_4028_, lean_object* v_info_4029_, lean_object* v_kinds_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v___y_4037_; uint8_t v___y_4038_; lean_object* v_a_4043_; lean_object* v___x_4046_; 
lean_inc(v_a_4034_);
lean_inc_ref(v_a_4033_);
lean_inc(v_a_4032_);
lean_inc_ref(v_a_4031_);
lean_inc_ref(v_f_4028_);
v___x_4046_ = lean_infer_type(v_f_4028_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4061_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4061_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4061_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___f_4053_; lean_object* v___x_4055_; 
v___x_4051_ = lean_array_get_size(v_kinds_4030_);
v___x_4052_ = lean_box(v_subsingletonInstImplicitRhs_4027_);
v___f_4053_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4053_, 0, v___x_4051_);
lean_closure_set(v___f_4053_, 1, v___x_4052_);
lean_closure_set(v___f_4053_, 2, v_f_4028_);
lean_closure_set(v___f_4053_, 3, v_info_4029_);
lean_closure_set(v___f_4053_, 4, v_kinds_4030_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set_tag(v___x_4049_, 1);
lean_ctor_set(v___x_4049_, 0, v___x_4051_);
v___x_4055_ = v___x_4049_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4051_);
v___x_4055_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
uint8_t v___x_4056_; uint8_t v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = 1;
v___x_4057_ = 0;
v___x_4058_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_4047_, v___x_4055_, v___f_4053_, v___x_4056_, v___x_4057_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4058_) == 0)
{
return v___x_4058_;
}
else
{
lean_object* v_a_4059_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v_a_4043_ = v_a_4059_;
goto v___jp_4042_;
}
}
}
}
else
{
lean_object* v_a_4062_; 
lean_dec_ref(v_kinds_4030_);
lean_dec_ref(v_info_4029_);
lean_dec_ref(v_f_4028_);
v_a_4062_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4046_, 1);
v_a_4043_ = v_a_4062_;
goto v___jp_4042_;
}
v___jp_4036_:
{
if (v___y_4038_ == 0)
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
lean_dec_ref(v___y_4037_);
v___x_4039_ = lean_box(0);
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
return v___x_4040_;
}
else
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4041_, 0, v___y_4037_);
return v___x_4041_;
}
}
v___jp_4042_:
{
uint8_t v___x_4044_; 
v___x_4044_ = l_Lean_Exception_isInterrupt(v_a_4043_);
if (v___x_4044_ == 0)
{
uint8_t v___x_4045_; 
lean_inc_ref(v_a_4043_);
v___x_4045_ = l_Lean_Exception_isRuntime(v_a_4043_);
v___y_4037_ = v_a_4043_;
v___y_4038_ = v___x_4045_;
goto v___jp_4036_;
}
else
{
v___y_4037_ = v_a_4043_;
v___y_4038_ = v___x_4044_;
goto v___jp_4036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* v_subsingletonInstImplicitRhs_4063_, lean_object* v_f_4064_, lean_object* v_info_4065_, lean_object* v_kinds_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4072_; lean_object* v_res_4073_; 
v_subsingletonInstImplicitRhs_boxed_4072_ = lean_unbox(v_subsingletonInstImplicitRhs_4063_);
v_res_4073_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_boxed_4072_, v_f_4064_, v_info_4065_, v_kinds_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t v_sz_4074_, size_t v_i_4075_, lean_object* v_bs_4076_){
_start:
{
uint8_t v___x_4077_; 
v___x_4077_ = lean_usize_dec_lt(v_i_4075_, v_sz_4074_);
if (v___x_4077_ == 0)
{
return v_bs_4076_;
}
else
{
lean_object* v_v_4078_; lean_object* v___x_4079_; lean_object* v_bs_x27_4080_; uint8_t v___y_4082_; uint8_t v___x_4088_; 
v_v_4078_ = lean_array_uget(v_bs_4076_, v_i_4075_);
v___x_4079_ = lean_unsigned_to_nat(0u);
v_bs_x27_4080_ = lean_array_uset(v_bs_4076_, v_i_4075_, v___x_4079_);
v___x_4088_ = lean_unbox(v_v_4078_);
switch(v___x_4088_)
{
case 3:
{
uint8_t v___x_4089_; 
lean_dec(v_v_4078_);
v___x_4089_ = 0;
v___y_4082_ = v___x_4089_;
goto v___jp_4081_;
}
case 5:
{
uint8_t v___x_4090_; 
lean_dec(v_v_4078_);
v___x_4090_ = 0;
v___y_4082_ = v___x_4090_;
goto v___jp_4081_;
}
default: 
{
uint8_t v___x_4091_; 
v___x_4091_ = lean_unbox(v_v_4078_);
lean_dec(v_v_4078_);
v___y_4082_ = v___x_4091_;
goto v___jp_4081_;
}
}
v___jp_4081_:
{
size_t v___x_4083_; size_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4083_ = ((size_t)1ULL);
v___x_4084_ = lean_usize_add(v_i_4075_, v___x_4083_);
v___x_4085_ = lean_box(v___y_4082_);
v___x_4086_ = lean_array_uset(v_bs_x27_4080_, v_i_4075_, v___x_4085_);
v_i_4075_ = v___x_4084_;
v_bs_4076_ = v___x_4086_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* v_sz_4092_, lean_object* v_i_4093_, lean_object* v_bs_4094_){
_start:
{
size_t v_sz_boxed_4095_; size_t v_i_boxed_4096_; lean_object* v_res_4097_; 
v_sz_boxed_4095_ = lean_unbox_usize(v_sz_4092_);
lean_dec(v_sz_4092_);
v_i_boxed_4096_ = lean_unbox_usize(v_i_4093_);
lean_dec(v_i_4093_);
v_res_4097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_4095_, v_i_boxed_4096_, v_bs_4094_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* v_f_4098_, lean_object* v_info_4099_, lean_object* v_kinds_4100_, uint8_t v_subsingletonInstImplicitRhs_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v___x_4107_; 
lean_inc_ref(v_kinds_4100_);
lean_inc_ref(v_info_4099_);
lean_inc_ref(v_f_4098_);
v___x_4107_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4101_, v_f_4098_, v_info_4099_, v_kinds_4100_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_a_4108_);
if (lean_obj_tag(v_a_4108_) == 1)
{
lean_dec_ref_known(v_a_4108_, 1);
lean_dec_ref(v_kinds_4100_);
lean_dec_ref(v_info_4099_);
lean_dec_ref(v_f_4098_);
return v___x_4107_;
}
else
{
lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4121_; 
lean_dec(v_a_4108_);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; 
v_unused_4122_ = lean_ctor_get(v___x_4107_, 0);
lean_dec(v_unused_4122_);
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4121_;
goto v_resetjp_4109_;
}
else
{
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4121_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
uint8_t v___x_4112_; 
v___x_4112_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_4100_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
lean_dec_ref(v_kinds_4100_);
lean_dec_ref(v_info_4099_);
lean_dec_ref(v_f_4098_);
v___x_4113_ = lean_box(0);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v___x_4113_);
v___x_4115_ = v___x_4110_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
else
{
size_t v_sz_4117_; size_t v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
lean_del_object(v___x_4110_);
v_sz_4117_ = lean_array_size(v_kinds_4100_);
v___x_4118_ = ((size_t)0ULL);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4117_, v___x_4118_, v_kinds_4100_);
v___x_4120_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4101_, v_f_4098_, v_info_4099_, v___x_4119_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
return v___x_4120_;
}
}
}
}
else
{
lean_dec_ref(v_kinds_4100_);
lean_dec_ref(v_info_4099_);
lean_dec_ref(v_f_4098_);
return v___x_4107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* v_f_4123_, lean_object* v_info_4124_, lean_object* v_kinds_4125_, lean_object* v_subsingletonInstImplicitRhs_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4132_; lean_object* v_res_4133_; 
v_subsingletonInstImplicitRhs_boxed_4132_ = lean_unbox(v_subsingletonInstImplicitRhs_4126_);
v_res_4133_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4123_, v_info_4124_, v_kinds_4125_, v_subsingletonInstImplicitRhs_boxed_4132_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* v_f_4134_, uint8_t v_subsingletonInstImplicitRhs_4135_, lean_object* v_maxArgs_x3f_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
lean_object* v___x_4142_; lean_object* v_a_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4142_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_4134_, v_a_4138_);
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = l_Lean_Expr_cleanupAnnotations(v_a_4143_);
lean_inc_ref(v___x_4144_);
v___x_4145_ = l_Lean_Meta_getFunInfo(v___x_4144_, v_maxArgs_x3f_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4147_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4145_, 1);
lean_inc_ref(v___x_4144_);
v___x_4147_ = l_Lean_Meta_getCongrSimpKinds(v___x_4144_, v_a_4146_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4149_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v___x_4149_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4144_, v_a_4146_, v_a_4148_, v_subsingletonInstImplicitRhs_4135_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
return v___x_4149_;
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec(v_a_4146_);
lean_dec_ref(v___x_4144_);
v_a_4150_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4147_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4147_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec_ref(v___x_4144_);
v_a_4158_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4145_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4145_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* v_f_4166_, lean_object* v_subsingletonInstImplicitRhs_4167_, lean_object* v_maxArgs_x3f_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4174_; lean_object* v_res_4175_; 
v_subsingletonInstImplicitRhs_boxed_4174_ = lean_unbox(v_subsingletonInstImplicitRhs_4167_);
v_res_4175_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4166_, v_subsingletonInstImplicitRhs_boxed_4174_, v_maxArgs_x3f_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
return v_res_4175_;
}
}
static lean_object* _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4180_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4181_ = lean_string_utf8_byte_size(v___x_4180_);
return v___x_4181_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4182_){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; uint8_t v___x_4186_; 
v___x_4183_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4184_ = lean_string_utf8_byte_size(v_s_4182_);
v___x_4185_ = lean_obj_once(&l_Lean_Meta_isHCongrReservedNameSuffix___closed__0, &l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0);
v___x_4186_ = lean_nat_dec_le(v___x_4185_, v___x_4184_);
if (v___x_4186_ == 0)
{
lean_dec_ref(v_s_4182_);
return v___x_4186_;
}
else
{
lean_object* v___x_4187_; uint8_t v___x_4188_; 
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = lean_string_memcmp(v_s_4182_, v___x_4183_, v___x_4187_, v___x_4187_, v___x_4185_);
if (v___x_4188_ == 0)
{
lean_dec_ref(v_s_4182_);
return v___x_4188_;
}
else
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4189_ = lean_unsigned_to_nat(7u);
lean_inc_ref(v_s_4182_);
v___x_4190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4190_, 0, v_s_4182_);
lean_ctor_set(v___x_4190_, 1, v___x_4187_);
lean_ctor_set(v___x_4190_, 2, v___x_4184_);
v___x_4191_ = l_String_Slice_Pos_nextn(v___x_4190_, v___x_4187_, v___x_4189_);
lean_dec_ref_known(v___x_4190_, 3);
v___x_4192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4192_, 0, v_s_4182_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
lean_ctor_set(v___x_4192_, 2, v___x_4184_);
v___x_4193_ = l_String_Slice_isNat(v___x_4192_);
lean_dec_ref_known(v___x_4192_, 3);
return v___x_4193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* v_s_4194_){
_start:
{
uint8_t v_res_4195_; lean_object* v_r_4196_; 
v_res_4195_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4194_);
v_r_4196_ = lean_box(v_res_4195_);
return v_r_4196_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4246_ = lean_unsigned_to_nat(3482611248u);
v___x_4247_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4248_ = l_Lean_Name_num___override(v___x_4247_, v___x_4246_);
return v___x_4248_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4250_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4251_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4252_ = l_Lean_Name_str___override(v___x_4251_, v___x_4250_);
return v___x_4252_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4255_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4256_ = l_Lean_Name_str___override(v___x_4255_, v___x_4254_);
return v___x_4256_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4257_ = lean_unsigned_to_nat(2u);
v___x_4258_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4259_ = l_Lean_Name_num___override(v___x_4258_, v___x_4257_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4261_; uint8_t v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4261_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4262_ = 0;
v___x_4263_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4264_ = l_Lean_registerTraceClass(v___x_4261_, v___x_4262_, v___x_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object* v_a_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4267_, lean_object* v_as_4268_, size_t v_i_4269_, size_t v_stop_4270_, lean_object* v_b_4271_){
_start:
{
lean_object* v___y_4273_; uint8_t v___x_4277_; 
v___x_4277_ = lean_usize_dec_eq(v_i_4269_, v_stop_4270_);
if (v___x_4277_ == 0)
{
lean_object* v___x_4278_; lean_object* v_fst_4279_; uint8_t v___x_4280_; 
v___x_4278_ = lean_array_uget_borrowed(v_as_4268_, v_i_4269_);
v_fst_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_fst_4279_);
lean_inc_ref(v_env_4267_);
v___x_4280_ = l_Lean_Environment_contains(v_env_4267_, v_fst_4279_, v___x_4277_);
if (v___x_4280_ == 0)
{
v___y_4273_ = v_b_4271_;
goto v___jp_4272_;
}
else
{
lean_object* v___x_4281_; 
lean_inc(v___x_4278_);
v___x_4281_ = lean_array_push(v_b_4271_, v___x_4278_);
v___y_4273_ = v___x_4281_;
goto v___jp_4272_;
}
}
else
{
lean_dec_ref(v_env_4267_);
return v_b_4271_;
}
v___jp_4272_:
{
size_t v___x_4274_; size_t v___x_4275_; 
v___x_4274_ = ((size_t)1ULL);
v___x_4275_ = lean_usize_add(v_i_4269_, v___x_4274_);
v_i_4269_ = v___x_4275_;
v_b_4271_ = v___y_4273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4282_, lean_object* v_as_4283_, lean_object* v_i_4284_, lean_object* v_stop_4285_, lean_object* v_b_4286_){
_start:
{
size_t v_i_boxed_4287_; size_t v_stop_boxed_4288_; lean_object* v_res_4289_; 
v_i_boxed_4287_ = lean_unbox_usize(v_i_4284_);
lean_dec(v_i_4284_);
v_stop_boxed_4288_ = lean_unbox_usize(v_stop_4285_);
lean_dec(v_stop_4285_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4282_, v_as_4283_, v_i_boxed_4287_, v_stop_boxed_4288_, v_b_4286_);
lean_dec_ref(v_as_4283_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4290_, lean_object* v_x_4291_){
_start:
{
if (lean_obj_tag(v_x_4291_) == 0)
{
lean_object* v_k_4292_; lean_object* v_v_4293_; lean_object* v_l_4294_; lean_object* v_r_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v_k_4292_ = lean_ctor_get(v_x_4291_, 1);
v_v_4293_ = lean_ctor_get(v_x_4291_, 2);
v_l_4294_ = lean_ctor_get(v_x_4291_, 3);
v_r_4295_ = lean_ctor_get(v_x_4291_, 4);
v___x_4296_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4290_, v_l_4294_);
lean_inc(v_v_4293_);
lean_inc(v_k_4292_);
v___x_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4297_, 0, v_k_4292_);
lean_ctor_set(v___x_4297_, 1, v_v_4293_);
v___x_4298_ = lean_array_push(v___x_4296_, v___x_4297_);
v_init_4290_ = v___x_4298_;
v_x_4291_ = v_r_4295_;
goto _start;
}
else
{
return v_init_4290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4300_, lean_object* v_x_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4300_, v_x_4301_);
lean_dec(v_x_4301_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4309_, lean_object* v_s_4310_){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4311_ = lean_unsigned_to_nat(0u);
v___x_4312_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4313_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4312_, v_s_4310_);
v___x_4314_ = lean_array_get_size(v___x_4313_);
v___x_4315_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4316_ = lean_nat_dec_lt(v___x_4311_, v___x_4314_);
if (v___x_4316_ == 0)
{
lean_object* v___x_4317_; 
lean_dec_ref(v___x_4313_);
lean_dec_ref(v_env_4309_);
v___x_4317_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4317_;
}
else
{
uint8_t v___x_4318_; 
v___x_4318_ = lean_nat_dec_le(v___x_4314_, v___x_4314_);
if (v___x_4318_ == 0)
{
if (v___x_4316_ == 0)
{
lean_object* v___x_4319_; 
lean_dec_ref(v___x_4313_);
lean_dec_ref(v_env_4309_);
v___x_4319_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4319_;
}
else
{
size_t v___x_4320_; size_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4320_ = ((size_t)0ULL);
v___x_4321_ = lean_usize_of_nat(v___x_4314_);
v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4309_, v___x_4313_, v___x_4320_, v___x_4321_, v___x_4315_);
lean_dec_ref(v___x_4313_);
lean_inc_ref_n(v___x_4322_, 2);
v___x_4323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
lean_ctor_set(v___x_4323_, 2, v___x_4322_);
return v___x_4323_;
}
}
else
{
size_t v___x_4324_; size_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4324_ = ((size_t)0ULL);
v___x_4325_ = lean_usize_of_nat(v___x_4314_);
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4309_, v___x_4313_, v___x_4324_, v___x_4325_, v___x_4315_);
lean_dec_ref(v___x_4313_);
lean_inc_ref_n(v___x_4326_, 2);
v___x_4327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
lean_ctor_set(v___x_4327_, 2, v___x_4326_);
return v___x_4327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4328_, lean_object* v_s_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4328_, v_s_4329_);
lean_dec(v_s_4329_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___f_4340_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4341_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4342_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4343_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4341_, v___x_4342_, v___f_4340_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4346_, lean_object* v_t_4347_){
_start:
{
lean_object* v___x_4348_; 
v___x_4348_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4346_, v_t_4347_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4349_, lean_object* v_t_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4349_, v_t_4350_);
lean_dec(v_t_4350_);
return v_res_4351_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object* v_env_4352_, lean_object* v_n_4353_){
_start:
{
if (lean_obj_tag(v_n_4353_) == 1)
{
lean_object* v_pre_4354_; lean_object* v_str_4355_; uint8_t v___y_4357_; uint8_t v___x_4359_; 
v_pre_4354_ = lean_ctor_get(v_n_4353_, 0);
lean_inc(v_pre_4354_);
v_str_4355_ = lean_ctor_get(v_n_4353_, 1);
lean_inc_ref_n(v_str_4355_, 2);
lean_dec_ref_known(v_n_4353_, 2);
v___x_4359_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4355_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; uint8_t v___x_4361_; 
v___x_4360_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4361_ = lean_string_dec_eq(v_str_4355_, v___x_4360_);
lean_dec_ref(v_str_4355_);
v___y_4357_ = v___x_4361_;
goto v___jp_4356_;
}
else
{
lean_dec_ref(v_str_4355_);
v___y_4357_ = v___x_4359_;
goto v___jp_4356_;
}
v___jp_4356_:
{
if (v___y_4357_ == 0)
{
lean_dec(v_pre_4354_);
lean_dec_ref(v_env_4352_);
return v___y_4357_;
}
else
{
uint8_t v___x_4358_; 
v___x_4358_ = l_Lean_Environment_contains(v_env_4352_, v_pre_4354_, v___y_4357_);
return v___x_4358_;
}
}
}
else
{
uint8_t v___x_4362_; 
lean_dec(v_n_4353_);
lean_dec_ref(v_env_4352_);
v___x_4362_ = 0;
return v___x_4362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_env_4363_, lean_object* v_n_4364_){
_start:
{
uint8_t v_res_4365_; lean_object* v_r_4366_; 
v_res_4365_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4363_, v_n_4364_);
v_r_4366_ = lean_box(v_res_4365_);
return v_r_4366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4369_; lean_object* v___x_4370_; 
v___f_4369_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_));
v___x_4370_ = l_Lean_registerReservedNamePredicate(v___f_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object* v_thm_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v___x_4376_; lean_object* v_env_4377_; lean_object* v_toConstantVal_4378_; lean_object* v_value_4379_; lean_object* v_all_4380_; uint8_t v___y_4382_; lean_object* v_type_4390_; uint8_t v___x_4391_; 
v___x_4376_ = lean_st_ref_get(v___y_4374_);
v_env_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc_ref_n(v_env_4377_, 2);
lean_dec(v___x_4376_);
v_toConstantVal_4378_ = lean_ctor_get(v_thm_4373_, 0);
v_value_4379_ = lean_ctor_get(v_thm_4373_, 1);
v_all_4380_ = lean_ctor_get(v_thm_4373_, 2);
v_type_4390_ = lean_ctor_get(v_toConstantVal_4378_, 2);
v___x_4391_ = l_Lean_Environment_hasUnsafe(v_env_4377_, v_type_4390_);
if (v___x_4391_ == 0)
{
uint8_t v___x_4392_; 
v___x_4392_ = l_Lean_Environment_hasUnsafe(v_env_4377_, v_value_4379_);
v___y_4382_ = v___x_4392_;
goto v___jp_4381_;
}
else
{
lean_dec_ref(v_env_4377_);
v___y_4382_ = v___x_4391_;
goto v___jp_4381_;
}
v___jp_4381_:
{
if (v___y_4382_ == 0)
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4383_, 0, v_thm_4373_);
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
return v___x_4384_;
}
else
{
lean_object* v___x_4385_; uint8_t v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
lean_inc(v_all_4380_);
lean_inc_ref(v_value_4379_);
lean_inc_ref(v_toConstantVal_4378_);
lean_dec_ref(v_thm_4373_);
v___x_4385_ = lean_box(0);
v___x_4386_ = 0;
v___x_4387_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4387_, 0, v_toConstantVal_4378_);
lean_ctor_set(v___x_4387_, 1, v_value_4379_);
lean_ctor_set(v___x_4387_, 2, v___x_4385_);
lean_ctor_set(v___x_4387_, 3, v_all_4380_);
lean_ctor_set_uint8(v___x_4387_, sizeof(void*)*4, v___x_4386_);
v___x_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
v___x_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
return v___x_4389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_thm_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4393_, v___y_4394_);
lean_dec(v___y_4394_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_thm_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4397_, v___y_4401_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object* v_thm_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
return v_res_4410_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_4411_; double v___x_4412_; 
v___x_4411_ = lean_unsigned_to_nat(0u);
v___x_4412_ = lean_float_of_nat(v___x_4411_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_cls_4416_, lean_object* v_msg_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v_ref_4423_; lean_object* v___x_4424_; lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4469_; 
v_ref_4423_ = lean_ctor_get(v___y_4420_, 2);
v___x_4424_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4469_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4469_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4429_; lean_object* v_traceState_4430_; lean_object* v_env_4431_; lean_object* v_nextMacroScope_4432_; lean_object* v_ngen_4433_; lean_object* v_auxDeclNGen_4434_; lean_object* v_cache_4435_; lean_object* v_messages_4436_; lean_object* v_infoState_4437_; lean_object* v_snapshotTasks_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4468_; 
v___x_4429_ = lean_st_ref_take(v___y_4421_);
v_traceState_4430_ = lean_ctor_get(v___x_4429_, 4);
v_env_4431_ = lean_ctor_get(v___x_4429_, 0);
v_nextMacroScope_4432_ = lean_ctor_get(v___x_4429_, 1);
v_ngen_4433_ = lean_ctor_get(v___x_4429_, 2);
v_auxDeclNGen_4434_ = lean_ctor_get(v___x_4429_, 3);
v_cache_4435_ = lean_ctor_get(v___x_4429_, 5);
v_messages_4436_ = lean_ctor_get(v___x_4429_, 6);
v_infoState_4437_ = lean_ctor_get(v___x_4429_, 7);
v_snapshotTasks_4438_ = lean_ctor_get(v___x_4429_, 8);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4440_ = v___x_4429_;
v_isShared_4441_ = v_isSharedCheck_4468_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_snapshotTasks_4438_);
lean_inc(v_infoState_4437_);
lean_inc(v_messages_4436_);
lean_inc(v_cache_4435_);
lean_inc(v_traceState_4430_);
lean_inc(v_auxDeclNGen_4434_);
lean_inc(v_ngen_4433_);
lean_inc(v_nextMacroScope_4432_);
lean_inc(v_env_4431_);
lean_dec(v___x_4429_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4468_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
uint64_t v_tid_4442_; lean_object* v_traces_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4467_; 
v_tid_4442_ = lean_ctor_get_uint64(v_traceState_4430_, sizeof(void*)*1);
v_traces_4443_ = lean_ctor_get(v_traceState_4430_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v_traceState_4430_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4445_ = v_traceState_4430_;
v_isShared_4446_ = v_isSharedCheck_4467_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_traces_4443_);
lean_dec(v_traceState_4430_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4467_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4447_; double v___x_4448_; uint8_t v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4457_; 
v___x_4447_ = lean_box(0);
v___x_4448_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0);
v___x_4449_ = 0;
v___x_4450_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1));
v___x_4451_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4451_, 0, v_cls_4416_);
lean_ctor_set(v___x_4451_, 1, v___x_4447_);
lean_ctor_set(v___x_4451_, 2, v___x_4450_);
lean_ctor_set_float(v___x_4451_, sizeof(void*)*3, v___x_4448_);
lean_ctor_set_float(v___x_4451_, sizeof(void*)*3 + 8, v___x_4448_);
lean_ctor_set_uint8(v___x_4451_, sizeof(void*)*3 + 16, v___x_4449_);
v___x_4452_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2));
v___x_4453_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4451_);
lean_ctor_set(v___x_4453_, 1, v_a_4425_);
lean_ctor_set(v___x_4453_, 2, v___x_4452_);
lean_inc(v_ref_4423_);
v___x_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4454_, 0, v_ref_4423_);
lean_ctor_set(v___x_4454_, 1, v___x_4453_);
v___x_4455_ = l_Lean_PersistentArray_push___redArg(v_traces_4443_, v___x_4454_);
if (v_isShared_4446_ == 0)
{
lean_ctor_set(v___x_4445_, 0, v___x_4455_);
v___x_4457_ = v___x_4445_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4455_);
lean_ctor_set_uint64(v_reuseFailAlloc_4466_, sizeof(void*)*1, v_tid_4442_);
v___x_4457_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4459_; 
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 4, v___x_4457_);
v___x_4459_ = v___x_4440_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_env_4431_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v_nextMacroScope_4432_);
lean_ctor_set(v_reuseFailAlloc_4465_, 2, v_ngen_4433_);
lean_ctor_set(v_reuseFailAlloc_4465_, 3, v_auxDeclNGen_4434_);
lean_ctor_set(v_reuseFailAlloc_4465_, 4, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4465_, 5, v_cache_4435_);
lean_ctor_set(v_reuseFailAlloc_4465_, 6, v_messages_4436_);
lean_ctor_set(v_reuseFailAlloc_4465_, 7, v_infoState_4437_);
lean_ctor_set(v_reuseFailAlloc_4465_, 8, v_snapshotTasks_4438_);
v___x_4459_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4463_; 
v___x_4460_ = lean_st_ref_put(v___y_4421_, v___x_4459_);
v___x_4461_ = lean_box(0);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4461_);
v___x_4463_ = v___x_4427_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4461_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_4470_, lean_object* v_msg_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4470_, v_msg_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
return v_res_4477_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4478_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4481_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
return v___x_4482_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4487_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4488_ = l_Lean_Name_append(v___x_4487_, v___x_4486_);
return v___x_4488_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4491_ = l_Lean_stringToMessageData(v___x_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4492_, uint8_t v___x_4493_, lean_object* v_name_4494_, lean_object* v_argKinds_4495_, lean_object* v___x_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___x_4542_; lean_object* v_a_4543_; lean_object* v___x_4544_; 
v___x_4542_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_4492_, v___y_4500_);
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_a_4543_);
lean_dec_ref(v___x_4542_);
v___x_4544_ = l_Lean_addDecl(v_a_4543_, v___x_4493_, v___y_4499_, v___y_4500_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_toCold_4545_; lean_object* v_options_4546_; uint8_t v_hasTrace_4547_; 
lean_dec_ref_known(v___x_4544_, 1);
v_toCold_4545_ = lean_ctor_get(v___y_4499_, 0);
v_options_4546_ = lean_ctor_get(v_toCold_4545_, 2);
v_hasTrace_4547_ = lean_ctor_get_uint8(v_options_4546_, sizeof(void*)*1);
if (v_hasTrace_4547_ == 0)
{
v___y_4503_ = v___y_4498_;
v___y_4504_ = v___y_4500_;
goto v___jp_4502_;
}
else
{
lean_object* v_inheritedTraceOptions_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; 
v_inheritedTraceOptions_4548_ = lean_ctor_get(v_toCold_4545_, 11);
v___x_4549_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4550_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4551_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4548_, v_options_4546_, v___x_4550_);
if (v___x_4551_ == 0)
{
v___y_4503_ = v___y_4498_;
v___y_4504_ = v___y_4500_;
goto v___jp_4502_;
}
else
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4552_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4494_);
v___x_4553_ = l_Lean_MessageData_ofName(v_name_4494_);
v___x_4554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
v___x_4557_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_4549_, v___x_4556_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_dec_ref_known(v___x_4557_, 1);
v___y_4503_ = v___y_4498_;
v___y_4504_ = v___y_4500_;
goto v___jp_4502_;
}
else
{
lean_dec_ref(v___x_4496_);
lean_dec_ref(v_argKinds_4495_);
lean_dec(v_name_4494_);
return v___x_4557_;
}
}
}
}
else
{
lean_dec_ref(v___x_4496_);
lean_dec_ref(v_argKinds_4495_);
lean_dec(v_name_4494_);
return v___x_4544_;
}
v___jp_4502_:
{
lean_object* v___x_4505_; lean_object* v_env_4506_; lean_object* v_nextMacroScope_4507_; lean_object* v_ngen_4508_; lean_object* v_auxDeclNGen_4509_; lean_object* v_traceState_4510_; lean_object* v_messages_4511_; lean_object* v_infoState_4512_; lean_object* v_snapshotTasks_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4540_; 
v___x_4505_ = lean_st_ref_take(v___y_4504_);
v_env_4506_ = lean_ctor_get(v___x_4505_, 0);
v_nextMacroScope_4507_ = lean_ctor_get(v___x_4505_, 1);
v_ngen_4508_ = lean_ctor_get(v___x_4505_, 2);
v_auxDeclNGen_4509_ = lean_ctor_get(v___x_4505_, 3);
v_traceState_4510_ = lean_ctor_get(v___x_4505_, 4);
v_messages_4511_ = lean_ctor_get(v___x_4505_, 6);
v_infoState_4512_ = lean_ctor_get(v___x_4505_, 7);
v_snapshotTasks_4513_ = lean_ctor_get(v___x_4505_, 8);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4540_ == 0)
{
lean_object* v_unused_4541_; 
v_unused_4541_ = lean_ctor_get(v___x_4505_, 5);
lean_dec(v_unused_4541_);
v___x_4515_ = v___x_4505_;
v_isShared_4516_ = v_isSharedCheck_4540_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_snapshotTasks_4513_);
lean_inc(v_infoState_4512_);
lean_inc(v_messages_4511_);
lean_inc(v_traceState_4510_);
lean_inc(v_auxDeclNGen_4509_);
lean_inc(v_ngen_4508_);
lean_inc(v_nextMacroScope_4507_);
lean_inc(v_env_4506_);
lean_dec(v___x_4505_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4540_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4521_; 
v___x_4517_ = l_Lean_Meta_congrKindsExt;
v___x_4518_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4517_, v_env_4506_, v_name_4494_, v_argKinds_4495_);
v___x_4519_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 5, v___x_4519_);
lean_ctor_set(v___x_4515_, 0, v___x_4518_);
v___x_4521_ = v___x_4515_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4518_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_nextMacroScope_4507_);
lean_ctor_set(v_reuseFailAlloc_4539_, 2, v_ngen_4508_);
lean_ctor_set(v_reuseFailAlloc_4539_, 3, v_auxDeclNGen_4509_);
lean_ctor_set(v_reuseFailAlloc_4539_, 4, v_traceState_4510_);
lean_ctor_set(v_reuseFailAlloc_4539_, 5, v___x_4519_);
lean_ctor_set(v_reuseFailAlloc_4539_, 6, v_messages_4511_);
lean_ctor_set(v_reuseFailAlloc_4539_, 7, v_infoState_4512_);
lean_ctor_set(v_reuseFailAlloc_4539_, 8, v_snapshotTasks_4513_);
v___x_4521_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v_mctx_4524_; lean_object* v_zetaDeltaFVarIds_4525_; lean_object* v_postponed_4526_; lean_object* v_diag_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4537_; 
v___x_4522_ = lean_st_ref_put(v___y_4504_, v___x_4521_);
v___x_4523_ = lean_st_ref_take(v___y_4503_);
v_mctx_4524_ = lean_ctor_get(v___x_4523_, 0);
v_zetaDeltaFVarIds_4525_ = lean_ctor_get(v___x_4523_, 2);
v_postponed_4526_ = lean_ctor_get(v___x_4523_, 3);
v_diag_4527_ = lean_ctor_get(v___x_4523_, 4);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4537_ == 0)
{
lean_object* v_unused_4538_; 
v_unused_4538_ = lean_ctor_get(v___x_4523_, 1);
lean_dec(v_unused_4538_);
v___x_4529_ = v___x_4523_;
v_isShared_4530_ = v_isSharedCheck_4537_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_diag_4527_);
lean_inc(v_postponed_4526_);
lean_inc(v_zetaDeltaFVarIds_4525_);
lean_inc(v_mctx_4524_);
lean_dec(v___x_4523_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4537_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 1, v___x_4496_);
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_mctx_4524_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v___x_4496_);
lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_zetaDeltaFVarIds_4525_);
lean_ctor_set(v_reuseFailAlloc_4536_, 3, v_postponed_4526_);
lean_ctor_set(v_reuseFailAlloc_4536_, 4, v_diag_4527_);
v___x_4532_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4533_ = lean_st_ref_put(v___y_4503_, v___x_4532_);
v___x_4534_ = lean_box(0);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
return v___x_4535_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4558_, lean_object* v___x_4559_, lean_object* v_name_4560_, lean_object* v_argKinds_4561_, lean_object* v___x_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
uint8_t v___x_11865__boxed_4568_; lean_object* v_res_4569_; 
v___x_11865__boxed_4568_ = lean_unbox(v___x_4559_);
v_res_4569_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4558_, v___x_11865__boxed_4568_, v_name_4560_, v_argKinds_4561_, v___x_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
if (lean_obj_tag(v_a_4570_) == 0)
{
lean_object* v___x_4572_; 
v___x_4572_ = l_List_reverse___redArg(v_a_4571_);
return v___x_4572_;
}
else
{
lean_object* v_head_4573_; lean_object* v_tail_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4583_; 
v_head_4573_ = lean_ctor_get(v_a_4570_, 0);
v_tail_4574_ = lean_ctor_get(v_a_4570_, 1);
v_isSharedCheck_4583_ = !lean_is_exclusive(v_a_4570_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4576_ = v_a_4570_;
v_isShared_4577_ = v_isSharedCheck_4583_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_tail_4574_);
lean_inc(v_head_4573_);
lean_dec(v_a_4570_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4583_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4578_ = l_Lean_mkLevelParam(v_head_4573_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 1, v_a_4571_);
lean_ctor_set(v___x_4576_, 0, v___x_4578_);
v___x_4580_ = v___x_4576_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4582_, 1, v_a_4571_);
v___x_4580_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
v_a_4570_ = v_tail_4574_;
v_a_4571_ = v___x_4580_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4584_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
return v___x_4586_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4587_ = lean_box(1);
v___x_4588_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4589_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
lean_ctor_set(v___x_4590_, 1, v___x_4588_);
lean_ctor_set(v___x_4590_, 2, v___x_4587_);
return v___x_4590_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4593_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4594_ = lean_unsigned_to_nat(0u);
v___x_4595_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
lean_ctor_set(v___x_4595_, 2, v___x_4594_);
lean_ctor_set(v___x_4595_, 3, v___x_4594_);
lean_ctor_set(v___x_4595_, 4, v___x_4593_);
lean_ctor_set(v___x_4595_, 5, v___x_4593_);
lean_ctor_set(v___x_4595_, 6, v___x_4593_);
lean_ctor_set(v___x_4595_, 7, v___x_4593_);
lean_ctor_set(v___x_4595_, 8, v___x_4593_);
lean_ctor_set(v___x_4595_, 9, v___x_4593_);
lean_ctor_set(v___x_4595_, 10, v___x_4593_);
return v___x_4595_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4597_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
lean_ctor_set(v___x_4597_, 1, v___x_4596_);
lean_ctor_set(v___x_4597_, 2, v___x_4596_);
lean_ctor_set(v___x_4597_, 3, v___x_4596_);
lean_ctor_set(v___x_4597_, 4, v___x_4596_);
lean_ctor_set(v___x_4597_, 5, v___x_4596_);
return v___x_4597_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
lean_ctor_set(v___x_4599_, 2, v___x_4598_);
lean_ctor_set(v___x_4599_, 3, v___x_4598_);
lean_ctor_set(v___x_4599_, 4, v___x_4598_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4600_, lean_object* v_name_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
if (lean_obj_tag(v_name_4601_) == 1)
{
lean_object* v_pre_4605_; lean_object* v_str_4606_; lean_object* v___x_4607_; lean_object* v_env_4608_; uint8_t v___x_4609_; uint8_t v___x_4610_; 
v_pre_4605_ = lean_ctor_get(v_name_4601_, 0);
lean_inc_n(v_pre_4605_, 2);
v_str_4606_ = lean_ctor_get(v_name_4601_, 1);
v___x_4607_ = lean_st_ref_get(v___y_4603_);
v_env_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc_ref(v_env_4608_);
lean_dec(v___x_4607_);
v___x_4609_ = 1;
v___x_4610_ = l_Lean_Environment_contains(v_env_4608_, v_pre_4605_, v___x_4609_);
if (v___x_4610_ == 0)
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
lean_dec_ref_known(v_name_4601_, 2);
lean_dec(v_pre_4605_);
lean_dec(v___x_4600_);
v___x_4611_ = lean_box(v___x_4610_);
v___x_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
return v___x_4612_;
}
else
{
uint8_t v___x_4613_; lean_object* v___y_4615_; uint8_t v___y_4616_; lean_object* v_a_4621_; 
lean_inc_ref(v_str_4606_);
v___x_4613_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4606_);
if (v___x_4613_ == 0)
{
lean_object* v___x_4624_; uint8_t v___x_4625_; 
v___x_4624_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4625_ = lean_string_dec_eq(v_str_4606_, v___x_4624_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
lean_dec_ref_known(v_name_4601_, 2);
lean_dec(v_pre_4605_);
lean_dec(v___x_4600_);
v___x_4626_ = lean_box(v___x_4625_);
v___x_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4626_);
return v___x_4627_;
}
else
{
uint8_t v___x_4628_; uint8_t v___x_4629_; uint8_t v___x_4630_; lean_object* v___x_4631_; uint64_t v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v_a_4646_; lean_object* v___x_4650_; 
v___x_4628_ = 1;
v___x_4629_ = 0;
v___x_4630_ = 2;
v___x_4631_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4631_, 0, v___x_4613_);
lean_ctor_set_uint8(v___x_4631_, 1, v___x_4613_);
lean_ctor_set_uint8(v___x_4631_, 2, v___x_4613_);
lean_ctor_set_uint8(v___x_4631_, 3, v___x_4613_);
lean_ctor_set_uint8(v___x_4631_, 4, v___x_4613_);
lean_ctor_set_uint8(v___x_4631_, 5, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 6, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 7, v___x_4613_);
lean_ctor_set_uint8(v___x_4631_, 8, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 9, v___x_4628_);
lean_ctor_set_uint8(v___x_4631_, 10, v___x_4629_);
lean_ctor_set_uint8(v___x_4631_, 11, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 12, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 13, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 14, v___x_4630_);
lean_ctor_set_uint8(v___x_4631_, 15, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 16, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 17, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 18, v___x_4625_);
lean_ctor_set_uint8(v___x_4631_, 19, v___x_4613_);
v___x_4632_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4631_);
v___x_4633_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4633_, 0, v___x_4631_);
lean_ctor_set_uint64(v___x_4633_, sizeof(void*)*1, v___x_4632_);
v___x_4634_ = lean_unsigned_to_nat(0u);
v___x_4635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4636_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4637_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4638_ = lean_box(0);
lean_inc(v___x_4600_);
v___x_4639_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4639_, 0, v___x_4633_);
lean_ctor_set(v___x_4639_, 1, v___x_4600_);
lean_ctor_set(v___x_4639_, 2, v___x_4636_);
lean_ctor_set(v___x_4639_, 3, v___x_4637_);
lean_ctor_set(v___x_4639_, 4, v___x_4638_);
lean_ctor_set(v___x_4639_, 5, v___x_4634_);
lean_ctor_set(v___x_4639_, 6, v___x_4638_);
lean_ctor_set_uint8(v___x_4639_, sizeof(void*)*7, v___x_4613_);
lean_ctor_set_uint8(v___x_4639_, sizeof(void*)*7 + 1, v___x_4613_);
lean_ctor_set_uint8(v___x_4639_, sizeof(void*)*7 + 2, v___x_4613_);
lean_ctor_set_uint8(v___x_4639_, sizeof(void*)*7 + 3, v___x_4609_);
v___x_4640_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4641_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4642_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4640_);
lean_ctor_set(v___x_4643_, 1, v___x_4641_);
lean_ctor_set(v___x_4643_, 2, v___x_4600_);
lean_ctor_set(v___x_4643_, 3, v___x_4635_);
lean_ctor_set(v___x_4643_, 4, v___x_4642_);
v___x_4644_ = lean_st_mk_ref(v___x_4643_);
lean_inc(v_pre_4605_);
v___x_4650_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4605_, v___x_4639_, v___x_4644_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v___x_4650_, 1);
v___x_4652_ = l_Lean_ConstantInfo_levelParams(v_a_4651_);
lean_dec(v_a_4651_);
v___x_4653_ = lean_box(0);
lean_inc(v___x_4652_);
v___x_4654_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4652_, v___x_4653_);
lean_inc(v_pre_4605_);
v___x_4655_ = l_Lean_mkConst(v_pre_4605_, v___x_4654_);
lean_inc_ref(v___x_4655_);
v___x_4656_ = l_Lean_Meta_getFunInfo(v___x_4655_, v___x_4638_, v___x_4639_, v___x_4644_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4658_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref_known(v___x_4656_, 1);
lean_inc_ref(v___x_4655_);
v___x_4658_ = l_Lean_Meta_getCongrSimpKinds(v___x_4655_, v_a_4657_, v___x_4639_, v___x_4644_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4660_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4659_);
lean_dec_ref_known(v___x_4658_, 1);
v___x_4660_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4655_, v_a_4657_, v_a_4659_, v___x_4609_, v___x_4639_, v___x_4644_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
if (lean_obj_tag(v_a_4661_) == 1)
{
lean_object* v_val_4662_; lean_object* v_type_4663_; lean_object* v_proof_4664_; lean_object* v_argKinds_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4678_; 
v_val_4662_ = lean_ctor_get(v_a_4661_, 0);
lean_inc(v_val_4662_);
lean_dec_ref_known(v_a_4661_, 1);
v_type_4663_ = lean_ctor_get(v_val_4662_, 0);
v_proof_4664_ = lean_ctor_get(v_val_4662_, 1);
v_argKinds_4665_ = lean_ctor_get(v_val_4662_, 2);
v_isSharedCheck_4678_ = !lean_is_exclusive(v_val_4662_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4667_ = v_val_4662_;
v_isShared_4668_ = v_isSharedCheck_4678_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_argKinds_4665_);
lean_inc(v_proof_4664_);
lean_inc(v_type_4663_);
lean_dec(v_val_4662_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4678_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
lean_inc_ref(v_name_4601_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 2, v_type_4663_);
lean_ctor_set(v___x_4667_, 1, v___x_4652_);
lean_ctor_set(v___x_4667_, 0, v_name_4601_);
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_name_4601_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4677_, 2, v_type_4663_);
v___x_4670_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___f_4674_; lean_object* v___x_4675_; 
lean_inc_ref_n(v_name_4601_, 2);
v___x_4671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4671_, 0, v_name_4601_);
lean_ctor_set(v___x_4671_, 1, v___x_4653_);
v___x_4672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4670_);
lean_ctor_set(v___x_4672_, 1, v_proof_4664_);
lean_ctor_set(v___x_4672_, 2, v___x_4671_);
v___x_4673_ = lean_box(v___x_4613_);
v___f_4674_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4674_, 0, v___x_4672_);
lean_closure_set(v___f_4674_, 1, v___x_4673_);
lean_closure_set(v___f_4674_, 2, v_name_4601_);
lean_closure_set(v___f_4674_, 3, v_argKinds_4665_);
lean_closure_set(v___f_4674_, 4, v___x_4641_);
v___x_4675_ = l_Lean_Meta_realizeConst(v_pre_4605_, v_name_4601_, v___f_4674_, v___x_4639_, v___x_4644_, v___y_4602_, v___y_4603_);
lean_dec_ref_known(v___x_4639_, 7);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_dec_ref_known(v___x_4675_, 1);
v_a_4646_ = v___x_4609_;
goto v___jp_4645_;
}
else
{
lean_object* v_a_4676_; 
lean_dec(v___x_4644_);
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v___x_4675_, 1);
v_a_4621_ = v_a_4676_;
goto v___jp_4620_;
}
}
}
}
else
{
lean_dec(v_a_4661_);
lean_dec(v___x_4652_);
lean_dec_ref_known(v___x_4639_, 7);
lean_dec_ref_known(v_name_4601_, 2);
lean_dec(v_pre_4605_);
v_a_4646_ = v___x_4613_;
goto v___jp_4645_;
}
}
else
{
lean_object* v_a_4679_; 
lean_dec(v___x_4652_);
lean_dec(v___x_4644_);
lean_dec_ref_known(v___x_4639_, 7);
lean_dec_ref_known(v_name_4601_, 2);
lean_dec(v_pre_4605_);
v_a_4679_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4660_, 1);
v_a_4621_ = v_a_4679_;
goto v___jp_4620_;
}
}
else
{
lean_object* v_a_4680_; 
lean_dec(v_a_4657_);
lean_dec_ref(v___x_4655_);
lean_dec(v___x_4652_);
lean_dec(v___x_4644_);
lean_dec_ref_known(v___x_4639_, 7);
lean_dec_ref_known(v_name_4601_, 2);
lean_dec(v_pre_4605_);
v_a_4680_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4680_);
lean_dec_ref_known(v___x_4658_, 1);
v_a_4621_ = v_a_4680_;
goto v___jp_4620_;
}
}
else
{
lean_object* v_a_4681_; 
lean_dec_ref(v___x_4655_);
lean_dec(v___x_4652_);
lean_dec(v___x_4644_);
lean_dec_ref_known(v___x_4639_, 7);
lean_dec_ref_known(v_name_4601_, 2);
lean_dec(v_pre_4605_);
v_a_4681_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4681_);
lean_dec_ref_known(v___x_4656_, 1);
v_a_4621_ = v_a_4681_;
goto v___jp_4620_;
}
}
else
{
lean_object* v_a_4682_; 
lean_dec(v___x_4644_);
lean_dec_ref_known(v___x_4639_, 7);
lean_dec_ref_known(v_name_4601_, 2);
lean_dec(v_pre_4605_);
v_a_4682_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4650_, 1);
v_a_4621_ = v_a_4682_;
goto v___jp_4620_;
}
v___jp_4645_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = lean_st_ref_get(v___x_4644_);
lean_dec(v___x_4644_);
lean_dec(v___x_4647_);
v___x_4648_ = lean_box(v_a_4646_);
v___x_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
return v___x_4649_;
}
}
}
else
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; lean_object* v___y_4690_; uint8_t v___y_4691_; lean_object* v_a_4696_; uint8_t v___x_4699_; uint8_t v___x_4700_; uint8_t v___x_4701_; lean_object* v___x_4702_; uint64_t v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4683_ = lean_unsigned_to_nat(7u);
v___x_4684_ = lean_unsigned_to_nat(0u);
v___x_4685_ = lean_string_utf8_byte_size(v_str_4606_);
lean_inc_ref(v_str_4606_);
v___x_4686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4686_, 0, v_str_4606_);
lean_ctor_set(v___x_4686_, 1, v___x_4684_);
lean_ctor_set(v___x_4686_, 2, v___x_4685_);
v___x_4687_ = l_String_Slice_Pos_nextn(v___x_4686_, v___x_4684_, v___x_4683_);
lean_dec_ref_known(v___x_4686_, 3);
v___x_4688_ = 0;
v___x_4699_ = 1;
v___x_4700_ = 0;
v___x_4701_ = 2;
v___x_4702_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4702_, 0, v___x_4688_);
lean_ctor_set_uint8(v___x_4702_, 1, v___x_4688_);
lean_ctor_set_uint8(v___x_4702_, 2, v___x_4688_);
lean_ctor_set_uint8(v___x_4702_, 3, v___x_4688_);
lean_ctor_set_uint8(v___x_4702_, 4, v___x_4688_);
lean_ctor_set_uint8(v___x_4702_, 5, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 6, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 7, v___x_4688_);
lean_ctor_set_uint8(v___x_4702_, 8, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 9, v___x_4699_);
lean_ctor_set_uint8(v___x_4702_, 10, v___x_4700_);
lean_ctor_set_uint8(v___x_4702_, 11, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 12, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 13, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 14, v___x_4701_);
lean_ctor_set_uint8(v___x_4702_, 15, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 16, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 17, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 18, v___x_4613_);
lean_ctor_set_uint8(v___x_4702_, 19, v___x_4688_);
v___x_4703_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4702_);
v___x_4704_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4704_, 0, v___x_4702_);
lean_ctor_set_uint64(v___x_4704_, sizeof(void*)*1, v___x_4703_);
v___x_4705_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4706_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4707_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4708_ = lean_box(0);
lean_inc(v___x_4600_);
v___x_4709_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4709_, 0, v___x_4704_);
lean_ctor_set(v___x_4709_, 1, v___x_4600_);
lean_ctor_set(v___x_4709_, 2, v___x_4706_);
lean_ctor_set(v___x_4709_, 3, v___x_4707_);
lean_ctor_set(v___x_4709_, 4, v___x_4708_);
lean_ctor_set(v___x_4709_, 5, v___x_4684_);
lean_ctor_set(v___x_4709_, 6, v___x_4708_);
lean_ctor_set_uint8(v___x_4709_, sizeof(void*)*7, v___x_4688_);
lean_ctor_set_uint8(v___x_4709_, sizeof(void*)*7 + 1, v___x_4688_);
lean_ctor_set_uint8(v___x_4709_, sizeof(void*)*7 + 2, v___x_4688_);
lean_ctor_set_uint8(v___x_4709_, sizeof(void*)*7 + 3, v___x_4609_);
v___x_4710_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4711_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4712_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4710_);
lean_ctor_set(v___x_4713_, 1, v___x_4711_);
lean_ctor_set(v___x_4713_, 2, v___x_4600_);
lean_ctor_set(v___x_4713_, 3, v___x_4705_);
lean_ctor_set(v___x_4713_, 4, v___x_4712_);
v___x_4714_ = lean_st_mk_ref(v___x_4713_);
lean_inc(v_pre_4605_);
v___x_4715_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4605_, v___x_4709_, v___x_4714_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref_known(v___x_4715_, 1);
lean_inc_ref(v_str_4606_);
v___x_4717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4717_, 0, v_str_4606_);
lean_ctor_set(v___x_4717_, 1, v___x_4687_);
lean_ctor_set(v___x_4717_, 2, v___x_4685_);
v___x_4718_ = l_String_Slice_toNat_x21(v___x_4717_);
lean_dec_ref_known(v___x_4717_, 3);
v___x_4719_ = l_Lean_ConstantInfo_levelParams(v_a_4716_);
lean_dec(v_a_4716_);
v___x_4720_ = lean_box(0);
lean_inc(v___x_4719_);
v___x_4721_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4719_, v___x_4720_);
lean_inc(v_pre_4605_);
v___x_4722_ = l_Lean_mkConst(v_pre_4605_, v___x_4721_);
v___x_4723_ = l_Lean_Meta_mkHCongrWithArity(v___x_4722_, v___x_4718_, v___x_4709_, v___x_4714_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v_type_4725_; lean_object* v_proof_4726_; lean_object* v_argKinds_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4750_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v_type_4725_ = lean_ctor_get(v_a_4724_, 0);
v_proof_4726_ = lean_ctor_get(v_a_4724_, 1);
v_argKinds_4727_ = lean_ctor_get(v_a_4724_, 2);
v_isSharedCheck_4750_ = !lean_is_exclusive(v_a_4724_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4729_ = v_a_4724_;
v_isShared_4730_ = v_isSharedCheck_4750_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_argKinds_4727_);
lean_inc(v_proof_4726_);
lean_inc(v_type_4725_);
lean_dec(v_a_4724_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4750_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
lean_inc_ref(v_name_4601_);
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 2, v_type_4725_);
lean_ctor_set(v___x_4729_, 1, v___x_4719_);
lean_ctor_set(v___x_4729_, 0, v_name_4601_);
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_name_4601_);
lean_ctor_set(v_reuseFailAlloc_4749_, 1, v___x_4719_);
lean_ctor_set(v_reuseFailAlloc_4749_, 2, v_type_4725_);
v___x_4732_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___f_4736_; lean_object* v___x_4737_; 
lean_inc_ref_n(v_name_4601_, 2);
v___x_4733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4733_, 0, v_name_4601_);
lean_ctor_set(v___x_4733_, 1, v___x_4720_);
v___x_4734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4732_);
lean_ctor_set(v___x_4734_, 1, v_proof_4726_);
lean_ctor_set(v___x_4734_, 2, v___x_4733_);
v___x_4735_ = lean_box(v___x_4688_);
v___f_4736_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4736_, 0, v___x_4734_);
lean_closure_set(v___f_4736_, 1, v___x_4735_);
lean_closure_set(v___f_4736_, 2, v_name_4601_);
lean_closure_set(v___f_4736_, 3, v_argKinds_4727_);
lean_closure_set(v___f_4736_, 4, v___x_4711_);
v___x_4737_ = l_Lean_Meta_realizeConst(v_pre_4605_, v_name_4601_, v___f_4736_, v___x_4709_, v___x_4714_, v___y_4602_, v___y_4603_);
lean_dec_ref_known(v___x_4709_, 7);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4746_; 
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4746_ == 0)
{
lean_object* v_unused_4747_; 
v_unused_4747_ = lean_ctor_get(v___x_4737_, 0);
lean_dec(v_unused_4747_);
v___x_4739_ = v___x_4737_;
v_isShared_4740_ = v_isSharedCheck_4746_;
goto v_resetjp_4738_;
}
else
{
lean_dec(v___x_4737_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4746_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4744_; 
v___x_4741_ = lean_st_ref_get(v___x_4714_);
lean_dec(v___x_4714_);
lean_dec(v___x_4741_);
v___x_4742_ = lean_box(v___x_4609_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4742_);
v___x_4744_ = v___x_4739_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4742_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
else
{
lean_object* v_a_4748_; 
lean_dec(v___x_4714_);
v_a_4748_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4748_);
lean_dec_ref_known(v___x_4737_, 1);
v_a_4696_ = v_a_4748_;
goto v___jp_4695_;
}
}
}
}
else
{
lean_object* v_a_4751_; 
lean_dec(v___x_4719_);
lean_dec(v___x_4714_);
lean_dec_ref_known(v___x_4709_, 7);
lean_dec(v_pre_4605_);
lean_dec_ref_known(v_name_4601_, 2);
v_a_4751_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4751_);
lean_dec_ref_known(v___x_4723_, 1);
v_a_4696_ = v_a_4751_;
goto v___jp_4695_;
}
}
else
{
lean_object* v_a_4752_; 
lean_dec(v___x_4714_);
lean_dec_ref_known(v___x_4709_, 7);
lean_dec(v___x_4687_);
lean_dec(v_pre_4605_);
lean_dec_ref_known(v_name_4601_, 2);
v_a_4752_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4752_);
lean_dec_ref_known(v___x_4715_, 1);
v_a_4696_ = v_a_4752_;
goto v___jp_4695_;
}
v___jp_4689_:
{
if (v___y_4691_ == 0)
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
lean_dec_ref(v___y_4690_);
v___x_4692_ = lean_box(v___x_4688_);
v___x_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
return v___x_4693_;
}
else
{
lean_object* v___x_4694_; 
v___x_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4694_, 0, v___y_4690_);
return v___x_4694_;
}
}
v___jp_4695_:
{
uint8_t v___x_4697_; 
v___x_4697_ = l_Lean_Exception_isInterrupt(v_a_4696_);
if (v___x_4697_ == 0)
{
uint8_t v___x_4698_; 
lean_inc_ref(v_a_4696_);
v___x_4698_ = l_Lean_Exception_isRuntime(v_a_4696_);
v___y_4690_ = v_a_4696_;
v___y_4691_ = v___x_4698_;
goto v___jp_4689_;
}
else
{
v___y_4690_ = v_a_4696_;
v___y_4691_ = v___x_4697_;
goto v___jp_4689_;
}
}
}
v___jp_4614_:
{
if (v___y_4616_ == 0)
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
lean_dec_ref(v___y_4615_);
v___x_4617_ = lean_box(v___x_4613_);
v___x_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
return v___x_4618_;
}
else
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___y_4615_);
return v___x_4619_;
}
}
v___jp_4620_:
{
uint8_t v___x_4622_; 
v___x_4622_ = l_Lean_Exception_isInterrupt(v_a_4621_);
if (v___x_4622_ == 0)
{
uint8_t v___x_4623_; 
lean_inc_ref(v_a_4621_);
v___x_4623_ = l_Lean_Exception_isRuntime(v_a_4621_);
v___y_4615_ = v_a_4621_;
v___y_4616_ = v___x_4623_;
goto v___jp_4614_;
}
else
{
v___y_4615_ = v_a_4621_;
v___y_4616_ = v___x_4622_;
goto v___jp_4614_;
}
}
}
}
else
{
uint8_t v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
lean_dec(v_name_4601_);
lean_dec(v___x_4600_);
v___x_4753_ = 0;
v___x_4754_ = lean_box(v___x_4753_);
v___x_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4754_);
return v___x_4755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4756_, lean_object* v_name_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4756_, v_name_4757_, v___y_4758_, v___y_4759_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4765_; lean_object* v___x_4766_; 
v___f_4765_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4766_ = l_Lean_registerReservedNameAction(v___f_4765_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_a_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* v_msg_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v___f_4775_; lean_object* v___x_1734__overap_4776_; lean_object* v___x_4777_; 
v___f_4775_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1734__overap_4776_ = lean_panic_fn_borrowed(v___f_4775_, v_msg_4769_);
lean_inc(v___y_4773_);
lean_inc_ref(v___y_4772_);
lean_inc(v___y_4771_);
lean_inc_ref(v___y_4770_);
v___x_4777_ = lean_apply_5(v___x_1734__overap_4776_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, lean_box(0));
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
return v_res_4784_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4786_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4787_ = lean_unsigned_to_nat(8u);
v___x_4788_ = lean_unsigned_to_nat(461u);
v___x_4789_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0));
v___x_4790_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4791_ = l_mkPanicMessageWithDecl(v___x_4790_, v___x_4789_, v___x_4788_, v___x_4787_, v___x_4786_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* v_thmName_4792_, lean_object* v_levels_4793_, lean_object* v___x_4794_, lean_object* v_____r_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
lean_inc(v_thmName_4792_);
v___x_4801_ = l_Lean_mkConst(v_thmName_4792_, v_levels_4793_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc(v___y_4797_);
lean_inc_ref(v___y_4796_);
lean_inc_ref(v___x_4801_);
v___x_4802_ = lean_infer_type(v___x_4801_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4846_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4805_ = v___x_4802_;
v_isShared_4806_ = v_isSharedCheck_4846_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4802_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4846_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4807_; lean_object* v_env_4808_; lean_object* v___x_4809_; lean_object* v_toEnvExtension_4810_; lean_object* v_asyncMode_4811_; uint8_t v___x_4812_; lean_object* v___x_4813_; 
v___x_4807_ = lean_st_ref_get(v___y_4799_);
v_env_4808_ = lean_ctor_get(v___x_4807_, 0);
lean_inc_ref(v_env_4808_);
lean_dec(v___x_4807_);
v___x_4809_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4810_ = lean_ctor_get(v___x_4809_, 0);
v_asyncMode_4811_ = lean_ctor_get(v_toEnvExtension_4810_, 2);
v___x_4812_ = 0;
v___x_4813_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4794_, v___x_4809_, v_env_4808_, v_thmName_4792_, v_asyncMode_4811_, v___x_4812_);
if (lean_obj_tag(v___x_4813_) == 1)
{
lean_object* v_val_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4826_; 
v_val_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4826_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_val_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4826_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4818_; lean_object* v___x_4820_; 
v___x_4818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4818_, 0, v_a_4803_);
lean_ctor_set(v___x_4818_, 1, v___x_4801_);
lean_ctor_set(v___x_4818_, 2, v_val_4814_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v___x_4818_);
v___x_4820_ = v___x_4816_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
lean_object* v___x_4821_; lean_object* v___x_4823_; 
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 0, v___x_4821_);
v___x_4823_ = v___x_4805_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4821_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
else
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
lean_dec(v___x_4813_);
lean_del_object(v___x_4805_);
lean_dec(v_a_4803_);
lean_dec_ref(v___x_4801_);
v___x_4827_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1);
v___x_4828_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4827_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4837_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4831_ = v___x_4828_;
v_isShared_4832_ = v_isSharedCheck_4837_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4828_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4837_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4833_; lean_object* v___x_4835_; 
v___x_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4833_, 0, v_a_4829_);
if (v_isShared_4832_ == 0)
{
lean_ctor_set(v___x_4831_, 0, v___x_4833_);
v___x_4835_ = v___x_4831_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4833_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
else
{
lean_object* v_a_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4845_; 
v_a_4838_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4840_ = v___x_4828_;
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_a_4838_);
lean_dec(v___x_4828_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4843_; 
if (v_isShared_4841_ == 0)
{
v___x_4843_ = v___x_4840_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_a_4838_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
}
}
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec_ref(v___x_4801_);
lean_dec_ref(v___x_4794_);
lean_dec(v_thmName_4792_);
v_a_4847_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4802_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4802_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* v_thmName_4855_, lean_object* v_levels_4856_, lean_object* v___x_4857_, lean_object* v_____r_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4855_, v_levels_4856_, v___x_4857_, v_____r_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
return v_res_4864_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0(void){
_start:
{
lean_object* v___x_4865_; 
v___x_4865_ = l_Array_instInhabited(lean_box(0));
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* v_declName_4866_, lean_object* v_levels_4867_, lean_object* v_numArgs_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
lean_object* v___y_4875_; uint8_t v___y_4876_; lean_object* v_a_4881_; lean_object* v___y_4885_; lean_object* v___x_4896_; lean_object* v_env_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v_suffix_4901_; lean_object* v_thmName_4902_; uint8_t v___x_4903_; 
v___x_4896_ = lean_st_ref_get(v_a_4872_);
v_env_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc_ref(v_env_4897_);
lean_dec(v___x_4896_);
v___x_4898_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_4899_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4900_ = l_Nat_reprFast(v_numArgs_4868_);
v_suffix_4901_ = lean_string_append(v___x_4899_, v___x_4900_);
lean_dec_ref(v___x_4900_);
v_thmName_4902_ = l_Lean_Name_str___override(v_declName_4866_, v_suffix_4901_);
v___x_4903_ = l_Lean_Environment_containsOnBranch(v_env_4897_, v_thmName_4902_);
lean_dec_ref(v_env_4897_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; 
lean_inc(v_thmName_4902_);
v___x_4904_ = l_Lean_executeReservedNameAction(v_thmName_4902_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
lean_dec_ref_known(v___x_4904_, 1);
v___x_4905_ = lean_box(0);
v___x_4906_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4902_, v_levels_4867_, v___x_4898_, v___x_4905_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
v___y_4885_ = v___x_4906_;
goto v___jp_4884_;
}
else
{
lean_object* v_a_4907_; 
lean_dec(v_thmName_4902_);
lean_dec(v_levels_4867_);
v_a_4907_ = lean_ctor_get(v___x_4904_, 0);
lean_inc(v_a_4907_);
lean_dec_ref_known(v___x_4904_, 1);
v_a_4881_ = v_a_4907_;
goto v___jp_4880_;
}
}
else
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = lean_box(0);
v___x_4909_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4902_, v_levels_4867_, v___x_4898_, v___x_4908_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
v___y_4885_ = v___x_4909_;
goto v___jp_4884_;
}
v___jp_4874_:
{
if (v___y_4876_ == 0)
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
lean_dec_ref(v___y_4875_);
v___x_4877_ = lean_box(0);
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
else
{
lean_object* v___x_4879_; 
v___x_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___y_4875_);
return v___x_4879_;
}
}
v___jp_4880_:
{
uint8_t v___x_4882_; 
v___x_4882_ = l_Lean_Exception_isInterrupt(v_a_4881_);
if (v___x_4882_ == 0)
{
uint8_t v___x_4883_; 
lean_inc_ref(v_a_4881_);
v___x_4883_ = l_Lean_Exception_isRuntime(v_a_4881_);
v___y_4875_ = v_a_4881_;
v___y_4876_ = v___x_4883_;
goto v___jp_4874_;
}
else
{
v___y_4875_ = v_a_4881_;
v___y_4876_ = v___x_4882_;
goto v___jp_4874_;
}
}
v___jp_4884_:
{
if (lean_obj_tag(v___y_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4894_; 
v_a_4886_ = lean_ctor_get(v___y_4885_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___y_4885_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4888_ = v___y_4885_;
v_isShared_4889_ = v_isSharedCheck_4894_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___y_4885_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4894_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v_a_4890_; lean_object* v___x_4892_; 
v_a_4890_ = lean_ctor_get(v_a_4886_, 0);
lean_inc(v_a_4890_);
lean_dec(v_a_4886_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 0, v_a_4890_);
v___x_4892_ = v___x_4888_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4890_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
else
{
lean_object* v_a_4895_; 
v_a_4895_ = lean_ctor_get(v___y_4885_, 0);
lean_inc(v_a_4895_);
lean_dec_ref_known(v___y_4885_, 1);
v_a_4881_ = v_a_4895_;
goto v___jp_4880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object* v_declName_4910_, lean_object* v_levels_4911_, lean_object* v_numArgs_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_4910_, v_levels_4911_, v_numArgs_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
lean_dec(v_a_4916_);
lean_dec_ref(v_a_4915_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* v_____r_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0));
v___x_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* v_____r_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
return v_res_4935_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4937_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4938_ = lean_unsigned_to_nat(8u);
v___x_4939_ = lean_unsigned_to_nat(478u);
v___x_4940_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0));
v___x_4941_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4942_ = l_mkPanicMessageWithDecl(v___x_4941_, v___x_4940_, v___x_4939_, v___x_4938_, v___x_4937_);
return v___x_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object* v_thmName_4943_, lean_object* v_levels_4944_, lean_object* v___x_4945_, lean_object* v_____r_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_inc(v_thmName_4943_);
v___x_4952_ = l_Lean_mkConst(v_thmName_4943_, v_levels_4944_);
lean_inc(v___y_4950_);
lean_inc_ref(v___y_4949_);
lean_inc(v___y_4948_);
lean_inc_ref(v___y_4947_);
lean_inc_ref(v___x_4952_);
v___x_4953_ = lean_infer_type(v___x_4952_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4997_; 
v_a_4954_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4956_ = v___x_4953_;
v_isShared_4957_ = v_isSharedCheck_4997_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4953_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4997_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4958_; lean_object* v_env_4959_; lean_object* v___x_4960_; lean_object* v_toEnvExtension_4961_; lean_object* v_asyncMode_4962_; uint8_t v___x_4963_; lean_object* v___x_4964_; 
v___x_4958_ = lean_st_ref_get(v___y_4950_);
v_env_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc_ref(v_env_4959_);
lean_dec(v___x_4958_);
v___x_4960_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4961_ = lean_ctor_get(v___x_4960_, 0);
v_asyncMode_4962_ = lean_ctor_get(v_toEnvExtension_4961_, 2);
v___x_4963_ = 0;
v___x_4964_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4945_, v___x_4960_, v_env_4959_, v_thmName_4943_, v_asyncMode_4962_, v___x_4963_);
if (lean_obj_tag(v___x_4964_) == 1)
{
lean_object* v_val_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4977_; 
v_val_4965_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4967_ = v___x_4964_;
v_isShared_4968_ = v_isSharedCheck_4977_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_val_4965_);
lean_dec(v___x_4964_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4977_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4969_; lean_object* v___x_4971_; 
v___x_4969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4969_, 0, v_a_4954_);
lean_ctor_set(v___x_4969_, 1, v___x_4952_);
lean_ctor_set(v___x_4969_, 2, v_val_4965_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 0, v___x_4969_);
v___x_4971_ = v___x_4967_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v___x_4969_);
v___x_4971_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
lean_object* v___x_4972_; lean_object* v___x_4974_; 
v___x_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4971_);
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v___x_4972_);
v___x_4974_ = v___x_4956_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v___x_4972_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
else
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
lean_dec(v___x_4964_);
lean_del_object(v___x_4956_);
lean_dec(v_a_4954_);
lean_dec_ref(v___x_4952_);
v___x_4978_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1);
v___x_4979_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4978_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4988_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4982_ = v___x_4979_;
v_isShared_4983_ = v_isSharedCheck_4988_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4979_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4988_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4984_; lean_object* v___x_4986_; 
v___x_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4984_, 0, v_a_4980_);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 0, v___x_4984_);
v___x_4986_ = v___x_4982_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4984_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
v_a_4989_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4979_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4979_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_dec_ref(v___x_4952_);
lean_dec_ref(v___x_4945_);
lean_dec(v_thmName_4943_);
v_a_4998_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4953_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4953_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object* v_thmName_5006_, lean_object* v_levels_5007_, lean_object* v___x_5008_, lean_object* v_____r_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5006_, v_levels_5007_, v___x_5008_, v_____r_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
lean_dec(v___y_5013_);
lean_dec_ref(v___y_5012_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
return v_res_5015_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1(void){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5017_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0));
v___x_5018_ = l_Lean_stringToMessageData(v___x_5017_);
return v___x_5018_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3(void){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2));
v___x_5021_ = l_Lean_stringToMessageData(v___x_5020_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* v_declName_5022_, lean_object* v_levels_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v_a_5030_; lean_object* v___y_5048_; lean_object* v___x_5050_; lean_object* v_env_5051_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v_thmName_5057_; lean_object* v___y_5059_; uint8_t v___y_5060_; lean_object* v_a_5088_; lean_object* v___y_5092_; uint8_t v___x_5095_; 
v___x_5050_ = lean_st_ref_get(v_a_5027_);
v_env_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc_ref(v_env_5051_);
lean_dec(v___x_5050_);
v___x_5055_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_5056_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v_thmName_5057_ = l_Lean_Name_str___override(v_declName_5022_, v___x_5056_);
v___x_5095_ = l_Lean_Environment_containsOnBranch(v_env_5051_, v_thmName_5057_);
lean_dec_ref(v_env_5051_);
if (v___x_5095_ == 0)
{
lean_object* v___x_5096_; 
lean_inc(v_thmName_5057_);
v___x_5096_ = l_Lean_executeReservedNameAction(v_thmName_5057_, v_a_5026_, v_a_5027_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
lean_dec_ref_known(v___x_5096_, 1);
v___x_5097_ = lean_box(0);
lean_inc(v_thmName_5057_);
v___x_5098_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5057_, v_levels_5023_, v___x_5055_, v___x_5097_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
v___y_5092_ = v___x_5098_;
goto v___jp_5091_;
}
else
{
lean_object* v_a_5099_; 
lean_dec(v_levels_5023_);
v_a_5099_ = lean_ctor_get(v___x_5096_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5096_, 1);
v_a_5088_ = v_a_5099_;
goto v___jp_5087_;
}
}
else
{
lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5100_ = lean_box(0);
lean_inc(v_thmName_5057_);
v___x_5101_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5057_, v_levels_5023_, v___x_5055_, v___x_5100_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
v___y_5092_ = v___x_5101_;
goto v___jp_5091_;
}
v___jp_5029_:
{
if (lean_obj_tag(v_a_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
v_a_5031_ = lean_ctor_get(v_a_5030_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v_a_5030_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v_a_5030_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v_a_5030_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
v_a_5039_ = lean_ctor_get(v_a_5030_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v_a_5030_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v_a_5030_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v_a_5030_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
lean_ctor_set_tag(v___x_5041_, 0);
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5039_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
v___jp_5047_:
{
lean_object* v_a_5049_; 
v_a_5049_ = lean_ctor_get(v___y_5048_, 0);
lean_inc(v_a_5049_);
lean_dec_ref(v___y_5048_);
v_a_5030_ = v_a_5049_;
goto v___jp_5029_;
}
v___jp_5052_:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = lean_box(0);
v___x_5054_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v___x_5053_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
v___y_5048_ = v___x_5054_;
goto v___jp_5047_;
}
v___jp_5058_:
{
if (v___y_5060_ == 0)
{
lean_object* v_toCold_5061_; lean_object* v_options_5062_; uint8_t v_hasTrace_5063_; 
v_toCold_5061_ = lean_ctor_get(v_a_5026_, 0);
v_options_5062_ = lean_ctor_get(v_toCold_5061_, 2);
v_hasTrace_5063_ = lean_ctor_get_uint8(v_options_5062_, sizeof(void*)*1);
if (v_hasTrace_5063_ == 0)
{
lean_dec_ref(v___y_5059_);
lean_dec(v_thmName_5057_);
goto v___jp_5052_;
}
else
{
lean_object* v_inheritedTraceOptions_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; uint8_t v___x_5067_; 
v_inheritedTraceOptions_5064_ = lean_ctor_get(v_toCold_5061_, 11);
v___x_5065_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_5066_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_5067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5064_, v_options_5062_, v___x_5066_);
if (v___x_5067_ == 0)
{
lean_dec_ref(v___y_5059_);
lean_dec(v_thmName_5057_);
goto v___jp_5052_;
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___x_5068_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1);
v___x_5069_ = l_Lean_MessageData_ofName(v_thmName_5057_);
v___x_5070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5068_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
v___x_5071_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3);
v___x_5072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5070_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = l_Lean_Exception_toMessageData(v___y_5059_);
v___x_5074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5072_);
lean_ctor_set(v___x_5074_, 1, v___x_5073_);
v___x_5075_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_5065_, v___x_5074_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v_a_5076_; lean_object* v___x_5077_; 
v_a_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_a_5076_);
lean_dec_ref_known(v___x_5075_, 1);
v___x_5077_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_a_5076_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
v___y_5048_ = v___x_5077_;
goto v___jp_5047_;
}
else
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
v_a_5078_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5080_ = v___x_5075_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5075_);
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
v_reuseFailAlloc_5084_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
lean_object* v___x_5086_; 
lean_dec(v_thmName_5057_);
v___x_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5086_, 0, v___y_5059_);
return v___x_5086_;
}
}
v___jp_5087_:
{
uint8_t v___x_5089_; 
v___x_5089_ = l_Lean_Exception_isInterrupt(v_a_5088_);
if (v___x_5089_ == 0)
{
uint8_t v___x_5090_; 
lean_inc_ref(v_a_5088_);
v___x_5090_ = l_Lean_Exception_isRuntime(v_a_5088_);
v___y_5059_ = v_a_5088_;
v___y_5060_ = v___x_5090_;
goto v___jp_5058_;
}
else
{
v___y_5059_ = v_a_5088_;
v___y_5060_ = v___x_5089_;
goto v___jp_5058_;
}
}
v___jp_5091_:
{
if (lean_obj_tag(v___y_5092_) == 0)
{
lean_object* v_a_5093_; 
lean_dec(v_thmName_5057_);
v_a_5093_ = lean_ctor_get(v___y_5092_, 0);
lean_inc(v_a_5093_);
lean_dec_ref_known(v___y_5092_, 1);
v_a_5030_ = v_a_5093_;
goto v___jp_5029_;
}
else
{
lean_object* v_a_5094_; 
v_a_5094_ = lean_ctor_get(v___y_5092_, 0);
lean_inc(v_a_5094_);
lean_dec_ref_known(v___y_5092_, 1);
v_a_5088_ = v_a_5094_;
goto v___jp_5087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object* v_declName_5102_, lean_object* v_levels_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_5102_, v_levels_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_);
lean_dec(v_a_5107_);
lean_dec_ref(v_a_5106_);
lean_dec(v_a_5105_);
lean_dec_ref(v_a_5104_);
return v_res_5109_;
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
