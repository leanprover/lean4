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
uint8_t v_x_345__boxed_198_; lean_object* v_res_199_; 
v_x_345__boxed_198_ = lean_unbox(v_x_196_);
v_res_199_ = l_Lean_Meta_instReprCongrArgKind_repr(v_x_345__boxed_198_, v_prec_197_);
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
uint8_t v_x_17__boxed_209_; uint8_t v_y_18__boxed_210_; uint8_t v_res_211_; lean_object* v_r_212_; 
v_x_17__boxed_209_ = lean_unbox(v_x_207_);
v_y_18__boxed_210_ = lean_unbox(v_y_208_);
v_res_211_ = l_Lean_Meta_instBEqCongrArgKind_beq(v_x_17__boxed_209_, v_y_18__boxed_210_);
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
uint8_t v___x_1902__boxed_717_; lean_object* v_res_718_; 
v___x_1902__boxed_717_ = lean_unbox(v___x_707_);
v_res_718_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(v___x_705_, v___x_706_, v___x_1902__boxed_717_, v___x_708_, v___x_709_, v_a_710_, v_type_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
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
uint8_t v___x_1958__boxed_801_; lean_object* v_res_802_; 
v___x_1958__boxed_801_ = lean_unbox(v___x_792_);
v_res_802_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(v_type_788_, v_motive_789_, v___x_790_, v_b_791_, v___x_1958__boxed_801_, v___x_793_, v_a_794_, v_eqPr_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
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
uint8_t v___x_1917__boxed_839_; lean_object* v_res_840_; 
v___x_1917__boxed_839_ = lean_unbox(v___x_830_);
v_res_840_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(v___x_825_, v___x_826_, v_type_827_, v_a_828_, v___x_829_, v___x_1917__boxed_839_, v___x_831_, v_b_832_, v_motive_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
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
uint8_t v___x_4841__boxed_1095_; uint8_t v___x_4842__boxed_1096_; lean_object* v_res_1097_; 
v___x_4841__boxed_1095_ = lean_unbox(v___x_1086_);
v___x_4842__boxed_1096_ = lean_unbox(v___x_1087_);
v_res_1097_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1083_, v_xs_1084_, v_f_1085_, v___x_4841__boxed_1095_, v___x_4842__boxed_1096_, v_eqs_1088_, v_argKinds_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
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
lean_object* v___x_1104_; lean_object* v_env_1105_; lean_object* v___x_1106_; lean_object* v_mctx_1107_; lean_object* v_lctx_1108_; lean_object* v_options_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1104_ = lean_st_ref_get(v___y_1102_);
v_env_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_env_1105_);
lean_dec(v___x_1104_);
v___x_1106_ = lean_st_ref_get(v___y_1100_);
v_mctx_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc_ref(v_mctx_1107_);
lean_dec(v___x_1106_);
v_lctx_1108_ = lean_ctor_get(v___y_1099_, 2);
v_options_1109_ = lean_ctor_get(v___y_1101_, 2);
lean_inc_ref(v_options_1109_);
lean_inc_ref(v_lctx_1108_);
v___x_1110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1110_, 0, v_env_1105_);
lean_ctor_set(v___x_1110_, 1, v_mctx_1107_);
lean_ctor_set(v___x_1110_, 2, v_lctx_1108_);
lean_ctor_set(v___x_1110_, 3, v_options_1109_);
v___x_1111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v_msgData_1098_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0___boxed(lean_object* v_msgData_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msgData_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object* v_msg_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_ref_1126_; lean_object* v___x_1127_; lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
v_ref_1126_ = lean_ctor_get(v___y_1123_, 5);
v___x_1127_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_inc(v_ref_1126_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_ref_1126_);
lean_ctor_set(v___x_1132_, 1, v_a_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 1);
lean_ctor_set(v___x_1130_, 0, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object* v_msg_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1(lean_object* v_xs_1153_, lean_object* v_numArgs_1154_, lean_object* v_f_1155_, lean_object* v_ys_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_array_get_size(v_xs_1153_);
v___x_1164_ = lean_nat_dec_eq(v___x_1163_, v_numArgs_1154_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v_ys_1156_);
lean_dec_ref(v_xs_1153_);
v___x_1165_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1);
v___x_1166_ = l_Nat_reprFast(v_numArgs_1154_);
v___x_1167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
v___x_1168_ = l_Lean_MessageData_ofFormat(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1165_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = l_Nat_reprFast(v___x_1163_);
v___x_1173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = l_Lean_MessageData_ofFormat(v___x_1173_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1171_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_indentExpr(v_f_1155_);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v___x_1179_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1180_;
}
else
{
lean_object* v_lctx_1181_; lean_object* v_localInstances_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___f_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec(v_numArgs_1154_);
v_lctx_1181_ = lean_ctor_get(v___y_1158_, 2);
v_localInstances_1182_ = lean_ctor_get(v___y_1158_, 3);
v___x_1183_ = 0;
v___x_1184_ = lean_box(v___x_1183_);
v___x_1185_ = lean_box(v___x_1164_);
lean_inc_ref(v_xs_1153_);
lean_inc_ref(v_ys_1156_);
v___f_1186_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1186_, 0, v_ys_1156_);
lean_closure_set(v___f_1186_, 1, v_xs_1153_);
lean_closure_set(v___f_1186_, 2, v_f_1155_);
lean_closure_set(v___f_1186_, 3, v___x_1184_);
lean_closure_set(v___f_1186_, 4, v___x_1185_);
lean_inc_ref(v_lctx_1181_);
v___x_1187_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_1156_, v_lctx_1181_);
v___x_1188_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_1156_, v___x_1187_);
v___x_1189_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_xs_1153_, v___x_1188_);
v___x_1190_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed), 9, 4);
lean_closure_set(v___x_1190_, 0, lean_box(0));
lean_closure_set(v___x_1190_, 1, v_xs_1153_);
lean_closure_set(v___x_1190_, 2, v_ys_1156_);
lean_closure_set(v___x_1190_, 3, v___f_1186_);
lean_inc_ref(v_localInstances_1182_);
v___x_1191_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v___x_1189_, v_localInstances_1182_, v___x_1190_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object* v_xs_1192_, lean_object* v_numArgs_1193_, lean_object* v_f_1194_, lean_object* v_ys_1195_, lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Meta_mkHCongrWithArity___lam__1(v_xs_1192_, v_numArgs_1193_, v_f_1194_, v_ys_1195_, v_x_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v_x_1196_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object* v_numArgs_1203_, lean_object* v_f_1204_, lean_object* v_a_1205_, lean_object* v___x_1206_, lean_object* v_xs_1207_, lean_object* v_x_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___f_1214_; uint8_t v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; 
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1214_, 0, v_xs_1207_);
lean_closure_set(v___f_1214_, 1, v_numArgs_1203_);
lean_closure_set(v___f_1214_, 2, v_f_1204_);
v___x_1215_ = 1;
v___x_1216_ = 0;
v___x_1217_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1205_, v___x_1206_, v___f_1214_, v___x_1215_, v___x_1216_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object* v_numArgs_1218_, lean_object* v_f_1219_, lean_object* v_a_1220_, lean_object* v___x_1221_, lean_object* v_xs_1222_, lean_object* v_x_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Meta_mkHCongrWithArity___lam__2(v_numArgs_1218_, v_f_1219_, v_a_1220_, v___x_1221_, v_xs_1222_, v_x_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v_x_1223_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object* v_f_1230_, lean_object* v_numArgs_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1237_; 
lean_inc(v_a_1235_);
lean_inc_ref(v_a_1234_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc_ref(v_f_1230_);
v___x_1237_ = lean_infer_type(v_f_1230_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; uint8_t v___x_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc_n(v_a_1238_, 2);
lean_dec_ref_known(v___x_1237_, 1);
lean_inc(v_numArgs_1231_);
v___x_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_numArgs_1231_);
lean_inc_ref(v___x_1239_);
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1240_, 0, v_numArgs_1231_);
lean_closure_set(v___f_1240_, 1, v_f_1230_);
lean_closure_set(v___f_1240_, 2, v_a_1238_);
lean_closure_set(v___f_1240_, 3, v___x_1239_);
v___x_1241_ = 1;
v___x_1242_ = 0;
v___x_1243_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1238_, v___x_1239_, v___f_1240_, v___x_1241_, v___x_1242_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
return v___x_1243_;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec(v_numArgs_1231_);
lean_dec_ref(v_f_1230_);
v_a_1244_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1237_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1237_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___boxed(lean_object* v_f_1252_, lean_object* v_numArgs_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Meta_mkHCongrWithArity(v_f_1252_, v_numArgs_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object* v_00_u03b1_1260_, lean_object* v_msg_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object* v_00_u03b1_1268_, lean_object* v_msg_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(v_00_u03b1_1268_, v_msg_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object* v_as_1276_, size_t v_sz_1277_, size_t v_i_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_1276_, v_sz_1277_, v_i_1278_, v_b_1279_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object* v_as_1286_, lean_object* v_sz_1287_, lean_object* v_i_1288_, lean_object* v_b_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
size_t v_sz_boxed_1295_; size_t v_i_boxed_1296_; lean_object* v_res_1297_; 
v_sz_boxed_1295_ = lean_unbox_usize(v_sz_1287_);
lean_dec(v_sz_1287_);
v_i_boxed_1296_ = lean_unbox_usize(v_i_1288_);
lean_dec(v_i_1288_);
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(v_as_1286_, v_sz_boxed_1295_, v_i_boxed_1296_, v_b_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec_ref(v_as_1286_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object* v_f_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
lean_inc_ref(v_f_1298_);
v___x_1305_ = l_Lean_Meta_getFunInfo(v_f_1298_, v___x_1304_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = l_Lean_Meta_FunInfo_getArity(v_a_1306_);
lean_dec(v_a_1306_);
v___x_1308_ = l_Lean_Meta_mkHCongrWithArity(v_f_1298_, v___x_1307_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1308_;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v_f_1298_);
v_a_1309_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1305_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1305_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr___boxed(lean_object* v_f_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Meta_mkHCongr(v_f_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object* v_a_1324_, lean_object* v_as_1325_, size_t v_i_1326_, size_t v_stop_1327_){
_start:
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_usize_dec_eq(v_i_1326_, v_stop_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_array_uget_borrowed(v_as_1325_, v_i_1326_);
v___x_1330_ = lean_nat_dec_eq(v_a_1324_, v___x_1329_);
if (v___x_1330_ == 0)
{
size_t v___x_1331_; size_t v___x_1332_; 
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1326_, v___x_1331_);
v_i_1326_ = v___x_1332_;
goto _start;
}
else
{
return v___x_1330_;
}
}
else
{
uint8_t v___x_1334_; 
v___x_1334_ = 0;
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object* v_a_1335_, lean_object* v_as_1336_, lean_object* v_i_1337_, lean_object* v_stop_1338_){
_start:
{
size_t v_i_boxed_1339_; size_t v_stop_boxed_1340_; uint8_t v_res_1341_; lean_object* v_r_1342_; 
v_i_boxed_1339_ = lean_unbox_usize(v_i_1337_);
lean_dec(v_i_1337_);
v_stop_boxed_1340_ = lean_unbox_usize(v_stop_1338_);
lean_dec(v_stop_1338_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1335_, v_as_1336_, v_i_boxed_1339_, v_stop_boxed_1340_);
lean_dec_ref(v_as_1336_);
lean_dec(v_a_1335_);
v_r_1342_ = lean_box(v_res_1341_);
return v_r_1342_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object* v_as_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_get_size(v_as_1343_);
v___x_1347_ = lean_nat_dec_lt(v___x_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
return v___x_1347_;
}
else
{
if (v___x_1347_ == 0)
{
return v___x_1347_;
}
else
{
size_t v___x_1348_; size_t v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1346_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1344_, v_as_1343_, v___x_1348_, v___x_1349_);
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object* v_as_1351_, lean_object* v_a_1352_){
_start:
{
uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_as_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_as_1351_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(lean_object* v_next_1355_, lean_object* v_upperBound_1356_, lean_object* v___x_1357_, lean_object* v_a_1358_, lean_object* v_b_1359_){
_start:
{
lean_object* v_a_1361_; uint8_t v___x_1369_; 
v___x_1369_ = lean_nat_dec_lt(v_a_1358_, v_upperBound_1356_);
if (v___x_1369_ == 0)
{
lean_dec(v_a_1358_);
return v_b_1359_;
}
else
{
lean_object* v___x_1370_; lean_object* v_backDeps_1371_; uint8_t v___x_1372_; 
v___x_1370_ = lean_array_fget_borrowed(v___x_1357_, v_a_1358_);
v_backDeps_1371_ = lean_ctor_get(v___x_1370_, 0);
v___x_1372_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_backDeps_1371_, v_next_1355_);
if (v___x_1372_ == 0)
{
v_a_1361_ = v_b_1359_;
goto v___jp_1360_;
}
else
{
uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1373_ = 0;
v___x_1374_ = lean_box(v___x_1373_);
v___x_1375_ = lean_array_get(v___x_1374_, v_b_1359_, v_a_1358_);
lean_dec(v___x_1374_);
v___x_1376_ = lean_unbox(v___x_1375_);
lean_dec(v___x_1375_);
switch(v___x_1376_)
{
case 2:
{
lean_dec(v_a_1358_);
goto v___jp_1365_;
}
case 0:
{
lean_dec(v_a_1358_);
goto v___jp_1365_;
}
default: 
{
v_a_1361_ = v_b_1359_;
goto v___jp_1360_;
}
}
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_add(v_a_1358_, v___x_1362_);
lean_dec(v_a_1358_);
v_a_1358_ = v___x_1363_;
v_b_1359_ = v_a_1361_;
goto _start;
}
v___jp_1365_:
{
uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = 0;
v___x_1367_ = lean_box(v___x_1366_);
v___x_1368_ = lean_array_set(v_b_1359_, v_next_1355_, v___x_1367_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(lean_object* v_next_1377_, lean_object* v_upperBound_1378_, lean_object* v___x_1379_, lean_object* v_a_1380_, lean_object* v_b_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1377_, v_upperBound_1378_, v___x_1379_, v_a_1380_, v_b_1381_);
lean_dec_ref(v___x_1379_);
lean_dec(v_upperBound_1378_);
lean_dec(v_next_1377_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object* v_upperBound_1383_, lean_object* v___x_1384_, lean_object* v___x_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_nat_dec_lt(v_a_1386_, v_upperBound_1383_);
if (v___x_1388_ == 0)
{
lean_dec(v_a_1386_);
return v_b_1387_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_add(v_a_1386_, v___x_1389_);
lean_inc(v___x_1390_);
v___x_1391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_a_1386_, v___x_1384_, v___x_1385_, v___x_1390_, v_b_1387_);
lean_dec(v_a_1386_);
v_a_1386_ = v___x_1390_;
v_b_1387_ = v___x_1391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object* v_upperBound_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v_a_1396_, lean_object* v_b_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1393_, v___x_1394_, v___x_1395_, v_a_1396_, v_b_1397_);
lean_dec_ref(v___x_1395_);
lean_dec(v___x_1394_);
lean_dec(v_upperBound_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object* v_info_1399_, lean_object* v_kinds_1400_){
_start:
{
lean_object* v_paramInfo_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_paramInfo_1401_ = lean_ctor_get(v_info_1399_, 0);
v___x_1402_ = lean_array_get_size(v_paramInfo_1401_);
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v___x_1402_, v___x_1402_, v_paramInfo_1401_, v___x_1403_, v_kinds_1400_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object* v_info_1405_, lean_object* v_kinds_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_1405_, v_kinds_1406_);
lean_dec_ref(v_info_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(lean_object* v_next_1408_, lean_object* v_upperBound_1409_, lean_object* v___x_1410_, lean_object* v_inst_1411_, lean_object* v_R_1412_, lean_object* v_a_1413_, lean_object* v_b_1414_, lean_object* v_c_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1408_, v_upperBound_1409_, v___x_1410_, v_a_1413_, v_b_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(lean_object* v_next_1417_, lean_object* v_upperBound_1418_, lean_object* v___x_1419_, lean_object* v_inst_1420_, lean_object* v_R_1421_, lean_object* v_a_1422_, lean_object* v_b_1423_, lean_object* v_c_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(v_next_1417_, v_upperBound_1418_, v___x_1419_, v_inst_1420_, v_R_1421_, v_a_1422_, v_b_1423_, v_c_1424_);
lean_dec_ref(v___x_1419_);
lean_dec(v_upperBound_1418_);
lean_dec(v_next_1417_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object* v_upperBound_1426_, lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v_inst_1429_, lean_object* v_R_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_, lean_object* v_c_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1426_, v___x_1427_, v___x_1428_, v_a_1431_, v_b_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object* v_upperBound_1435_, lean_object* v___x_1436_, lean_object* v___x_1437_, lean_object* v_inst_1438_, lean_object* v_R_1439_, lean_object* v_a_1440_, lean_object* v_b_1441_, lean_object* v_c_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(v_upperBound_1435_, v___x_1436_, v___x_1437_, v_inst_1438_, v_R_1439_, v_a_1440_, v_b_1441_, v_c_1442_);
lean_dec_ref(v___x_1437_);
lean_dec(v___x_1436_);
lean_dec(v_upperBound_1435_);
return v_res_1443_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object* v_as_1444_, size_t v_i_1445_, size_t v_stop_1446_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_usize_dec_eq(v_i_1445_, v_stop_1446_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = 1;
v___x_1449_ = lean_array_uget_borrowed(v_as_1444_, v_i_1445_);
v___x_1450_ = lean_unbox(v___x_1449_);
switch(v___x_1450_)
{
case 3:
{
return v___x_1448_;
}
case 5:
{
return v___x_1448_;
}
default: 
{
if (v___x_1447_ == 0)
{
size_t v___x_1451_; size_t v___x_1452_; 
v___x_1451_ = ((size_t)1ULL);
v___x_1452_ = lean_usize_add(v_i_1445_, v___x_1451_);
v_i_1445_ = v___x_1452_;
goto _start;
}
else
{
return v___x_1448_;
}
}
}
}
else
{
uint8_t v___x_1454_; 
v___x_1454_ = 0;
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object* v_as_1455_, lean_object* v_i_1456_, lean_object* v_stop_1457_){
_start:
{
size_t v_i_boxed_1458_; size_t v_stop_boxed_1459_; uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_i_boxed_1458_ = lean_unbox_usize(v_i_1456_);
lean_dec(v_i_1456_);
v_stop_boxed_1459_ = lean_unbox_usize(v_stop_1457_);
lean_dec(v_stop_1457_);
v_res_1460_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_as_1455_, v_i_boxed_1458_, v_stop_boxed_1459_);
lean_dec_ref(v_as_1455_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object* v_kinds_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = lean_array_get_size(v_kinds_1462_);
v___x_1465_ = lean_nat_dec_lt(v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
return v___x_1465_;
}
else
{
if (v___x_1465_ == 0)
{
return v___x_1465_;
}
else
{
size_t v___x_1466_; size_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = ((size_t)0ULL);
v___x_1467_ = lean_usize_of_nat(v___x_1464_);
v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_kinds_1462_, v___x_1466_, v___x_1467_);
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object* v_kinds_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_1469_);
lean_dec_ref(v_kinds_1469_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object* v___x_1472_, lean_object* v_k_1473_, lean_object* v_xs_1474_, lean_object* v_type_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_array_get_borrowed(v___x_1472_, v_xs_1474_, v___x_1481_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___x_1482_);
v___x_1483_ = lean_apply_7(v_k_1473_, v___x_1482_, v_type_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, lean_box(0));
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object* v___x_1484_, lean_object* v_k_1485_, lean_object* v_xs_1486_, lean_object* v_type_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(v___x_1484_, v_k_1485_, v_xs_1486_, v_type_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec_ref(v_xs_1486_);
lean_dec_ref(v___x_1484_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object* v_type_1494_, lean_object* v_k_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1501_ = l_Lean_instInhabitedExpr;
v___f_1502_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1502_, 0, v___x_1501_);
lean_closure_set(v___f_1502_, 1, v_k_1495_);
v___x_1503_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_1504_ = 1;
v___x_1505_ = 0;
v___x_1506_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_1494_, v___x_1503_, v___f_1502_, v___x_1504_, v___x_1505_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(lean_object* v_type_1507_, lean_object* v_k_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1507_, v_k_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object* v_00_u03b1_1515_, lean_object* v_type_1516_, lean_object* v_k_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1516_, v_k_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_type_1525_, lean_object* v_k_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(v_00_u03b1_1524_, v_type_1525_, v_k_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object* v_kinds_1536_, uint8_t v___x_1537_, lean_object* v_as_1538_, size_t v_sz_1539_, size_t v_i_1540_, lean_object* v_b_1541_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_usize_dec_lt(v_i_1540_, v_sz_1539_);
if (v___x_1542_ == 0)
{
lean_inc_ref(v_b_1541_);
return v_b_1541_;
}
else
{
lean_object* v___x_1543_; lean_object* v_a_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1543_ = lean_box(0);
v_a_1544_ = lean_array_uget_borrowed(v_as_1538_, v_i_1540_);
v___x_1545_ = 0;
v___x_1546_ = lean_box(v___x_1545_);
v___x_1547_ = lean_array_get(v___x_1546_, v_kinds_1536_, v_a_1544_);
lean_dec(v___x_1546_);
v___x_1548_ = lean_unbox(v___x_1547_);
lean_dec(v___x_1547_);
if (v___x_1548_ == 2)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_box(v___x_1537_);
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___x_1543_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; 
v___x_1552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v___x_1553_ = ((size_t)1ULL);
v___x_1554_ = lean_usize_add(v_i_1540_, v___x_1553_);
v_i_1540_ = v___x_1554_;
v_b_1541_ = v___x_1552_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object* v_kinds_1556_, lean_object* v___x_1557_, lean_object* v_as_1558_, lean_object* v_sz_1559_, lean_object* v_i_1560_, lean_object* v_b_1561_){
_start:
{
uint8_t v___x_663__boxed_1562_; size_t v_sz_boxed_1563_; size_t v_i_boxed_1564_; lean_object* v_res_1565_; 
v___x_663__boxed_1562_ = lean_unbox(v___x_1557_);
v_sz_boxed_1563_ = lean_unbox_usize(v_sz_1559_);
lean_dec(v_sz_1559_);
v_i_boxed_1564_ = lean_unbox_usize(v_i_1560_);
lean_dec(v_i_1560_);
v_res_1565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1556_, v___x_663__boxed_1562_, v_as_1558_, v_sz_boxed_1563_, v_i_boxed_1564_, v_b_1561_);
lean_dec_ref(v_b_1561_);
lean_dec_ref(v_as_1558_);
lean_dec_ref(v_kinds_1556_);
return v_res_1565_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object* v_info_1566_, lean_object* v_kinds_1567_, lean_object* v_i_1568_){
_start:
{
lean_object* v_paramInfo_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v_isDecInst_1572_; 
v_paramInfo_1569_ = lean_ctor_get(v_info_1566_, 0);
v___x_1570_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_1571_ = lean_array_get_borrowed(v___x_1570_, v_paramInfo_1569_, v_i_1568_);
v_isDecInst_1572_ = lean_ctor_get_uint8(v___x_1571_, sizeof(void*)*1 + 3);
if (v_isDecInst_1572_ == 0)
{
return v_isDecInst_1572_;
}
else
{
lean_object* v_backDeps_1573_; lean_object* v___x_1574_; size_t v_sz_1575_; size_t v___x_1576_; lean_object* v___x_1577_; lean_object* v_fst_1578_; 
v_backDeps_1573_ = lean_ctor_get(v___x_1571_, 0);
v___x_1574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v_sz_1575_ = lean_array_size(v_backDeps_1573_);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1567_, v_isDecInst_1572_, v_backDeps_1573_, v_sz_1575_, v___x_1576_, v___x_1574_);
v_fst_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_fst_1578_);
lean_dec_ref(v___x_1577_);
if (lean_obj_tag(v_fst_1578_) == 0)
{
uint8_t v___x_1579_; 
v___x_1579_ = 0;
return v___x_1579_;
}
else
{
lean_object* v_val_1580_; uint8_t v___x_1581_; 
v_val_1580_ = lean_ctor_get(v_fst_1578_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v_fst_1578_, 1);
v___x_1581_ = lean_unbox(v_val_1580_);
lean_dec(v_val_1580_);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object* v_info_1582_, lean_object* v_kinds_1583_, lean_object* v_i_1584_){
_start:
{
uint8_t v_res_1585_; lean_object* v_r_1586_; 
v_res_1585_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_1582_, v_kinds_1583_, v_i_1584_);
lean_dec(v_i_1584_);
lean_dec_ref(v_kinds_1583_);
lean_dec_ref(v_info_1582_);
v_r_1586_ = lean_box(v_res_1585_);
return v_r_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(lean_object* v_type_1587_, lean_object* v_k_1588_, uint8_t v_cleanupAnnotations_1589_, uint8_t v_whnfType_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; 
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1596_, 0, v_k_1588_);
v___x_1597_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1587_, v___f_1596_, v_cleanupAnnotations_1589_, v_whnfType_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_a_1606_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1597_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1597_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(lean_object* v_type_1614_, lean_object* v_k_1615_, lean_object* v_cleanupAnnotations_1616_, lean_object* v_whnfType_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1623_; uint8_t v_whnfType_boxed_1624_; lean_object* v_res_1625_; 
v_cleanupAnnotations_boxed_1623_ = lean_unbox(v_cleanupAnnotations_1616_);
v_whnfType_boxed_1624_ = lean_unbox(v_whnfType_1617_);
v_res_1625_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1614_, v_k_1615_, v_cleanupAnnotations_boxed_1623_, v_whnfType_boxed_1624_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_object* v_00_u03b1_1626_, lean_object* v_type_1627_, lean_object* v_k_1628_, uint8_t v_cleanupAnnotations_1629_, uint8_t v_whnfType_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1627_, v_k_1628_, v_cleanupAnnotations_1629_, v_whnfType_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(lean_object* v_00_u03b1_1637_, lean_object* v_type_1638_, lean_object* v_k_1639_, lean_object* v_cleanupAnnotations_1640_, lean_object* v_whnfType_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1647_; uint8_t v_whnfType_boxed_1648_; lean_object* v_res_1649_; 
v_cleanupAnnotations_boxed_1647_ = lean_unbox(v_cleanupAnnotations_1640_);
v_whnfType_boxed_1648_ = lean_unbox(v_whnfType_1641_);
v_res_1649_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(v_00_u03b1_1637_, v_type_1638_, v_k_1639_, v_cleanupAnnotations_boxed_1647_, v_whnfType_boxed_1648_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(lean_object* v_upperBound_1650_, lean_object* v_val_1651_, lean_object* v_xs_1652_, lean_object* v___x_1653_, lean_object* v___x_1654_, uint8_t v___x_1655_, lean_object* v_a_1656_, lean_object* v_b_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_a_1663_; uint8_t v___x_1667_; 
v___x_1667_ = lean_nat_dec_lt(v_a_1656_, v_upperBound_1650_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; 
lean_dec(v_a_1656_);
lean_dec(v___x_1654_);
lean_dec_ref(v___x_1653_);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_b_1657_);
return v___x_1668_;
}
else
{
lean_object* v_numParams_1669_; uint8_t v___x_1670_; 
v_numParams_1669_ = lean_ctor_get(v_val_1651_, 3);
v___x_1670_ = lean_nat_dec_lt(v_a_1656_, v_numParams_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = lean_array_fget_borrowed(v_xs_1652_, v_a_1656_);
v___x_1672_ = l_Lean_Expr_fvarId_x21(v___x_1671_);
v___x_1673_ = l_Lean_FVarId_getDecl___redArg(v___x_1672_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; uint8_t v___y_1676_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1679_ = l_Lean_LocalDecl_userName(v_a_1674_);
lean_dec(v_a_1674_);
lean_inc(v___x_1654_);
lean_inc_ref(v___x_1653_);
v___x_1680_ = l_Lean_isSubobjectField_x3f(v___x_1653_, v___x_1654_, v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 0)
{
v___y_1676_ = v___x_1670_;
goto v___jp_1675_;
}
else
{
lean_dec_ref_known(v___x_1680_, 1);
v___y_1676_ = v___x_1655_;
goto v___jp_1675_;
}
v___jp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_box(v___y_1676_);
v___x_1678_ = lean_array_push(v_b_1657_, v___x_1677_);
v_a_1663_ = v___x_1678_;
goto v___jp_1662_;
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_b_1657_);
lean_dec(v_a_1656_);
lean_dec(v___x_1654_);
lean_dec_ref(v___x_1653_);
v_a_1681_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1673_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1673_);
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
uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = 0;
v___x_1690_ = lean_box(v___x_1689_);
v___x_1691_ = lean_array_push(v_b_1657_, v___x_1690_);
v_a_1663_ = v___x_1691_;
goto v___jp_1662_;
}
}
v___jp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_nat_add(v_a_1656_, v___x_1664_);
lean_dec(v_a_1656_);
v_a_1656_ = v___x_1665_;
v_b_1657_ = v_a_1663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_1692_, lean_object* v_val_1693_, lean_object* v_xs_1694_, lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v___x_1697_, lean_object* v_a_1698_, lean_object* v_b_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v___x_5663__boxed_1704_; lean_object* v_res_1705_; 
v___x_5663__boxed_1704_ = lean_unbox(v___x_1697_);
v_res_1705_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1692_, v_val_1693_, v_xs_1694_, v___x_1695_, v___x_1696_, v___x_5663__boxed_1704_, v_a_1698_, v_b_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v_xs_1694_);
lean_dec_ref(v_val_1693_);
lean_dec(v_upperBound_1692_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object* v_val_1708_, lean_object* v_induct_1709_, uint8_t v___x_1710_, lean_object* v_xs_1711_, lean_object* v_x_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v_env_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1718_ = lean_st_ref_get(v___y_1716_);
v_env_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc_ref(v_env_1719_);
lean_dec(v___x_1718_);
v___x_1720_ = lean_array_get_size(v_xs_1711_);
v___x_1721_ = lean_unsigned_to_nat(0u);
v___x_1722_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0));
v___x_1723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v___x_1720_, v_val_1708_, v_xs_1711_, v_env_1719_, v_induct_1709_, v___x_1710_, v___x_1721_, v___x_1722_, v___y_1713_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1732_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_a_1724_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1728_);
v___x_1730_ = v___x_1726_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_a_1733_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1723_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1723_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object* v_val_1741_, lean_object* v_induct_1742_, lean_object* v___x_1743_, lean_object* v_xs_1744_, lean_object* v_x_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_5750__boxed_1751_; lean_object* v_res_1752_; 
v___x_5750__boxed_1751_ = lean_unbox(v___x_1743_);
v_res_1752_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1741_, v_induct_1742_, v___x_5750__boxed_1751_, v_xs_1744_, v_x_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v_x_1745_);
lean_dec_ref(v_xs_1744_);
lean_dec_ref(v_val_1741_);
return v_res_1752_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
lean_ctor_set(v___x_1758_, 2, v___x_1757_);
lean_ctor_set(v___x_1758_, 3, v___x_1757_);
lean_ctor_set(v___x_1758_, 4, v___x_1756_);
lean_ctor_set(v___x_1758_, 5, v___x_1756_);
lean_ctor_set(v___x_1758_, 6, v___x_1756_);
lean_ctor_set(v___x_1758_, 7, v___x_1756_);
lean_ctor_set(v___x_1758_, 8, v___x_1756_);
lean_ctor_set(v___x_1758_, 9, v___x_1756_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = lean_unsigned_to_nat(32u);
v___x_1760_ = lean_mk_empty_array_with_capacity(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1762_ = ((size_t)5ULL);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_unsigned_to_nat(32u);
v___x_1765_ = lean_mk_empty_array_with_capacity(v___x_1764_);
v___x_1766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1767_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v___x_1765_);
lean_ctor_set(v___x_1767_, 2, v___x_1763_);
lean_ctor_set(v___x_1767_, 3, v___x_1763_);
lean_ctor_set_usize(v___x_1767_, 4, v___x_1762_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1768_ = lean_box(1);
v___x_1769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1769_);
lean_ctor_set(v___x_1771_, 2, v___x_1768_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
return v___x_1774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1777_ = l_Lean_stringToMessageData(v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1780_ = l_Lean_stringToMessageData(v___x_1779_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1793_, lean_object* v_declHint_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v_env_1798_; uint8_t v___x_1799_; 
v___x_1797_ = lean_st_ref_get(v___y_1795_);
v_env_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc_ref(v_env_1798_);
lean_dec(v___x_1797_);
v___x_1799_ = l_Lean_Name_isAnonymous(v_declHint_1794_);
if (v___x_1799_ == 0)
{
uint8_t v_isExporting_1800_; 
v_isExporting_1800_ = lean_ctor_get_uint8(v_env_1798_, sizeof(void*)*8);
if (v_isExporting_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref(v_env_1798_);
lean_dec(v_declHint_1794_);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_msg_1793_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
lean_inc_ref(v_env_1798_);
v___x_1802_ = l_Lean_Environment_setExporting(v_env_1798_, v___x_1799_);
lean_inc(v_declHint_1794_);
lean_inc_ref(v___x_1802_);
v___x_1803_ = l_Lean_Environment_contains(v___x_1802_, v_declHint_1794_, v_isExporting_1800_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v___x_1802_);
lean_dec_ref(v_env_1798_);
lean_dec(v_declHint_1794_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_msg_1793_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_c_1810_; lean_object* v___x_1811_; 
v___x_1805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1806_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1807_ = l_Lean_Options_empty;
v___x_1808_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1802_);
lean_ctor_set(v___x_1808_, 1, v___x_1805_);
lean_ctor_set(v___x_1808_, 2, v___x_1806_);
lean_ctor_set(v___x_1808_, 3, v___x_1807_);
lean_inc(v_declHint_1794_);
v___x_1809_ = l_Lean_MessageData_ofConstName(v_declHint_1794_, v___x_1799_);
v_c_1810_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1810_, 0, v___x_1808_);
lean_ctor_set(v_c_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1798_, v_declHint_1794_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec_ref(v_env_1798_);
lean_dec(v_declHint_1794_);
v___x_1812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v_c_1810_);
v___x_1814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = l_Lean_MessageData_note(v___x_1815_);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_msg_1793_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
else
{
lean_object* v_val_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1854_; 
v_val_1819_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1821_ = v___x_1811_;
v_isShared_1822_ = v_isSharedCheck_1854_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_val_1819_);
lean_dec(v___x_1811_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1854_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_mod_1826_; uint8_t v___x_1827_; 
v___x_1823_ = lean_box(0);
v___x_1824_ = l_Lean_Environment_header(v_env_1798_);
lean_dec_ref(v_env_1798_);
v___x_1825_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1824_);
v_mod_1826_ = lean_array_get(v___x_1823_, v___x_1825_, v_val_1819_);
lean_dec(v_val_1819_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = l_Lean_isPrivateName(v_declHint_1794_);
lean_dec(v_declHint_1794_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_c_1810_);
v___x_1830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = l_Lean_MessageData_ofName(v_mod_1826_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_MessageData_note(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_msg_1793_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1837_);
v___x_1839_ = v___x_1821_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_c_1810_);
v___x_1843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_MessageData_ofName(v_mod_1826_);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l_Lean_MessageData_note(v___x_1848_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_msg_1793_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1850_);
v___x_1852_ = v___x_1821_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1855_; 
lean_dec_ref(v_env_1798_);
lean_dec(v_declHint_1794_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_msg_1793_);
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1856_, lean_object* v_declHint_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1856_, v_declHint_1857_, v___y_1858_);
lean_dec(v___y_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msg_1861_, lean_object* v_declHint_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1878_; 
v___x_1868_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1861_, v_declHint_1862_, v___y_1866_);
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1873_ = l_Lean_unknownIdentifierMessageTag;
v___x_1874_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v_a_1869_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1879_, lean_object* v_declHint_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1879_, v_declHint_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1887_, lean_object* v_msg_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_fileName_1894_; lean_object* v_fileMap_1895_; lean_object* v_options_1896_; lean_object* v_currRecDepth_1897_; lean_object* v_maxRecDepth_1898_; lean_object* v_ref_1899_; lean_object* v_currNamespace_1900_; lean_object* v_openDecls_1901_; lean_object* v_initHeartbeats_1902_; lean_object* v_maxHeartbeats_1903_; lean_object* v_quotContext_1904_; lean_object* v_currMacroScope_1905_; uint8_t v_diag_1906_; lean_object* v_cancelTk_x3f_1907_; uint8_t v_suppressElabErrors_1908_; lean_object* v_inheritedTraceOptions_1909_; lean_object* v_ref_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_fileName_1894_ = lean_ctor_get(v___y_1891_, 0);
v_fileMap_1895_ = lean_ctor_get(v___y_1891_, 1);
v_options_1896_ = lean_ctor_get(v___y_1891_, 2);
v_currRecDepth_1897_ = lean_ctor_get(v___y_1891_, 3);
v_maxRecDepth_1898_ = lean_ctor_get(v___y_1891_, 4);
v_ref_1899_ = lean_ctor_get(v___y_1891_, 5);
v_currNamespace_1900_ = lean_ctor_get(v___y_1891_, 6);
v_openDecls_1901_ = lean_ctor_get(v___y_1891_, 7);
v_initHeartbeats_1902_ = lean_ctor_get(v___y_1891_, 8);
v_maxHeartbeats_1903_ = lean_ctor_get(v___y_1891_, 9);
v_quotContext_1904_ = lean_ctor_get(v___y_1891_, 10);
v_currMacroScope_1905_ = lean_ctor_get(v___y_1891_, 11);
v_diag_1906_ = lean_ctor_get_uint8(v___y_1891_, sizeof(void*)*14);
v_cancelTk_x3f_1907_ = lean_ctor_get(v___y_1891_, 12);
v_suppressElabErrors_1908_ = lean_ctor_get_uint8(v___y_1891_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1909_ = lean_ctor_get(v___y_1891_, 13);
v_ref_1910_ = l_Lean_replaceRef(v_ref_1887_, v_ref_1899_);
lean_inc_ref(v_inheritedTraceOptions_1909_);
lean_inc(v_cancelTk_x3f_1907_);
lean_inc(v_currMacroScope_1905_);
lean_inc(v_quotContext_1904_);
lean_inc(v_maxHeartbeats_1903_);
lean_inc(v_initHeartbeats_1902_);
lean_inc(v_openDecls_1901_);
lean_inc(v_currNamespace_1900_);
lean_inc(v_maxRecDepth_1898_);
lean_inc(v_currRecDepth_1897_);
lean_inc_ref(v_options_1896_);
lean_inc_ref(v_fileMap_1895_);
lean_inc_ref(v_fileName_1894_);
v___x_1911_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1911_, 0, v_fileName_1894_);
lean_ctor_set(v___x_1911_, 1, v_fileMap_1895_);
lean_ctor_set(v___x_1911_, 2, v_options_1896_);
lean_ctor_set(v___x_1911_, 3, v_currRecDepth_1897_);
lean_ctor_set(v___x_1911_, 4, v_maxRecDepth_1898_);
lean_ctor_set(v___x_1911_, 5, v_ref_1910_);
lean_ctor_set(v___x_1911_, 6, v_currNamespace_1900_);
lean_ctor_set(v___x_1911_, 7, v_openDecls_1901_);
lean_ctor_set(v___x_1911_, 8, v_initHeartbeats_1902_);
lean_ctor_set(v___x_1911_, 9, v_maxHeartbeats_1903_);
lean_ctor_set(v___x_1911_, 10, v_quotContext_1904_);
lean_ctor_set(v___x_1911_, 11, v_currMacroScope_1905_);
lean_ctor_set(v___x_1911_, 12, v_cancelTk_x3f_1907_);
lean_ctor_set(v___x_1911_, 13, v_inheritedTraceOptions_1909_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*14, v_diag_1906_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*14 + 1, v_suppressElabErrors_1908_);
v___x_1912_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1888_, v___y_1889_, v___y_1890_, v___x_1911_, v___y_1892_);
lean_dec_ref_known(v___x_1911_, 14);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1913_, lean_object* v_msg_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1913_, v_msg_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v_ref_1913_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1921_, lean_object* v_msg_1922_, lean_object* v_declHint_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; lean_object* v_a_1930_; lean_object* v___x_1931_; 
v___x_1929_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1922_, v_declHint_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1929_);
v___x_1931_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1921_, v_a_1930_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1932_, lean_object* v_msg_1933_, lean_object* v_declHint_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1932_, v_msg_1933_, v_declHint_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v_ref_1932_);
return v_res_1940_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
return v___x_1943_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1946_ = l_Lean_stringToMessageData(v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1947_, lean_object* v_constName_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1954_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1955_ = 0;
lean_inc(v_constName_1948_);
v___x_1956_ = l_Lean_MessageData_ofConstName(v_constName_1948_, v___x_1955_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1954_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1947_, v___x_1959_, v_constName_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1961_, lean_object* v_constName_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1961_, v_constName_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v_ref_1961_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_ref_1975_; lean_object* v___x_1976_; 
v_ref_1975_ = lean_ctor_get(v___y_1972_, 5);
v___x_1976_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1975_, v_constName_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v_env_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; 
v___x_1990_ = lean_st_ref_get(v___y_1988_);
v_env_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_ref(v_env_1991_);
lean_dec(v___x_1990_);
v___x_1992_ = 0;
lean_inc(v_constName_1984_);
v___x_1993_ = l_Lean_Environment_find_x3f(v_env_1991_, v_constName_1984_, v___x_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1994_;
}
else
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec(v_constName_1984_);
v_val_1995_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1993_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v___x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 0);
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_val_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
if (lean_obj_tag(v_f_2010_) == 4)
{
lean_object* v_declName_2016_; lean_object* v___x_2017_; 
v_declName_2016_ = lean_ctor_get(v_f_2010_, 0);
lean_inc(v_declName_2016_);
lean_dec_ref_known(v_f_2010_, 2);
v___x_2017_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2016_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2041_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2041_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2041_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
if (lean_obj_tag(v_a_2018_) == 6)
{
lean_object* v_val_2022_; lean_object* v___x_2023_; lean_object* v_env_2024_; lean_object* v_toConstantVal_2025_; lean_object* v_induct_2026_; uint8_t v___x_2027_; 
v_val_2022_ = lean_ctor_get(v_a_2018_, 0);
lean_inc_ref(v_val_2022_);
lean_dec_ref_known(v_a_2018_, 1);
v___x_2023_ = lean_st_ref_get(v_a_2014_);
v_env_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc_ref(v_env_2024_);
lean_dec(v___x_2023_);
v_toConstantVal_2025_ = lean_ctor_get(v_val_2022_, 0);
v_induct_2026_ = lean_ctor_get(v_val_2022_, 1);
lean_inc(v_induct_2026_);
v___x_2027_ = l_Lean_isClass(v_env_2024_, v_induct_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec(v_induct_2026_);
lean_dec_ref(v_val_2022_);
v___x_2028_ = lean_box(0);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2028_);
v___x_2030_ = v___x_2020_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
else
{
lean_object* v_type_2032_; lean_object* v___x_2033_; lean_object* v___f_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; 
lean_del_object(v___x_2020_);
v_type_2032_ = lean_ctor_get(v_toConstantVal_2025_, 2);
lean_inc_ref(v_type_2032_);
v___x_2033_ = lean_box(v___x_2027_);
v___f_2034_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2034_, 0, v_val_2022_);
lean_closure_set(v___f_2034_, 1, v_induct_2026_);
lean_closure_set(v___f_2034_, 2, v___x_2033_);
v___x_2035_ = 0;
v___x_2036_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2032_, v___f_2034_, v___x_2027_, v___x_2035_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2036_;
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v_a_2018_);
v___x_2037_ = lean_box(0);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2037_);
v___x_2039_ = v___x_2020_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
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
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
v_a_2042_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2017_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2017_);
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
lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec_ref(v_f_2010_);
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2059_, lean_object* v_val_2060_, lean_object* v_xs_2061_, lean_object* v___x_2062_, lean_object* v___x_2063_, uint8_t v___x_2064_, lean_object* v_inst_2065_, lean_object* v_R_2066_, lean_object* v_a_2067_, lean_object* v_b_2068_, lean_object* v_c_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2059_, v_val_2060_, v_xs_2061_, v___x_2062_, v___x_2063_, v___x_2064_, v_a_2067_, v_b_2068_, v___y_2070_, v___y_2072_, v___y_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2076_, lean_object* v_val_2077_, lean_object* v_xs_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v___x_2081_, lean_object* v_inst_2082_, lean_object* v_R_2083_, lean_object* v_a_2084_, lean_object* v_b_2085_, lean_object* v_c_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v___x_6330__boxed_2092_; lean_object* v_res_2093_; 
v___x_6330__boxed_2092_ = lean_unbox(v___x_2081_);
v_res_2093_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2076_, v_val_2077_, v_xs_2078_, v___x_2079_, v___x_2080_, v___x_6330__boxed_2092_, v_inst_2082_, v_R_2083_, v_a_2084_, v_b_2085_, v_c_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_xs_2078_);
lean_dec_ref(v_val_2077_);
lean_dec(v_upperBound_2076_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2094_, lean_object* v_constName_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2102_, lean_object* v_constName_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2102_, v_constName_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2110_, lean_object* v_ref_2111_, lean_object* v_constName_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2111_, v_constName_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2119_, lean_object* v_ref_2120_, lean_object* v_constName_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2119_, v_ref_2120_, v_constName_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v_ref_2120_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2128_, lean_object* v_ref_2129_, lean_object* v_msg_2130_, lean_object* v_declHint_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2129_, v_msg_2130_, v_declHint_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_ref_2139_, lean_object* v_msg_2140_, lean_object* v_declHint_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2138_, v_ref_2139_, v_msg_2140_, v_declHint_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v_ref_2139_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2148_, lean_object* v_declHint_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2148_, v_declHint_2149_, v___y_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2156_, lean_object* v_declHint_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2156_, v_declHint_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2164_, lean_object* v_ref_2165_, lean_object* v_msg_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2165_, v_msg_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2173_, lean_object* v_ref_2174_, lean_object* v_msg_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2173_, v_ref_2174_, v_msg_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v_ref_2174_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2182_, lean_object* v_a_2183_, lean_object* v_____r_2184_, lean_object* v_result_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2182_, v_result_2185_, v_a_2183_);
if (v___x_2191_ == 0)
{
uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2192_ = 0;
v___x_2193_ = lean_box(v___x_2192_);
v___x_2194_ = lean_array_push(v_result_2185_, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
else
{
uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2197_ = 5;
v___x_2198_ = lean_box(v___x_2197_);
v___x_2199_ = lean_array_push(v_result_2185_, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2202_, lean_object* v_a_2203_, lean_object* v_____r_2204_, lean_object* v_result_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2202_, v_a_2203_, v_____r_2204_, v_result_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v_a_2203_);
lean_dec_ref(v_info_2202_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2212_, lean_object* v_upperBound_2213_, lean_object* v___x_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_b_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_a_2224_; lean_object* v___y_2229_; uint8_t v___x_2248_; 
v___x_2248_ = lean_nat_dec_lt(v_a_2216_, v_upperBound_2213_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_dec(v_a_2216_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_b_2217_);
return v___x_2249_;
}
else
{
lean_object* v_resultDeps_2250_; uint8_t v___x_2251_; 
v_resultDeps_2250_ = lean_ctor_get(v_info_2212_, 1);
v___x_2251_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2250_, v_a_2216_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; uint8_t v_isProp_2253_; 
v___x_2252_ = lean_array_fget_borrowed(v___x_2214_, v_a_2216_);
v_isProp_2253_ = lean_ctor_get_uint8(v___x_2252_, sizeof(void*)*1 + 2);
if (v_isProp_2253_ == 0)
{
uint8_t v_isInstance_2254_; 
v_isInstance_2254_ = lean_ctor_get_uint8(v___x_2252_, sizeof(void*)*1 + 4);
if (v_isInstance_2254_ == 0)
{
uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = 2;
v___x_2256_ = lean_box(v___x_2255_);
v___x_2257_ = lean_array_push(v_b_2217_, v___x_2256_);
v_a_2224_ = v___x_2257_;
goto v___jp_2223_;
}
else
{
if (lean_obj_tag(v_a_2215_) == 1)
{
lean_object* v_val_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v_val_2258_ = lean_ctor_get(v_a_2215_, 0);
v___x_2259_ = lean_array_get_size(v_val_2258_);
v___x_2260_ = lean_nat_dec_lt(v_a_2216_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_box(0);
v___x_2262_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2212_, v_a_2216_, v___x_2261_, v_b_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2262_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = lean_array_fget_borrowed(v_val_2258_, v_a_2216_);
v___x_2264_ = lean_unbox(v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_box(0);
v___x_2266_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2212_, v_a_2216_, v___x_2265_, v_b_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2266_;
goto v___jp_2228_;
}
else
{
uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = 2;
v___x_2268_ = lean_box(v___x_2267_);
v___x_2269_ = lean_array_push(v_b_2217_, v___x_2268_);
v_a_2224_ = v___x_2269_;
goto v___jp_2223_;
}
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_box(0);
v___x_2271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2212_, v_a_2216_, v___x_2270_, v_b_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2271_;
goto v___jp_2228_;
}
}
}
else
{
uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = 3;
v___x_2273_ = lean_box(v___x_2272_);
v___x_2274_ = lean_array_push(v_b_2217_, v___x_2273_);
v_a_2224_ = v___x_2274_;
goto v___jp_2223_;
}
}
else
{
uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = 0;
v___x_2276_ = lean_box(v___x_2275_);
v___x_2277_ = lean_array_push(v_b_2217_, v___x_2276_);
v_a_2224_ = v___x_2277_;
goto v___jp_2223_;
}
}
v___jp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_unsigned_to_nat(1u);
v___x_2226_ = lean_nat_add(v_a_2216_, v___x_2225_);
lean_dec(v_a_2216_);
v_a_2216_ = v___x_2226_;
v_b_2217_ = v_a_2224_;
goto _start;
}
v___jp_2228_:
{
if (lean_obj_tag(v___y_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2239_; 
v_a_2230_ = lean_ctor_get(v___y_2229_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___y_2229_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2232_ = v___y_2229_;
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___y_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
if (lean_obj_tag(v_a_2230_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; 
lean_dec(v_a_2216_);
v_a_2234_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v_a_2230_, 1);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_a_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v_a_2238_; 
lean_del_object(v___x_2232_);
v_a_2238_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v_a_2230_, 1);
v_a_2224_ = v_a_2238_;
goto v___jp_2223_;
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_a_2216_);
v_a_2240_ = lean_ctor_get(v___y_2229_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___y_2229_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___y_2229_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___y_2229_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2278_, lean_object* v_upperBound_2279_, lean_object* v___x_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_b_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2278_, v_upperBound_2279_, v___x_2280_, v_a_2281_, v_a_2282_, v_b_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v_a_2281_);
lean_dec_ref(v___x_2280_);
lean_dec(v_upperBound_2279_);
lean_dec_ref(v_info_2278_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2292_, lean_object* v_info_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2292_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v_paramInfo_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v_result_2304_; lean_object* v___x_2305_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v_paramInfo_2301_ = lean_ctor_get(v_info_2293_, 0);
v___x_2302_ = lean_array_get_size(v_paramInfo_2301_);
v___x_2303_ = lean_unsigned_to_nat(0u);
v_result_2304_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2305_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2293_, v___x_2302_, v_paramInfo_2301_, v_a_2300_, v___x_2303_, v_result_2304_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2300_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2314_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2314_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2314_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2310_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2293_, v_a_2306_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2310_);
v___x_2312_ = v___x_2308_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
else
{
return v___x_2305_;
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v_a_2315_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2299_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2299_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2323_, lean_object* v_info_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Meta_getCongrSimpKinds(v_f_2323_, v_info_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec_ref(v_info_2324_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2331_, lean_object* v_upperBound_2332_, lean_object* v___x_2333_, lean_object* v_a_2334_, lean_object* v_inst_2335_, lean_object* v_R_2336_, lean_object* v_a_2337_, lean_object* v_b_2338_, lean_object* v_c_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2331_, v_upperBound_2332_, v___x_2333_, v_a_2334_, v_a_2337_, v_b_2338_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2346_, lean_object* v_upperBound_2347_, lean_object* v___x_2348_, lean_object* v_a_2349_, lean_object* v_inst_2350_, lean_object* v_R_2351_, lean_object* v_a_2352_, lean_object* v_b_2353_, lean_object* v_c_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2346_, v_upperBound_2347_, v___x_2348_, v_a_2349_, v_inst_2350_, v_R_2351_, v_a_2352_, v_b_2353_, v_c_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v_a_2349_);
lean_dec_ref(v___x_2348_);
lean_dec(v_upperBound_2347_);
lean_dec_ref(v_info_2346_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2361_, lean_object* v_info_2362_, lean_object* v___x_2363_, lean_object* v_a_2364_, lean_object* v_b_2365_){
_start:
{
lean_object* v_a_2368_; uint8_t v___x_2372_; 
v___x_2372_ = lean_nat_dec_lt(v_a_2364_, v_upperBound_2361_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; 
lean_dec(v_a_2364_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v_b_2365_);
return v___x_2373_;
}
else
{
lean_object* v_resultDeps_2374_; uint8_t v___x_2375_; 
v_resultDeps_2374_ = lean_ctor_get(v_info_2362_, 1);
v___x_2375_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2374_, v_a_2364_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = lean_nat_dec_eq(v_a_2364_, v___x_2376_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; uint8_t v_isProp_2379_; 
v___x_2378_ = lean_array_fget_borrowed(v___x_2363_, v_a_2364_);
v_isProp_2379_ = lean_ctor_get_uint8(v___x_2378_, sizeof(void*)*1 + 2);
if (v_isProp_2379_ == 0)
{
uint8_t v_isInstance_2380_; 
v_isInstance_2380_ = lean_ctor_get_uint8(v___x_2378_, sizeof(void*)*1 + 4);
if (v_isInstance_2380_ == 0)
{
uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = 0;
v___x_2382_ = lean_box(v___x_2381_);
v___x_2383_ = lean_array_push(v_b_2365_, v___x_2382_);
v_a_2368_ = v___x_2383_;
goto v___jp_2367_;
}
else
{
uint8_t v___x_2384_; 
v___x_2384_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2362_, v_b_2365_, v_a_2364_);
if (v___x_2384_ == 0)
{
uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = 0;
v___x_2386_ = lean_box(v___x_2385_);
v___x_2387_ = lean_array_push(v_b_2365_, v___x_2386_);
v_a_2368_ = v___x_2387_;
goto v___jp_2367_;
}
else
{
uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = 5;
v___x_2389_ = lean_box(v___x_2388_);
v___x_2390_ = lean_array_push(v_b_2365_, v___x_2389_);
v_a_2368_ = v___x_2390_;
goto v___jp_2367_;
}
}
}
else
{
uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = 3;
v___x_2392_ = lean_box(v___x_2391_);
v___x_2393_ = lean_array_push(v_b_2365_, v___x_2392_);
v_a_2368_ = v___x_2393_;
goto v___jp_2367_;
}
}
else
{
uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = 2;
v___x_2395_ = lean_box(v___x_2394_);
v___x_2396_ = lean_array_push(v_b_2365_, v___x_2395_);
v_a_2368_ = v___x_2396_;
goto v___jp_2367_;
}
}
else
{
uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = 0;
v___x_2398_ = lean_box(v___x_2397_);
v___x_2399_ = lean_array_push(v_b_2365_, v___x_2398_);
v_a_2368_ = v___x_2399_;
goto v___jp_2367_;
}
}
v___jp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_a_2364_, v___x_2369_);
lean_dec(v_a_2364_);
v_a_2364_ = v___x_2370_;
v_b_2365_ = v_a_2368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2400_, lean_object* v_info_2401_, lean_object* v___x_2402_, lean_object* v_a_2403_, lean_object* v_b_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2400_, v_info_2401_, v___x_2402_, v_a_2403_, v_b_2404_);
lean_dec_ref(v___x_2402_);
lean_dec_ref(v_info_2401_);
lean_dec(v_upperBound_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_paramInfo_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_result_2416_; lean_object* v___x_2417_; 
v_paramInfo_2413_ = lean_ctor_get(v_info_2407_, 0);
v___x_2414_ = lean_array_get_size(v_paramInfo_2413_);
v___x_2415_ = lean_unsigned_to_nat(0u);
v_result_2416_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2417_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2414_, v_info_2407_, v_paramInfo_2413_, v___x_2415_, v_result_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2407_, v_a_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
else
{
return v___x_2417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec_ref(v_info_2427_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2434_, lean_object* v_info_2435_, lean_object* v___x_2436_, lean_object* v_inst_2437_, lean_object* v_R_2438_, lean_object* v_a_2439_, lean_object* v_b_2440_, lean_object* v_c_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2434_, v_info_2435_, v___x_2436_, v_a_2439_, v_b_2440_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2448_, lean_object* v_info_2449_, lean_object* v___x_2450_, lean_object* v_inst_2451_, lean_object* v_R_2452_, lean_object* v_a_2453_, lean_object* v_b_2454_, lean_object* v_c_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2448_, v_info_2449_, v___x_2450_, v_inst_2451_, v_R_2452_, v_a_2453_, v_b_2454_, v_c_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec_ref(v___x_2450_);
lean_dec_ref(v_info_2449_);
lean_dec(v_upperBound_2448_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(lean_object* v_x_2462_){
_start:
{
if (lean_obj_tag(v_x_2462_) == 0)
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_unsigned_to_nat(0u);
return v___x_2463_;
}
else
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_unsigned_to_nat(1u);
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___boxed(lean_object* v_x_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(v_x_2465_);
lean_dec_ref(v_x_2465_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2467_, lean_object* v_k_2468_){
_start:
{
if (lean_obj_tag(v_t_2467_) == 0)
{
lean_object* v_fvarId_2469_; lean_object* v___x_2470_; 
v_fvarId_2469_ = lean_ctor_get(v_t_2467_, 0);
lean_inc(v_fvarId_2469_);
lean_dec_ref_known(v_t_2467_, 1);
v___x_2470_ = lean_apply_1(v_k_2468_, v_fvarId_2469_);
return v___x_2470_;
}
else
{
lean_object* v_lhs_2471_; lean_object* v_rhs_2472_; lean_object* v___x_2473_; 
v_lhs_2471_ = lean_ctor_get(v_t_2467_, 0);
lean_inc(v_lhs_2471_);
v_rhs_2472_ = lean_ctor_get(v_t_2467_, 1);
lean_inc(v_rhs_2472_);
lean_dec_ref_known(v_t_2467_, 2);
v___x_2473_ = lean_apply_2(v_k_2468_, v_lhs_2471_, v_rhs_2472_);
return v___x_2473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2474_, lean_object* v_ctorIdx_2475_, lean_object* v_t_2476_, lean_object* v_h_2477_, lean_object* v_k_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2476_, v_k_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2480_, lean_object* v_ctorIdx_2481_, lean_object* v_t_2482_, lean_object* v_h_2483_, lean_object* v_k_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2480_, v_ctorIdx_2481_, v_t_2482_, v_h_2483_, v_k_2484_);
lean_dec(v_ctorIdx_2481_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2486_, lean_object* v_hyp_2487_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2486_, v_hyp_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2489_, lean_object* v_t_2490_, lean_object* v_h_2491_, lean_object* v_hyp_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2490_, v_hyp_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2494_, lean_object* v_decSubsingleton_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2494_, v_decSubsingleton_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2497_, lean_object* v_t_2498_, lean_object* v_h_2499_, lean_object* v_decSubsingleton_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2498_, v_decSubsingleton_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2502_, lean_object* v_fvarId_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2502_, v_fvarId_2503_);
if (lean_obj_tag(v___x_2504_) == 1)
{
lean_object* v_val_2505_; lean_object* v___x_2506_; 
v_val_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_val_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = l_Lean_Expr_fvarId_x21(v_val_2505_);
lean_dec(v_val_2505_);
return v___x_2506_;
}
else
{
lean_dec(v___x_2504_);
lean_inc(v_fvarId_2503_);
return v_fvarId_2503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2507_, lean_object* v_fvarId_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2507_, v_fvarId_2508_);
lean_dec(v_fvarId_2508_);
lean_dec(v_s_2507_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2510_, v_x_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2517_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2534_, v_x_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2542_, lean_object* v_mvarId_2543_, lean_object* v_x_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2543_, v_x_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_mvarId_2552_, lean_object* v_x_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2551_, v_mvarId_2552_, v_x_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2560_, lean_object* v___y_2561_){
_start:
{
uint8_t v___x_2563_; 
v___x_2563_ = l_Lean_Expr_hasMVar(v_e_2560_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_e_2560_);
return v___x_2564_;
}
else
{
lean_object* v___x_2565_; lean_object* v_mctx_2566_; lean_object* v___x_2567_; lean_object* v_fst_2568_; lean_object* v_snd_2569_; lean_object* v___x_2570_; lean_object* v_cache_2571_; lean_object* v_zetaDeltaFVarIds_2572_; lean_object* v_postponed_2573_; lean_object* v_diag_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2583_; 
v___x_2565_ = lean_st_ref_get(v___y_2561_);
v_mctx_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc_ref(v_mctx_2566_);
lean_dec(v___x_2565_);
v___x_2567_ = l_Lean_instantiateMVarsCore(v_mctx_2566_, v_e_2560_);
v_fst_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_fst_2568_);
v_snd_2569_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_snd_2569_);
lean_dec_ref(v___x_2567_);
v___x_2570_ = lean_st_ref_take(v___y_2561_);
v_cache_2571_ = lean_ctor_get(v___x_2570_, 1);
v_zetaDeltaFVarIds_2572_ = lean_ctor_get(v___x_2570_, 2);
v_postponed_2573_ = lean_ctor_get(v___x_2570_, 3);
v_diag_2574_ = lean_ctor_get(v___x_2570_, 4);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; 
v_unused_2584_ = lean_ctor_get(v___x_2570_, 0);
lean_dec(v_unused_2584_);
v___x_2576_ = v___x_2570_;
v_isShared_2577_ = v_isSharedCheck_2583_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_diag_2574_);
lean_inc(v_postponed_2573_);
lean_inc(v_zetaDeltaFVarIds_2572_);
lean_inc(v_cache_2571_);
lean_dec(v___x_2570_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2583_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_snd_2569_);
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_snd_2569_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_cache_2571_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_zetaDeltaFVarIds_2572_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_postponed_2573_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_diag_2574_);
v___x_2579_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_st_ref_set(v___y_2561_, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_fst_2568_);
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2585_, v___y_2586_);
lean_dec(v___y_2586_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2589_, v___y_2591_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2603_, lean_object* v_x_2604_, lean_object* v_x_2605_, lean_object* v_x_2606_){
_start:
{
lean_object* v_ks_2607_; lean_object* v_vs_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2632_; 
v_ks_2607_ = lean_ctor_get(v_x_2603_, 0);
v_vs_2608_ = lean_ctor_get(v_x_2603_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_x_2603_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2610_ = v_x_2603_;
v_isShared_2611_ = v_isSharedCheck_2632_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_vs_2608_);
lean_inc(v_ks_2607_);
lean_dec(v_x_2603_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2632_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = lean_array_get_size(v_ks_2607_);
v___x_2613_ = lean_nat_dec_lt(v_x_2604_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
lean_dec(v_x_2604_);
v___x_2614_ = lean_array_push(v_ks_2607_, v_x_2605_);
v___x_2615_ = lean_array_push(v_vs_2608_, v_x_2606_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 1, v___x_2615_);
lean_ctor_set(v___x_2610_, 0, v___x_2614_);
v___x_2617_ = v___x_2610_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
else
{
lean_object* v_k_x27_2619_; uint8_t v___x_2620_; 
v_k_x27_2619_ = lean_array_fget_borrowed(v_ks_2607_, v_x_2604_);
v___x_2620_ = l_Lean_instBEqMVarId_beq(v_x_2605_, v_k_x27_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2622_; 
if (v_isShared_2611_ == 0)
{
v___x_2622_ = v___x_2610_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_ks_2607_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_vs_2608_);
v___x_2622_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_unsigned_to_nat(1u);
v___x_2624_ = lean_nat_add(v_x_2604_, v___x_2623_);
lean_dec(v_x_2604_);
v_x_2603_ = v___x_2622_;
v_x_2604_ = v___x_2624_;
goto _start;
}
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2627_ = lean_array_fset(v_ks_2607_, v_x_2604_, v_x_2605_);
v___x_2628_ = lean_array_fset(v_vs_2608_, v_x_2604_, v_x_2606_);
lean_dec(v_x_2604_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 1, v___x_2628_);
lean_ctor_set(v___x_2610_, 0, v___x_2627_);
v___x_2630_ = v___x_2610_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2633_, lean_object* v_k_2634_, lean_object* v_v_2635_){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2633_, v___x_2636_, v_k_2634_, v_v_2635_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2639_, size_t v_x_2640_, size_t v_x_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_){
_start:
{
if (lean_obj_tag(v_x_2639_) == 0)
{
lean_object* v_es_2644_; size_t v___x_2645_; size_t v___x_2646_; lean_object* v_j_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_es_2644_ = lean_ctor_get(v_x_2639_, 0);
v___x_2645_ = ((size_t)31ULL);
v___x_2646_ = lean_usize_land(v_x_2640_, v___x_2645_);
v_j_2647_ = lean_usize_to_nat(v___x_2646_);
v___x_2648_ = lean_array_get_size(v_es_2644_);
v___x_2649_ = lean_nat_dec_lt(v_j_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_dec(v_j_2647_);
lean_dec(v_x_2643_);
lean_dec(v_x_2642_);
return v_x_2639_;
}
else
{
lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2688_; 
lean_inc_ref(v_es_2644_);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_x_2639_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v_x_2639_, 0);
lean_dec(v_unused_2689_);
v___x_2651_ = v_x_2639_;
v_isShared_2652_ = v_isSharedCheck_2688_;
goto v_resetjp_2650_;
}
else
{
lean_dec(v_x_2639_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2688_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_v_2653_; lean_object* v___x_2654_; lean_object* v_xs_x27_2655_; lean_object* v___y_2657_; 
v_v_2653_ = lean_array_fget(v_es_2644_, v_j_2647_);
v___x_2654_ = lean_box(0);
v_xs_x27_2655_ = lean_array_fset(v_es_2644_, v_j_2647_, v___x_2654_);
switch(lean_obj_tag(v_v_2653_))
{
case 0:
{
lean_object* v_key_2662_; lean_object* v_val_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2673_; 
v_key_2662_ = lean_ctor_get(v_v_2653_, 0);
v_val_2663_ = lean_ctor_get(v_v_2653_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_v_2653_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2665_ = v_v_2653_;
v_isShared_2666_ = v_isSharedCheck_2673_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_val_2663_);
lean_inc(v_key_2662_);
lean_dec(v_v_2653_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2673_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
uint8_t v___x_2667_; 
v___x_2667_ = l_Lean_instBEqMVarId_beq(v_x_2642_, v_key_2662_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_del_object(v___x_2665_);
v___x_2668_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2662_, v_val_2663_, v_x_2642_, v_x_2643_);
v___x_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
v___y_2657_ = v___x_2669_;
goto v___jp_2656_;
}
else
{
lean_object* v___x_2671_; 
lean_dec(v_val_2663_);
lean_dec(v_key_2662_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v_x_2643_);
lean_ctor_set(v___x_2665_, 0, v_x_2642_);
v___x_2671_ = v___x_2665_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_x_2642_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_x_2643_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
v___y_2657_ = v___x_2671_;
goto v___jp_2656_;
}
}
}
}
case 1:
{
lean_object* v_node_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2686_; 
v_node_2674_ = lean_ctor_get(v_v_2653_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_v_2653_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2676_ = v_v_2653_;
v_isShared_2677_ = v_isSharedCheck_2686_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_node_2674_);
lean_dec(v_v_2653_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2686_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
size_t v___x_2678_; size_t v___x_2679_; size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2678_ = ((size_t)5ULL);
v___x_2679_ = lean_usize_shift_right(v_x_2640_, v___x_2678_);
v___x_2680_ = ((size_t)1ULL);
v___x_2681_ = lean_usize_add(v_x_2641_, v___x_2680_);
v___x_2682_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2674_, v___x_2679_, v___x_2681_, v_x_2642_, v_x_2643_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2682_);
v___x_2684_ = v___x_2676_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
v___y_2657_ = v___x_2684_;
goto v___jp_2656_;
}
}
}
default: 
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2687_, 0, v_x_2642_);
lean_ctor_set(v___x_2687_, 1, v_x_2643_);
v___y_2657_ = v___x_2687_;
goto v___jp_2656_;
}
}
v___jp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_array_fset(v_xs_x27_2655_, v_j_2647_, v___y_2657_);
lean_dec(v_j_2647_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2658_);
v___x_2660_ = v___x_2651_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
else
{
lean_object* v_ks_2690_; lean_object* v_vs_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2711_; 
v_ks_2690_ = lean_ctor_get(v_x_2639_, 0);
v_vs_2691_ = lean_ctor_get(v_x_2639_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_x_2639_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2693_ = v_x_2639_;
v_isShared_2694_ = v_isSharedCheck_2711_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_vs_2691_);
lean_inc(v_ks_2690_);
lean_dec(v_x_2639_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2711_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_ks_2690_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_vs_2691_);
v___x_2696_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v_newNode_2697_; uint8_t v___y_2699_; size_t v___x_2705_; uint8_t v___x_2706_; 
v_newNode_2697_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2696_, v_x_2642_, v_x_2643_);
v___x_2705_ = ((size_t)7ULL);
v___x_2706_ = lean_usize_dec_le(v___x_2705_, v_x_2641_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2707_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2697_);
v___x_2708_ = lean_unsigned_to_nat(4u);
v___x_2709_ = lean_nat_dec_lt(v___x_2707_, v___x_2708_);
lean_dec(v___x_2707_);
v___y_2699_ = v___x_2709_;
goto v___jp_2698_;
}
else
{
v___y_2699_ = v___x_2706_;
goto v___jp_2698_;
}
v___jp_2698_:
{
if (v___y_2699_ == 0)
{
lean_object* v_ks_2700_; lean_object* v_vs_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_ks_2700_ = lean_ctor_get(v_newNode_2697_, 0);
lean_inc_ref(v_ks_2700_);
v_vs_2701_ = lean_ctor_get(v_newNode_2697_, 1);
lean_inc_ref(v_vs_2701_);
lean_dec_ref(v_newNode_2697_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v___x_2703_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2704_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2641_, v_ks_2700_, v_vs_2701_, v___x_2702_, v___x_2703_);
lean_dec_ref(v_vs_2701_);
lean_dec_ref(v_ks_2700_);
return v___x_2704_;
}
else
{
return v_newNode_2697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_2712_, lean_object* v_keys_2713_, lean_object* v_vals_2714_, lean_object* v_i_2715_, lean_object* v_entries_2716_){
_start:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = lean_array_get_size(v_keys_2713_);
v___x_2718_ = lean_nat_dec_lt(v_i_2715_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_dec(v_i_2715_);
return v_entries_2716_;
}
else
{
lean_object* v_k_2719_; lean_object* v_v_2720_; uint64_t v___x_2721_; size_t v_h_2722_; size_t v___x_2723_; lean_object* v___x_2724_; size_t v___x_2725_; size_t v___x_2726_; size_t v___x_2727_; size_t v_h_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_k_2719_ = lean_array_fget_borrowed(v_keys_2713_, v_i_2715_);
v_v_2720_ = lean_array_fget_borrowed(v_vals_2714_, v_i_2715_);
v___x_2721_ = l_Lean_instHashableMVarId_hash(v_k_2719_);
v_h_2722_ = lean_uint64_to_usize(v___x_2721_);
v___x_2723_ = ((size_t)5ULL);
v___x_2724_ = lean_unsigned_to_nat(1u);
v___x_2725_ = ((size_t)1ULL);
v___x_2726_ = lean_usize_sub(v_depth_2712_, v___x_2725_);
v___x_2727_ = lean_usize_mul(v___x_2723_, v___x_2726_);
v_h_2728_ = lean_usize_shift_right(v_h_2722_, v___x_2727_);
v___x_2729_ = lean_nat_add(v_i_2715_, v___x_2724_);
lean_dec(v_i_2715_);
lean_inc(v_v_2720_);
lean_inc(v_k_2719_);
v___x_2730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_2716_, v_h_2728_, v_depth_2712_, v_k_2719_, v_v_2720_);
v_i_2715_ = v___x_2729_;
v_entries_2716_ = v___x_2730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2732_, lean_object* v_keys_2733_, lean_object* v_vals_2734_, lean_object* v_i_2735_, lean_object* v_entries_2736_){
_start:
{
size_t v_depth_boxed_2737_; lean_object* v_res_2738_; 
v_depth_boxed_2737_ = lean_unbox_usize(v_depth_2732_);
lean_dec(v_depth_2732_);
v_res_2738_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_2737_, v_keys_2733_, v_vals_2734_, v_i_2735_, v_entries_2736_);
lean_dec_ref(v_vals_2734_);
lean_dec_ref(v_keys_2733_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_2739_, lean_object* v_x_2740_, lean_object* v_x_2741_, lean_object* v_x_2742_, lean_object* v_x_2743_){
_start:
{
size_t v_x_4152__boxed_2744_; size_t v_x_4153__boxed_2745_; lean_object* v_res_2746_; 
v_x_4152__boxed_2744_ = lean_unbox_usize(v_x_2740_);
lean_dec(v_x_2740_);
v_x_4153__boxed_2745_ = lean_unbox_usize(v_x_2741_);
lean_dec(v_x_2741_);
v_res_2746_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2739_, v_x_4152__boxed_2744_, v_x_4153__boxed_2745_, v_x_2742_, v_x_2743_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object* v_x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_){
_start:
{
uint64_t v___x_2750_; size_t v___x_2751_; size_t v___x_2752_; lean_object* v___x_2753_; 
v___x_2750_ = l_Lean_instHashableMVarId_hash(v_x_2748_);
v___x_2751_ = lean_uint64_to_usize(v___x_2750_);
v___x_2752_ = ((size_t)1ULL);
v___x_2753_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2747_, v___x_2751_, v___x_2752_, v_x_2748_, v_x_2749_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object* v_mvarId_2754_, lean_object* v_val_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; lean_object* v_mctx_2759_; lean_object* v_cache_2760_; lean_object* v_zetaDeltaFVarIds_2761_; lean_object* v_postponed_2762_; lean_object* v_diag_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2791_; 
v___x_2758_ = lean_st_ref_take(v___y_2756_);
v_mctx_2759_ = lean_ctor_get(v___x_2758_, 0);
v_cache_2760_ = lean_ctor_get(v___x_2758_, 1);
v_zetaDeltaFVarIds_2761_ = lean_ctor_get(v___x_2758_, 2);
v_postponed_2762_ = lean_ctor_get(v___x_2758_, 3);
v_diag_2763_ = lean_ctor_get(v___x_2758_, 4);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2765_ = v___x_2758_;
v_isShared_2766_ = v_isSharedCheck_2791_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_diag_2763_);
lean_inc(v_postponed_2762_);
lean_inc(v_zetaDeltaFVarIds_2761_);
lean_inc(v_cache_2760_);
lean_inc(v_mctx_2759_);
lean_dec(v___x_2758_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2791_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_depth_2767_; lean_object* v_levelAssignDepth_2768_; lean_object* v_lmvarCounter_2769_; lean_object* v_mvarCounter_2770_; lean_object* v_lDecls_2771_; lean_object* v_decls_2772_; lean_object* v_userNames_2773_; lean_object* v_lAssignment_2774_; lean_object* v_eAssignment_2775_; lean_object* v_dAssignment_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2790_; 
v_depth_2767_ = lean_ctor_get(v_mctx_2759_, 0);
v_levelAssignDepth_2768_ = lean_ctor_get(v_mctx_2759_, 1);
v_lmvarCounter_2769_ = lean_ctor_get(v_mctx_2759_, 2);
v_mvarCounter_2770_ = lean_ctor_get(v_mctx_2759_, 3);
v_lDecls_2771_ = lean_ctor_get(v_mctx_2759_, 4);
v_decls_2772_ = lean_ctor_get(v_mctx_2759_, 5);
v_userNames_2773_ = lean_ctor_get(v_mctx_2759_, 6);
v_lAssignment_2774_ = lean_ctor_get(v_mctx_2759_, 7);
v_eAssignment_2775_ = lean_ctor_get(v_mctx_2759_, 8);
v_dAssignment_2776_ = lean_ctor_get(v_mctx_2759_, 9);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_mctx_2759_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2778_ = v_mctx_2759_;
v_isShared_2779_ = v_isSharedCheck_2790_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_dAssignment_2776_);
lean_inc(v_eAssignment_2775_);
lean_inc(v_lAssignment_2774_);
lean_inc(v_userNames_2773_);
lean_inc(v_decls_2772_);
lean_inc(v_lDecls_2771_);
lean_inc(v_mvarCounter_2770_);
lean_inc(v_lmvarCounter_2769_);
lean_inc(v_levelAssignDepth_2768_);
lean_inc(v_depth_2767_);
lean_dec(v_mctx_2759_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2790_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2780_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2775_, v_mvarId_2754_, v_val_2755_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 8, v___x_2780_);
v___x_2782_ = v___x_2778_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_depth_2767_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_levelAssignDepth_2768_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_lmvarCounter_2769_);
lean_ctor_set(v_reuseFailAlloc_2789_, 3, v_mvarCounter_2770_);
lean_ctor_set(v_reuseFailAlloc_2789_, 4, v_lDecls_2771_);
lean_ctor_set(v_reuseFailAlloc_2789_, 5, v_decls_2772_);
lean_ctor_set(v_reuseFailAlloc_2789_, 6, v_userNames_2773_);
lean_ctor_set(v_reuseFailAlloc_2789_, 7, v_lAssignment_2774_);
lean_ctor_set(v_reuseFailAlloc_2789_, 8, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2789_, 9, v_dAssignment_2776_);
v___x_2782_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2784_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2782_);
v___x_2784_ = v___x_2765_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_cache_2760_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_zetaDeltaFVarIds_2761_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v_postponed_2762_);
lean_ctor_set(v_reuseFailAlloc_2788_, 4, v_diag_2763_);
v___x_2784_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = lean_st_ref_set(v___y_2756_, v___x_2784_);
v___x_2786_ = lean_box(0);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2792_, lean_object* v_val_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2792_, v_val_2793_, v___y_2794_);
lean_dec(v___y_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2805_, lean_object* v_as_2806_, size_t v_sz_2807_, size_t v_i_2808_, lean_object* v_b_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_a_2816_; uint8_t v___x_2820_; 
v___x_2820_ = lean_usize_dec_lt(v_i_2808_, v_sz_2807_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_b_2809_);
return v___x_2821_;
}
else
{
lean_object* v_fst_2822_; lean_object* v_snd_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; lean_object* v_a_2826_; 
v_fst_2822_ = lean_ctor_get(v_b_2809_, 0);
lean_inc(v_fst_2822_);
v_snd_2823_ = lean_ctor_get(v_b_2809_, 1);
lean_inc(v_snd_2823_);
lean_dec_ref(v_b_2809_);
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_nat_dec_eq(v___x_2805_, v___x_2824_);
v_a_2826_ = lean_array_uget_borrowed(v_as_2806_, v_i_2808_);
if (lean_obj_tag(v_a_2826_) == 0)
{
lean_object* v_fvarId_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_fvarId_2827_ = lean_ctor_get(v_a_2826_, 0);
v___x_2828_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2823_, v_fvarId_2827_);
v___x_2829_ = l_Lean_Meta_substCore(v_fst_2822_, v___x_2828_, v___x_2820_, v_snd_2823_, v___x_2820_, v___x_2825_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v_fst_2831_; lean_object* v_snd_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v_fst_2831_ = lean_ctor_get(v_a_2830_, 0);
v_snd_2832_ = lean_ctor_get(v_a_2830_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_a_2830_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v_a_2830_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_snd_2832_);
lean_inc(v_fst_2831_);
lean_dec(v_a_2830_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 1, v_fst_2831_);
lean_ctor_set(v___x_2834_, 0, v_snd_2832_);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_snd_2832_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_fst_2831_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
v_a_2816_ = v___x_2837_;
goto v___jp_2815_;
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
v_a_2840_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2829_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2829_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_lhs_2848_; lean_object* v_rhs_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_lhs_2848_ = lean_ctor_get(v_a_2826_, 0);
v_rhs_2849_ = lean_ctor_get(v_a_2826_, 1);
v___x_2850_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2823_, v_lhs_2848_);
v___x_2851_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2823_, v_rhs_2849_);
v___x_2852_ = l_Lean_mkFVar(v___x_2850_);
v___x_2853_ = l_Lean_mkFVar(v___x_2851_);
lean_inc_ref(v___x_2853_);
lean_inc_ref(v___x_2852_);
v___x_2854_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2854_, 0, v___x_2852_);
lean_closure_set(v___x_2854_, 1, v___x_2853_);
lean_inc(v_fst_2822_);
v___x_2855_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2822_, v___x_2854_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2858_ = lean_unsigned_to_nat(2u);
v___x_2859_ = lean_mk_empty_array_with_capacity(v___x_2858_);
v___x_2860_ = lean_array_push(v___x_2859_, v___x_2852_);
v___x_2861_ = lean_array_push(v___x_2860_, v___x_2853_);
v___x_2862_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2862_, 0, v___x_2857_);
lean_closure_set(v___x_2862_, 1, v___x_2861_);
lean_inc(v_fst_2822_);
v___x_2863_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2822_, v___x_2862_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___x_2865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
v___x_2866_ = l_Lean_MVarId_assert(v_fst_2822_, v___x_2865_, v_a_2856_, v_a_2864_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2868_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v___x_2868_ = l_Lean_Meta_intro1Core(v_a_2867_, v___x_2825_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v_fst_2870_; lean_object* v_snd_2871_; lean_object* v___x_2872_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v_fst_2870_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_fst_2870_);
v_snd_2871_ = lean_ctor_get(v_a_2869_, 1);
lean_inc(v_snd_2871_);
lean_dec(v_a_2869_);
v___x_2872_ = l_Lean_Meta_substCore(v_snd_2871_, v_fst_2870_, v___x_2820_, v_snd_2823_, v___x_2820_, v___x_2825_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v_fst_2874_; lean_object* v_snd_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v_fst_2874_ = lean_ctor_get(v_a_2873_, 0);
v_snd_2875_ = lean_ctor_get(v_a_2873_, 1);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_a_2873_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v_a_2873_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_snd_2875_);
lean_inc(v_fst_2874_);
lean_dec(v_a_2873_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 1, v_fst_2874_);
lean_ctor_set(v___x_2877_, 0, v_snd_2875_);
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_snd_2875_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_fst_2874_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
v_a_2816_ = v___x_2880_;
goto v___jp_2815_;
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_a_2883_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2872_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2872_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_snd_2823_);
v_a_2891_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2868_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2868_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
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
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_snd_2823_);
v_a_2899_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2866_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2866_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
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
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_a_2856_);
lean_dec(v_snd_2823_);
lean_dec(v_fst_2822_);
v_a_2907_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2863_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2863_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref(v___x_2853_);
lean_dec_ref(v___x_2852_);
lean_dec(v_snd_2823_);
lean_dec(v_fst_2822_);
v_a_2915_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2855_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2855_);
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
}
v___jp_2815_:
{
size_t v___x_2817_; size_t v___x_2818_; 
v___x_2817_ = ((size_t)1ULL);
v___x_2818_ = lean_usize_add(v_i_2808_, v___x_2817_);
v_i_2808_ = v___x_2818_;
v_b_2809_ = v_a_2816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_2923_, lean_object* v_as_2924_, lean_object* v_sz_2925_, lean_object* v_i_2926_, lean_object* v_b_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
size_t v_sz_boxed_2933_; size_t v_i_boxed_2934_; lean_object* v_res_2935_; 
v_sz_boxed_2933_ = lean_unbox_usize(v_sz_2925_);
lean_dec(v_sz_2925_);
v_i_boxed_2934_ = lean_unbox_usize(v_i_2926_);
lean_dec(v_i_2926_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2923_, v_as_2924_, v_sz_boxed_2933_, v_i_boxed_2934_, v_b_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_as_2924_);
lean_dec(v___x_2923_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_2936_, lean_object* v_as_2937_, size_t v_i_2938_, size_t v_stop_2939_, lean_object* v_b_2940_){
_start:
{
lean_object* v___y_2942_; uint8_t v___x_2946_; 
v___x_2946_ = lean_usize_dec_eq(v_i_2938_, v_stop_2939_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_box(0);
v___x_2948_ = lean_array_uget_borrowed(v_as_2937_, v_i_2938_);
v___x_2949_ = lean_array_get_borrowed(v___x_2947_, v_eqs_2936_, v___x_2948_);
if (lean_obj_tag(v___x_2949_) == 0)
{
v___y_2942_ = v_b_2940_;
goto v___jp_2941_;
}
else
{
lean_object* v_val_2950_; lean_object* v___x_2951_; 
v_val_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_val_2950_);
v___x_2951_ = lean_array_push(v_b_2940_, v_val_2950_);
v___y_2942_ = v___x_2951_;
goto v___jp_2941_;
}
}
else
{
return v_b_2940_;
}
v___jp_2941_:
{
size_t v___x_2943_; size_t v___x_2944_; 
v___x_2943_ = ((size_t)1ULL);
v___x_2944_ = lean_usize_add(v_i_2938_, v___x_2943_);
v_i_2938_ = v___x_2944_;
v_b_2940_ = v___y_2942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_2952_, lean_object* v_as_2953_, lean_object* v_i_2954_, lean_object* v_stop_2955_, lean_object* v_b_2956_){
_start:
{
size_t v_i_boxed_2957_; size_t v_stop_boxed_2958_; lean_object* v_res_2959_; 
v_i_boxed_2957_ = lean_unbox_usize(v_i_2954_);
lean_dec(v_i_2954_);
v_stop_boxed_2958_ = lean_unbox_usize(v_stop_2955_);
lean_dec(v_stop_2955_);
v_res_2959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2952_, v_as_2953_, v_i_boxed_2957_, v_stop_boxed_2958_, v_b_2956_);
lean_dec_ref(v_as_2953_);
lean_dec_ref(v_eqs_2952_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_2962_, lean_object* v_as_2963_, lean_object* v_start_2964_, lean_object* v_stop_2965_){
_start:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_2967_ = lean_nat_dec_lt(v_start_2964_, v_stop_2965_);
if (v___x_2967_ == 0)
{
return v___x_2966_;
}
else
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_array_get_size(v_as_2963_);
v___x_2969_ = lean_nat_dec_le(v_stop_2965_, v___x_2968_);
if (v___x_2969_ == 0)
{
uint8_t v___x_2970_; 
v___x_2970_ = lean_nat_dec_lt(v_start_2964_, v___x_2968_);
if (v___x_2970_ == 0)
{
return v___x_2966_;
}
else
{
size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_usize_of_nat(v_start_2964_);
v___x_2972_ = lean_usize_of_nat(v___x_2968_);
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2962_, v_as_2963_, v___x_2971_, v___x_2972_, v___x_2966_);
return v___x_2973_;
}
}
else
{
size_t v___x_2974_; size_t v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = lean_usize_of_nat(v_start_2964_);
v___x_2975_ = lean_usize_of_nat(v_stop_2965_);
v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2962_, v_as_2963_, v___x_2974_, v___x_2975_, v___x_2966_);
return v___x_2976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_2977_, lean_object* v_as_2978_, lean_object* v_start_2979_, lean_object* v_stop_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2977_, v_as_2978_, v_start_2979_, v_stop_2980_);
lean_dec(v_stop_2980_);
lean_dec(v_start_2979_);
lean_dec_ref(v_as_2978_);
lean_dec_ref(v_eqs_2977_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_2982_, lean_object* v_type_2983_, lean_object* v_deps_2984_, lean_object* v_eqs_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v_eqs_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2991_ = lean_unsigned_to_nat(0u);
v___x_2992_ = lean_array_get_size(v_deps_2984_);
v_eqs_2993_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2985_, v_deps_2984_, v___x_2991_, v___x_2992_);
v___x_2994_ = lean_array_get_size(v_eqs_2993_);
v___x_2995_ = lean_nat_dec_eq(v___x_2994_, v___x_2991_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; uint8_t v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_type_2983_);
v___x_2997_ = 0;
v___x_2998_ = lean_box(0);
v___x_2999_ = l_Lean_Meta_mkFreshExprMVar(v___x_2996_, v___x_2997_, v___x_2998_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; size_t v_sz_3004_; size_t v___x_3005_; lean_object* v___x_3006_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = l_Lean_Expr_mvarId_x21(v_a_3000_);
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v_sz_3004_ = lean_array_size(v_eqs_2993_);
v___x_3005_ = ((size_t)0ULL);
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2994_, v_eqs_2993_, v_sz_3004_, v___x_3005_, v___x_3003_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
lean_dec_ref(v_eqs_2993_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_fst_3008_; lean_object* v_snd_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v_fst_3008_ = lean_ctor_get(v_a_3007_, 0);
lean_inc(v_fst_3008_);
v_snd_3009_ = lean_ctor_get(v_a_3007_, 1);
lean_inc(v_snd_3009_);
lean_dec(v_a_3007_);
v___x_3010_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_3009_, v_fvarId_2982_);
lean_dec(v_fvarId_2982_);
lean_dec(v_snd_3009_);
v___x_3011_ = l_Lean_mkFVar(v___x_3010_);
v___x_3012_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_3008_, v___x_3011_, v_a_2987_);
lean_dec_ref(v___x_3012_);
v___x_3013_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_3000_, v_a_2987_);
return v___x_3013_;
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_a_3000_);
lean_dec(v_fvarId_2982_);
v_a_3014_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3006_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3006_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_dec_ref(v_eqs_2993_);
lean_dec(v_fvarId_2982_);
return v___x_2999_;
}
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec_ref(v_eqs_2993_);
lean_dec_ref(v_type_2983_);
v___x_3022_ = l_Lean_mkFVar(v_fvarId_2982_);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3024_, lean_object* v_type_3025_, lean_object* v_deps_3026_, lean_object* v_eqs_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3024_, v_type_3025_, v_deps_3026_, v_eqs_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec_ref(v_eqs_3027_);
lean_dec_ref(v_deps_3026_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3034_, lean_object* v_val_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3034_, v_val_3035_, v___y_3037_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3042_, lean_object* v_val_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3042_, v_val_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3050_, lean_object* v_x_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3051_, v_x_3052_, v_x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3055_, lean_object* v_x_3056_, size_t v_x_3057_, size_t v_x_3058_, lean_object* v_x_3059_, lean_object* v_x_3060_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3056_, v_x_3057_, v_x_3058_, v_x_3059_, v_x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3062_, lean_object* v_x_3063_, lean_object* v_x_3064_, lean_object* v_x_3065_, lean_object* v_x_3066_, lean_object* v_x_3067_){
_start:
{
size_t v_x_4757__boxed_3068_; size_t v_x_4758__boxed_3069_; lean_object* v_res_3070_; 
v_x_4757__boxed_3068_ = lean_unbox_usize(v_x_3064_);
lean_dec(v_x_3064_);
v_x_4758__boxed_3069_ = lean_unbox_usize(v_x_3065_);
lean_dec(v_x_3065_);
v_res_3070_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3062_, v_x_3063_, v_x_4757__boxed_3068_, v_x_4758__boxed_3069_, v_x_3066_, v_x_3067_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3071_, lean_object* v_n_3072_, lean_object* v_k_3073_, lean_object* v_v_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3072_, v_k_3073_, v_v_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3076_, size_t v_depth_3077_, lean_object* v_keys_3078_, lean_object* v_vals_3079_, lean_object* v_heq_3080_, lean_object* v_i_3081_, lean_object* v_entries_3082_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3077_, v_keys_3078_, v_vals_3079_, v_i_3081_, v_entries_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3084_, lean_object* v_depth_3085_, lean_object* v_keys_3086_, lean_object* v_vals_3087_, lean_object* v_heq_3088_, lean_object* v_i_3089_, lean_object* v_entries_3090_){
_start:
{
size_t v_depth_boxed_3091_; lean_object* v_res_3092_; 
v_depth_boxed_3091_ = lean_unbox_usize(v_depth_3085_);
lean_dec(v_depth_3085_);
v_res_3092_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3084_, v_depth_boxed_3091_, v_keys_3086_, v_vals_3087_, v_heq_3088_, v_i_3089_, v_entries_3090_);
lean_dec_ref(v_vals_3087_);
lean_dec_ref(v_keys_3086_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3093_, lean_object* v_x_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_, lean_object* v_x_3097_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3094_, v_x_3095_, v_x_3096_, v_x_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___f_3106_; lean_object* v___x_1803__overap_3107_; lean_object* v___x_3108_; 
v___f_3106_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1803__overap_3107_ = lean_panic_fn_borrowed(v___f_3106_, v_msg_3100_);
lean_inc(v___y_3104_);
lean_inc_ref(v___y_3103_);
lean_inc(v___y_3102_);
lean_inc_ref(v___y_3101_);
v___x_3108_ = lean_apply_5(v___x_1803__overap_3107_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, lean_box(0));
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
return v_res_3115_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3119_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3120_ = lean_unsigned_to_nat(34u);
v___x_3121_ = lean_unsigned_to_nat(360u);
v___x_3122_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3123_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3124_ = l_mkPanicMessageWithDecl(v___x_3123_, v___x_3122_, v___x_3121_, v___x_3120_, v___x_3119_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3125_, lean_object* v___x_3126_, lean_object* v___x_3127_, lean_object* v_i_3128_, lean_object* v_kinds_3129_, lean_object* v___x_3130_, lean_object* v_lhs_3131_, lean_object* v_rhs_3132_, lean_object* v_type_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
uint8_t v___x_1990__boxed_3139_; uint8_t v___x_1991__boxed_3140_; lean_object* v_res_3141_; 
v___x_1990__boxed_3139_ = lean_unbox(v___x_3126_);
v___x_1991__boxed_3140_ = lean_unbox(v___x_3127_);
v_res_3141_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3125_, v___x_1990__boxed_3139_, v___x_1991__boxed_3140_, v_i_3128_, v_kinds_3129_, v___x_3130_, v_lhs_3131_, v_rhs_3132_, v_type_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3142_, uint8_t v___x_3143_, uint8_t v___x_3144_, lean_object* v_i_3145_, lean_object* v___x_3146_, lean_object* v_kinds_3147_, lean_object* v_typeSub_3148_, lean_object* v_lhs_3149_, lean_object* v_rhs_3150_, lean_object* v_type_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; 
lean_inc_ref(v_rhs_3150_);
v___x_3157_ = lean_array_push(v___x_3142_, v_rhs_3150_);
v___x_3158_ = 1;
v___x_3159_ = l_Lean_Meta_mkLambdaFVars(v___x_3157_, v_type_3151_, v___x_3143_, v___x_3144_, v___x_3143_, v___x_3144_, v___x_3158_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec_ref(v___x_3157_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_nat_add(v_i_3145_, v___x_3146_);
v___x_3162_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3147_, v___x_3161_, v_typeSub_3148_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3165_ = lean_unsigned_to_nat(2u);
v___x_3166_ = lean_mk_empty_array_with_capacity(v___x_3165_);
v___x_3167_ = lean_array_push(v___x_3166_, v_lhs_3149_);
v___x_3168_ = lean_array_push(v___x_3167_, v_rhs_3150_);
lean_inc_ref(v___x_3168_);
v___x_3169_ = l_Lean_Meta_mkAppM(v___x_3164_, v___x_3168_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___x_3169_, 1);
v___x_3171_ = l_Lean_Meta_mkEqNDRec(v_a_3160_, v_a_3163_, v_a_3170_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref_known(v___x_3171_, 1);
v___x_3173_ = l_Lean_Meta_mkLambdaFVars(v___x_3168_, v_a_3172_, v___x_3143_, v___x_3144_, v___x_3143_, v___x_3144_, v___x_3158_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec_ref(v___x_3168_);
return v___x_3173_;
}
else
{
lean_dec_ref(v___x_3168_);
return v___x_3171_;
}
}
else
{
lean_dec_ref(v___x_3168_);
lean_dec(v_a_3163_);
lean_dec(v_a_3160_);
return v___x_3169_;
}
}
else
{
lean_dec(v_a_3160_);
lean_dec_ref(v_rhs_3150_);
lean_dec_ref(v_lhs_3149_);
return v___x_3162_;
}
}
else
{
lean_dec_ref(v_rhs_3150_);
lean_dec_ref(v_lhs_3149_);
lean_dec_ref(v_typeSub_3148_);
lean_dec_ref(v_kinds_3147_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3174_, lean_object* v___x_3175_, lean_object* v___x_3176_, lean_object* v_i_3177_, lean_object* v___x_3178_, lean_object* v_kinds_3179_, lean_object* v_typeSub_3180_, lean_object* v_lhs_3181_, lean_object* v_rhs_3182_, lean_object* v_type_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
uint8_t v___x_2053__boxed_3189_; uint8_t v___x_2054__boxed_3190_; lean_object* v_res_3191_; 
v___x_2053__boxed_3189_ = lean_unbox(v___x_3175_);
v___x_2054__boxed_3190_ = lean_unbox(v___x_3176_);
v_res_3191_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3174_, v___x_2053__boxed_3189_, v___x_2054__boxed_3190_, v_i_3177_, v___x_3178_, v_kinds_3179_, v_typeSub_3180_, v_lhs_3181_, v_rhs_3182_, v_type_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___x_3178_);
lean_dec(v_i_3177_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(lean_object* v_kinds_3192_, lean_object* v_i_3193_, uint8_t v___x_3194_, uint8_t v___x_3195_, lean_object* v_lhs_3196_, lean_object* v_type_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3206_ = 0;
v___x_3207_ = lean_box(v___x_3206_);
v___x_3208_ = lean_array_get(v___x_3207_, v_kinds_3192_, v_i_3193_);
lean_dec(v___x_3207_);
v___x_3209_ = lean_unbox(v___x_3208_);
lean_dec(v___x_3208_);
switch(v___x_3209_)
{
case 1:
{
lean_dec_ref(v_type_3197_);
lean_dec_ref(v_lhs_3196_);
lean_dec(v_i_3193_);
lean_dec_ref(v_kinds_3192_);
goto v___jp_3203_;
}
case 2:
{
lean_object* v___x_3210_; 
lean_inc_ref(v_lhs_3196_);
v___x_3210_ = l_Lean_Meta_mkEqRefl(v_lhs_3196_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3212_ = l_Lean_Expr_bindingBody_x21(v_type_3197_);
v___x_3213_ = l_Lean_Expr_bindingBody_x21(v___x_3212_);
lean_dec_ref(v___x_3212_);
v___x_3214_ = lean_unsigned_to_nat(2u);
v___x_3215_ = lean_mk_empty_array_with_capacity(v___x_3214_);
lean_inc_ref(v___x_3215_);
v___x_3216_ = lean_array_push(v___x_3215_, v_a_3211_);
lean_inc_ref(v_lhs_3196_);
v___x_3217_ = lean_array_push(v___x_3216_, v_lhs_3196_);
v___x_3218_ = lean_expr_instantiate(v___x_3213_, v___x_3217_);
lean_dec_ref(v___x_3217_);
lean_dec_ref(v___x_3213_);
v___x_3219_ = lean_box(v___x_3194_);
v___x_3220_ = lean_box(v___x_3195_);
v___f_3221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3221_, 0, v___x_3215_);
lean_closure_set(v___f_3221_, 1, v___x_3219_);
lean_closure_set(v___f_3221_, 2, v___x_3220_);
lean_closure_set(v___f_3221_, 3, v_i_3193_);
lean_closure_set(v___f_3221_, 4, v_kinds_3192_);
lean_closure_set(v___f_3221_, 5, v___x_3218_);
lean_closure_set(v___f_3221_, 6, v_lhs_3196_);
v___x_3222_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3197_, v___f_3221_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
return v___x_3222_;
}
else
{
lean_dec_ref(v_type_3197_);
lean_dec_ref(v_lhs_3196_);
lean_dec(v_i_3193_);
lean_dec_ref(v_kinds_3192_);
return v___x_3210_;
}
}
case 4:
{
lean_dec_ref(v_type_3197_);
lean_dec_ref(v_lhs_3196_);
lean_dec(v_i_3193_);
lean_dec_ref(v_kinds_3192_);
goto v___jp_3203_;
}
case 5:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v_typeSub_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___f_3230_; lean_object* v___x_3231_; 
v___x_3223_ = l_Lean_Expr_bindingBody_x21(v_type_3197_);
v___x_3224_ = lean_unsigned_to_nat(1u);
v___x_3225_ = lean_mk_empty_array_with_capacity(v___x_3224_);
lean_inc_ref(v_lhs_3196_);
lean_inc_ref(v___x_3225_);
v___x_3226_ = lean_array_push(v___x_3225_, v_lhs_3196_);
v_typeSub_3227_ = lean_expr_instantiate(v___x_3223_, v___x_3226_);
lean_dec_ref(v___x_3226_);
lean_dec_ref(v___x_3223_);
v___x_3228_ = lean_box(v___x_3194_);
v___x_3229_ = lean_box(v___x_3195_);
v___f_3230_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3230_, 0, v___x_3225_);
lean_closure_set(v___f_3230_, 1, v___x_3228_);
lean_closure_set(v___f_3230_, 2, v___x_3229_);
lean_closure_set(v___f_3230_, 3, v_i_3193_);
lean_closure_set(v___f_3230_, 4, v___x_3224_);
lean_closure_set(v___f_3230_, 5, v_kinds_3192_);
lean_closure_set(v___f_3230_, 6, v_typeSub_3227_);
lean_closure_set(v___f_3230_, 7, v_lhs_3196_);
v___x_3231_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3197_, v___f_3230_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
return v___x_3231_;
}
default: 
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_unsigned_to_nat(1u);
v___x_3233_ = lean_nat_add(v_i_3193_, v___x_3232_);
lean_dec(v_i_3193_);
v___x_3234_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3192_, v___x_3233_, v_type_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; lean_object* v___x_3239_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3236_ = lean_mk_empty_array_with_capacity(v___x_3232_);
v___x_3237_ = lean_array_push(v___x_3236_, v_lhs_3196_);
v___x_3238_ = 1;
v___x_3239_ = l_Lean_Meta_mkLambdaFVars(v___x_3237_, v_a_3235_, v___x_3194_, v___x_3195_, v___x_3194_, v___x_3195_, v___x_3238_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec_ref(v___x_3237_);
return v___x_3239_;
}
else
{
lean_dec_ref(v_lhs_3196_);
return v___x_3234_;
}
}
}
v___jp_3203_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3205_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3204_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
return v___x_3205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v_kinds_3240_, lean_object* v_i_3241_, lean_object* v___x_3242_, lean_object* v___x_3243_, lean_object* v_lhs_3244_, lean_object* v_type_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v___x_2090__boxed_3251_; uint8_t v___x_2091__boxed_3252_; lean_object* v_res_3253_; 
v___x_2090__boxed_3251_ = lean_unbox(v___x_3242_);
v___x_2091__boxed_3252_ = lean_unbox(v___x_3243_);
v_res_3253_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v_kinds_3240_, v_i_3241_, v___x_2090__boxed_3251_, v___x_2091__boxed_3252_, v_lhs_3244_, v_type_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
return v_res_3253_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3254_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3255_ = lean_unsigned_to_nat(43u);
v___x_3256_ = lean_unsigned_to_nat(355u);
v___x_3257_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3258_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3259_ = l_mkPanicMessageWithDecl(v___x_3258_, v___x_3257_, v___x_3256_, v___x_3255_, v___x_3254_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3260_, lean_object* v_i_3261_, lean_object* v_type_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3268_ = lean_array_get_size(v_kinds_3260_);
v___x_3269_ = lean_nat_dec_eq(v_i_3261_, v___x_3268_);
if (v___x_3269_ == 0)
{
uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; 
v___x_3270_ = 1;
v___x_3271_ = lean_box(v___x_3269_);
v___x_3272_ = lean_box(v___x_3270_);
v___f_3273_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3273_, 0, v_kinds_3260_);
lean_closure_set(v___f_3273_, 1, v_i_3261_);
lean_closure_set(v___f_3273_, 2, v___x_3271_);
lean_closure_set(v___f_3273_, 3, v___x_3272_);
v___x_3274_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3262_, v___f_3273_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
lean_dec(v_i_3261_);
lean_dec_ref(v_kinds_3260_);
v___x_3275_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3276_ = lean_unsigned_to_nat(3u);
v___x_3277_ = l_Lean_Expr_isAppOfArity(v_type_3262_, v___x_3275_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_dec_ref(v_type_3262_);
v___x_3278_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3279_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3278_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
return v___x_3279_;
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = l_Lean_Expr_appFn_x21(v_type_3262_);
lean_dec_ref(v_type_3262_);
v___x_3281_ = l_Lean_Expr_appArg_x21(v___x_3280_);
lean_dec_ref(v___x_3280_);
v___x_3282_ = l_Lean_Meta_mkEqRefl(v___x_3281_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
return v___x_3282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* v___x_3283_, lean_object* v_rhs_3284_, uint8_t v___x_3285_, uint8_t v___x_3286_, lean_object* v_i_3287_, lean_object* v_kinds_3288_, lean_object* v___x_3289_, lean_object* v_lhs_3290_, lean_object* v_heq_3291_, lean_object* v_type_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; 
lean_inc_ref(v_rhs_3284_);
v___x_3298_ = lean_array_push(v___x_3283_, v_rhs_3284_);
lean_inc_ref(v_heq_3291_);
v___x_3299_ = lean_array_push(v___x_3298_, v_heq_3291_);
v___x_3300_ = 1;
v___x_3301_ = l_Lean_Meta_mkLambdaFVars(v___x_3299_, v_type_3292_, v___x_3285_, v___x_3286_, v___x_3285_, v___x_3286_, v___x_3300_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec_ref(v___x_3299_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = lean_unsigned_to_nat(1u);
v___x_3304_ = lean_nat_add(v_i_3287_, v___x_3303_);
v___x_3305_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3288_, v___x_3304_, v___x_3289_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3305_, 1);
lean_inc_ref(v_heq_3291_);
v___x_3307_ = l_Lean_Meta_mkEqRec(v_a_3302_, v_a_3306_, v_heq_3291_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3307_, 1);
v___x_3309_ = lean_unsigned_to_nat(3u);
v___x_3310_ = lean_mk_empty_array_with_capacity(v___x_3309_);
v___x_3311_ = lean_array_push(v___x_3310_, v_lhs_3290_);
v___x_3312_ = lean_array_push(v___x_3311_, v_rhs_3284_);
v___x_3313_ = lean_array_push(v___x_3312_, v_heq_3291_);
v___x_3314_ = l_Lean_Meta_mkLambdaFVars(v___x_3313_, v_a_3308_, v___x_3285_, v___x_3286_, v___x_3285_, v___x_3286_, v___x_3300_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec_ref(v___x_3313_);
return v___x_3314_;
}
else
{
lean_dec_ref(v_heq_3291_);
lean_dec_ref(v_lhs_3290_);
lean_dec_ref(v_rhs_3284_);
return v___x_3307_;
}
}
else
{
lean_dec(v_a_3302_);
lean_dec_ref(v_heq_3291_);
lean_dec_ref(v_lhs_3290_);
lean_dec_ref(v_rhs_3284_);
return v___x_3305_;
}
}
else
{
lean_dec_ref(v_heq_3291_);
lean_dec_ref(v_lhs_3290_);
lean_dec_ref(v___x_3289_);
lean_dec_ref(v_kinds_3288_);
lean_dec_ref(v_rhs_3284_);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* v___x_3315_, lean_object* v_rhs_3316_, lean_object* v___x_3317_, lean_object* v___x_3318_, lean_object* v_i_3319_, lean_object* v_kinds_3320_, lean_object* v___x_3321_, lean_object* v_lhs_3322_, lean_object* v_heq_3323_, lean_object* v_type_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v___x_2001__boxed_3330_; uint8_t v___x_2002__boxed_3331_; lean_object* v_res_3332_; 
v___x_2001__boxed_3330_ = lean_unbox(v___x_3317_);
v___x_2002__boxed_3331_ = lean_unbox(v___x_3318_);
v_res_3332_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3315_, v_rhs_3316_, v___x_2001__boxed_3330_, v___x_2002__boxed_3331_, v_i_3319_, v_kinds_3320_, v___x_3321_, v_lhs_3322_, v_heq_3323_, v_type_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v_i_3319_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* v___x_3333_, uint8_t v___x_3334_, uint8_t v___x_3335_, lean_object* v_i_3336_, lean_object* v_kinds_3337_, lean_object* v___x_3338_, lean_object* v_lhs_3339_, lean_object* v_rhs_3340_, lean_object* v_type_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___f_3349_; lean_object* v___x_3350_; 
v___x_3347_ = lean_box(v___x_3334_);
v___x_3348_ = lean_box(v___x_3335_);
v___f_3349_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3349_, 0, v___x_3333_);
lean_closure_set(v___f_3349_, 1, v_rhs_3340_);
lean_closure_set(v___f_3349_, 2, v___x_3347_);
lean_closure_set(v___f_3349_, 3, v___x_3348_);
lean_closure_set(v___f_3349_, 4, v_i_3336_);
lean_closure_set(v___f_3349_, 5, v_kinds_3337_);
lean_closure_set(v___f_3349_, 6, v___x_3338_);
lean_closure_set(v___f_3349_, 7, v_lhs_3339_);
v___x_3350_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3341_, v___f_3349_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object* v_kinds_3351_, lean_object* v_i_3352_, lean_object* v_type_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3351_, v_i_3352_, v_type_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec_ref(v_a_3354_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* v_type_3360_, lean_object* v_kinds_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3361_, v___x_3367_, v_type_3360_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object* v_type_3369_, lean_object* v_kinds_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3369_, v_kinds_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_msg_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___f_3383_; lean_object* v___x_2082__overap_3384_; lean_object* v___x_3385_; 
v___f_3383_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_2082__overap_3384_ = lean_panic_fn_borrowed(v___f_3383_, v_msg_3377_);
lean_inc(v___y_3381_);
lean_inc_ref(v___y_3380_);
lean_inc(v___y_3379_);
lean_inc_ref(v___y_3378_);
v___x_3385_ = lean_apply_5(v___x_2082__overap_3384_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, lean_box(0));
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_msg_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_msg_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(lean_object* v_bs_3393_, lean_object* v_k_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3393_, v_k_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_a_3409_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3400_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3400_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg___boxed(lean_object* v_bs_3417_, lean_object* v_k_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3417_, v_k_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v_bs_3417_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(lean_object* v_00_u03b1_3425_, lean_object* v_bs_3426_, lean_object* v_k_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3426_, v_k_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3434_, lean_object* v_bs_3435_, lean_object* v_k_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(v_00_u03b1_3434_, v_bs_3435_, v_k_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec_ref(v_bs_3435_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(size_t v_sz_3443_, size_t v_i_3444_, lean_object* v_bs_3445_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3444_, v_sz_3443_);
if (v___x_3446_ == 0)
{
return v_bs_3445_;
}
else
{
lean_object* v_v_3447_; lean_object* v___x_3448_; lean_object* v_bs_x27_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
v_v_3447_ = lean_array_uget(v_bs_3445_, v_i_3444_);
v___x_3448_ = lean_unsigned_to_nat(0u);
v_bs_x27_3449_ = lean_array_uset(v_bs_3445_, v_i_3444_, v___x_3448_);
v___x_3450_ = l_Lean_Expr_fvarId_x21(v_v_3447_);
lean_dec(v_v_3447_);
v___x_3451_ = 1;
v___x_3452_ = lean_box(v___x_3451_);
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3450_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = ((size_t)1ULL);
v___x_3455_ = lean_usize_add(v_i_3444_, v___x_3454_);
v___x_3456_ = lean_array_uset(v_bs_x27_3449_, v_i_3444_, v___x_3453_);
v_i_3444_ = v___x_3455_;
v_bs_3445_ = v___x_3456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0___boxed(lean_object* v_sz_3458_, lean_object* v_i_3459_, lean_object* v_bs_3460_){
_start:
{
size_t v_sz_boxed_3461_; size_t v_i_boxed_3462_; lean_object* v_res_3463_; 
v_sz_boxed_3461_ = lean_unbox_usize(v_sz_3458_);
lean_dec(v_sz_3458_);
v_i_boxed_3462_ = lean_unbox_usize(v_i_3459_);
lean_dec(v_i_3459_);
v_res_3463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_boxed_3461_, v_i_boxed_3462_, v_bs_3460_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(lean_object* v_bs_3464_, lean_object* v_k_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
size_t v_sz_3471_; size_t v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_sz_3471_ = lean_array_size(v_bs_3464_);
v___x_3472_ = ((size_t)0ULL);
v___x_3473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_3471_, v___x_3472_, v_bs_3464_);
v___x_3474_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v___x_3473_, v_k_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec_ref(v___x_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg___boxed(lean_object* v_bs_3475_, lean_object* v_k_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3475_, v_k_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_00_u03b1_3483_, lean_object* v_bs_3484_, lean_object* v_k_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3484_, v_k_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3492_, lean_object* v_bs_3493_, lean_object* v_k_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_00_u03b1_3492_, v_bs_3493_, v_k_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3501_, lean_object* v_rhss_3502_, lean_object* v_lhs_3503_, lean_object* v_eqs_3504_, lean_object* v_hyps_3505_, uint8_t v_subsingletonInstImplicitRhs_3506_, lean_object* v_f_3507_, lean_object* v_info_3508_, lean_object* v_kinds_3509_, lean_object* v_lhss_3510_, lean_object* v_b_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_nat_add(v_i_3501_, v___x_3517_);
lean_inc_ref(v_b_3511_);
v___x_3519_ = lean_array_push(v_rhss_3502_, v_b_3511_);
v___x_3520_ = l_Lean_Expr_fvarId_x21(v_lhs_3503_);
v___x_3521_ = l_Lean_Expr_fvarId_x21(v_b_3511_);
v___x_3522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
v___x_3524_ = lean_array_push(v_eqs_3504_, v___x_3523_);
v___x_3525_ = lean_array_push(v_hyps_3505_, v_b_3511_);
v___x_3526_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3506_, v_f_3507_, v_info_3508_, v_kinds_3509_, v_lhss_3510_, v___x_3518_, v___x_3519_, v___x_3524_, v___x_3525_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3527_, lean_object* v_rhss_3528_, lean_object* v_lhs_3529_, lean_object* v_eqs_3530_, lean_object* v_hyps_3531_, lean_object* v_subsingletonInstImplicitRhs_3532_, lean_object* v_f_3533_, lean_object* v_info_3534_, lean_object* v_kinds_3535_, lean_object* v_lhss_3536_, lean_object* v_b_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3543_; lean_object* v_res_3544_; 
v_subsingletonInstImplicitRhs_boxed_3543_ = lean_unbox(v_subsingletonInstImplicitRhs_3532_);
v_res_3544_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3527_, v_rhss_3528_, v_lhs_3529_, v_eqs_3530_, v_hyps_3531_, v_subsingletonInstImplicitRhs_boxed_3543_, v_f_3533_, v_info_3534_, v_kinds_3535_, v_lhss_3536_, v_b_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec_ref(v_lhs_3529_);
lean_dec(v_i_3527_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3545_, lean_object* v_rhss_3546_, lean_object* v_lhs_3547_, lean_object* v_eqs_3548_, lean_object* v_hyps_3549_, uint8_t v_subsingletonInstImplicitRhs_3550_, lean_object* v_f_3551_, lean_object* v_info_3552_, lean_object* v_kinds_3553_, lean_object* v_lhss_3554_, lean_object* v_name_3555_, uint8_t v_bi_3556_, lean_object* v_type_3557_, uint8_t v_kind_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_box(v_subsingletonInstImplicitRhs_3550_);
v___f_3565_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3565_, 0, v_i_3545_);
lean_closure_set(v___f_3565_, 1, v_rhss_3546_);
lean_closure_set(v___f_3565_, 2, v_lhs_3547_);
lean_closure_set(v___f_3565_, 3, v_eqs_3548_);
lean_closure_set(v___f_3565_, 4, v_hyps_3549_);
lean_closure_set(v___f_3565_, 5, v___x_3564_);
lean_closure_set(v___f_3565_, 6, v_f_3551_);
lean_closure_set(v___f_3565_, 7, v_info_3552_);
lean_closure_set(v___f_3565_, 8, v_kinds_3553_);
lean_closure_set(v___f_3565_, 9, v_lhss_3554_);
v___x_3566_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3555_, v_bi_3556_, v_type_3557_, v___f_3565_, v_kind_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
v_a_3575_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3566_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3566_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3583_, lean_object* v_rhss_3584_, lean_object* v_lhss_3585_, lean_object* v_i_3586_, lean_object* v_eqs_3587_, lean_object* v_hyps_3588_, uint8_t v_subsingletonInstImplicitRhs_3589_, lean_object* v_f_3590_, lean_object* v_info_3591_, lean_object* v_kinds_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; 
lean_inc(v___y_3596_);
lean_inc_ref(v___y_3595_);
lean_inc(v___y_3594_);
lean_inc_ref(v___y_3593_);
lean_inc_ref(v_lhs_3583_);
v___x_3598_ = lean_infer_type(v_lhs_3583_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; uint8_t v___y_3606_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = lean_array_get_size(v_rhss_3584_);
v___x_3601_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3585_);
v___x_3602_ = l_Array_toSubarray___redArg(v_lhss_3585_, v___x_3601_, v___x_3600_);
v___x_3603_ = l_Subarray_copy___redArg(v___x_3602_);
v___x_3604_ = l_Lean_Expr_replaceFVars(v_a_3599_, v___x_3603_, v_rhss_3584_);
lean_dec_ref(v___x_3603_);
lean_dec(v_a_3599_);
if (v_subsingletonInstImplicitRhs_3589_ == 0)
{
uint8_t v___x_3621_; 
v___x_3621_ = 1;
v___y_3606_ = v___x_3621_;
goto v___jp_3605_;
}
else
{
uint8_t v___x_3622_; 
v___x_3622_ = 3;
v___y_3606_ = v___x_3622_;
goto v___jp_3605_;
}
v___jp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = l_Lean_Expr_fvarId_x21(v_lhs_3583_);
v___x_3608_ = l_Lean_FVarId_getDecl___redArg(v___x_3607_, v___y_3593_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; lean_object* v___x_3612_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3610_ = l_Lean_LocalDecl_userName(v_a_3609_);
lean_dec(v_a_3609_);
v___x_3611_ = 0;
v___x_3612_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3586_, v_rhss_3584_, v_lhs_3583_, v_eqs_3587_, v_hyps_3588_, v_subsingletonInstImplicitRhs_3589_, v_f_3590_, v_info_3591_, v_kinds_3592_, v_lhss_3585_, v___x_3610_, v___y_3606_, v___x_3604_, v___x_3611_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v___x_3612_;
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec_ref(v___x_3604_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec_ref(v_kinds_3592_);
lean_dec_ref(v_info_3591_);
lean_dec_ref(v_f_3590_);
lean_dec_ref(v_hyps_3588_);
lean_dec_ref(v_eqs_3587_);
lean_dec(v_i_3586_);
lean_dec_ref(v_lhss_3585_);
lean_dec_ref(v_rhss_3584_);
lean_dec_ref(v_lhs_3583_);
v_a_3613_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3608_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3608_);
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
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec_ref(v_kinds_3592_);
lean_dec_ref(v_info_3591_);
lean_dec_ref(v_f_3590_);
lean_dec_ref(v_hyps_3588_);
lean_dec_ref(v_eqs_3587_);
lean_dec(v_i_3586_);
lean_dec_ref(v_lhss_3585_);
lean_dec_ref(v_rhss_3584_);
lean_dec_ref(v_lhs_3583_);
v_a_3623_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3598_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3598_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3631_, lean_object* v_rhss_3632_, lean_object* v_lhss_3633_, lean_object* v_i_3634_, lean_object* v_eqs_3635_, lean_object* v_hyps_3636_, lean_object* v_subsingletonInstImplicitRhs_3637_, lean_object* v_f_3638_, lean_object* v_info_3639_, lean_object* v_kinds_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3646_; lean_object* v_res_3647_; 
v_subsingletonInstImplicitRhs_boxed_3646_ = lean_unbox(v_subsingletonInstImplicitRhs_3637_);
v_res_3647_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3631_, v_rhss_3632_, v_lhss_3633_, v_i_3634_, v_eqs_3635_, v_hyps_3636_, v_subsingletonInstImplicitRhs_boxed_3646_, v_f_3638_, v_info_3639_, v_kinds_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v_res_3647_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3650_ = lean_unsigned_to_nat(38u);
v___x_3651_ = lean_unsigned_to_nat(328u);
v___x_3652_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3653_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3654_ = l_mkPanicMessageWithDecl(v___x_3653_, v___x_3652_, v___x_3651_, v___x_3650_, v___x_3649_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3655_, lean_object* v_f_3656_, lean_object* v_info_3657_, lean_object* v_kinds_3658_, lean_object* v_lhss_3659_, lean_object* v_i_3660_, lean_object* v_rhss_3661_, lean_object* v_eqs_3662_, lean_object* v_hyps_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v___x_3669_; uint8_t v___x_3670_; 
v___x_3669_ = lean_array_get_size(v_kinds_3658_);
v___x_3670_ = lean_nat_dec_eq(v_i_3660_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; lean_object* v_lhs_3672_; lean_object* v_hyps_3673_; uint8_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
v___x_3671_ = l_Lean_instInhabitedExpr;
v_lhs_3672_ = lean_array_get_borrowed(v___x_3671_, v_lhss_3659_, v_i_3660_);
lean_inc(v_lhs_3672_);
v_hyps_3673_ = lean_array_push(v_hyps_3663_, v_lhs_3672_);
v___x_3674_ = 0;
v___x_3675_ = lean_box(v___x_3674_);
v___x_3676_ = lean_array_get(v___x_3675_, v_kinds_3658_, v_i_3660_);
lean_dec(v___x_3675_);
v___x_3677_ = lean_unbox(v___x_3676_);
lean_dec(v___x_3676_);
switch(v___x_3677_)
{
case 0:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3678_ = lean_unsigned_to_nat(1u);
v___x_3679_ = lean_nat_add(v_i_3660_, v___x_3678_);
lean_dec(v_i_3660_);
lean_inc(v_lhs_3672_);
v___x_3680_ = lean_array_push(v_rhss_3661_, v_lhs_3672_);
v___x_3681_ = lean_box(0);
v___x_3682_ = lean_array_push(v_eqs_3662_, v___x_3681_);
v_i_3660_ = v___x_3679_;
v_rhss_3661_ = v___x_3680_;
v_eqs_3662_ = v___x_3682_;
v_hyps_3663_ = v_hyps_3673_;
goto _start;
}
case 2:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_inc(v_lhs_3672_);
v___x_3684_ = l_Lean_Expr_fvarId_x21(v_lhs_3672_);
v___x_3685_ = l_Lean_FVarId_getDecl___redArg(v___x_3684_, v_a_3664_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v___x_3687_ = l_Lean_LocalDecl_userName(v_a_3686_);
v___x_3688_ = l_Lean_LocalDecl_binderInfo(v_a_3686_);
v___x_3689_ = l_Lean_LocalDecl_type(v_a_3686_);
lean_dec(v_a_3686_);
v___x_3690_ = 0;
lean_inc(v___x_3687_);
v___x_3691_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3660_, v_rhss_3661_, v_eqs_3662_, v_hyps_3673_, v_subsingletonInstImplicitRhs_3655_, v_f_3656_, v_info_3657_, v_kinds_3658_, v_lhss_3659_, v_lhs_3672_, v___x_3687_, v___x_3687_, v___x_3688_, v___x_3689_, v___x_3690_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
return v___x_3691_;
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec_ref(v_hyps_3673_);
lean_dec(v_lhs_3672_);
lean_dec_ref(v_eqs_3662_);
lean_dec_ref(v_rhss_3661_);
lean_dec(v_i_3660_);
lean_dec_ref(v_lhss_3659_);
lean_dec_ref(v_kinds_3658_);
lean_dec_ref(v_info_3657_);
lean_dec_ref(v_f_3656_);
v_a_3692_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3685_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3685_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
case 3:
{
lean_object* v___x_3700_; 
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
lean_inc(v_a_3665_);
lean_inc_ref(v_a_3664_);
lean_inc(v_lhs_3672_);
v___x_3700_ = lean_infer_type(v_lhs_3672_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v_paramInfo_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v_backDeps_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v_paramInfo_3702_ = lean_ctor_get(v_info_3657_, 0);
v___x_3703_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_3704_ = lean_array_get_borrowed(v___x_3703_, v_paramInfo_3702_, v_i_3660_);
v_backDeps_3705_ = lean_ctor_get(v___x_3704_, 0);
v___x_3706_ = lean_array_get_size(v_rhss_3661_);
v___x_3707_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3659_);
v___x_3708_ = l_Array_toSubarray___redArg(v_lhss_3659_, v___x_3707_, v___x_3706_);
v___x_3709_ = l_Subarray_copy___redArg(v___x_3708_);
v___x_3710_ = l_Lean_Expr_replaceFVars(v_a_3701_, v___x_3709_, v_rhss_3661_);
lean_dec_ref(v___x_3709_);
lean_dec(v_a_3701_);
v___x_3711_ = l_Lean_Expr_fvarId_x21(v_lhs_3672_);
v___x_3712_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3711_, v___x_3710_, v_backDeps_3705_, v_eqs_3662_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v___x_3714_ = lean_unsigned_to_nat(1u);
v___x_3715_ = lean_nat_add(v_i_3660_, v___x_3714_);
lean_dec(v_i_3660_);
v___x_3716_ = lean_array_push(v_rhss_3661_, v_a_3713_);
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_array_push(v_eqs_3662_, v___x_3717_);
v_i_3660_ = v___x_3715_;
v_rhss_3661_ = v___x_3716_;
v_eqs_3662_ = v___x_3718_;
v_hyps_3663_ = v_hyps_3673_;
goto _start;
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v_hyps_3673_);
lean_dec_ref(v_eqs_3662_);
lean_dec_ref(v_rhss_3661_);
lean_dec(v_i_3660_);
lean_dec_ref(v_lhss_3659_);
lean_dec_ref(v_kinds_3658_);
lean_dec_ref(v_info_3657_);
lean_dec_ref(v_f_3656_);
v_a_3720_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3712_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3712_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec_ref(v_hyps_3673_);
lean_dec_ref(v_eqs_3662_);
lean_dec_ref(v_rhss_3661_);
lean_dec(v_i_3660_);
lean_dec_ref(v_lhss_3659_);
lean_dec_ref(v_kinds_3658_);
lean_dec_ref(v_info_3657_);
lean_dec_ref(v_f_3656_);
v_a_3728_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3700_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3700_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
case 5:
{
lean_object* v___x_3736_; lean_object* v___f_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_inc_n(v_lhs_3672_, 2);
v___x_3736_ = lean_box(v_subsingletonInstImplicitRhs_3655_);
v___f_3737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3737_, 0, v_lhs_3672_);
lean_closure_set(v___f_3737_, 1, v_rhss_3661_);
lean_closure_set(v___f_3737_, 2, v_lhss_3659_);
lean_closure_set(v___f_3737_, 3, v_i_3660_);
lean_closure_set(v___f_3737_, 4, v_eqs_3662_);
lean_closure_set(v___f_3737_, 5, v_hyps_3673_);
lean_closure_set(v___f_3737_, 6, v___x_3736_);
lean_closure_set(v___f_3737_, 7, v_f_3656_);
lean_closure_set(v___f_3737_, 8, v_info_3657_);
lean_closure_set(v___f_3737_, 9, v_kinds_3658_);
v___x_3738_ = lean_unsigned_to_nat(1u);
v___x_3739_ = lean_mk_empty_array_with_capacity(v___x_3738_);
v___x_3740_ = lean_array_push(v___x_3739_, v_lhs_3672_);
v___x_3741_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v___x_3740_, v___f_3737_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
return v___x_3741_;
}
default: 
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_dec_ref(v_hyps_3673_);
lean_dec_ref(v_eqs_3662_);
lean_dec_ref(v_rhss_3661_);
lean_dec(v_i_3660_);
lean_dec_ref(v_lhss_3659_);
lean_dec_ref(v_kinds_3658_);
lean_dec_ref(v_info_3657_);
lean_dec_ref(v_f_3656_);
v___x_3742_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3743_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v___x_3742_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
return v___x_3743_;
}
}
}
else
{
lean_object* v_lhs_3744_; lean_object* v_rhs_3745_; lean_object* v___x_3746_; 
lean_dec_ref(v_eqs_3662_);
lean_dec(v_i_3660_);
lean_dec_ref(v_info_3657_);
lean_inc_ref(v_f_3656_);
v_lhs_3744_ = l_Lean_mkAppN(v_f_3656_, v_lhss_3659_);
lean_dec_ref(v_lhss_3659_);
v_rhs_3745_ = l_Lean_mkAppN(v_f_3656_, v_rhss_3661_);
lean_dec_ref(v_rhss_3661_);
v___x_3746_ = l_Lean_Meta_mkEq(v_lhs_3744_, v_rhs_3745_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; uint8_t v___x_3748_; uint8_t v___x_3749_; lean_object* v___x_3750_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
v___x_3748_ = 0;
v___x_3749_ = 1;
v___x_3750_ = l_Lean_Meta_mkForallFVars(v_hyps_3663_, v_a_3747_, v___x_3748_, v___x_3670_, v___x_3670_, v___x_3749_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
lean_dec_ref(v_hyps_3663_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3752_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc_n(v_a_3751_, 2);
lean_dec_ref_known(v___x_3750_, 1);
lean_inc_ref(v_kinds_3658_);
v___x_3752_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3751_, v_kinds_3658_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3761_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3755_ = v___x_3752_;
v_isShared_3756_ = v_isSharedCheck_3761_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3752_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3761_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3757_; lean_object* v___x_3759_; 
v___x_3757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3757_, 0, v_a_3751_);
lean_ctor_set(v___x_3757_, 1, v_a_3753_);
lean_ctor_set(v___x_3757_, 2, v_kinds_3658_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v___x_3757_);
v___x_3759_ = v___x_3755_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v_a_3751_);
lean_dec_ref(v_kinds_3658_);
v_a_3762_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3752_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3752_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v_kinds_3658_);
v_a_3770_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3750_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3750_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v_hyps_3663_);
lean_dec_ref(v_kinds_3658_);
v_a_3778_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3746_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3746_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3786_, lean_object* v_rhss_3787_, lean_object* v_b_3788_, lean_object* v_eqs_3789_, lean_object* v_hyps_3790_, uint8_t v_subsingletonInstImplicitRhs_3791_, lean_object* v_f_3792_, lean_object* v_info_3793_, lean_object* v_kinds_3794_, lean_object* v_lhss_3795_, lean_object* v_eq_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3802_ = lean_unsigned_to_nat(1u);
v___x_3803_ = lean_nat_add(v_i_3786_, v___x_3802_);
lean_inc_ref(v_b_3788_);
v___x_3804_ = lean_array_push(v_rhss_3787_, v_b_3788_);
v___x_3805_ = l_Lean_Expr_fvarId_x21(v_eq_3796_);
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
v___x_3808_ = lean_array_push(v_eqs_3789_, v___x_3807_);
v___x_3809_ = lean_array_push(v_hyps_3790_, v_b_3788_);
v___x_3810_ = lean_array_push(v___x_3809_, v_eq_3796_);
v___x_3811_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3791_, v_f_3792_, v_info_3793_, v_kinds_3794_, v_lhss_3795_, v___x_3803_, v___x_3804_, v___x_3808_, v___x_3810_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_3812_, lean_object* v_rhss_3813_, lean_object* v_b_3814_, lean_object* v_eqs_3815_, lean_object* v_hyps_3816_, lean_object* v_subsingletonInstImplicitRhs_3817_, lean_object* v_f_3818_, lean_object* v_info_3819_, lean_object* v_kinds_3820_, lean_object* v_lhss_3821_, lean_object* v_eq_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3828_; lean_object* v_res_3829_; 
v_subsingletonInstImplicitRhs_boxed_3828_ = lean_unbox(v_subsingletonInstImplicitRhs_3817_);
v_res_3829_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3812_, v_rhss_3813_, v_b_3814_, v_eqs_3815_, v_hyps_3816_, v_subsingletonInstImplicitRhs_boxed_3828_, v_f_3818_, v_info_3819_, v_kinds_3820_, v_lhss_3821_, v_eq_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v_i_3812_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(lean_object* v_lhs_3831_, lean_object* v_i_3832_, lean_object* v_rhss_3833_, lean_object* v_eqs_3834_, lean_object* v_hyps_3835_, uint8_t v_subsingletonInstImplicitRhs_3836_, lean_object* v_f_3837_, lean_object* v_info_3838_, lean_object* v_kinds_3839_, lean_object* v_lhss_3840_, lean_object* v___x_3841_, lean_object* v_b_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; 
lean_inc_ref(v_b_3842_);
v___x_3848_ = l_Lean_Meta_mkEq(v_lhs_3831_, v_b_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3850_; lean_object* v___f_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
v___x_3850_ = lean_box(v_subsingletonInstImplicitRhs_3836_);
v___f_3851_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3851_, 0, v_i_3832_);
lean_closure_set(v___f_3851_, 1, v_rhss_3833_);
lean_closure_set(v___f_3851_, 2, v_b_3842_);
lean_closure_set(v___f_3851_, 3, v_eqs_3834_);
lean_closure_set(v___f_3851_, 4, v_hyps_3835_);
lean_closure_set(v___f_3851_, 5, v___x_3850_);
lean_closure_set(v___f_3851_, 6, v_f_3837_);
lean_closure_set(v___f_3851_, 7, v_info_3838_);
lean_closure_set(v___f_3851_, 8, v_kinds_3839_);
lean_closure_set(v___f_3851_, 9, v_lhss_3840_);
v___x_3852_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0));
v___x_3853_ = lean_name_append_before(v___x_3841_, v___x_3852_);
v___x_3854_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3853_, v_a_3849_, v___f_3851_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3854_;
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec_ref(v_b_3842_);
lean_dec(v___x_3841_);
lean_dec_ref(v_lhss_3840_);
lean_dec_ref(v_kinds_3839_);
lean_dec_ref(v_info_3838_);
lean_dec_ref(v_f_3837_);
lean_dec_ref(v_hyps_3835_);
lean_dec_ref(v_eqs_3834_);
lean_dec_ref(v_rhss_3833_);
lean_dec(v_i_3832_);
v_a_3855_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3848_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3848_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v_lhs_3863_ = _args[0];
lean_object* v_i_3864_ = _args[1];
lean_object* v_rhss_3865_ = _args[2];
lean_object* v_eqs_3866_ = _args[3];
lean_object* v_hyps_3867_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3868_ = _args[5];
lean_object* v_f_3869_ = _args[6];
lean_object* v_info_3870_ = _args[7];
lean_object* v_kinds_3871_ = _args[8];
lean_object* v_lhss_3872_ = _args[9];
lean_object* v___x_3873_ = _args[10];
lean_object* v_b_3874_ = _args[11];
lean_object* v___y_3875_ = _args[12];
lean_object* v___y_3876_ = _args[13];
lean_object* v___y_3877_ = _args[14];
lean_object* v___y_3878_ = _args[15];
lean_object* v___y_3879_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3880_; lean_object* v_res_3881_; 
v_subsingletonInstImplicitRhs_boxed_3880_ = lean_unbox(v_subsingletonInstImplicitRhs_3868_);
v_res_3881_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(v_lhs_3863_, v_i_3864_, v_rhss_3865_, v_eqs_3866_, v_hyps_3867_, v_subsingletonInstImplicitRhs_boxed_3880_, v_f_3869_, v_info_3870_, v_kinds_3871_, v_lhss_3872_, v___x_3873_, v_b_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_3882_, lean_object* v_rhss_3883_, lean_object* v_eqs_3884_, lean_object* v_hyps_3885_, uint8_t v_subsingletonInstImplicitRhs_3886_, lean_object* v_f_3887_, lean_object* v_info_3888_, lean_object* v_kinds_3889_, lean_object* v_lhss_3890_, lean_object* v_lhs_3891_, lean_object* v___x_3892_, lean_object* v_name_3893_, uint8_t v_bi_3894_, lean_object* v_type_3895_, uint8_t v_kind_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; lean_object* v___f_3903_; lean_object* v___x_3904_; 
v___x_3902_ = lean_box(v_subsingletonInstImplicitRhs_3886_);
v___f_3903_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3903_, 0, v_lhs_3891_);
lean_closure_set(v___f_3903_, 1, v_i_3882_);
lean_closure_set(v___f_3903_, 2, v_rhss_3883_);
lean_closure_set(v___f_3903_, 3, v_eqs_3884_);
lean_closure_set(v___f_3903_, 4, v_hyps_3885_);
lean_closure_set(v___f_3903_, 5, v___x_3902_);
lean_closure_set(v___f_3903_, 6, v_f_3887_);
lean_closure_set(v___f_3903_, 7, v_info_3888_);
lean_closure_set(v___f_3903_, 8, v_kinds_3889_);
lean_closure_set(v___f_3903_, 9, v_lhss_3890_);
lean_closure_set(v___f_3903_, 10, v___x_3892_);
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
lean_object* v_eqs_3923_ = _args[2];
lean_object* v_hyps_3924_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3925_ = _args[4];
lean_object* v_f_3926_ = _args[5];
lean_object* v_info_3927_ = _args[6];
lean_object* v_kinds_3928_ = _args[7];
lean_object* v_lhss_3929_ = _args[8];
lean_object* v_lhs_3930_ = _args[9];
lean_object* v___x_3931_ = _args[10];
lean_object* v_name_3932_ = _args[11];
lean_object* v_bi_3933_ = _args[12];
lean_object* v_type_3934_ = _args[13];
lean_object* v_kind_3935_ = _args[14];
lean_object* v___y_3936_ = _args[15];
lean_object* v___y_3937_ = _args[16];
lean_object* v___y_3938_ = _args[17];
lean_object* v___y_3939_ = _args[18];
lean_object* v___y_3940_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3941_; uint8_t v_bi_boxed_3942_; uint8_t v_kind_boxed_3943_; lean_object* v_res_3944_; 
v_subsingletonInstImplicitRhs_boxed_3941_ = lean_unbox(v_subsingletonInstImplicitRhs_3925_);
v_bi_boxed_3942_ = lean_unbox(v_bi_3933_);
v_kind_boxed_3943_ = lean_unbox(v_kind_3935_);
v_res_3944_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3921_, v_rhss_3922_, v_eqs_3923_, v_hyps_3924_, v_subsingletonInstImplicitRhs_boxed_3941_, v_f_3926_, v_info_3927_, v_kinds_3928_, v_lhss_3929_, v_lhs_3930_, v___x_3931_, v_name_3932_, v_bi_boxed_3942_, v_type_3934_, v_kind_boxed_3943_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_3945_ = _args[0];
lean_object* v_rhss_3946_ = _args[1];
lean_object* v_lhs_3947_ = _args[2];
lean_object* v_eqs_3948_ = _args[3];
lean_object* v_hyps_3949_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3950_ = _args[5];
lean_object* v_f_3951_ = _args[6];
lean_object* v_info_3952_ = _args[7];
lean_object* v_kinds_3953_ = _args[8];
lean_object* v_lhss_3954_ = _args[9];
lean_object* v_name_3955_ = _args[10];
lean_object* v_bi_3956_ = _args[11];
lean_object* v_type_3957_ = _args[12];
lean_object* v_kind_3958_ = _args[13];
lean_object* v___y_3959_ = _args[14];
lean_object* v___y_3960_ = _args[15];
lean_object* v___y_3961_ = _args[16];
lean_object* v___y_3962_ = _args[17];
lean_object* v___y_3963_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3964_; uint8_t v_bi_boxed_3965_; uint8_t v_kind_boxed_3966_; lean_object* v_res_3967_; 
v_subsingletonInstImplicitRhs_boxed_3964_ = lean_unbox(v_subsingletonInstImplicitRhs_3950_);
v_bi_boxed_3965_ = lean_unbox(v_bi_3956_);
v_kind_boxed_3966_ = lean_unbox(v_kind_3958_);
v_res_3967_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3945_, v_rhss_3946_, v_lhs_3947_, v_eqs_3948_, v_hyps_3949_, v_subsingletonInstImplicitRhs_boxed_3964_, v_f_3951_, v_info_3952_, v_kinds_3953_, v_lhss_3954_, v_name_3955_, v_bi_boxed_3965_, v_type_3957_, v_kind_boxed_3966_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
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
lean_inc(v_a_4115_);
if (lean_obj_tag(v_a_4115_) == 1)
{
lean_dec_ref_known(v_a_4115_, 1);
lean_dec_ref(v_kinds_4107_);
lean_dec_ref(v_info_4106_);
lean_dec_ref(v_f_4105_);
return v___x_4114_;
}
else
{
lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4128_; 
lean_dec(v_a_4115_);
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
static lean_object* _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4188_ = lean_string_utf8_byte_size(v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4189_){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4190_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4191_ = lean_string_utf8_byte_size(v_s_4189_);
v___x_4192_ = lean_obj_once(&l_Lean_Meta_isHCongrReservedNameSuffix___closed__0, &l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0);
v___x_4193_ = lean_nat_dec_le(v___x_4192_, v___x_4191_);
if (v___x_4193_ == 0)
{
lean_dec_ref(v_s_4189_);
return v___x_4193_;
}
else
{
lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4194_ = lean_unsigned_to_nat(0u);
v___x_4195_ = lean_string_memcmp(v_s_4189_, v___x_4190_, v___x_4194_, v___x_4194_, v___x_4192_);
if (v___x_4195_ == 0)
{
lean_dec_ref(v_s_4189_);
return v___x_4195_;
}
else
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v___x_4196_ = lean_unsigned_to_nat(7u);
lean_inc_ref(v_s_4189_);
v___x_4197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4197_, 0, v_s_4189_);
lean_ctor_set(v___x_4197_, 1, v___x_4194_);
lean_ctor_set(v___x_4197_, 2, v___x_4191_);
v___x_4198_ = l_String_Slice_Pos_nextn(v___x_4197_, v___x_4194_, v___x_4196_);
lean_dec_ref_known(v___x_4197_, 3);
v___x_4199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4199_, 0, v_s_4189_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
lean_ctor_set(v___x_4199_, 2, v___x_4191_);
v___x_4200_ = l_String_Slice_isNat(v___x_4199_);
lean_dec_ref_known(v___x_4199_, 3);
return v___x_4200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* v_s_4201_){
_start:
{
uint8_t v_res_4202_; lean_object* v_r_4203_; 
v_res_4202_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4201_);
v_r_4203_ = lean_box(v_res_4202_);
return v_r_4203_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4253_ = lean_unsigned_to_nat(3482611248u);
v___x_4254_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4255_ = l_Lean_Name_num___override(v___x_4254_, v___x_4253_);
return v___x_4255_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4257_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4258_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4259_ = l_Lean_Name_str___override(v___x_4258_, v___x_4257_);
return v___x_4259_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4261_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4262_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4263_ = l_Lean_Name_str___override(v___x_4262_, v___x_4261_);
return v___x_4263_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4264_ = lean_unsigned_to_nat(2u);
v___x_4265_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4266_ = l_Lean_Name_num___override(v___x_4265_, v___x_4264_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4268_; uint8_t v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4268_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4269_ = 0;
v___x_4270_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4271_ = l_Lean_registerTraceClass(v___x_4268_, v___x_4269_, v___x_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4274_, lean_object* v_as_4275_, size_t v_i_4276_, size_t v_stop_4277_, lean_object* v_b_4278_){
_start:
{
lean_object* v___y_4280_; uint8_t v___x_4284_; 
v___x_4284_ = lean_usize_dec_eq(v_i_4276_, v_stop_4277_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; lean_object* v_fst_4286_; uint8_t v___x_4287_; 
v___x_4285_ = lean_array_uget_borrowed(v_as_4275_, v_i_4276_);
v_fst_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_fst_4286_);
lean_inc_ref(v_env_4274_);
v___x_4287_ = l_Lean_Environment_contains(v_env_4274_, v_fst_4286_, v___x_4284_);
if (v___x_4287_ == 0)
{
v___y_4280_ = v_b_4278_;
goto v___jp_4279_;
}
else
{
lean_object* v___x_4288_; 
lean_inc(v___x_4285_);
v___x_4288_ = lean_array_push(v_b_4278_, v___x_4285_);
v___y_4280_ = v___x_4288_;
goto v___jp_4279_;
}
}
else
{
lean_dec_ref(v_env_4274_);
return v_b_4278_;
}
v___jp_4279_:
{
size_t v___x_4281_; size_t v___x_4282_; 
v___x_4281_ = ((size_t)1ULL);
v___x_4282_ = lean_usize_add(v_i_4276_, v___x_4281_);
v_i_4276_ = v___x_4282_;
v_b_4278_ = v___y_4280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4289_, lean_object* v_as_4290_, lean_object* v_i_4291_, lean_object* v_stop_4292_, lean_object* v_b_4293_){
_start:
{
size_t v_i_boxed_4294_; size_t v_stop_boxed_4295_; lean_object* v_res_4296_; 
v_i_boxed_4294_ = lean_unbox_usize(v_i_4291_);
lean_dec(v_i_4291_);
v_stop_boxed_4295_ = lean_unbox_usize(v_stop_4292_);
lean_dec(v_stop_4292_);
v_res_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4289_, v_as_4290_, v_i_boxed_4294_, v_stop_boxed_4295_, v_b_4293_);
lean_dec_ref(v_as_4290_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4297_, lean_object* v_x_4298_){
_start:
{
if (lean_obj_tag(v_x_4298_) == 0)
{
lean_object* v_k_4299_; lean_object* v_v_4300_; lean_object* v_l_4301_; lean_object* v_r_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_k_4299_ = lean_ctor_get(v_x_4298_, 1);
v_v_4300_ = lean_ctor_get(v_x_4298_, 2);
v_l_4301_ = lean_ctor_get(v_x_4298_, 3);
v_r_4302_ = lean_ctor_get(v_x_4298_, 4);
v___x_4303_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4297_, v_l_4301_);
lean_inc(v_v_4300_);
lean_inc(v_k_4299_);
v___x_4304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4304_, 0, v_k_4299_);
lean_ctor_set(v___x_4304_, 1, v_v_4300_);
v___x_4305_ = lean_array_push(v___x_4303_, v___x_4304_);
v_init_4297_ = v___x_4305_;
v_x_4298_ = v_r_4302_;
goto _start;
}
else
{
return v_init_4297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4307_, lean_object* v_x_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4307_, v_x_4308_);
lean_dec(v_x_4308_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4316_, lean_object* v_s_4317_){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; 
v___x_4318_ = lean_unsigned_to_nat(0u);
v___x_4319_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4320_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4319_, v_s_4317_);
v___x_4321_ = lean_array_get_size(v___x_4320_);
v___x_4322_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4323_ = lean_nat_dec_lt(v___x_4318_, v___x_4321_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4324_; 
lean_dec_ref(v___x_4320_);
lean_dec_ref(v_env_4316_);
v___x_4324_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4324_;
}
else
{
uint8_t v___x_4325_; 
v___x_4325_ = lean_nat_dec_le(v___x_4321_, v___x_4321_);
if (v___x_4325_ == 0)
{
if (v___x_4323_ == 0)
{
lean_object* v___x_4326_; 
lean_dec_ref(v___x_4320_);
lean_dec_ref(v_env_4316_);
v___x_4326_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4326_;
}
else
{
size_t v___x_4327_; size_t v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4327_ = ((size_t)0ULL);
v___x_4328_ = lean_usize_of_nat(v___x_4321_);
v___x_4329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4316_, v___x_4320_, v___x_4327_, v___x_4328_, v___x_4322_);
lean_dec_ref(v___x_4320_);
lean_inc_ref_n(v___x_4329_, 2);
v___x_4330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
lean_ctor_set(v___x_4330_, 2, v___x_4329_);
return v___x_4330_;
}
}
else
{
size_t v___x_4331_; size_t v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4331_ = ((size_t)0ULL);
v___x_4332_ = lean_usize_of_nat(v___x_4321_);
v___x_4333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4316_, v___x_4320_, v___x_4331_, v___x_4332_, v___x_4322_);
lean_dec_ref(v___x_4320_);
lean_inc_ref_n(v___x_4333_, 2);
v___x_4334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
lean_ctor_set(v___x_4334_, 2, v___x_4333_);
return v___x_4334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4335_, lean_object* v_s_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4335_, v_s_4336_);
lean_dec(v_s_4336_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___f_4347_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4348_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4349_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4350_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4348_, v___x_4349_, v___f_4347_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4353_, lean_object* v_t_4354_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4353_, v_t_4354_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4356_, lean_object* v_t_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4356_, v_t_4357_);
lean_dec(v_t_4357_);
return v_res_4358_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object* v_env_4359_, lean_object* v_n_4360_){
_start:
{
if (lean_obj_tag(v_n_4360_) == 1)
{
lean_object* v_pre_4361_; lean_object* v_str_4362_; uint8_t v___y_4364_; uint8_t v___x_4366_; 
v_pre_4361_ = lean_ctor_get(v_n_4360_, 0);
lean_inc(v_pre_4361_);
v_str_4362_ = lean_ctor_get(v_n_4360_, 1);
lean_inc_ref_n(v_str_4362_, 2);
lean_dec_ref_known(v_n_4360_, 2);
v___x_4366_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4362_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; uint8_t v___x_4368_; 
v___x_4367_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4368_ = lean_string_dec_eq(v_str_4362_, v___x_4367_);
lean_dec_ref(v_str_4362_);
v___y_4364_ = v___x_4368_;
goto v___jp_4363_;
}
else
{
lean_dec_ref(v_str_4362_);
v___y_4364_ = v___x_4366_;
goto v___jp_4363_;
}
v___jp_4363_:
{
if (v___y_4364_ == 0)
{
lean_dec(v_pre_4361_);
lean_dec_ref(v_env_4359_);
return v___y_4364_;
}
else
{
uint8_t v___x_4365_; 
v___x_4365_ = l_Lean_Environment_contains(v_env_4359_, v_pre_4361_, v___y_4364_);
return v___x_4365_;
}
}
}
else
{
uint8_t v___x_4369_; 
lean_dec(v_n_4360_);
lean_dec_ref(v_env_4359_);
v___x_4369_ = 0;
return v___x_4369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_env_4370_, lean_object* v_n_4371_){
_start:
{
uint8_t v_res_4372_; lean_object* v_r_4373_; 
v_res_4372_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4370_, v_n_4371_);
v_r_4373_ = lean_box(v_res_4372_);
return v_r_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4376_; lean_object* v___x_4377_; 
v___f_4376_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_));
v___x_4377_ = l_Lean_registerReservedNamePredicate(v___f_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_a_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object* v_thm_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; lean_object* v_env_4384_; lean_object* v_toConstantVal_4385_; lean_object* v_value_4386_; lean_object* v_all_4387_; uint8_t v___y_4389_; lean_object* v_type_4397_; uint8_t v___x_4398_; 
v___x_4383_ = lean_st_ref_get(v___y_4381_);
v_env_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc_ref_n(v_env_4384_, 2);
lean_dec(v___x_4383_);
v_toConstantVal_4385_ = lean_ctor_get(v_thm_4380_, 0);
v_value_4386_ = lean_ctor_get(v_thm_4380_, 1);
v_all_4387_ = lean_ctor_get(v_thm_4380_, 2);
v_type_4397_ = lean_ctor_get(v_toConstantVal_4385_, 2);
v___x_4398_ = l_Lean_Environment_hasUnsafe(v_env_4384_, v_type_4397_);
if (v___x_4398_ == 0)
{
uint8_t v___x_4399_; 
v___x_4399_ = l_Lean_Environment_hasUnsafe(v_env_4384_, v_value_4386_);
v___y_4389_ = v___x_4399_;
goto v___jp_4388_;
}
else
{
lean_dec_ref(v_env_4384_);
v___y_4389_ = v___x_4398_;
goto v___jp_4388_;
}
v___jp_4388_:
{
if (v___y_4389_ == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4390_, 0, v_thm_4380_);
v___x_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
return v___x_4391_;
}
else
{
lean_object* v___x_4392_; uint8_t v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
lean_inc(v_all_4387_);
lean_inc_ref(v_value_4386_);
lean_inc_ref(v_toConstantVal_4385_);
lean_dec_ref(v_thm_4380_);
v___x_4392_ = lean_box(0);
v___x_4393_ = 0;
v___x_4394_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4394_, 0, v_toConstantVal_4385_);
lean_ctor_set(v___x_4394_, 1, v_value_4386_);
lean_ctor_set(v___x_4394_, 2, v___x_4392_);
lean_ctor_set(v___x_4394_, 3, v_all_4387_);
lean_ctor_set_uint8(v___x_4394_, sizeof(void*)*4, v___x_4393_);
v___x_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_thm_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4400_, v___y_4401_);
lean_dec(v___y_4401_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_thm_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4404_, v___y_4408_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object* v_thm_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
return v_res_4417_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_4418_; double v___x_4419_; 
v___x_4418_ = lean_unsigned_to_nat(0u);
v___x_4419_ = lean_float_of_nat(v___x_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_cls_4423_, lean_object* v_msg_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v_ref_4430_; lean_object* v___x_4431_; lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4476_; 
v_ref_4430_ = lean_ctor_get(v___y_4427_, 5);
v___x_4431_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4434_ = v___x_4431_;
v_isShared_4435_ = v_isSharedCheck_4476_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4431_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4476_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; lean_object* v_traceState_4437_; lean_object* v_env_4438_; lean_object* v_nextMacroScope_4439_; lean_object* v_ngen_4440_; lean_object* v_auxDeclNGen_4441_; lean_object* v_cache_4442_; lean_object* v_messages_4443_; lean_object* v_infoState_4444_; lean_object* v_snapshotTasks_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4475_; 
v___x_4436_ = lean_st_ref_take(v___y_4428_);
v_traceState_4437_ = lean_ctor_get(v___x_4436_, 4);
v_env_4438_ = lean_ctor_get(v___x_4436_, 0);
v_nextMacroScope_4439_ = lean_ctor_get(v___x_4436_, 1);
v_ngen_4440_ = lean_ctor_get(v___x_4436_, 2);
v_auxDeclNGen_4441_ = lean_ctor_get(v___x_4436_, 3);
v_cache_4442_ = lean_ctor_get(v___x_4436_, 5);
v_messages_4443_ = lean_ctor_get(v___x_4436_, 6);
v_infoState_4444_ = lean_ctor_get(v___x_4436_, 7);
v_snapshotTasks_4445_ = lean_ctor_get(v___x_4436_, 8);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4447_ = v___x_4436_;
v_isShared_4448_ = v_isSharedCheck_4475_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_snapshotTasks_4445_);
lean_inc(v_infoState_4444_);
lean_inc(v_messages_4443_);
lean_inc(v_cache_4442_);
lean_inc(v_traceState_4437_);
lean_inc(v_auxDeclNGen_4441_);
lean_inc(v_ngen_4440_);
lean_inc(v_nextMacroScope_4439_);
lean_inc(v_env_4438_);
lean_dec(v___x_4436_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4475_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
uint64_t v_tid_4449_; lean_object* v_traces_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4474_; 
v_tid_4449_ = lean_ctor_get_uint64(v_traceState_4437_, sizeof(void*)*1);
v_traces_4450_ = lean_ctor_get(v_traceState_4437_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_traceState_4437_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4452_ = v_traceState_4437_;
v_isShared_4453_ = v_isSharedCheck_4474_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_traces_4450_);
lean_dec(v_traceState_4437_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4474_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4454_; double v___x_4455_; uint8_t v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4454_ = lean_box(0);
v___x_4455_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0);
v___x_4456_ = 0;
v___x_4457_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1));
v___x_4458_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4458_, 0, v_cls_4423_);
lean_ctor_set(v___x_4458_, 1, v___x_4454_);
lean_ctor_set(v___x_4458_, 2, v___x_4457_);
lean_ctor_set_float(v___x_4458_, sizeof(void*)*3, v___x_4455_);
lean_ctor_set_float(v___x_4458_, sizeof(void*)*3 + 8, v___x_4455_);
lean_ctor_set_uint8(v___x_4458_, sizeof(void*)*3 + 16, v___x_4456_);
v___x_4459_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2));
v___x_4460_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4458_);
lean_ctor_set(v___x_4460_, 1, v_a_4432_);
lean_ctor_set(v___x_4460_, 2, v___x_4459_);
lean_inc(v_ref_4430_);
v___x_4461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4461_, 0, v_ref_4430_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v___x_4462_ = l_Lean_PersistentArray_push___redArg(v_traces_4450_, v___x_4461_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 0, v___x_4462_);
v___x_4464_ = v___x_4452_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4462_);
lean_ctor_set_uint64(v_reuseFailAlloc_4473_, sizeof(void*)*1, v_tid_4449_);
v___x_4464_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
lean_object* v___x_4466_; 
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 4, v___x_4464_);
v___x_4466_ = v___x_4447_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_env_4438_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_nextMacroScope_4439_);
lean_ctor_set(v_reuseFailAlloc_4472_, 2, v_ngen_4440_);
lean_ctor_set(v_reuseFailAlloc_4472_, 3, v_auxDeclNGen_4441_);
lean_ctor_set(v_reuseFailAlloc_4472_, 4, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4472_, 5, v_cache_4442_);
lean_ctor_set(v_reuseFailAlloc_4472_, 6, v_messages_4443_);
lean_ctor_set(v_reuseFailAlloc_4472_, 7, v_infoState_4444_);
lean_ctor_set(v_reuseFailAlloc_4472_, 8, v_snapshotTasks_4445_);
v___x_4466_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4470_; 
v___x_4467_ = lean_st_ref_set(v___y_4428_, v___x_4466_);
v___x_4468_ = lean_box(0);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v___x_4468_);
v___x_4470_ = v___x_4434_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_4477_, lean_object* v_msg_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4477_, v_msg_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
return v_res_4484_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4485_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
return v___x_4487_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
return v___x_4489_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4493_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4494_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4495_ = l_Lean_Name_append(v___x_4494_, v___x_4493_);
return v___x_4495_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4498_ = l_Lean_stringToMessageData(v___x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4499_, uint8_t v___x_4500_, lean_object* v_name_4501_, lean_object* v_argKinds_4502_, lean_object* v___x_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___x_4549_; lean_object* v_a_4550_; lean_object* v___x_4551_; 
v___x_4549_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_4499_, v___y_4507_);
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref(v___x_4549_);
v___x_4551_ = l_Lean_addDecl(v_a_4550_, v___x_4500_, v___y_4506_, v___y_4507_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_options_4552_; uint8_t v_hasTrace_4553_; 
lean_dec_ref_known(v___x_4551_, 1);
v_options_4552_ = lean_ctor_get(v___y_4506_, 2);
v_hasTrace_4553_ = lean_ctor_get_uint8(v_options_4552_, sizeof(void*)*1);
if (v_hasTrace_4553_ == 0)
{
v___y_4510_ = v___y_4505_;
v___y_4511_ = v___y_4507_;
goto v___jp_4509_;
}
else
{
lean_object* v_inheritedTraceOptions_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; 
v_inheritedTraceOptions_4554_ = lean_ctor_get(v___y_4506_, 13);
v___x_4555_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4556_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4557_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4554_, v_options_4552_, v___x_4556_);
if (v___x_4557_ == 0)
{
v___y_4510_ = v___y_4505_;
v___y_4511_ = v___y_4507_;
goto v___jp_4509_;
}
else
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4558_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4501_);
v___x_4559_ = l_Lean_MessageData_ofName(v_name_4501_);
v___x_4560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4560_);
lean_ctor_set(v___x_4562_, 1, v___x_4561_);
v___x_4563_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_4555_, v___x_4562_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_dec_ref_known(v___x_4563_, 1);
v___y_4510_ = v___y_4505_;
v___y_4511_ = v___y_4507_;
goto v___jp_4509_;
}
else
{
lean_dec_ref(v___x_4503_);
lean_dec_ref(v_argKinds_4502_);
lean_dec(v_name_4501_);
return v___x_4563_;
}
}
}
}
else
{
lean_dec_ref(v___x_4503_);
lean_dec_ref(v_argKinds_4502_);
lean_dec(v_name_4501_);
return v___x_4551_;
}
v___jp_4509_:
{
lean_object* v___x_4512_; lean_object* v_env_4513_; lean_object* v_nextMacroScope_4514_; lean_object* v_ngen_4515_; lean_object* v_auxDeclNGen_4516_; lean_object* v_traceState_4517_; lean_object* v_messages_4518_; lean_object* v_infoState_4519_; lean_object* v_snapshotTasks_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4547_; 
v___x_4512_ = lean_st_ref_take(v___y_4511_);
v_env_4513_ = lean_ctor_get(v___x_4512_, 0);
v_nextMacroScope_4514_ = lean_ctor_get(v___x_4512_, 1);
v_ngen_4515_ = lean_ctor_get(v___x_4512_, 2);
v_auxDeclNGen_4516_ = lean_ctor_get(v___x_4512_, 3);
v_traceState_4517_ = lean_ctor_get(v___x_4512_, 4);
v_messages_4518_ = lean_ctor_get(v___x_4512_, 6);
v_infoState_4519_ = lean_ctor_get(v___x_4512_, 7);
v_snapshotTasks_4520_ = lean_ctor_get(v___x_4512_, 8);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4547_ == 0)
{
lean_object* v_unused_4548_; 
v_unused_4548_ = lean_ctor_get(v___x_4512_, 5);
lean_dec(v_unused_4548_);
v___x_4522_ = v___x_4512_;
v_isShared_4523_ = v_isSharedCheck_4547_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_snapshotTasks_4520_);
lean_inc(v_infoState_4519_);
lean_inc(v_messages_4518_);
lean_inc(v_traceState_4517_);
lean_inc(v_auxDeclNGen_4516_);
lean_inc(v_ngen_4515_);
lean_inc(v_nextMacroScope_4514_);
lean_inc(v_env_4513_);
lean_dec(v___x_4512_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4547_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4528_; 
v___x_4524_ = l_Lean_Meta_congrKindsExt;
v___x_4525_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4524_, v_env_4513_, v_name_4501_, v_argKinds_4502_);
v___x_4526_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 5, v___x_4526_);
lean_ctor_set(v___x_4522_, 0, v___x_4525_);
v___x_4528_ = v___x_4522_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___x_4525_);
lean_ctor_set(v_reuseFailAlloc_4546_, 1, v_nextMacroScope_4514_);
lean_ctor_set(v_reuseFailAlloc_4546_, 2, v_ngen_4515_);
lean_ctor_set(v_reuseFailAlloc_4546_, 3, v_auxDeclNGen_4516_);
lean_ctor_set(v_reuseFailAlloc_4546_, 4, v_traceState_4517_);
lean_ctor_set(v_reuseFailAlloc_4546_, 5, v___x_4526_);
lean_ctor_set(v_reuseFailAlloc_4546_, 6, v_messages_4518_);
lean_ctor_set(v_reuseFailAlloc_4546_, 7, v_infoState_4519_);
lean_ctor_set(v_reuseFailAlloc_4546_, 8, v_snapshotTasks_4520_);
v___x_4528_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v_mctx_4531_; lean_object* v_zetaDeltaFVarIds_4532_; lean_object* v_postponed_4533_; lean_object* v_diag_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4544_; 
v___x_4529_ = lean_st_ref_set(v___y_4511_, v___x_4528_);
v___x_4530_ = lean_st_ref_take(v___y_4510_);
v_mctx_4531_ = lean_ctor_get(v___x_4530_, 0);
v_zetaDeltaFVarIds_4532_ = lean_ctor_get(v___x_4530_, 2);
v_postponed_4533_ = lean_ctor_get(v___x_4530_, 3);
v_diag_4534_ = lean_ctor_get(v___x_4530_, 4);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4544_ == 0)
{
lean_object* v_unused_4545_; 
v_unused_4545_ = lean_ctor_get(v___x_4530_, 1);
lean_dec(v_unused_4545_);
v___x_4536_ = v___x_4530_;
v_isShared_4537_ = v_isSharedCheck_4544_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_diag_4534_);
lean_inc(v_postponed_4533_);
lean_inc(v_zetaDeltaFVarIds_4532_);
lean_inc(v_mctx_4531_);
lean_dec(v___x_4530_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4544_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 1, v___x_4503_);
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_mctx_4531_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_zetaDeltaFVarIds_4532_);
lean_ctor_set(v_reuseFailAlloc_4543_, 3, v_postponed_4533_);
lean_ctor_set(v_reuseFailAlloc_4543_, 4, v_diag_4534_);
v___x_4539_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_st_ref_set(v___y_4510_, v___x_4539_);
v___x_4541_ = lean_box(0);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4564_, lean_object* v___x_4565_, lean_object* v_name_4566_, lean_object* v_argKinds_4567_, lean_object* v___x_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
uint8_t v___x_15956__boxed_4574_; lean_object* v_res_4575_; 
v___x_15956__boxed_4574_ = lean_unbox(v___x_4565_);
v_res_4575_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4564_, v___x_15956__boxed_4574_, v_name_4566_, v_argKinds_4567_, v___x_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
if (lean_obj_tag(v_a_4576_) == 0)
{
lean_object* v___x_4578_; 
v___x_4578_ = l_List_reverse___redArg(v_a_4577_);
return v___x_4578_;
}
else
{
lean_object* v_head_4579_; lean_object* v_tail_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4589_; 
v_head_4579_ = lean_ctor_get(v_a_4576_, 0);
v_tail_4580_ = lean_ctor_get(v_a_4576_, 1);
v_isSharedCheck_4589_ = !lean_is_exclusive(v_a_4576_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4582_ = v_a_4576_;
v_isShared_4583_ = v_isSharedCheck_4589_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_tail_4580_);
lean_inc(v_head_4579_);
lean_dec(v_a_4576_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4589_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4584_; lean_object* v___x_4586_; 
v___x_4584_ = l_Lean_mkLevelParam(v_head_4579_);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 1, v_a_4577_);
lean_ctor_set(v___x_4582_, 0, v___x_4584_);
v___x_4586_ = v___x_4582_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4584_);
lean_ctor_set(v_reuseFailAlloc_4588_, 1, v_a_4577_);
v___x_4586_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
v_a_4576_ = v_tail_4580_;
v_a_4577_ = v___x_4586_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4590_; 
v___x_4590_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4590_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4591_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
return v___x_4592_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4593_ = lean_box(1);
v___x_4594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4595_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
lean_ctor_set(v___x_4596_, 1, v___x_4594_);
lean_ctor_set(v___x_4596_, 2, v___x_4593_);
return v___x_4596_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4599_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4600_ = lean_unsigned_to_nat(0u);
v___x_4601_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
lean_ctor_set(v___x_4601_, 2, v___x_4600_);
lean_ctor_set(v___x_4601_, 3, v___x_4600_);
lean_ctor_set(v___x_4601_, 4, v___x_4599_);
lean_ctor_set(v___x_4601_, 5, v___x_4599_);
lean_ctor_set(v___x_4601_, 6, v___x_4599_);
lean_ctor_set(v___x_4601_, 7, v___x_4599_);
lean_ctor_set(v___x_4601_, 8, v___x_4599_);
lean_ctor_set(v___x_4601_, 9, v___x_4599_);
return v___x_4601_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4603_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
lean_ctor_set(v___x_4603_, 2, v___x_4602_);
lean_ctor_set(v___x_4603_, 3, v___x_4602_);
lean_ctor_set(v___x_4603_, 4, v___x_4602_);
lean_ctor_set(v___x_4603_, 5, v___x_4602_);
return v___x_4603_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
lean_ctor_set(v___x_4605_, 2, v___x_4604_);
lean_ctor_set(v___x_4605_, 3, v___x_4604_);
lean_ctor_set(v___x_4605_, 4, v___x_4604_);
return v___x_4605_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4606_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4608_ = lean_box(1);
v___x_4609_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4610_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
lean_ctor_set(v___x_4611_, 1, v___x_4609_);
lean_ctor_set(v___x_4611_, 2, v___x_4608_);
lean_ctor_set(v___x_4611_, 3, v___x_4607_);
lean_ctor_set(v___x_4611_, 4, v___x_4606_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v_name_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
if (lean_obj_tag(v_name_4612_) == 1)
{
lean_object* v_pre_4616_; lean_object* v_str_4617_; lean_object* v___x_4618_; lean_object* v_env_4619_; uint8_t v___x_4620_; uint8_t v___x_4621_; 
v_pre_4616_ = lean_ctor_get(v_name_4612_, 0);
lean_inc_n(v_pre_4616_, 2);
v_str_4617_ = lean_ctor_get(v_name_4612_, 1);
v___x_4618_ = lean_st_ref_get(v___y_4614_);
v_env_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc_ref(v_env_4619_);
lean_dec(v___x_4618_);
v___x_4620_ = 1;
v___x_4621_ = l_Lean_Environment_contains(v_env_4619_, v_pre_4616_, v___x_4620_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v___x_4622_ = lean_box(v___x_4621_);
v___x_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
return v___x_4623_;
}
else
{
uint8_t v___x_4624_; lean_object* v___y_4626_; uint8_t v___y_4627_; lean_object* v_a_4632_; 
lean_inc_ref(v_str_4617_);
v___x_4624_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4617_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4635_; uint8_t v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4636_ = lean_string_dec_eq(v_str_4617_, v___x_4635_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v___x_4637_ = lean_box(v___x_4636_);
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
return v___x_4638_;
}
else
{
uint8_t v___x_4639_; uint8_t v___x_4640_; uint8_t v___x_4641_; lean_object* v___x_4642_; uint64_t v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v_a_4655_; lean_object* v___x_4659_; 
v___x_4639_ = 1;
v___x_4640_ = 0;
v___x_4641_ = 2;
v___x_4642_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4642_, 0, v___x_4624_);
lean_ctor_set_uint8(v___x_4642_, 1, v___x_4624_);
lean_ctor_set_uint8(v___x_4642_, 2, v___x_4624_);
lean_ctor_set_uint8(v___x_4642_, 3, v___x_4624_);
lean_ctor_set_uint8(v___x_4642_, 4, v___x_4624_);
lean_ctor_set_uint8(v___x_4642_, 5, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 6, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 7, v___x_4624_);
lean_ctor_set_uint8(v___x_4642_, 8, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 9, v___x_4639_);
lean_ctor_set_uint8(v___x_4642_, 10, v___x_4640_);
lean_ctor_set_uint8(v___x_4642_, 11, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 12, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 13, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 14, v___x_4641_);
lean_ctor_set_uint8(v___x_4642_, 15, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 16, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 17, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 18, v___x_4636_);
lean_ctor_set_uint8(v___x_4642_, 19, v___x_4624_);
v___x_4643_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4642_);
v___x_4644_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4644_, 0, v___x_4642_);
lean_ctor_set_uint64(v___x_4644_, sizeof(void*)*1, v___x_4643_);
v___x_4645_ = lean_box(1);
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4648_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4649_ = lean_box(0);
v___x_4650_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4650_, 0, v___x_4644_);
lean_ctor_set(v___x_4650_, 1, v___x_4645_);
lean_ctor_set(v___x_4650_, 2, v___x_4647_);
lean_ctor_set(v___x_4650_, 3, v___x_4648_);
lean_ctor_set(v___x_4650_, 4, v___x_4649_);
lean_ctor_set(v___x_4650_, 5, v___x_4646_);
lean_ctor_set(v___x_4650_, 6, v___x_4649_);
lean_ctor_set_uint8(v___x_4650_, sizeof(void*)*7, v___x_4624_);
lean_ctor_set_uint8(v___x_4650_, sizeof(void*)*7 + 1, v___x_4624_);
lean_ctor_set_uint8(v___x_4650_, sizeof(void*)*7 + 2, v___x_4624_);
lean_ctor_set_uint8(v___x_4650_, sizeof(void*)*7 + 3, v___x_4620_);
v___x_4651_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4652_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4653_ = lean_st_mk_ref(v___x_4652_);
lean_inc(v_pre_4616_);
v___x_4659_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4616_, v___x_4650_, v___x_4653_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
lean_inc(v_a_4660_);
lean_dec_ref_known(v___x_4659_, 1);
v___x_4661_ = l_Lean_ConstantInfo_levelParams(v_a_4660_);
lean_dec(v_a_4660_);
v___x_4662_ = lean_box(0);
lean_inc(v___x_4661_);
v___x_4663_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4661_, v___x_4662_);
lean_inc(v_pre_4616_);
v___x_4664_ = l_Lean_mkConst(v_pre_4616_, v___x_4663_);
lean_inc_ref(v___x_4664_);
v___x_4665_ = l_Lean_Meta_getFunInfo(v___x_4664_, v___x_4649_, v___x_4650_, v___x_4653_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4667_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
lean_inc_ref(v___x_4664_);
v___x_4667_ = l_Lean_Meta_getCongrSimpKinds(v___x_4664_, v_a_4666_, v___x_4650_, v___x_4653_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4669_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v___x_4667_, 1);
v___x_4669_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4664_, v_a_4666_, v_a_4668_, v___x_4620_, v___x_4650_, v___x_4653_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref_known(v___x_4669_, 1);
if (lean_obj_tag(v_a_4670_) == 1)
{
lean_object* v_val_4671_; lean_object* v_type_4672_; lean_object* v_proof_4673_; lean_object* v_argKinds_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4687_; 
v_val_4671_ = lean_ctor_get(v_a_4670_, 0);
lean_inc(v_val_4671_);
lean_dec_ref_known(v_a_4670_, 1);
v_type_4672_ = lean_ctor_get(v_val_4671_, 0);
v_proof_4673_ = lean_ctor_get(v_val_4671_, 1);
v_argKinds_4674_ = lean_ctor_get(v_val_4671_, 2);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_val_4671_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4676_ = v_val_4671_;
v_isShared_4677_ = v_isSharedCheck_4687_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_argKinds_4674_);
lean_inc(v_proof_4673_);
lean_inc(v_type_4672_);
lean_dec(v_val_4671_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4687_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
lean_inc_ref(v_name_4612_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 2, v_type_4672_);
lean_ctor_set(v___x_4676_, 1, v___x_4661_);
lean_ctor_set(v___x_4676_, 0, v_name_4612_);
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_name_4612_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v___x_4661_);
lean_ctor_set(v_reuseFailAlloc_4686_, 2, v_type_4672_);
v___x_4679_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___f_4683_; lean_object* v___x_4684_; 
lean_inc_ref_n(v_name_4612_, 2);
v___x_4680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4680_, 0, v_name_4612_);
lean_ctor_set(v___x_4680_, 1, v___x_4662_);
v___x_4681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4679_);
lean_ctor_set(v___x_4681_, 1, v_proof_4673_);
lean_ctor_set(v___x_4681_, 2, v___x_4680_);
v___x_4682_ = lean_box(v___x_4624_);
v___f_4683_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4683_, 0, v___x_4681_);
lean_closure_set(v___f_4683_, 1, v___x_4682_);
lean_closure_set(v___f_4683_, 2, v_name_4612_);
lean_closure_set(v___f_4683_, 3, v_argKinds_4674_);
lean_closure_set(v___f_4683_, 4, v___x_4651_);
v___x_4684_ = l_Lean_Meta_realizeConst(v_pre_4616_, v_name_4612_, v___f_4683_, v___x_4650_, v___x_4653_, v___y_4613_, v___y_4614_);
lean_dec_ref_known(v___x_4650_, 7);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_dec_ref_known(v___x_4684_, 1);
v_a_4655_ = v___x_4620_;
goto v___jp_4654_;
}
else
{
lean_object* v_a_4685_; 
lean_dec(v___x_4653_);
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4684_, 1);
v_a_4632_ = v_a_4685_;
goto v___jp_4631_;
}
}
}
}
else
{
lean_dec(v_a_4670_);
lean_dec(v___x_4661_);
lean_dec_ref_known(v___x_4650_, 7);
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v_a_4655_ = v___x_4624_;
goto v___jp_4654_;
}
}
else
{
lean_object* v_a_4688_; 
lean_dec(v___x_4661_);
lean_dec(v___x_4653_);
lean_dec_ref_known(v___x_4650_, 7);
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v_a_4688_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v___x_4669_, 1);
v_a_4632_ = v_a_4688_;
goto v___jp_4631_;
}
}
else
{
lean_object* v_a_4689_; 
lean_dec(v_a_4666_);
lean_dec_ref(v___x_4664_);
lean_dec(v___x_4661_);
lean_dec(v___x_4653_);
lean_dec_ref_known(v___x_4650_, 7);
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v_a_4689_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4689_);
lean_dec_ref_known(v___x_4667_, 1);
v_a_4632_ = v_a_4689_;
goto v___jp_4631_;
}
}
else
{
lean_object* v_a_4690_; 
lean_dec_ref(v___x_4664_);
lean_dec(v___x_4661_);
lean_dec(v___x_4653_);
lean_dec_ref_known(v___x_4650_, 7);
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v_a_4690_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4690_);
lean_dec_ref_known(v___x_4665_, 1);
v_a_4632_ = v_a_4690_;
goto v___jp_4631_;
}
}
else
{
lean_object* v_a_4691_; 
lean_dec(v___x_4653_);
lean_dec_ref_known(v___x_4650_, 7);
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v_a_4691_ = lean_ctor_get(v___x_4659_, 0);
lean_inc(v_a_4691_);
lean_dec_ref_known(v___x_4659_, 1);
v_a_4632_ = v_a_4691_;
goto v___jp_4631_;
}
v___jp_4654_:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4656_ = lean_st_ref_get(v___x_4653_);
lean_dec(v___x_4653_);
lean_dec(v___x_4656_);
v___x_4657_ = lean_box(v_a_4655_);
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
return v___x_4658_;
}
}
}
else
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; uint8_t v___x_4697_; lean_object* v___y_4699_; uint8_t v___y_4700_; lean_object* v_a_4705_; uint8_t v___x_4708_; uint8_t v___x_4709_; uint8_t v___x_4710_; lean_object* v___x_4711_; uint64_t v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4692_ = lean_unsigned_to_nat(7u);
v___x_4693_ = lean_unsigned_to_nat(0u);
v___x_4694_ = lean_string_utf8_byte_size(v_str_4617_);
lean_inc_ref(v_str_4617_);
v___x_4695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4695_, 0, v_str_4617_);
lean_ctor_set(v___x_4695_, 1, v___x_4693_);
lean_ctor_set(v___x_4695_, 2, v___x_4694_);
v___x_4696_ = l_String_Slice_Pos_nextn(v___x_4695_, v___x_4693_, v___x_4692_);
lean_dec_ref_known(v___x_4695_, 3);
v___x_4697_ = 0;
v___x_4708_ = 1;
v___x_4709_ = 0;
v___x_4710_ = 2;
v___x_4711_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4711_, 0, v___x_4697_);
lean_ctor_set_uint8(v___x_4711_, 1, v___x_4697_);
lean_ctor_set_uint8(v___x_4711_, 2, v___x_4697_);
lean_ctor_set_uint8(v___x_4711_, 3, v___x_4697_);
lean_ctor_set_uint8(v___x_4711_, 4, v___x_4697_);
lean_ctor_set_uint8(v___x_4711_, 5, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 6, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 7, v___x_4697_);
lean_ctor_set_uint8(v___x_4711_, 8, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 9, v___x_4708_);
lean_ctor_set_uint8(v___x_4711_, 10, v___x_4709_);
lean_ctor_set_uint8(v___x_4711_, 11, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 12, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 13, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 14, v___x_4710_);
lean_ctor_set_uint8(v___x_4711_, 15, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 16, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 17, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 18, v___x_4624_);
lean_ctor_set_uint8(v___x_4711_, 19, v___x_4697_);
v___x_4712_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4711_);
v___x_4713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4713_, 0, v___x_4711_);
lean_ctor_set_uint64(v___x_4713_, sizeof(void*)*1, v___x_4712_);
v___x_4714_ = lean_box(1);
v___x_4715_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4716_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4717_ = lean_box(0);
v___x_4718_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4718_, 0, v___x_4713_);
lean_ctor_set(v___x_4718_, 1, v___x_4714_);
lean_ctor_set(v___x_4718_, 2, v___x_4715_);
lean_ctor_set(v___x_4718_, 3, v___x_4716_);
lean_ctor_set(v___x_4718_, 4, v___x_4717_);
lean_ctor_set(v___x_4718_, 5, v___x_4693_);
lean_ctor_set(v___x_4718_, 6, v___x_4717_);
lean_ctor_set_uint8(v___x_4718_, sizeof(void*)*7, v___x_4697_);
lean_ctor_set_uint8(v___x_4718_, sizeof(void*)*7 + 1, v___x_4697_);
lean_ctor_set_uint8(v___x_4718_, sizeof(void*)*7 + 2, v___x_4697_);
lean_ctor_set_uint8(v___x_4718_, sizeof(void*)*7 + 3, v___x_4620_);
v___x_4719_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4720_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4721_ = lean_st_mk_ref(v___x_4720_);
lean_inc(v_pre_4616_);
v___x_4722_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4616_, v___x_4718_, v___x_4721_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4722_, 1);
lean_inc_ref(v_str_4617_);
v___x_4724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4724_, 0, v_str_4617_);
lean_ctor_set(v___x_4724_, 1, v___x_4696_);
lean_ctor_set(v___x_4724_, 2, v___x_4694_);
v___x_4725_ = l_String_Slice_toNat_x21(v___x_4724_);
lean_dec_ref_known(v___x_4724_, 3);
v___x_4726_ = l_Lean_ConstantInfo_levelParams(v_a_4723_);
lean_dec(v_a_4723_);
v___x_4727_ = lean_box(0);
lean_inc(v___x_4726_);
v___x_4728_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4726_, v___x_4727_);
lean_inc(v_pre_4616_);
v___x_4729_ = l_Lean_mkConst(v_pre_4616_, v___x_4728_);
v___x_4730_ = l_Lean_Meta_mkHCongrWithArity(v___x_4729_, v___x_4725_, v___x_4718_, v___x_4721_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v_type_4732_; lean_object* v_proof_4733_; lean_object* v_argKinds_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4757_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
v_type_4732_ = lean_ctor_get(v_a_4731_, 0);
v_proof_4733_ = lean_ctor_get(v_a_4731_, 1);
v_argKinds_4734_ = lean_ctor_get(v_a_4731_, 2);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_a_4731_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4736_ = v_a_4731_;
v_isShared_4737_ = v_isSharedCheck_4757_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_argKinds_4734_);
lean_inc(v_proof_4733_);
lean_inc(v_type_4732_);
lean_dec(v_a_4731_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4757_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
lean_inc_ref(v_name_4612_);
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 2, v_type_4732_);
lean_ctor_set(v___x_4736_, 1, v___x_4726_);
lean_ctor_set(v___x_4736_, 0, v_name_4612_);
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_name_4612_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v___x_4726_);
lean_ctor_set(v_reuseFailAlloc_4756_, 2, v_type_4732_);
v___x_4739_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___f_4743_; lean_object* v___x_4744_; 
lean_inc_ref_n(v_name_4612_, 2);
v___x_4740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4740_, 0, v_name_4612_);
lean_ctor_set(v___x_4740_, 1, v___x_4727_);
v___x_4741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4739_);
lean_ctor_set(v___x_4741_, 1, v_proof_4733_);
lean_ctor_set(v___x_4741_, 2, v___x_4740_);
v___x_4742_ = lean_box(v___x_4697_);
v___f_4743_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4743_, 0, v___x_4741_);
lean_closure_set(v___f_4743_, 1, v___x_4742_);
lean_closure_set(v___f_4743_, 2, v_name_4612_);
lean_closure_set(v___f_4743_, 3, v_argKinds_4734_);
lean_closure_set(v___f_4743_, 4, v___x_4719_);
v___x_4744_ = l_Lean_Meta_realizeConst(v_pre_4616_, v_name_4612_, v___f_4743_, v___x_4718_, v___x_4721_, v___y_4613_, v___y_4614_);
lean_dec_ref_known(v___x_4718_, 7);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4753_; 
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v___x_4744_, 0);
lean_dec(v_unused_4754_);
v___x_4746_ = v___x_4744_;
v_isShared_4747_ = v_isSharedCheck_4753_;
goto v_resetjp_4745_;
}
else
{
lean_dec(v___x_4744_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4753_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4751_; 
v___x_4748_ = lean_st_ref_get(v___x_4721_);
lean_dec(v___x_4721_);
lean_dec(v___x_4748_);
v___x_4749_ = lean_box(v___x_4620_);
if (v_isShared_4747_ == 0)
{
lean_ctor_set(v___x_4746_, 0, v___x_4749_);
v___x_4751_ = v___x_4746_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4749_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
else
{
lean_object* v_a_4755_; 
lean_dec(v___x_4721_);
v_a_4755_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4744_, 1);
v_a_4705_ = v_a_4755_;
goto v___jp_4704_;
}
}
}
}
else
{
lean_object* v_a_4758_; 
lean_dec(v___x_4726_);
lean_dec(v___x_4721_);
lean_dec_ref_known(v___x_4718_, 7);
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v_a_4758_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v___x_4730_, 1);
v_a_4705_ = v_a_4758_;
goto v___jp_4704_;
}
}
else
{
lean_object* v_a_4759_; 
lean_dec(v___x_4721_);
lean_dec_ref_known(v___x_4718_, 7);
lean_dec(v___x_4696_);
lean_dec_ref_known(v_name_4612_, 2);
lean_dec(v_pre_4616_);
v_a_4759_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4759_);
lean_dec_ref_known(v___x_4722_, 1);
v_a_4705_ = v_a_4759_;
goto v___jp_4704_;
}
v___jp_4698_:
{
if (v___y_4700_ == 0)
{
lean_object* v___x_4701_; lean_object* v___x_4702_; 
lean_dec_ref(v___y_4699_);
v___x_4701_ = lean_box(v___x_4697_);
v___x_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4701_);
return v___x_4702_;
}
else
{
lean_object* v___x_4703_; 
v___x_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4703_, 0, v___y_4699_);
return v___x_4703_;
}
}
v___jp_4704_:
{
uint8_t v___x_4706_; 
v___x_4706_ = l_Lean_Exception_isInterrupt(v_a_4705_);
if (v___x_4706_ == 0)
{
uint8_t v___x_4707_; 
lean_inc_ref(v_a_4705_);
v___x_4707_ = l_Lean_Exception_isRuntime(v_a_4705_);
v___y_4699_ = v_a_4705_;
v___y_4700_ = v___x_4707_;
goto v___jp_4698_;
}
else
{
v___y_4699_ = v_a_4705_;
v___y_4700_ = v___x_4706_;
goto v___jp_4698_;
}
}
}
v___jp_4625_:
{
if (v___y_4627_ == 0)
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
lean_dec_ref(v___y_4626_);
v___x_4628_ = lean_box(v___x_4624_);
v___x_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4628_);
return v___x_4629_;
}
else
{
lean_object* v___x_4630_; 
v___x_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4630_, 0, v___y_4626_);
return v___x_4630_;
}
}
v___jp_4631_:
{
uint8_t v___x_4633_; 
v___x_4633_ = l_Lean_Exception_isInterrupt(v_a_4632_);
if (v___x_4633_ == 0)
{
uint8_t v___x_4634_; 
lean_inc_ref(v_a_4632_);
v___x_4634_ = l_Lean_Exception_isRuntime(v_a_4632_);
v___y_4626_ = v_a_4632_;
v___y_4627_ = v___x_4634_;
goto v___jp_4625_;
}
else
{
v___y_4626_ = v_a_4632_;
v___y_4627_ = v___x_4633_;
goto v___jp_4625_;
}
}
}
}
else
{
uint8_t v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec(v_name_4612_);
v___x_4760_ = 0;
v___x_4761_ = lean_box(v___x_4760_);
v___x_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
return v___x_4762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_name_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4770_; lean_object* v___x_4771_; 
v___f_4770_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4771_ = l_Lean_registerReservedNameAction(v___f_4770_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_a_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* v_msg_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v___f_4780_; lean_object* v___x_1830__overap_4781_; lean_object* v___x_4782_; 
v___f_4780_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1830__overap_4781_ = lean_panic_fn_borrowed(v___f_4780_, v_msg_4774_);
lean_inc(v___y_4778_);
lean_inc_ref(v___y_4777_);
lean_inc(v___y_4776_);
lean_inc_ref(v___y_4775_);
v___x_4782_ = lean_apply_5(v___x_1830__overap_4781_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, lean_box(0));
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
lean_dec(v___y_4787_);
lean_dec_ref(v___y_4786_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
return v_res_4789_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4791_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4792_ = lean_unsigned_to_nat(8u);
v___x_4793_ = lean_unsigned_to_nat(461u);
v___x_4794_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0));
v___x_4795_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4796_ = l_mkPanicMessageWithDecl(v___x_4795_, v___x_4794_, v___x_4793_, v___x_4792_, v___x_4791_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* v_thmName_4797_, lean_object* v_levels_4798_, lean_object* v___x_4799_, lean_object* v_____r_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; 
lean_inc(v_thmName_4797_);
v___x_4806_ = l_Lean_mkConst(v_thmName_4797_, v_levels_4798_);
lean_inc(v___y_4804_);
lean_inc_ref(v___y_4803_);
lean_inc(v___y_4802_);
lean_inc_ref(v___y_4801_);
lean_inc_ref(v___x_4806_);
v___x_4807_ = lean_infer_type(v___x_4806_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4851_; 
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4810_ = v___x_4807_;
v_isShared_4811_ = v_isSharedCheck_4851_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4807_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4851_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4812_; lean_object* v_env_4813_; lean_object* v___x_4814_; lean_object* v_toEnvExtension_4815_; lean_object* v_asyncMode_4816_; uint8_t v___x_4817_; lean_object* v___x_4818_; 
v___x_4812_ = lean_st_ref_get(v___y_4804_);
v_env_4813_ = lean_ctor_get(v___x_4812_, 0);
lean_inc_ref(v_env_4813_);
lean_dec(v___x_4812_);
v___x_4814_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4815_ = lean_ctor_get(v___x_4814_, 0);
v_asyncMode_4816_ = lean_ctor_get(v_toEnvExtension_4815_, 2);
v___x_4817_ = 0;
v___x_4818_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4799_, v___x_4814_, v_env_4813_, v_thmName_4797_, v_asyncMode_4816_, v___x_4817_);
if (lean_obj_tag(v___x_4818_) == 1)
{
lean_object* v_val_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4831_; 
v_val_4819_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4821_ = v___x_4818_;
v_isShared_4822_ = v_isSharedCheck_4831_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_val_4819_);
lean_dec(v___x_4818_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4831_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4823_; lean_object* v___x_4825_; 
v___x_4823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4823_, 0, v_a_4808_);
lean_ctor_set(v___x_4823_, 1, v___x_4806_);
lean_ctor_set(v___x_4823_, 2, v_val_4819_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v___x_4823_);
v___x_4825_ = v___x_4821_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4823_);
v___x_4825_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v___x_4826_);
v___x_4828_ = v___x_4810_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
lean_dec(v___x_4818_);
lean_del_object(v___x_4810_);
lean_dec(v_a_4808_);
lean_dec_ref(v___x_4806_);
v___x_4832_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1);
v___x_4833_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4832_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4842_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4836_ = v___x_4833_;
v_isShared_4837_ = v_isSharedCheck_4842_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4833_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4842_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4838_; lean_object* v___x_4840_; 
v___x_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4838_, 0, v_a_4834_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 0, v___x_4838_);
v___x_4840_ = v___x_4836_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4838_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
else
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4850_; 
v_a_4843_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4845_ = v___x_4833_;
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4833_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4848_; 
if (v_isShared_4846_ == 0)
{
v___x_4848_ = v___x_4845_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_a_4843_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
}
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
lean_dec_ref(v___x_4806_);
lean_dec_ref(v___x_4799_);
lean_dec(v_thmName_4797_);
v_a_4852_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4807_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4807_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* v_thmName_4860_, lean_object* v_levels_4861_, lean_object* v___x_4862_, lean_object* v_____r_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4860_, v_levels_4861_, v___x_4862_, v_____r_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
return v_res_4869_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0(void){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Array_instInhabited(lean_box(0));
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* v_declName_4871_, lean_object* v_levels_4872_, lean_object* v_numArgs_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_){
_start:
{
lean_object* v___y_4880_; uint8_t v___y_4881_; lean_object* v_a_4886_; lean_object* v___y_4890_; lean_object* v___x_4901_; lean_object* v_env_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v_suffix_4906_; lean_object* v_thmName_4907_; uint8_t v___x_4908_; 
v___x_4901_ = lean_st_ref_get(v_a_4877_);
v_env_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc_ref(v_env_4902_);
lean_dec(v___x_4901_);
v___x_4903_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_4904_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4905_ = l_Nat_reprFast(v_numArgs_4873_);
v_suffix_4906_ = lean_string_append(v___x_4904_, v___x_4905_);
lean_dec_ref(v___x_4905_);
v_thmName_4907_ = l_Lean_Name_str___override(v_declName_4871_, v_suffix_4906_);
v___x_4908_ = l_Lean_Environment_containsOnBranch(v_env_4902_, v_thmName_4907_);
lean_dec_ref(v_env_4902_);
if (v___x_4908_ == 0)
{
lean_object* v___x_4909_; 
lean_inc(v_thmName_4907_);
v___x_4909_ = l_Lean_executeReservedNameAction(v_thmName_4907_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_dec_ref_known(v___x_4909_, 1);
v___x_4910_ = lean_box(0);
v___x_4911_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4907_, v_levels_4872_, v___x_4903_, v___x_4910_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
v___y_4890_ = v___x_4911_;
goto v___jp_4889_;
}
else
{
lean_object* v_a_4912_; 
lean_dec(v_thmName_4907_);
lean_dec(v_levels_4872_);
v_a_4912_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4912_);
lean_dec_ref_known(v___x_4909_, 1);
v_a_4886_ = v_a_4912_;
goto v___jp_4885_;
}
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___x_4913_ = lean_box(0);
v___x_4914_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4907_, v_levels_4872_, v___x_4903_, v___x_4913_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
v___y_4890_ = v___x_4914_;
goto v___jp_4889_;
}
v___jp_4879_:
{
if (v___y_4881_ == 0)
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
lean_dec_ref(v___y_4880_);
v___x_4882_ = lean_box(0);
v___x_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
return v___x_4883_;
}
else
{
lean_object* v___x_4884_; 
v___x_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4884_, 0, v___y_4880_);
return v___x_4884_;
}
}
v___jp_4885_:
{
uint8_t v___x_4887_; 
v___x_4887_ = l_Lean_Exception_isInterrupt(v_a_4886_);
if (v___x_4887_ == 0)
{
uint8_t v___x_4888_; 
lean_inc_ref(v_a_4886_);
v___x_4888_ = l_Lean_Exception_isRuntime(v_a_4886_);
v___y_4880_ = v_a_4886_;
v___y_4881_ = v___x_4888_;
goto v___jp_4879_;
}
else
{
v___y_4880_ = v_a_4886_;
v___y_4881_ = v___x_4887_;
goto v___jp_4879_;
}
}
v___jp_4889_:
{
if (lean_obj_tag(v___y_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4899_; 
v_a_4891_ = lean_ctor_get(v___y_4890_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___y_4890_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4893_ = v___y_4890_;
v_isShared_4894_ = v_isSharedCheck_4899_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___y_4890_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4899_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v_a_4895_; lean_object* v___x_4897_; 
v_a_4895_ = lean_ctor_get(v_a_4891_, 0);
lean_inc(v_a_4895_);
lean_dec(v_a_4891_);
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 0, v_a_4895_);
v___x_4897_ = v___x_4893_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4895_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
else
{
lean_object* v_a_4900_; 
v_a_4900_ = lean_ctor_get(v___y_4890_, 0);
lean_inc(v_a_4900_);
lean_dec_ref_known(v___y_4890_, 1);
v_a_4886_ = v_a_4900_;
goto v___jp_4885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object* v_declName_4915_, lean_object* v_levels_4916_, lean_object* v_numArgs_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_4915_, v_levels_4916_, v_numArgs_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_);
lean_dec(v_a_4921_);
lean_dec_ref(v_a_4920_);
lean_dec(v_a_4919_);
lean_dec_ref(v_a_4918_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* v_____r_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4932_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0));
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4932_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* v_____r_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
lean_dec(v___y_4938_);
lean_dec_ref(v___y_4937_);
lean_dec(v___y_4936_);
lean_dec_ref(v___y_4935_);
return v_res_4940_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4942_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4943_ = lean_unsigned_to_nat(8u);
v___x_4944_ = lean_unsigned_to_nat(478u);
v___x_4945_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0));
v___x_4946_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4947_ = l_mkPanicMessageWithDecl(v___x_4946_, v___x_4945_, v___x_4944_, v___x_4943_, v___x_4942_);
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object* v_thmName_4948_, lean_object* v_levels_4949_, lean_object* v___x_4950_, lean_object* v_____r_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
lean_inc(v_thmName_4948_);
v___x_4957_ = l_Lean_mkConst(v_thmName_4948_, v_levels_4949_);
lean_inc(v___y_4955_);
lean_inc_ref(v___y_4954_);
lean_inc(v___y_4953_);
lean_inc_ref(v___y_4952_);
lean_inc_ref(v___x_4957_);
v___x_4958_ = lean_infer_type(v___x_4957_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_5002_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4961_ = v___x_4958_;
v_isShared_4962_ = v_isSharedCheck_5002_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4958_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_5002_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4963_; lean_object* v_env_4964_; lean_object* v___x_4965_; lean_object* v_toEnvExtension_4966_; lean_object* v_asyncMode_4967_; uint8_t v___x_4968_; lean_object* v___x_4969_; 
v___x_4963_ = lean_st_ref_get(v___y_4955_);
v_env_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc_ref(v_env_4964_);
lean_dec(v___x_4963_);
v___x_4965_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4966_ = lean_ctor_get(v___x_4965_, 0);
v_asyncMode_4967_ = lean_ctor_get(v_toEnvExtension_4966_, 2);
v___x_4968_ = 0;
v___x_4969_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4950_, v___x_4965_, v_env_4964_, v_thmName_4948_, v_asyncMode_4967_, v___x_4968_);
if (lean_obj_tag(v___x_4969_) == 1)
{
lean_object* v_val_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4982_; 
v_val_4970_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4972_ = v___x_4969_;
v_isShared_4973_ = v_isSharedCheck_4982_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_val_4970_);
lean_dec(v___x_4969_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4982_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; lean_object* v___x_4976_; 
v___x_4974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4974_, 0, v_a_4959_);
lean_ctor_set(v___x_4974_, 1, v___x_4957_);
lean_ctor_set(v___x_4974_, 2, v_val_4970_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set(v___x_4972_, 0, v___x_4974_);
v___x_4976_ = v___x_4972_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4974_);
v___x_4976_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v___x_4977_; lean_object* v___x_4979_; 
v___x_4977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 0, v___x_4977_);
v___x_4979_ = v___x_4961_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4977_);
v___x_4979_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
return v___x_4979_;
}
}
}
}
else
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec(v___x_4969_);
lean_del_object(v___x_4961_);
lean_dec(v_a_4959_);
lean_dec_ref(v___x_4957_);
v___x_4983_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1);
v___x_4984_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4983_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4993_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4987_ = v___x_4984_;
v_isShared_4988_ = v_isSharedCheck_4993_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4984_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4993_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4989_; lean_object* v___x_4991_; 
v___x_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4989_, 0, v_a_4985_);
if (v_isShared_4988_ == 0)
{
lean_ctor_set(v___x_4987_, 0, v___x_4989_);
v___x_4991_ = v___x_4987_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4989_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
v_a_4994_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4996_ = v___x_4984_;
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4984_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4999_; 
if (v_isShared_4997_ == 0)
{
v___x_4999_ = v___x_4996_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4994_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_dec_ref(v___x_4957_);
lean_dec_ref(v___x_4950_);
lean_dec(v_thmName_4948_);
v_a_5003_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_4958_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_4958_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object* v_thmName_5011_, lean_object* v_levels_5012_, lean_object* v___x_5013_, lean_object* v_____r_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5011_, v_levels_5012_, v___x_5013_, v_____r_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
return v_res_5020_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1(void){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5022_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0));
v___x_5023_ = l_Lean_stringToMessageData(v___x_5022_);
return v___x_5023_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3(void){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5025_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2));
v___x_5026_ = l_Lean_stringToMessageData(v___x_5025_);
return v___x_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* v_declName_5027_, lean_object* v_levels_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_){
_start:
{
lean_object* v_a_5035_; lean_object* v___y_5053_; lean_object* v___x_5055_; lean_object* v_env_5056_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v_thmName_5062_; lean_object* v___y_5064_; uint8_t v___y_5065_; lean_object* v_a_5092_; lean_object* v___y_5096_; uint8_t v___x_5099_; 
v___x_5055_ = lean_st_ref_get(v_a_5032_);
v_env_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc_ref(v_env_5056_);
lean_dec(v___x_5055_);
v___x_5060_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_5061_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v_thmName_5062_ = l_Lean_Name_str___override(v_declName_5027_, v___x_5061_);
v___x_5099_ = l_Lean_Environment_containsOnBranch(v_env_5056_, v_thmName_5062_);
lean_dec_ref(v_env_5056_);
if (v___x_5099_ == 0)
{
lean_object* v___x_5100_; 
lean_inc(v_thmName_5062_);
v___x_5100_ = l_Lean_executeReservedNameAction(v_thmName_5062_, v_a_5031_, v_a_5032_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
lean_dec_ref_known(v___x_5100_, 1);
v___x_5101_ = lean_box(0);
lean_inc(v_thmName_5062_);
v___x_5102_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5062_, v_levels_5028_, v___x_5060_, v___x_5101_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
v___y_5096_ = v___x_5102_;
goto v___jp_5095_;
}
else
{
lean_object* v_a_5103_; 
lean_dec(v_levels_5028_);
v_a_5103_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___x_5100_, 1);
v_a_5092_ = v_a_5103_;
goto v___jp_5091_;
}
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5104_ = lean_box(0);
lean_inc(v_thmName_5062_);
v___x_5105_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5062_, v_levels_5028_, v___x_5060_, v___x_5104_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
v___y_5096_ = v___x_5105_;
goto v___jp_5095_;
}
v___jp_5034_:
{
if (lean_obj_tag(v_a_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
v_a_5036_ = lean_ctor_get(v_a_5035_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v_a_5035_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v_a_5035_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v_a_5035_);
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
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
v_a_5044_ = lean_ctor_get(v_a_5035_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v_a_5035_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v_a_5035_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v_a_5035_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
lean_ctor_set_tag(v___x_5046_, 0);
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
}
v___jp_5052_:
{
lean_object* v_a_5054_; 
v_a_5054_ = lean_ctor_get(v___y_5053_, 0);
lean_inc(v_a_5054_);
lean_dec_ref(v___y_5053_);
v_a_5035_ = v_a_5054_;
goto v___jp_5034_;
}
v___jp_5057_:
{
lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = lean_box(0);
v___x_5059_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v___x_5058_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
v___y_5053_ = v___x_5059_;
goto v___jp_5052_;
}
v___jp_5063_:
{
if (v___y_5065_ == 0)
{
lean_object* v_options_5066_; uint8_t v_hasTrace_5067_; 
v_options_5066_ = lean_ctor_get(v_a_5031_, 2);
v_hasTrace_5067_ = lean_ctor_get_uint8(v_options_5066_, sizeof(void*)*1);
if (v_hasTrace_5067_ == 0)
{
lean_dec_ref(v___y_5064_);
lean_dec(v_thmName_5062_);
goto v___jp_5057_;
}
else
{
lean_object* v_inheritedTraceOptions_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; uint8_t v___x_5071_; 
v_inheritedTraceOptions_5068_ = lean_ctor_get(v_a_5031_, 13);
v___x_5069_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_5070_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_5071_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5068_, v_options_5066_, v___x_5070_);
if (v___x_5071_ == 0)
{
lean_dec_ref(v___y_5064_);
lean_dec(v_thmName_5062_);
goto v___jp_5057_;
}
else
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5072_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1);
v___x_5073_ = l_Lean_MessageData_ofName(v_thmName_5062_);
v___x_5074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5072_);
lean_ctor_set(v___x_5074_, 1, v___x_5073_);
v___x_5075_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3);
v___x_5076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = l_Lean_Exception_toMessageData(v___y_5064_);
v___x_5078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5078_, 0, v___x_5076_);
lean_ctor_set(v___x_5078_, 1, v___x_5077_);
v___x_5079_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_5069_, v___x_5078_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v___x_5081_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref_known(v___x_5079_, 1);
v___x_5081_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_a_5080_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
v___y_5053_ = v___x_5081_;
goto v___jp_5052_;
}
else
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
v_a_5082_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5084_ = v___x_5079_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5079_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
}
}
else
{
lean_object* v___x_5090_; 
lean_dec(v_thmName_5062_);
v___x_5090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5090_, 0, v___y_5064_);
return v___x_5090_;
}
}
v___jp_5091_:
{
uint8_t v___x_5093_; 
v___x_5093_ = l_Lean_Exception_isInterrupt(v_a_5092_);
if (v___x_5093_ == 0)
{
uint8_t v___x_5094_; 
lean_inc_ref(v_a_5092_);
v___x_5094_ = l_Lean_Exception_isRuntime(v_a_5092_);
v___y_5064_ = v_a_5092_;
v___y_5065_ = v___x_5094_;
goto v___jp_5063_;
}
else
{
v___y_5064_ = v_a_5092_;
v___y_5065_ = v___x_5093_;
goto v___jp_5063_;
}
}
v___jp_5095_:
{
if (lean_obj_tag(v___y_5096_) == 0)
{
lean_object* v_a_5097_; 
lean_dec(v_thmName_5062_);
v_a_5097_ = lean_ctor_get(v___y_5096_, 0);
lean_inc(v_a_5097_);
lean_dec_ref_known(v___y_5096_, 1);
v_a_5035_ = v_a_5097_;
goto v___jp_5034_;
}
else
{
lean_object* v_a_5098_; 
v_a_5098_ = lean_ctor_get(v___y_5096_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___y_5096_, 1);
v_a_5092_ = v_a_5098_;
goto v___jp_5091_;
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
