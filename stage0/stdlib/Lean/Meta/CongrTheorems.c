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
uint8_t lean_bool_not(uint8_t);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(lean_object* v_lctx_871_, lean_object* v_localInsts_872_, lean_object* v_x_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(lean_object* v_lctx_896_, lean_object* v_localInsts_897_, lean_object* v_x_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_lctx_896_, v_localInsts_897_, v_x_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object* v_00_u03b1_905_, lean_object* v_lctx_906_, lean_object* v_localInsts_907_, lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_lctx_906_, v_localInsts_907_, v_x_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object* v_00_u03b1_915_, lean_object* v_lctx_916_, lean_object* v_localInsts_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1(v_00_u03b1_915_, v_lctx_916_, v_localInsts_917_, v_x_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object* v_as_925_, size_t v_sz_926_, size_t v_i_927_, lean_object* v_b_928_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object* v_as_1006_, lean_object* v_sz_1007_, lean_object* v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_){
_start:
{
size_t v_sz_boxed_1011_; size_t v_i_boxed_1012_; lean_object* v_res_1013_; 
v_sz_boxed_1011_ = lean_unbox_usize(v_sz_1007_);
lean_dec(v_sz_1007_);
v_i_boxed_1012_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_as_1006_, v_sz_boxed_1011_, v_i_boxed_1012_, v_b_1009_);
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
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_xs_1015_, v_sz_1034_, v___x_1035_, v___x_1033_);
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
uint8_t v___x_4556__boxed_1100_; uint8_t v___x_4557__boxed_1101_; lean_object* v_res_1102_; 
v___x_4556__boxed_1100_ = lean_unbox(v___x_1091_);
v___x_4557__boxed_1101_ = lean_unbox(v___x_1092_);
v_res_1102_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1088_, v_xs_1089_, v_f_1090_, v___x_4556__boxed_1100_, v___x_4557__boxed_1101_, v_eqs_1093_, v_argKinds_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v_xs_1089_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2_spec__2(lean_object* v_msgData_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2_spec__2___boxed(lean_object* v_msgData_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2_spec__2(v_msgData_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_ref_1131_ = lean_ctor_get(v___y_1128_, 5);
v___x_1132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2_spec__2(v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(lean_object* v_msg_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
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
lean_object* v___x_1168_; uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = lean_array_get_size(v_xs_1158_);
v___x_1169_ = lean_nat_dec_eq(v___x_1168_, v_numArgs_1159_);
v___x_1170_ = lean_bool_not(v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v_lctx_1171_; lean_object* v_localInstances_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v_numArgs_1159_);
v_lctx_1171_ = lean_ctor_get(v___y_1163_, 2);
v_localInstances_1172_ = lean_ctor_get(v___y_1163_, 3);
v___x_1173_ = 1;
v___x_1174_ = lean_box(v___x_1170_);
v___x_1175_ = lean_box(v___x_1173_);
lean_inc_ref(v_xs_1158_);
lean_inc_ref(v_ys_1161_);
v___f_1176_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1176_, 0, v_ys_1161_);
lean_closure_set(v___f_1176_, 1, v_xs_1158_);
lean_closure_set(v___f_1176_, 2, v_f_1160_);
lean_closure_set(v___f_1176_, 3, v___x_1174_);
lean_closure_set(v___f_1176_, 4, v___x_1175_);
lean_inc_ref(v_lctx_1171_);
v___x_1177_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_1161_, v_lctx_1171_);
v___x_1178_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_1161_, v___x_1177_);
v___x_1179_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_xs_1158_, v___x_1178_);
v___x_1180_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed), 9, 4);
lean_closure_set(v___x_1180_, 0, lean_box(0));
lean_closure_set(v___x_1180_, 1, v_xs_1158_);
lean_closure_set(v___x_1180_, 2, v_ys_1161_);
lean_closure_set(v___x_1180_, 3, v___f_1176_);
lean_inc_ref(v_localInstances_1172_);
v___x_1181_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v___x_1179_, v_localInstances_1172_, v___x_1180_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec_ref(v_ys_1161_);
lean_dec_ref(v_xs_1158_);
v___x_1182_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1);
v___x_1183_ = l_Nat_reprFast(v_numArgs_1159_);
v___x_1184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
v___x_1185_ = l_Lean_MessageData_ofFormat(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1182_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Nat_reprFast(v___x_1168_);
v___x_1190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
v___x_1191_ = l_Lean_MessageData_ofFormat(v___x_1190_);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1188_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = l_Lean_indentExpr(v_f_1160_);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v___x_1196_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object* v_xs_1198_, lean_object* v_numArgs_1199_, lean_object* v_f_1200_, lean_object* v_ys_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Meta_mkHCongrWithArity___lam__1(v_xs_1198_, v_numArgs_1199_, v_f_1200_, v_ys_1201_, v_x_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec_ref(v_x_1202_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object* v_numArgs_1209_, lean_object* v_f_1210_, lean_object* v_a_1211_, lean_object* v___x_1212_, lean_object* v_xs_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___f_1220_; uint8_t v___x_1221_; uint8_t v___x_1222_; lean_object* v___x_1223_; 
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1220_, 0, v_xs_1213_);
lean_closure_set(v___f_1220_, 1, v_numArgs_1209_);
lean_closure_set(v___f_1220_, 2, v_f_1210_);
v___x_1221_ = 1;
v___x_1222_ = 0;
v___x_1223_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1211_, v___x_1212_, v___f_1220_, v___x_1221_, v___x_1222_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object* v_numArgs_1224_, lean_object* v_f_1225_, lean_object* v_a_1226_, lean_object* v___x_1227_, lean_object* v_xs_1228_, lean_object* v_x_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Meta_mkHCongrWithArity___lam__2(v_numArgs_1224_, v_f_1225_, v_a_1226_, v___x_1227_, v_xs_1228_, v_x_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_x_1229_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object* v_f_1236_, lean_object* v_numArgs_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___x_1243_; 
lean_inc(v_a_1241_);
lean_inc_ref(v_a_1240_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
lean_inc_ref(v_f_1236_);
v___x_1243_ = lean_infer_type(v_f_1236_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v___f_1246_; uint8_t v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_n(v_a_1244_, 2);
lean_dec_ref_known(v___x_1243_, 1);
lean_inc(v_numArgs_1237_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_numArgs_1237_);
lean_inc_ref(v___x_1245_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1246_, 0, v_numArgs_1237_);
lean_closure_set(v___f_1246_, 1, v_f_1236_);
lean_closure_set(v___f_1246_, 2, v_a_1244_);
lean_closure_set(v___f_1246_, 3, v___x_1245_);
v___x_1247_ = 1;
v___x_1248_ = 0;
v___x_1249_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1244_, v___x_1245_, v___f_1246_, v___x_1247_, v___x_1248_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_numArgs_1237_);
lean_dec_ref(v_f_1236_);
v_a_1250_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1243_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1243_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___boxed(lean_object* v_f_1258_, lean_object* v_numArgs_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Meta_mkHCongrWithArity(v_f_1258_, v_numArgs_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object* v_as_1266_, size_t v_sz_1267_, size_t v_i_1268_, lean_object* v_b_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_as_1266_, v_sz_1267_, v_i_1268_, v_b_1269_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object* v_as_1276_, lean_object* v_sz_1277_, lean_object* v_i_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
size_t v_sz_boxed_1285_; size_t v_i_boxed_1286_; lean_object* v_res_1287_; 
v_sz_boxed_1285_ = lean_unbox_usize(v_sz_1277_);
lean_dec(v_sz_1277_);
v_i_boxed_1286_ = lean_unbox_usize(v_i_1278_);
lean_dec(v_i_1278_);
v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__0(v_as_1276_, v_sz_boxed_1285_, v_i_boxed_1286_, v_b_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec_ref(v_as_1276_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_object* v_00_u03b1_1288_, lean_object* v_msg_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_msg_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(lean_object* v_00_u03b1_1296_, lean_object* v_msg_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2(v_00_u03b1_1296_, v_msg_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object* v_f_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_box(0);
lean_inc_ref(v_f_1304_);
v___x_1311_ = l_Lean_Meta_getFunInfo(v_f_1304_, v___x_1310_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = l_Lean_Meta_FunInfo_getArity(v_a_1312_);
lean_dec(v_a_1312_);
v___x_1314_ = l_Lean_Meta_mkHCongrWithArity(v_f_1304_, v___x_1313_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
return v___x_1314_;
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_f_1304_);
v_a_1315_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1311_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1311_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr___boxed(lean_object* v_f_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Meta_mkHCongr(v_f_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1329_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object* v_a_1330_, lean_object* v_as_1331_, size_t v_i_1332_, size_t v_stop_1333_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_eq(v_i_1332_, v_stop_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = lean_array_uget_borrowed(v_as_1331_, v_i_1332_);
v___x_1336_ = lean_nat_dec_eq(v_a_1330_, v___x_1335_);
if (v___x_1336_ == 0)
{
size_t v___x_1337_; size_t v___x_1338_; 
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1332_, v___x_1337_);
v_i_1332_ = v___x_1338_;
goto _start;
}
else
{
return v___x_1336_;
}
}
else
{
uint8_t v___x_1340_; 
v___x_1340_ = 0;
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object* v_a_1341_, lean_object* v_as_1342_, lean_object* v_i_1343_, lean_object* v_stop_1344_){
_start:
{
size_t v_i_boxed_1345_; size_t v_stop_boxed_1346_; uint8_t v_res_1347_; lean_object* v_r_1348_; 
v_i_boxed_1345_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_stop_boxed_1346_ = lean_unbox_usize(v_stop_1344_);
lean_dec(v_stop_1344_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1341_, v_as_1342_, v_i_boxed_1345_, v_stop_boxed_1346_);
lean_dec_ref(v_as_1342_);
lean_dec(v_a_1341_);
v_r_1348_ = lean_box(v_res_1347_);
return v_r_1348_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object* v_as_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_array_get_size(v_as_1349_);
v___x_1353_ = lean_nat_dec_lt(v___x_1351_, v___x_1352_);
if (v___x_1353_ == 0)
{
return v___x_1353_;
}
else
{
if (v___x_1353_ == 0)
{
return v___x_1353_;
}
else
{
size_t v___x_1354_; size_t v___x_1355_; uint8_t v___x_1356_; 
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = lean_usize_of_nat(v___x_1352_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1350_, v_as_1349_, v___x_1354_, v___x_1355_);
return v___x_1356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object* v_as_1357_, lean_object* v_a_1358_){
_start:
{
uint8_t v_res_1359_; lean_object* v_r_1360_; 
v_res_1359_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_as_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_as_1357_);
v_r_1360_ = lean_box(v_res_1359_);
return v_r_1360_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(lean_object* v_next_1361_, lean_object* v_upperBound_1362_, lean_object* v___x_1363_, lean_object* v_a_1364_, lean_object* v_b_1365_){
_start:
{
lean_object* v_a_1367_; uint8_t v___x_1375_; 
v___x_1375_ = lean_nat_dec_lt(v_a_1364_, v_upperBound_1362_);
if (v___x_1375_ == 0)
{
lean_dec(v_a_1364_);
return v_b_1365_;
}
else
{
lean_object* v___x_1376_; lean_object* v_backDeps_1377_; uint8_t v___x_1378_; 
v___x_1376_ = lean_array_fget_borrowed(v___x_1363_, v_a_1364_);
v_backDeps_1377_ = lean_ctor_get(v___x_1376_, 0);
v___x_1378_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_backDeps_1377_, v_next_1361_);
if (v___x_1378_ == 0)
{
v_a_1367_ = v_b_1365_;
goto v___jp_1366_;
}
else
{
uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1379_ = 0;
v___x_1380_ = lean_box(v___x_1379_);
v___x_1381_ = lean_array_get(v___x_1380_, v_b_1365_, v_a_1364_);
lean_dec(v___x_1380_);
v___x_1382_ = lean_unbox(v___x_1381_);
lean_dec(v___x_1381_);
switch(v___x_1382_)
{
case 2:
{
lean_dec(v_a_1364_);
goto v___jp_1371_;
}
case 0:
{
lean_dec(v_a_1364_);
goto v___jp_1371_;
}
default: 
{
v_a_1367_ = v_b_1365_;
goto v___jp_1366_;
}
}
}
}
v___jp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_add(v_a_1364_, v___x_1368_);
lean_dec(v_a_1364_);
v_a_1364_ = v___x_1369_;
v_b_1365_ = v_a_1367_;
goto _start;
}
v___jp_1371_:
{
uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = 0;
v___x_1373_ = lean_box(v___x_1372_);
v___x_1374_ = lean_array_set(v_b_1365_, v_next_1361_, v___x_1373_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(lean_object* v_next_1383_, lean_object* v_upperBound_1384_, lean_object* v___x_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1383_, v_upperBound_1384_, v___x_1385_, v_a_1386_, v_b_1387_);
lean_dec_ref(v___x_1385_);
lean_dec(v_upperBound_1384_);
lean_dec(v_next_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object* v_upperBound_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v_a_1392_, lean_object* v_b_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_nat_dec_lt(v_a_1392_, v_upperBound_1389_);
if (v___x_1394_ == 0)
{
lean_dec(v_a_1392_);
return v_b_1393_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_add(v_a_1392_, v___x_1395_);
lean_inc(v___x_1396_);
v___x_1397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_a_1392_, v___x_1390_, v___x_1391_, v___x_1396_, v_b_1393_);
lean_dec(v_a_1392_);
v_a_1392_ = v___x_1396_;
v_b_1393_ = v___x_1397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object* v_upperBound_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v_a_1402_, lean_object* v_b_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1399_, v___x_1400_, v___x_1401_, v_a_1402_, v_b_1403_);
lean_dec_ref(v___x_1401_);
lean_dec(v___x_1400_);
lean_dec(v_upperBound_1399_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object* v_info_1405_, lean_object* v_kinds_1406_){
_start:
{
lean_object* v_paramInfo_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_paramInfo_1407_ = lean_ctor_get(v_info_1405_, 0);
v___x_1408_ = lean_array_get_size(v_paramInfo_1407_);
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v___x_1408_, v___x_1408_, v_paramInfo_1407_, v___x_1409_, v_kinds_1406_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object* v_info_1411_, lean_object* v_kinds_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_1411_, v_kinds_1412_);
lean_dec_ref(v_info_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(lean_object* v_next_1414_, lean_object* v_upperBound_1415_, lean_object* v___x_1416_, lean_object* v_inst_1417_, lean_object* v_R_1418_, lean_object* v_a_1419_, lean_object* v_b_1420_, lean_object* v_c_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1414_, v_upperBound_1415_, v___x_1416_, v_a_1419_, v_b_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(lean_object* v_next_1423_, lean_object* v_upperBound_1424_, lean_object* v___x_1425_, lean_object* v_inst_1426_, lean_object* v_R_1427_, lean_object* v_a_1428_, lean_object* v_b_1429_, lean_object* v_c_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(v_next_1423_, v_upperBound_1424_, v___x_1425_, v_inst_1426_, v_R_1427_, v_a_1428_, v_b_1429_, v_c_1430_);
lean_dec_ref(v___x_1425_);
lean_dec(v_upperBound_1424_);
lean_dec(v_next_1423_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object* v_upperBound_1432_, lean_object* v___x_1433_, lean_object* v___x_1434_, lean_object* v_inst_1435_, lean_object* v_R_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_, lean_object* v_c_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1432_, v___x_1433_, v___x_1434_, v_a_1437_, v_b_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object* v_upperBound_1441_, lean_object* v___x_1442_, lean_object* v___x_1443_, lean_object* v_inst_1444_, lean_object* v_R_1445_, lean_object* v_a_1446_, lean_object* v_b_1447_, lean_object* v_c_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(v_upperBound_1441_, v___x_1442_, v___x_1443_, v_inst_1444_, v_R_1445_, v_a_1446_, v_b_1447_, v_c_1448_);
lean_dec_ref(v___x_1443_);
lean_dec(v___x_1442_);
lean_dec(v_upperBound_1441_);
return v_res_1449_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object* v_as_1450_, size_t v_i_1451_, size_t v_stop_1452_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_usize_dec_eq(v_i_1451_, v_stop_1452_);
if (v___x_1453_ == 0)
{
uint8_t v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1454_ = 1;
v___x_1455_ = lean_array_uget_borrowed(v_as_1450_, v_i_1451_);
v___x_1456_ = lean_unbox(v___x_1455_);
switch(v___x_1456_)
{
case 3:
{
return v___x_1454_;
}
case 5:
{
return v___x_1454_;
}
default: 
{
if (v___x_1453_ == 0)
{
size_t v___x_1457_; size_t v___x_1458_; 
v___x_1457_ = ((size_t)1ULL);
v___x_1458_ = lean_usize_add(v_i_1451_, v___x_1457_);
v_i_1451_ = v___x_1458_;
goto _start;
}
else
{
return v___x_1454_;
}
}
}
}
else
{
uint8_t v___x_1460_; 
v___x_1460_ = 0;
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object* v_as_1461_, lean_object* v_i_1462_, lean_object* v_stop_1463_){
_start:
{
size_t v_i_boxed_1464_; size_t v_stop_boxed_1465_; uint8_t v_res_1466_; lean_object* v_r_1467_; 
v_i_boxed_1464_ = lean_unbox_usize(v_i_1462_);
lean_dec(v_i_1462_);
v_stop_boxed_1465_ = lean_unbox_usize(v_stop_1463_);
lean_dec(v_stop_1463_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_as_1461_, v_i_boxed_1464_, v_stop_boxed_1465_);
lean_dec_ref(v_as_1461_);
v_r_1467_ = lean_box(v_res_1466_);
return v_r_1467_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object* v_kinds_1468_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = lean_array_get_size(v_kinds_1468_);
v___x_1471_ = lean_nat_dec_lt(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
return v___x_1471_;
}
else
{
if (v___x_1471_ == 0)
{
return v___x_1471_;
}
else
{
size_t v___x_1472_; size_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = ((size_t)0ULL);
v___x_1473_ = lean_usize_of_nat(v___x_1470_);
v___x_1474_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_kinds_1468_, v___x_1472_, v___x_1473_);
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object* v_kinds_1475_){
_start:
{
uint8_t v_res_1476_; lean_object* v_r_1477_; 
v_res_1476_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_1475_);
lean_dec_ref(v_kinds_1475_);
v_r_1477_ = lean_box(v_res_1476_);
return v_r_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object* v___x_1478_, lean_object* v_k_1479_, lean_object* v_xs_1480_, lean_object* v_type_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = lean_array_get_borrowed(v___x_1478_, v_xs_1480_, v___x_1487_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___x_1488_);
v___x_1489_ = lean_apply_7(v_k_1479_, v___x_1488_, v_type_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, lean_box(0));
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object* v___x_1490_, lean_object* v_k_1491_, lean_object* v_xs_1492_, lean_object* v_type_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(v___x_1490_, v_k_1491_, v_xs_1492_, v_type_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec_ref(v_xs_1492_);
lean_dec_ref(v___x_1490_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object* v_type_1500_, lean_object* v_k_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v___f_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1507_ = l_Lean_instInhabitedExpr;
v___f_1508_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1508_, 0, v___x_1507_);
lean_closure_set(v___f_1508_, 1, v_k_1501_);
v___x_1509_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_1510_ = 1;
v___x_1511_ = 0;
v___x_1512_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_1500_, v___x_1509_, v___f_1508_, v___x_1510_, v___x_1511_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(lean_object* v_type_1513_, lean_object* v_k_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1513_, v_k_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object* v_00_u03b1_1521_, lean_object* v_type_1522_, lean_object* v_k_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1522_, v_k_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(lean_object* v_00_u03b1_1530_, lean_object* v_type_1531_, lean_object* v_k_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(v_00_u03b1_1530_, v_type_1531_, v_k_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object* v_kinds_1542_, uint8_t v___x_1543_, lean_object* v_as_1544_, size_t v_sz_1545_, size_t v_i_1546_, lean_object* v_b_1547_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_usize_dec_lt(v_i_1546_, v_sz_1545_);
if (v___x_1548_ == 0)
{
lean_inc_ref(v_b_1547_);
return v_b_1547_;
}
else
{
lean_object* v___x_1549_; lean_object* v_a_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1549_ = lean_box(0);
v_a_1550_ = lean_array_uget_borrowed(v_as_1544_, v_i_1546_);
v___x_1551_ = 0;
v___x_1552_ = lean_box(v___x_1551_);
v___x_1553_ = lean_array_get(v___x_1552_, v_kinds_1542_, v_a_1550_);
lean_dec(v___x_1552_);
v___x_1554_ = lean_unbox(v___x_1553_);
lean_dec(v___x_1553_);
if (v___x_1554_ == 2)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_box(v___x_1543_);
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___x_1549_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; size_t v___x_1559_; size_t v___x_1560_; 
v___x_1558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v___x_1559_ = ((size_t)1ULL);
v___x_1560_ = lean_usize_add(v_i_1546_, v___x_1559_);
v_i_1546_ = v___x_1560_;
v_b_1547_ = v___x_1558_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object* v_kinds_1562_, lean_object* v___x_1563_, lean_object* v_as_1564_, lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_b_1567_){
_start:
{
uint8_t v___x_663__boxed_1568_; size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v___x_663__boxed_1568_ = lean_unbox(v___x_1563_);
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1562_, v___x_663__boxed_1568_, v_as_1564_, v_sz_boxed_1569_, v_i_boxed_1570_, v_b_1567_);
lean_dec_ref(v_b_1567_);
lean_dec_ref(v_as_1564_);
lean_dec_ref(v_kinds_1562_);
return v_res_1571_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object* v_info_1572_, lean_object* v_kinds_1573_, lean_object* v_i_1574_){
_start:
{
lean_object* v_paramInfo_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v_isDecInst_1578_; 
v_paramInfo_1575_ = lean_ctor_get(v_info_1572_, 0);
v___x_1576_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_1577_ = lean_array_get_borrowed(v___x_1576_, v_paramInfo_1575_, v_i_1574_);
v_isDecInst_1578_ = lean_ctor_get_uint8(v___x_1577_, sizeof(void*)*1 + 3);
if (v_isDecInst_1578_ == 0)
{
return v_isDecInst_1578_;
}
else
{
lean_object* v_backDeps_1579_; lean_object* v___x_1580_; size_t v_sz_1581_; size_t v___x_1582_; lean_object* v___x_1583_; lean_object* v_fst_1584_; 
v_backDeps_1579_ = lean_ctor_get(v___x_1577_, 0);
v___x_1580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v_sz_1581_ = lean_array_size(v_backDeps_1579_);
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1573_, v_isDecInst_1578_, v_backDeps_1579_, v_sz_1581_, v___x_1582_, v___x_1580_);
v_fst_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_fst_1584_);
lean_dec_ref(v___x_1583_);
if (lean_obj_tag(v_fst_1584_) == 0)
{
uint8_t v___x_1585_; 
v___x_1585_ = 0;
return v___x_1585_;
}
else
{
lean_object* v_val_1586_; uint8_t v___x_1587_; 
v_val_1586_ = lean_ctor_get(v_fst_1584_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v_fst_1584_, 1);
v___x_1587_ = lean_unbox(v_val_1586_);
lean_dec(v_val_1586_);
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object* v_info_1588_, lean_object* v_kinds_1589_, lean_object* v_i_1590_){
_start:
{
uint8_t v_res_1591_; lean_object* v_r_1592_; 
v_res_1591_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_1588_, v_kinds_1589_, v_i_1590_);
lean_dec(v_i_1590_);
lean_dec_ref(v_kinds_1589_);
lean_dec_ref(v_info_1588_);
v_r_1592_ = lean_box(v_res_1591_);
return v_r_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(lean_object* v_type_1593_, lean_object* v_k_1594_, uint8_t v_cleanupAnnotations_1595_, uint8_t v_whnfType_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___f_1602_; lean_object* v___x_1603_; 
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1602_, 0, v_k_1594_);
v___x_1603_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1593_, v___f_1602_, v_cleanupAnnotations_1595_, v_whnfType_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1603_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1603_);
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
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(lean_object* v_type_1620_, lean_object* v_k_1621_, lean_object* v_cleanupAnnotations_1622_, lean_object* v_whnfType_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1629_; uint8_t v_whnfType_boxed_1630_; lean_object* v_res_1631_; 
v_cleanupAnnotations_boxed_1629_ = lean_unbox(v_cleanupAnnotations_1622_);
v_whnfType_boxed_1630_ = lean_unbox(v_whnfType_1623_);
v_res_1631_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1620_, v_k_1621_, v_cleanupAnnotations_boxed_1629_, v_whnfType_boxed_1630_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_object* v_00_u03b1_1632_, lean_object* v_type_1633_, lean_object* v_k_1634_, uint8_t v_cleanupAnnotations_1635_, uint8_t v_whnfType_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1633_, v_k_1634_, v_cleanupAnnotations_1635_, v_whnfType_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_type_1644_, lean_object* v_k_1645_, lean_object* v_cleanupAnnotations_1646_, lean_object* v_whnfType_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1653_; uint8_t v_whnfType_boxed_1654_; lean_object* v_res_1655_; 
v_cleanupAnnotations_boxed_1653_ = lean_unbox(v_cleanupAnnotations_1646_);
v_whnfType_boxed_1654_ = lean_unbox(v_whnfType_1647_);
v_res_1655_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(v_00_u03b1_1643_, v_type_1644_, v_k_1645_, v_cleanupAnnotations_boxed_1653_, v_whnfType_boxed_1654_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(lean_object* v_upperBound_1656_, lean_object* v_val_1657_, lean_object* v_xs_1658_, lean_object* v___x_1659_, lean_object* v___x_1660_, uint8_t v___x_1661_, lean_object* v_a_1662_, lean_object* v_b_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_a_1669_; uint8_t v___x_1673_; 
v___x_1673_ = lean_nat_dec_lt(v_a_1662_, v_upperBound_1656_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
lean_dec(v_a_1662_);
lean_dec(v___x_1660_);
lean_dec_ref(v___x_1659_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_b_1663_);
return v___x_1674_;
}
else
{
lean_object* v_numParams_1675_; uint8_t v___x_1676_; 
v_numParams_1675_ = lean_ctor_get(v_val_1657_, 3);
v___x_1676_ = lean_nat_dec_lt(v_a_1662_, v_numParams_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_array_fget_borrowed(v_xs_1658_, v_a_1662_);
v___x_1678_ = l_Lean_Expr_fvarId_x21(v___x_1677_);
v___x_1679_ = l_Lean_FVarId_getDecl___redArg(v___x_1678_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; uint8_t v___y_1682_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1685_ = l_Lean_LocalDecl_userName(v_a_1680_);
lean_dec(v_a_1680_);
lean_inc(v___x_1660_);
lean_inc_ref(v___x_1659_);
v___x_1686_ = l_Lean_isSubobjectField_x3f(v___x_1659_, v___x_1660_, v___x_1685_);
if (lean_obj_tag(v___x_1686_) == 0)
{
v___y_1682_ = v___x_1676_;
goto v___jp_1681_;
}
else
{
lean_dec_ref_known(v___x_1686_, 1);
v___y_1682_ = v___x_1661_;
goto v___jp_1681_;
}
v___jp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_box(v___y_1682_);
v___x_1684_ = lean_array_push(v_b_1663_, v___x_1683_);
v_a_1669_ = v___x_1684_;
goto v___jp_1668_;
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v_b_1663_);
lean_dec(v_a_1662_);
lean_dec(v___x_1660_);
lean_dec_ref(v___x_1659_);
v_a_1687_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1679_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1679_);
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
uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = 0;
v___x_1696_ = lean_box(v___x_1695_);
v___x_1697_ = lean_array_push(v_b_1663_, v___x_1696_);
v_a_1669_ = v___x_1697_;
goto v___jp_1668_;
}
}
v___jp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_nat_add(v_a_1662_, v___x_1670_);
lean_dec(v_a_1662_);
v_a_1662_ = v___x_1671_;
v_b_1663_ = v_a_1669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_1698_, lean_object* v_val_1699_, lean_object* v_xs_1700_, lean_object* v___x_1701_, lean_object* v___x_1702_, lean_object* v___x_1703_, lean_object* v_a_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v___x_5676__boxed_1710_; lean_object* v_res_1711_; 
v___x_5676__boxed_1710_ = lean_unbox(v___x_1703_);
v_res_1711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1698_, v_val_1699_, v_xs_1700_, v___x_1701_, v___x_1702_, v___x_5676__boxed_1710_, v_a_1704_, v_b_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_xs_1700_);
lean_dec_ref(v_val_1699_);
lean_dec(v_upperBound_1698_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object* v_val_1714_, lean_object* v_induct_1715_, uint8_t v___x_1716_, lean_object* v_xs_1717_, lean_object* v_x_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; lean_object* v_env_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1724_ = lean_st_ref_get(v___y_1722_);
v_env_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc_ref(v_env_1725_);
lean_dec(v___x_1724_);
v___x_1726_ = lean_array_get_size(v_xs_1717_);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0));
v___x_1729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v___x_1726_, v_val_1714_, v_xs_1717_, v_env_1725_, v_induct_1715_, v___x_1716_, v___x_1727_, v___x_1728_, v___y_1719_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1738_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_a_1730_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1734_);
v___x_1736_ = v___x_1732_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1729_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1729_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object* v_val_1747_, lean_object* v_induct_1748_, lean_object* v___x_1749_, lean_object* v_xs_1750_, lean_object* v_x_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v___x_5763__boxed_1757_; lean_object* v_res_1758_; 
v___x_5763__boxed_1757_ = lean_unbox(v___x_1749_);
v_res_1758_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1747_, v_induct_1748_, v___x_5763__boxed_1757_, v_xs_1750_, v_x_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec_ref(v_x_1751_);
lean_dec_ref(v_xs_1750_);
lean_dec_ref(v_val_1747_);
return v_res_1758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
lean_ctor_set(v___x_1764_, 2, v___x_1763_);
lean_ctor_set(v___x_1764_, 3, v___x_1763_);
lean_ctor_set(v___x_1764_, 4, v___x_1762_);
lean_ctor_set(v___x_1764_, 5, v___x_1762_);
lean_ctor_set(v___x_1764_, 6, v___x_1762_);
lean_ctor_set(v___x_1764_, 7, v___x_1762_);
lean_ctor_set(v___x_1764_, 8, v___x_1762_);
lean_ctor_set(v___x_1764_, 9, v___x_1762_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = lean_unsigned_to_nat(32u);
v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1768_ = ((size_t)5ULL);
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = lean_unsigned_to_nat(32u);
v___x_1771_ = lean_mk_empty_array_with_capacity(v___x_1770_);
v___x_1772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1773_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___x_1771_);
lean_ctor_set(v___x_1773_, 2, v___x_1769_);
lean_ctor_set(v___x_1773_, 3, v___x_1769_);
lean_ctor_set_usize(v___x_1773_, 4, v___x_1768_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1774_ = lean_box(1);
v___x_1775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
lean_ctor_set(v___x_1777_, 1, v___x_1775_);
lean_ctor_set(v___x_1777_, 2, v___x_1774_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1780_ = l_Lean_stringToMessageData(v___x_1779_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1795_ = l_Lean_stringToMessageData(v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1798_ = l_Lean_stringToMessageData(v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1799_, lean_object* v_declHint_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v_env_1804_; uint8_t v___y_1806_; uint8_t v___x_1862_; uint8_t v___x_1863_; 
v___x_1803_ = lean_st_ref_get(v___y_1801_);
v_env_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc_ref(v_env_1804_);
lean_dec(v___x_1803_);
v___x_1862_ = l_Lean_Name_isAnonymous(v_declHint_1800_);
v___x_1863_ = lean_bool_not(v___x_1862_);
if (v___x_1863_ == 0)
{
v___y_1806_ = v___x_1863_;
goto v___jp_1805_;
}
else
{
uint8_t v_isExporting_1864_; 
v_isExporting_1864_ = lean_ctor_get_uint8(v_env_1804_, sizeof(void*)*8);
v___y_1806_ = v_isExporting_1864_;
goto v___jp_1805_;
}
v___jp_1805_:
{
if (v___y_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_msg_1799_);
return v___x_1807_;
}
else
{
uint8_t v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1808_ = 0;
lean_inc_ref(v_env_1804_);
v___x_1809_ = l_Lean_Environment_setExporting(v_env_1804_, v___x_1808_);
lean_inc(v_declHint_1800_);
lean_inc_ref(v___x_1809_);
v___x_1810_ = l_Lean_Environment_contains(v___x_1809_, v_declHint_1800_, v___y_1806_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_msg_1799_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v_c_1817_; lean_object* v___x_1818_; 
v___x_1812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1814_ = l_Lean_Options_empty;
v___x_1815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1809_);
lean_ctor_set(v___x_1815_, 1, v___x_1812_);
lean_ctor_set(v___x_1815_, 2, v___x_1813_);
lean_ctor_set(v___x_1815_, 3, v___x_1814_);
lean_inc(v_declHint_1800_);
v___x_1816_ = l_Lean_MessageData_ofConstName(v_declHint_1800_, v___x_1808_);
v_c_1817_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1817_, 0, v___x_1815_);
lean_ctor_set(v_c_1817_, 1, v___x_1816_);
v___x_1818_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1804_, v_declHint_1800_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v_c_1817_);
v___x_1821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = l_Lean_MessageData_note(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v_msg_1799_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
else
{
lean_object* v_val_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1861_; 
v_val_1826_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1828_ = v___x_1818_;
v_isShared_1829_ = v_isSharedCheck_1861_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_val_1826_);
lean_dec(v___x_1818_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1861_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_mod_1833_; uint8_t v___x_1834_; 
v___x_1830_ = lean_box(0);
v___x_1831_ = l_Lean_Environment_header(v_env_1804_);
lean_dec_ref(v_env_1804_);
v___x_1832_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1831_);
v_mod_1833_ = lean_array_get(v___x_1830_, v___x_1832_, v_val_1826_);
lean_dec(v_val_1826_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = l_Lean_isPrivateName(v_declHint_1800_);
lean_dec(v_declHint_1800_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_c_1817_);
v___x_1837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_MessageData_ofName(v_mod_1833_);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = l_Lean_MessageData_note(v___x_1842_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_msg_1799_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1844_);
v___x_1846_ = v___x_1828_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_c_1817_);
v___x_1850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_MessageData_ofName(v_mod_1833_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Lean_MessageData_note(v___x_1855_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_msg_1799_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1857_);
v___x_1859_ = v___x_1828_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1865_, lean_object* v_declHint_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1865_, v_declHint_1866_, v___y_1867_);
lean_dec(v___y_1867_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msg_1870_, lean_object* v_declHint_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1887_; 
v___x_1877_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1870_, v_declHint_1871_, v___y_1875_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1882_ = l_Lean_unknownIdentifierMessageTag;
v___x_1883_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_a_1878_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1888_, lean_object* v_declHint_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1888_, v_declHint_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1896_, lean_object* v_msg_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_fileName_1903_; lean_object* v_fileMap_1904_; lean_object* v_options_1905_; lean_object* v_currRecDepth_1906_; lean_object* v_maxRecDepth_1907_; lean_object* v_ref_1908_; lean_object* v_currNamespace_1909_; lean_object* v_openDecls_1910_; lean_object* v_initHeartbeats_1911_; lean_object* v_maxHeartbeats_1912_; lean_object* v_quotContext_1913_; lean_object* v_currMacroScope_1914_; uint8_t v_diag_1915_; lean_object* v_cancelTk_x3f_1916_; uint8_t v_suppressElabErrors_1917_; lean_object* v_inheritedTraceOptions_1918_; lean_object* v_ref_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_fileName_1903_ = lean_ctor_get(v___y_1900_, 0);
v_fileMap_1904_ = lean_ctor_get(v___y_1900_, 1);
v_options_1905_ = lean_ctor_get(v___y_1900_, 2);
v_currRecDepth_1906_ = lean_ctor_get(v___y_1900_, 3);
v_maxRecDepth_1907_ = lean_ctor_get(v___y_1900_, 4);
v_ref_1908_ = lean_ctor_get(v___y_1900_, 5);
v_currNamespace_1909_ = lean_ctor_get(v___y_1900_, 6);
v_openDecls_1910_ = lean_ctor_get(v___y_1900_, 7);
v_initHeartbeats_1911_ = lean_ctor_get(v___y_1900_, 8);
v_maxHeartbeats_1912_ = lean_ctor_get(v___y_1900_, 9);
v_quotContext_1913_ = lean_ctor_get(v___y_1900_, 10);
v_currMacroScope_1914_ = lean_ctor_get(v___y_1900_, 11);
v_diag_1915_ = lean_ctor_get_uint8(v___y_1900_, sizeof(void*)*14);
v_cancelTk_x3f_1916_ = lean_ctor_get(v___y_1900_, 12);
v_suppressElabErrors_1917_ = lean_ctor_get_uint8(v___y_1900_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1918_ = lean_ctor_get(v___y_1900_, 13);
v_ref_1919_ = l_Lean_replaceRef(v_ref_1896_, v_ref_1908_);
lean_inc_ref(v_inheritedTraceOptions_1918_);
lean_inc(v_cancelTk_x3f_1916_);
lean_inc(v_currMacroScope_1914_);
lean_inc(v_quotContext_1913_);
lean_inc(v_maxHeartbeats_1912_);
lean_inc(v_initHeartbeats_1911_);
lean_inc(v_openDecls_1910_);
lean_inc(v_currNamespace_1909_);
lean_inc(v_maxRecDepth_1907_);
lean_inc(v_currRecDepth_1906_);
lean_inc_ref(v_options_1905_);
lean_inc_ref(v_fileMap_1904_);
lean_inc_ref(v_fileName_1903_);
v___x_1920_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1920_, 0, v_fileName_1903_);
lean_ctor_set(v___x_1920_, 1, v_fileMap_1904_);
lean_ctor_set(v___x_1920_, 2, v_options_1905_);
lean_ctor_set(v___x_1920_, 3, v_currRecDepth_1906_);
lean_ctor_set(v___x_1920_, 4, v_maxRecDepth_1907_);
lean_ctor_set(v___x_1920_, 5, v_ref_1919_);
lean_ctor_set(v___x_1920_, 6, v_currNamespace_1909_);
lean_ctor_set(v___x_1920_, 7, v_openDecls_1910_);
lean_ctor_set(v___x_1920_, 8, v_initHeartbeats_1911_);
lean_ctor_set(v___x_1920_, 9, v_maxHeartbeats_1912_);
lean_ctor_set(v___x_1920_, 10, v_quotContext_1913_);
lean_ctor_set(v___x_1920_, 11, v_currMacroScope_1914_);
lean_ctor_set(v___x_1920_, 12, v_cancelTk_x3f_1916_);
lean_ctor_set(v___x_1920_, 13, v_inheritedTraceOptions_1918_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*14, v_diag_1915_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*14 + 1, v_suppressElabErrors_1917_);
v___x_1921_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_msg_1897_, v___y_1898_, v___y_1899_, v___x_1920_, v___y_1901_);
lean_dec_ref_known(v___x_1920_, 14);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1922_, lean_object* v_msg_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1922_, v_msg_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v_ref_1922_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1930_, lean_object* v_msg_1931_, lean_object* v_declHint_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v_a_1939_; lean_object* v___x_1940_; 
v___x_1938_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1931_, v_declHint_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1938_);
v___x_1940_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1930_, v_a_1939_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1941_, lean_object* v_msg_1942_, lean_object* v_declHint_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1941_, v_msg_1942_, v_declHint_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v_ref_1941_);
return v_res_1949_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1952_ = l_Lean_stringToMessageData(v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1955_ = l_Lean_stringToMessageData(v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1956_, lean_object* v_constName_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1963_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1964_ = 0;
lean_inc(v_constName_1957_);
v___x_1965_ = l_Lean_MessageData_ofConstName(v_constName_1957_, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1963_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1956_, v___x_1968_, v_constName_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1970_, lean_object* v_constName_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1970_, v_constName_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v_ref_1970_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_ref_1984_; lean_object* v___x_1985_; 
v_ref_1984_ = lean_ctor_get(v___y_1981_, 5);
v___x_1985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1984_, v_constName_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v_env_2000_; uint8_t v___x_2001_; lean_object* v___x_2002_; 
v___x_1999_ = lean_st_ref_get(v___y_1997_);
v_env_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_ref(v_env_2000_);
lean_dec(v___x_1999_);
v___x_2001_ = 0;
lean_inc(v_constName_1993_);
v___x_2002_ = l_Lean_Environment_find_x3f(v_env_2000_, v_constName_1993_, v___x_2001_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_2003_;
}
else
{
lean_object* v_val_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec(v_constName_1993_);
v_val_2004_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2002_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_val_2004_);
lean_dec(v___x_2002_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 0);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_val_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
if (lean_obj_tag(v_f_2019_) == 4)
{
lean_object* v_declName_2025_; lean_object* v___x_2026_; 
v_declName_2025_ = lean_ctor_get(v_f_2019_, 0);
lean_inc(v_declName_2025_);
lean_dec_ref_known(v_f_2019_, 2);
v___x_2026_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2025_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2050_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2050_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2050_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
if (lean_obj_tag(v_a_2027_) == 6)
{
lean_object* v_val_2031_; lean_object* v___x_2032_; lean_object* v_env_2033_; lean_object* v_toConstantVal_2034_; lean_object* v_induct_2035_; uint8_t v___x_2036_; 
v_val_2031_ = lean_ctor_get(v_a_2027_, 0);
lean_inc_ref(v_val_2031_);
lean_dec_ref_known(v_a_2027_, 1);
v___x_2032_ = lean_st_ref_get(v_a_2023_);
v_env_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc_ref(v_env_2033_);
lean_dec(v___x_2032_);
v_toConstantVal_2034_ = lean_ctor_get(v_val_2031_, 0);
v_induct_2035_ = lean_ctor_get(v_val_2031_, 1);
lean_inc(v_induct_2035_);
v___x_2036_ = l_Lean_isClass(v_env_2033_, v_induct_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v_induct_2035_);
lean_dec_ref(v_val_2031_);
v___x_2037_ = lean_box(0);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2037_);
v___x_2039_ = v___x_2029_;
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
else
{
lean_object* v_type_2041_; lean_object* v___x_2042_; lean_object* v___f_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; 
lean_del_object(v___x_2029_);
v_type_2041_ = lean_ctor_get(v_toConstantVal_2034_, 2);
lean_inc_ref(v_type_2041_);
v___x_2042_ = lean_box(v___x_2036_);
v___f_2043_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2043_, 0, v_val_2031_);
lean_closure_set(v___f_2043_, 1, v_induct_2035_);
lean_closure_set(v___f_2043_, 2, v___x_2042_);
v___x_2044_ = 0;
v___x_2045_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2041_, v___f_2043_, v___x_2036_, v___x_2044_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
return v___x_2045_;
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec(v_a_2027_);
v___x_2046_ = lean_box(0);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2046_);
v___x_2048_ = v___x_2029_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2026_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2026_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_dec_ref(v_f_2019_);
v___x_2059_ = lean_box(0);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2068_, lean_object* v_val_2069_, lean_object* v_xs_2070_, lean_object* v___x_2071_, lean_object* v___x_2072_, uint8_t v___x_2073_, lean_object* v_inst_2074_, lean_object* v_R_2075_, lean_object* v_a_2076_, lean_object* v_b_2077_, lean_object* v_c_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2068_, v_val_2069_, v_xs_2070_, v___x_2071_, v___x_2072_, v___x_2073_, v_a_2076_, v_b_2077_, v___y_2079_, v___y_2081_, v___y_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2085_, lean_object* v_val_2086_, lean_object* v_xs_2087_, lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v_inst_2091_, lean_object* v_R_2092_, lean_object* v_a_2093_, lean_object* v_b_2094_, lean_object* v_c_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v___x_6349__boxed_2101_; lean_object* v_res_2102_; 
v___x_6349__boxed_2101_ = lean_unbox(v___x_2090_);
v_res_2102_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2085_, v_val_2086_, v_xs_2087_, v___x_2088_, v___x_2089_, v___x_6349__boxed_2101_, v_inst_2091_, v_R_2092_, v_a_2093_, v_b_2094_, v_c_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v_xs_2087_);
lean_dec_ref(v_val_2086_);
lean_dec(v_upperBound_2085_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2103_, lean_object* v_constName_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2111_, lean_object* v_constName_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2111_, v_constName_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2119_, lean_object* v_ref_2120_, lean_object* v_constName_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2120_, v_constName_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_ref_2129_, lean_object* v_constName_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2128_, v_ref_2129_, v_constName_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v_ref_2129_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2137_, lean_object* v_ref_2138_, lean_object* v_msg_2139_, lean_object* v_declHint_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2138_, v_msg_2139_, v_declHint_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_ref_2148_, lean_object* v_msg_2149_, lean_object* v_declHint_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2147_, v_ref_2148_, v_msg_2149_, v_declHint_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v_ref_2148_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2157_, lean_object* v_declHint_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2157_, v_declHint_2158_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2165_, lean_object* v_declHint_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2165_, v_declHint_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2173_, lean_object* v_ref_2174_, lean_object* v_msg_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2174_, v_msg_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2182_, lean_object* v_ref_2183_, lean_object* v_msg_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2182_, v_ref_2183_, v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v_ref_2183_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2191_, lean_object* v_a_2192_, lean_object* v_____r_2193_, lean_object* v_result_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v___x_2200_; 
v___x_2200_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2191_, v_result_2194_, v_a_2192_);
if (v___x_2200_ == 0)
{
uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2201_ = 0;
v___x_2202_ = lean_box(v___x_2201_);
v___x_2203_ = lean_array_push(v_result_2194_, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
else
{
uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2206_ = 5;
v___x_2207_ = lean_box(v___x_2206_);
v___x_2208_ = lean_array_push(v_result_2194_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2211_, lean_object* v_a_2212_, lean_object* v_____r_2213_, lean_object* v_result_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2211_, v_a_2212_, v_____r_2213_, v_result_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v_a_2212_);
lean_dec_ref(v_info_2211_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2221_, lean_object* v_upperBound_2222_, lean_object* v___x_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_b_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_a_2233_; lean_object* v___y_2238_; uint8_t v___x_2257_; 
v___x_2257_ = lean_nat_dec_lt(v_a_2225_, v_upperBound_2222_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
lean_dec(v_a_2225_);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v_b_2226_);
return v___x_2258_;
}
else
{
lean_object* v_resultDeps_2259_; uint8_t v___x_2260_; 
v_resultDeps_2259_ = lean_ctor_get(v_info_2221_, 1);
v___x_2260_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2259_, v_a_2225_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; uint8_t v_isProp_2262_; 
v___x_2261_ = lean_array_fget_borrowed(v___x_2223_, v_a_2225_);
v_isProp_2262_ = lean_ctor_get_uint8(v___x_2261_, sizeof(void*)*1 + 2);
if (v_isProp_2262_ == 0)
{
uint8_t v_isInstance_2263_; 
v_isInstance_2263_ = lean_ctor_get_uint8(v___x_2261_, sizeof(void*)*1 + 4);
if (v_isInstance_2263_ == 0)
{
uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = 2;
v___x_2265_ = lean_box(v___x_2264_);
v___x_2266_ = lean_array_push(v_b_2226_, v___x_2265_);
v_a_2233_ = v___x_2266_;
goto v___jp_2232_;
}
else
{
if (lean_obj_tag(v_a_2224_) == 1)
{
lean_object* v_val_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_val_2267_ = lean_ctor_get(v_a_2224_, 0);
v___x_2268_ = lean_array_get_size(v_val_2267_);
v___x_2269_ = lean_nat_dec_lt(v_a_2225_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_box(0);
v___x_2271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2221_, v_a_2225_, v___x_2270_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
v___y_2238_ = v___x_2271_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = lean_array_fget_borrowed(v_val_2267_, v_a_2225_);
v___x_2273_ = lean_unbox(v___x_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2221_, v_a_2225_, v___x_2274_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
v___y_2238_ = v___x_2275_;
goto v___jp_2237_;
}
else
{
uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = 2;
v___x_2277_ = lean_box(v___x_2276_);
v___x_2278_ = lean_array_push(v_b_2226_, v___x_2277_);
v_a_2233_ = v___x_2278_;
goto v___jp_2232_;
}
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2221_, v_a_2225_, v___x_2279_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
v___y_2238_ = v___x_2280_;
goto v___jp_2237_;
}
}
}
else
{
uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = 3;
v___x_2282_ = lean_box(v___x_2281_);
v___x_2283_ = lean_array_push(v_b_2226_, v___x_2282_);
v_a_2233_ = v___x_2283_;
goto v___jp_2232_;
}
}
else
{
uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = 0;
v___x_2285_ = lean_box(v___x_2284_);
v___x_2286_ = lean_array_push(v_b_2226_, v___x_2285_);
v_a_2233_ = v___x_2286_;
goto v___jp_2232_;
}
}
v___jp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_unsigned_to_nat(1u);
v___x_2235_ = lean_nat_add(v_a_2225_, v___x_2234_);
lean_dec(v_a_2225_);
v_a_2225_ = v___x_2235_;
v_b_2226_ = v_a_2233_;
goto _start;
}
v___jp_2237_:
{
if (lean_obj_tag(v___y_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2248_; 
v_a_2239_ = lean_ctor_get(v___y_2238_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___y_2238_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2241_ = v___y_2238_;
v_isShared_2242_ = v_isSharedCheck_2248_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___y_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2248_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
if (lean_obj_tag(v_a_2239_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; 
lean_dec(v_a_2225_);
v_a_2243_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v_a_2239_, 1);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v_a_2243_);
v___x_2245_ = v___x_2241_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
else
{
lean_object* v_a_2247_; 
lean_del_object(v___x_2241_);
v_a_2247_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v_a_2239_, 1);
v_a_2233_ = v_a_2247_;
goto v___jp_2232_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_a_2225_);
v_a_2249_ = lean_ctor_get(v___y_2238_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___y_2238_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___y_2238_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___y_2238_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2287_, lean_object* v_upperBound_2288_, lean_object* v___x_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_b_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2287_, v_upperBound_2288_, v___x_2289_, v_a_2290_, v_a_2291_, v_b_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v_a_2290_);
lean_dec_ref(v___x_2289_);
lean_dec(v_upperBound_2288_);
lean_dec_ref(v_info_2287_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2301_, lean_object* v_info_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2301_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v_paramInfo_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_result_2313_; lean_object* v___x_2314_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v_paramInfo_2310_ = lean_ctor_get(v_info_2302_, 0);
v___x_2311_ = lean_array_get_size(v_paramInfo_2310_);
v___x_2312_ = lean_unsigned_to_nat(0u);
v_result_2313_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2314_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2302_, v___x_2311_, v_paramInfo_2310_, v_a_2309_, v___x_2312_, v_result_2313_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2309_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2323_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2302_, v_a_2315_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2319_);
v___x_2321_ = v___x_2317_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
else
{
return v___x_2314_;
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
v_a_2324_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2308_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2308_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2332_, lean_object* v_info_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Meta_getCongrSimpKinds(v_f_2332_, v_info_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec_ref(v_info_2333_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2340_, lean_object* v_upperBound_2341_, lean_object* v___x_2342_, lean_object* v_a_2343_, lean_object* v_inst_2344_, lean_object* v_R_2345_, lean_object* v_a_2346_, lean_object* v_b_2347_, lean_object* v_c_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2340_, v_upperBound_2341_, v___x_2342_, v_a_2343_, v_a_2346_, v_b_2347_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2355_, lean_object* v_upperBound_2356_, lean_object* v___x_2357_, lean_object* v_a_2358_, lean_object* v_inst_2359_, lean_object* v_R_2360_, lean_object* v_a_2361_, lean_object* v_b_2362_, lean_object* v_c_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2355_, v_upperBound_2356_, v___x_2357_, v_a_2358_, v_inst_2359_, v_R_2360_, v_a_2361_, v_b_2362_, v_c_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v_a_2358_);
lean_dec_ref(v___x_2357_);
lean_dec(v_upperBound_2356_);
lean_dec_ref(v_info_2355_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2370_, lean_object* v_info_2371_, lean_object* v___x_2372_, lean_object* v_a_2373_, lean_object* v_b_2374_){
_start:
{
lean_object* v_a_2377_; uint8_t v___x_2381_; 
v___x_2381_ = lean_nat_dec_lt(v_a_2373_, v_upperBound_2370_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; 
lean_dec(v_a_2373_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_b_2374_);
return v___x_2382_;
}
else
{
lean_object* v_resultDeps_2383_; uint8_t v___x_2384_; 
v_resultDeps_2383_ = lean_ctor_get(v_info_2371_, 1);
v___x_2384_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2383_, v_a_2373_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2385_ = lean_unsigned_to_nat(0u);
v___x_2386_ = lean_nat_dec_eq(v_a_2373_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; uint8_t v_isProp_2388_; 
v___x_2387_ = lean_array_fget_borrowed(v___x_2372_, v_a_2373_);
v_isProp_2388_ = lean_ctor_get_uint8(v___x_2387_, sizeof(void*)*1 + 2);
if (v_isProp_2388_ == 0)
{
uint8_t v_isInstance_2389_; 
v_isInstance_2389_ = lean_ctor_get_uint8(v___x_2387_, sizeof(void*)*1 + 4);
if (v_isInstance_2389_ == 0)
{
uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = 0;
v___x_2391_ = lean_box(v___x_2390_);
v___x_2392_ = lean_array_push(v_b_2374_, v___x_2391_);
v_a_2377_ = v___x_2392_;
goto v___jp_2376_;
}
else
{
uint8_t v___x_2393_; 
v___x_2393_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2371_, v_b_2374_, v_a_2373_);
if (v___x_2393_ == 0)
{
uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = 0;
v___x_2395_ = lean_box(v___x_2394_);
v___x_2396_ = lean_array_push(v_b_2374_, v___x_2395_);
v_a_2377_ = v___x_2396_;
goto v___jp_2376_;
}
else
{
uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = 5;
v___x_2398_ = lean_box(v___x_2397_);
v___x_2399_ = lean_array_push(v_b_2374_, v___x_2398_);
v_a_2377_ = v___x_2399_;
goto v___jp_2376_;
}
}
}
else
{
uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = 3;
v___x_2401_ = lean_box(v___x_2400_);
v___x_2402_ = lean_array_push(v_b_2374_, v___x_2401_);
v_a_2377_ = v___x_2402_;
goto v___jp_2376_;
}
}
else
{
uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = 2;
v___x_2404_ = lean_box(v___x_2403_);
v___x_2405_ = lean_array_push(v_b_2374_, v___x_2404_);
v_a_2377_ = v___x_2405_;
goto v___jp_2376_;
}
}
else
{
uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = 0;
v___x_2407_ = lean_box(v___x_2406_);
v___x_2408_ = lean_array_push(v_b_2374_, v___x_2407_);
v_a_2377_ = v___x_2408_;
goto v___jp_2376_;
}
}
v___jp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_unsigned_to_nat(1u);
v___x_2379_ = lean_nat_add(v_a_2373_, v___x_2378_);
lean_dec(v_a_2373_);
v_a_2373_ = v___x_2379_;
v_b_2374_ = v_a_2377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2409_, lean_object* v_info_2410_, lean_object* v___x_2411_, lean_object* v_a_2412_, lean_object* v_b_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2409_, v_info_2410_, v___x_2411_, v_a_2412_, v_b_2413_);
lean_dec_ref(v___x_2411_);
lean_dec_ref(v_info_2410_);
lean_dec(v_upperBound_2409_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_paramInfo_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_result_2425_; lean_object* v___x_2426_; 
v_paramInfo_2422_ = lean_ctor_get(v_info_2416_, 0);
v___x_2423_ = lean_array_get_size(v_paramInfo_2422_);
v___x_2424_ = lean_unsigned_to_nat(0u);
v_result_2425_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2423_, v_info_2416_, v_paramInfo_2422_, v___x_2424_, v_result_2425_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2416_, v_a_2427_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec_ref(v_info_2436_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2443_, lean_object* v_info_2444_, lean_object* v___x_2445_, lean_object* v_inst_2446_, lean_object* v_R_2447_, lean_object* v_a_2448_, lean_object* v_b_2449_, lean_object* v_c_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2443_, v_info_2444_, v___x_2445_, v_a_2448_, v_b_2449_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2457_, lean_object* v_info_2458_, lean_object* v___x_2459_, lean_object* v_inst_2460_, lean_object* v_R_2461_, lean_object* v_a_2462_, lean_object* v_b_2463_, lean_object* v_c_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2457_, v_info_2458_, v___x_2459_, v_inst_2460_, v_R_2461_, v_a_2462_, v_b_2463_, v_c_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec_ref(v___x_2459_);
lean_dec_ref(v_info_2458_);
lean_dec(v_upperBound_2457_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(lean_object* v_x_2471_){
_start:
{
if (lean_obj_tag(v_x_2471_) == 0)
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_unsigned_to_nat(0u);
return v___x_2472_;
}
else
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_unsigned_to_nat(1u);
return v___x_2473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___boxed(lean_object* v_x_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx(v_x_2474_);
lean_dec_ref(v_x_2474_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2476_, lean_object* v_k_2477_){
_start:
{
if (lean_obj_tag(v_t_2476_) == 0)
{
lean_object* v_fvarId_2478_; lean_object* v___x_2479_; 
v_fvarId_2478_ = lean_ctor_get(v_t_2476_, 0);
lean_inc(v_fvarId_2478_);
lean_dec_ref_known(v_t_2476_, 1);
v___x_2479_ = lean_apply_1(v_k_2477_, v_fvarId_2478_);
return v___x_2479_;
}
else
{
lean_object* v_lhs_2480_; lean_object* v_rhs_2481_; lean_object* v___x_2482_; 
v_lhs_2480_ = lean_ctor_get(v_t_2476_, 0);
lean_inc(v_lhs_2480_);
v_rhs_2481_ = lean_ctor_get(v_t_2476_, 1);
lean_inc(v_rhs_2481_);
lean_dec_ref_known(v_t_2476_, 2);
v___x_2482_ = lean_apply_2(v_k_2477_, v_lhs_2480_, v_rhs_2481_);
return v___x_2482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2483_, lean_object* v_ctorIdx_2484_, lean_object* v_t_2485_, lean_object* v_h_2486_, lean_object* v_k_2487_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2485_, v_k_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2489_, lean_object* v_ctorIdx_2490_, lean_object* v_t_2491_, lean_object* v_h_2492_, lean_object* v_k_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2489_, v_ctorIdx_2490_, v_t_2491_, v_h_2492_, v_k_2493_);
lean_dec(v_ctorIdx_2490_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2495_, lean_object* v_hyp_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2495_, v_hyp_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2498_, lean_object* v_t_2499_, lean_object* v_h_2500_, lean_object* v_hyp_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2499_, v_hyp_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2503_, lean_object* v_decSubsingleton_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2503_, v_decSubsingleton_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2506_, lean_object* v_t_2507_, lean_object* v_h_2508_, lean_object* v_decSubsingleton_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2507_, v_decSubsingleton_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2511_, lean_object* v_fvarId_2512_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2511_, v_fvarId_2512_);
if (lean_obj_tag(v___x_2513_) == 1)
{
lean_object* v_val_2514_; lean_object* v___x_2515_; 
v_val_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = l_Lean_Expr_fvarId_x21(v_val_2514_);
lean_dec(v_val_2514_);
return v___x_2515_;
}
else
{
lean_dec(v___x_2513_);
lean_inc(v_fvarId_2512_);
return v_fvarId_2512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2516_, lean_object* v_fvarId_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2516_, v_fvarId_2517_);
lean_dec(v_fvarId_2517_);
lean_dec(v_s_2516_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2519_, lean_object* v_x_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2519_, v_x_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
v_a_2535_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2526_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2526_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2543_, lean_object* v_x_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2543_, v_x_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2551_, lean_object* v_mvarId_2552_, lean_object* v_x_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2552_, v_x_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2560_, lean_object* v_mvarId_2561_, lean_object* v_x_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2560_, v_mvarId_2561_, v_x_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2569_, lean_object* v___y_2570_){
_start:
{
uint8_t v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = l_Lean_Expr_hasMVar(v_e_2569_);
v___x_2573_ = lean_bool_not(v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v_mctx_2575_; lean_object* v___x_2576_; lean_object* v_fst_2577_; lean_object* v_snd_2578_; lean_object* v___x_2579_; lean_object* v_cache_2580_; lean_object* v_zetaDeltaFVarIds_2581_; lean_object* v_postponed_2582_; lean_object* v_diag_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2592_; 
v___x_2574_ = lean_st_ref_get(v___y_2570_);
v_mctx_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc_ref(v_mctx_2575_);
lean_dec(v___x_2574_);
v___x_2576_ = l_Lean_instantiateMVarsCore(v_mctx_2575_, v_e_2569_);
v_fst_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_fst_2577_);
v_snd_2578_ = lean_ctor_get(v___x_2576_, 1);
lean_inc(v_snd_2578_);
lean_dec_ref(v___x_2576_);
v___x_2579_ = lean_st_ref_take(v___y_2570_);
v_cache_2580_ = lean_ctor_get(v___x_2579_, 1);
v_zetaDeltaFVarIds_2581_ = lean_ctor_get(v___x_2579_, 2);
v_postponed_2582_ = lean_ctor_get(v___x_2579_, 3);
v_diag_2583_ = lean_ctor_get(v___x_2579_, 4);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2592_ == 0)
{
lean_object* v_unused_2593_; 
v_unused_2593_ = lean_ctor_get(v___x_2579_, 0);
lean_dec(v_unused_2593_);
v___x_2585_ = v___x_2579_;
v_isShared_2586_ = v_isSharedCheck_2592_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_diag_2583_);
lean_inc(v_postponed_2582_);
lean_inc(v_zetaDeltaFVarIds_2581_);
lean_inc(v_cache_2580_);
lean_dec(v___x_2579_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2592_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v_snd_2578_);
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_snd_2578_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_cache_2580_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_zetaDeltaFVarIds_2581_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_postponed_2582_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_diag_2583_);
v___x_2588_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = lean_st_ref_set(v___y_2570_, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v_fst_2577_);
return v___x_2590_;
}
}
}
else
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_e_2569_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2595_, v___y_2596_);
lean_dec(v___y_2596_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2599_, v___y_2601_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2613_, lean_object* v_x_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v_ks_2617_; lean_object* v_vs_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2642_; 
v_ks_2617_ = lean_ctor_get(v_x_2613_, 0);
v_vs_2618_ = lean_ctor_get(v_x_2613_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_x_2613_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2620_ = v_x_2613_;
v_isShared_2621_ = v_isSharedCheck_2642_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_vs_2618_);
lean_inc(v_ks_2617_);
lean_dec(v_x_2613_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2642_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = lean_array_get_size(v_ks_2617_);
v___x_2623_ = lean_nat_dec_lt(v_x_2614_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_dec(v_x_2614_);
v___x_2624_ = lean_array_push(v_ks_2617_, v_x_2615_);
v___x_2625_ = lean_array_push(v_vs_2618_, v_x_2616_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v___x_2625_);
lean_ctor_set(v___x_2620_, 0, v___x_2624_);
v___x_2627_ = v___x_2620_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
else
{
lean_object* v_k_x27_2629_; uint8_t v___x_2630_; 
v_k_x27_2629_ = lean_array_fget_borrowed(v_ks_2617_, v_x_2614_);
v___x_2630_ = l_Lean_instBEqMVarId_beq(v_x_2615_, v_k_x27_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2632_; 
if (v_isShared_2621_ == 0)
{
v___x_2632_ = v___x_2620_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_ks_2617_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_vs_2618_);
v___x_2632_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_nat_add(v_x_2614_, v___x_2633_);
lean_dec(v_x_2614_);
v_x_2613_ = v___x_2632_;
v_x_2614_ = v___x_2634_;
goto _start;
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2637_ = lean_array_fset(v_ks_2617_, v_x_2614_, v_x_2615_);
v___x_2638_ = lean_array_fset(v_vs_2618_, v_x_2614_, v_x_2616_);
lean_dec(v_x_2614_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v___x_2638_);
lean_ctor_set(v___x_2620_, 0, v___x_2637_);
v___x_2640_ = v___x_2620_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2643_, lean_object* v_k_2644_, lean_object* v_v_2645_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_unsigned_to_nat(0u);
v___x_2647_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2643_, v___x_2646_, v_k_2644_, v_v_2645_);
return v___x_2647_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2649_, size_t v_x_2650_, size_t v_x_2651_, lean_object* v_x_2652_, lean_object* v_x_2653_){
_start:
{
if (lean_obj_tag(v_x_2649_) == 0)
{
lean_object* v_es_2654_; size_t v___x_2655_; size_t v___x_2656_; lean_object* v_j_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_es_2654_ = lean_ctor_get(v_x_2649_, 0);
v___x_2655_ = ((size_t)31ULL);
v___x_2656_ = lean_usize_land(v_x_2650_, v___x_2655_);
v_j_2657_ = lean_usize_to_nat(v___x_2656_);
v___x_2658_ = lean_array_get_size(v_es_2654_);
v___x_2659_ = lean_nat_dec_lt(v_j_2657_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_dec(v_j_2657_);
lean_dec(v_x_2653_);
lean_dec(v_x_2652_);
return v_x_2649_;
}
else
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2698_; 
lean_inc_ref(v_es_2654_);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_x_2649_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v_x_2649_, 0);
lean_dec(v_unused_2699_);
v___x_2661_ = v_x_2649_;
v_isShared_2662_ = v_isSharedCheck_2698_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v_x_2649_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2698_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_v_2663_; lean_object* v___x_2664_; lean_object* v_xs_x27_2665_; lean_object* v___y_2667_; 
v_v_2663_ = lean_array_fget(v_es_2654_, v_j_2657_);
v___x_2664_ = lean_box(0);
v_xs_x27_2665_ = lean_array_fset(v_es_2654_, v_j_2657_, v___x_2664_);
switch(lean_obj_tag(v_v_2663_))
{
case 0:
{
lean_object* v_key_2672_; lean_object* v_val_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2683_; 
v_key_2672_ = lean_ctor_get(v_v_2663_, 0);
v_val_2673_ = lean_ctor_get(v_v_2663_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_v_2663_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2675_ = v_v_2663_;
v_isShared_2676_ = v_isSharedCheck_2683_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_val_2673_);
lean_inc(v_key_2672_);
lean_dec(v_v_2663_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2683_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
uint8_t v___x_2677_; 
v___x_2677_ = l_Lean_instBEqMVarId_beq(v_x_2652_, v_key_2672_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_del_object(v___x_2675_);
v___x_2678_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2672_, v_val_2673_, v_x_2652_, v_x_2653_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
v___y_2667_ = v___x_2679_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2681_; 
lean_dec(v_val_2673_);
lean_dec(v_key_2672_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 1, v_x_2653_);
lean_ctor_set(v___x_2675_, 0, v_x_2652_);
v___x_2681_ = v___x_2675_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_x_2652_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_x_2653_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
v___y_2667_ = v___x_2681_;
goto v___jp_2666_;
}
}
}
}
case 1:
{
lean_object* v_node_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2696_; 
v_node_2684_ = lean_ctor_get(v_v_2663_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_v_2663_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2686_ = v_v_2663_;
v_isShared_2687_ = v_isSharedCheck_2696_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_node_2684_);
lean_dec(v_v_2663_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2696_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
size_t v___x_2688_; size_t v___x_2689_; size_t v___x_2690_; size_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2688_ = ((size_t)5ULL);
v___x_2689_ = lean_usize_shift_right(v_x_2650_, v___x_2688_);
v___x_2690_ = ((size_t)1ULL);
v___x_2691_ = lean_usize_add(v_x_2651_, v___x_2690_);
v___x_2692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2684_, v___x_2689_, v___x_2691_, v_x_2652_, v_x_2653_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2692_);
v___x_2694_ = v___x_2686_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
v___y_2667_ = v___x_2694_;
goto v___jp_2666_;
}
}
}
default: 
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_x_2652_);
lean_ctor_set(v___x_2697_, 1, v_x_2653_);
v___y_2667_ = v___x_2697_;
goto v___jp_2666_;
}
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = lean_array_fset(v_xs_x27_2665_, v_j_2657_, v___y_2667_);
lean_dec(v_j_2657_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2668_);
v___x_2670_ = v___x_2661_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
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
}
else
{
lean_object* v_ks_2700_; lean_object* v_vs_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2721_; 
v_ks_2700_ = lean_ctor_get(v_x_2649_, 0);
v_vs_2701_ = lean_ctor_get(v_x_2649_, 1);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_x_2649_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2703_ = v_x_2649_;
v_isShared_2704_ = v_isSharedCheck_2721_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_vs_2701_);
lean_inc(v_ks_2700_);
lean_dec(v_x_2649_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2721_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_ks_2700_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_vs_2701_);
v___x_2706_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v_newNode_2707_; uint8_t v___y_2709_; size_t v___x_2715_; uint8_t v___x_2716_; 
v_newNode_2707_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2706_, v_x_2652_, v_x_2653_);
v___x_2715_ = ((size_t)7ULL);
v___x_2716_ = lean_usize_dec_le(v___x_2715_, v_x_2651_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2717_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2707_);
v___x_2718_ = lean_unsigned_to_nat(4u);
v___x_2719_ = lean_nat_dec_lt(v___x_2717_, v___x_2718_);
lean_dec(v___x_2717_);
v___y_2709_ = v___x_2719_;
goto v___jp_2708_;
}
else
{
v___y_2709_ = v___x_2716_;
goto v___jp_2708_;
}
v___jp_2708_:
{
if (v___y_2709_ == 0)
{
lean_object* v_ks_2710_; lean_object* v_vs_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_ks_2710_ = lean_ctor_get(v_newNode_2707_, 0);
lean_inc_ref(v_ks_2710_);
v_vs_2711_ = lean_ctor_get(v_newNode_2707_, 1);
lean_inc_ref(v_vs_2711_);
lean_dec_ref(v_newNode_2707_);
v___x_2712_ = lean_unsigned_to_nat(0u);
v___x_2713_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2714_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2651_, v_ks_2710_, v_vs_2711_, v___x_2712_, v___x_2713_);
lean_dec_ref(v_vs_2711_);
lean_dec_ref(v_ks_2710_);
return v___x_2714_;
}
else
{
return v_newNode_2707_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_2722_, lean_object* v_keys_2723_, lean_object* v_vals_2724_, lean_object* v_i_2725_, lean_object* v_entries_2726_){
_start:
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = lean_array_get_size(v_keys_2723_);
v___x_2728_ = lean_nat_dec_lt(v_i_2725_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_dec(v_i_2725_);
return v_entries_2726_;
}
else
{
lean_object* v_k_2729_; lean_object* v_v_2730_; uint64_t v___x_2731_; size_t v_h_2732_; size_t v___x_2733_; lean_object* v___x_2734_; size_t v___x_2735_; size_t v___x_2736_; size_t v___x_2737_; size_t v_h_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_k_2729_ = lean_array_fget_borrowed(v_keys_2723_, v_i_2725_);
v_v_2730_ = lean_array_fget_borrowed(v_vals_2724_, v_i_2725_);
v___x_2731_ = l_Lean_instHashableMVarId_hash(v_k_2729_);
v_h_2732_ = lean_uint64_to_usize(v___x_2731_);
v___x_2733_ = ((size_t)5ULL);
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2735_ = ((size_t)1ULL);
v___x_2736_ = lean_usize_sub(v_depth_2722_, v___x_2735_);
v___x_2737_ = lean_usize_mul(v___x_2733_, v___x_2736_);
v_h_2738_ = lean_usize_shift_right(v_h_2732_, v___x_2737_);
v___x_2739_ = lean_nat_add(v_i_2725_, v___x_2734_);
lean_dec(v_i_2725_);
lean_inc(v_v_2730_);
lean_inc(v_k_2729_);
v___x_2740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_2726_, v_h_2738_, v_depth_2722_, v_k_2729_, v_v_2730_);
v_i_2725_ = v___x_2739_;
v_entries_2726_ = v___x_2740_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2742_, lean_object* v_keys_2743_, lean_object* v_vals_2744_, lean_object* v_i_2745_, lean_object* v_entries_2746_){
_start:
{
size_t v_depth_boxed_2747_; lean_object* v_res_2748_; 
v_depth_boxed_2747_ = lean_unbox_usize(v_depth_2742_);
lean_dec(v_depth_2742_);
v_res_2748_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_2747_, v_keys_2743_, v_vals_2744_, v_i_2745_, v_entries_2746_);
lean_dec_ref(v_vals_2744_);
lean_dec_ref(v_keys_2743_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
size_t v_x_4156__boxed_2754_; size_t v_x_4157__boxed_2755_; lean_object* v_res_2756_; 
v_x_4156__boxed_2754_ = lean_unbox_usize(v_x_2750_);
lean_dec(v_x_2750_);
v_x_4157__boxed_2755_ = lean_unbox_usize(v_x_2751_);
lean_dec(v_x_2751_);
v_res_2756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2749_, v_x_4156__boxed_2754_, v_x_4157__boxed_2755_, v_x_2752_, v_x_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_){
_start:
{
uint64_t v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; 
v___x_2760_ = l_Lean_instHashableMVarId_hash(v_x_2758_);
v___x_2761_ = lean_uint64_to_usize(v___x_2760_);
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2757_, v___x_2761_, v___x_2762_, v_x_2758_, v_x_2759_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object* v_mvarId_2764_, lean_object* v_val_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2768_; lean_object* v_mctx_2769_; lean_object* v_cache_2770_; lean_object* v_zetaDeltaFVarIds_2771_; lean_object* v_postponed_2772_; lean_object* v_diag_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2801_; 
v___x_2768_ = lean_st_ref_take(v___y_2766_);
v_mctx_2769_ = lean_ctor_get(v___x_2768_, 0);
v_cache_2770_ = lean_ctor_get(v___x_2768_, 1);
v_zetaDeltaFVarIds_2771_ = lean_ctor_get(v___x_2768_, 2);
v_postponed_2772_ = lean_ctor_get(v___x_2768_, 3);
v_diag_2773_ = lean_ctor_get(v___x_2768_, 4);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2775_ = v___x_2768_;
v_isShared_2776_ = v_isSharedCheck_2801_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_diag_2773_);
lean_inc(v_postponed_2772_);
lean_inc(v_zetaDeltaFVarIds_2771_);
lean_inc(v_cache_2770_);
lean_inc(v_mctx_2769_);
lean_dec(v___x_2768_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2801_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_depth_2777_; lean_object* v_levelAssignDepth_2778_; lean_object* v_lmvarCounter_2779_; lean_object* v_mvarCounter_2780_; lean_object* v_lDecls_2781_; lean_object* v_decls_2782_; lean_object* v_userNames_2783_; lean_object* v_lAssignment_2784_; lean_object* v_eAssignment_2785_; lean_object* v_dAssignment_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2800_; 
v_depth_2777_ = lean_ctor_get(v_mctx_2769_, 0);
v_levelAssignDepth_2778_ = lean_ctor_get(v_mctx_2769_, 1);
v_lmvarCounter_2779_ = lean_ctor_get(v_mctx_2769_, 2);
v_mvarCounter_2780_ = lean_ctor_get(v_mctx_2769_, 3);
v_lDecls_2781_ = lean_ctor_get(v_mctx_2769_, 4);
v_decls_2782_ = lean_ctor_get(v_mctx_2769_, 5);
v_userNames_2783_ = lean_ctor_get(v_mctx_2769_, 6);
v_lAssignment_2784_ = lean_ctor_get(v_mctx_2769_, 7);
v_eAssignment_2785_ = lean_ctor_get(v_mctx_2769_, 8);
v_dAssignment_2786_ = lean_ctor_get(v_mctx_2769_, 9);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_mctx_2769_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2788_ = v_mctx_2769_;
v_isShared_2789_ = v_isSharedCheck_2800_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_dAssignment_2786_);
lean_inc(v_eAssignment_2785_);
lean_inc(v_lAssignment_2784_);
lean_inc(v_userNames_2783_);
lean_inc(v_decls_2782_);
lean_inc(v_lDecls_2781_);
lean_inc(v_mvarCounter_2780_);
lean_inc(v_lmvarCounter_2779_);
lean_inc(v_levelAssignDepth_2778_);
lean_inc(v_depth_2777_);
lean_dec(v_mctx_2769_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2800_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2790_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2785_, v_mvarId_2764_, v_val_2765_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 8, v___x_2790_);
v___x_2792_ = v___x_2788_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_depth_2777_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_levelAssignDepth_2778_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_lmvarCounter_2779_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v_mvarCounter_2780_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v_lDecls_2781_);
lean_ctor_set(v_reuseFailAlloc_2799_, 5, v_decls_2782_);
lean_ctor_set(v_reuseFailAlloc_2799_, 6, v_userNames_2783_);
lean_ctor_set(v_reuseFailAlloc_2799_, 7, v_lAssignment_2784_);
lean_ctor_set(v_reuseFailAlloc_2799_, 8, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2799_, 9, v_dAssignment_2786_);
v___x_2792_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2792_);
v___x_2794_ = v___x_2775_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_cache_2770_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_zetaDeltaFVarIds_2771_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v_postponed_2772_);
lean_ctor_set(v_reuseFailAlloc_2798_, 4, v_diag_2773_);
v___x_2794_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2795_ = lean_st_ref_set(v___y_2766_, v___x_2794_);
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
return v___x_2797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2802_, lean_object* v_val_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2802_, v_val_2803_, v___y_2804_);
lean_dec(v___y_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2815_, lean_object* v_as_2816_, size_t v_sz_2817_, size_t v_i_2818_, lean_object* v_b_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_a_2826_; uint8_t v___x_2830_; 
v___x_2830_ = lean_usize_dec_lt(v_i_2818_, v_sz_2817_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_b_2819_);
return v___x_2831_;
}
else
{
lean_object* v_fst_2832_; lean_object* v_snd_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v_a_2836_; 
v_fst_2832_ = lean_ctor_get(v_b_2819_, 0);
lean_inc(v_fst_2832_);
v_snd_2833_ = lean_ctor_get(v_b_2819_, 1);
lean_inc(v_snd_2833_);
lean_dec_ref(v_b_2819_);
v___x_2834_ = lean_unsigned_to_nat(0u);
v___x_2835_ = lean_nat_dec_eq(v___x_2815_, v___x_2834_);
v_a_2836_ = lean_array_uget_borrowed(v_as_2816_, v_i_2818_);
if (lean_obj_tag(v_a_2836_) == 0)
{
lean_object* v_fvarId_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_fvarId_2837_ = lean_ctor_get(v_a_2836_, 0);
v___x_2838_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2833_, v_fvarId_2837_);
v___x_2839_ = l_Lean_Meta_substCore(v_fst_2832_, v___x_2838_, v___x_2830_, v_snd_2833_, v___x_2830_, v___x_2835_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v_fst_2841_; lean_object* v_snd_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v_fst_2841_ = lean_ctor_get(v_a_2840_, 0);
v_snd_2842_ = lean_ctor_get(v_a_2840_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_a_2840_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v_a_2840_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_snd_2842_);
lean_inc(v_fst_2841_);
lean_dec(v_a_2840_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v_fst_2841_);
lean_ctor_set(v___x_2844_, 0, v_snd_2842_);
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_snd_2842_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_fst_2841_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
v_a_2826_ = v___x_2847_;
goto v___jp_2825_;
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
v_a_2850_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2839_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2839_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_lhs_2858_; lean_object* v_rhs_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_lhs_2858_ = lean_ctor_get(v_a_2836_, 0);
v_rhs_2859_ = lean_ctor_get(v_a_2836_, 1);
v___x_2860_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2833_, v_lhs_2858_);
v___x_2861_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2833_, v_rhs_2859_);
v___x_2862_ = l_Lean_mkFVar(v___x_2860_);
v___x_2863_ = l_Lean_mkFVar(v___x_2861_);
lean_inc_ref(v___x_2863_);
lean_inc_ref(v___x_2862_);
v___x_2864_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2864_, 0, v___x_2862_);
lean_closure_set(v___x_2864_, 1, v___x_2863_);
lean_inc(v_fst_2832_);
v___x_2865_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2832_, v___x_2864_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2868_ = lean_unsigned_to_nat(2u);
v___x_2869_ = lean_mk_empty_array_with_capacity(v___x_2868_);
v___x_2870_ = lean_array_push(v___x_2869_, v___x_2862_);
v___x_2871_ = lean_array_push(v___x_2870_, v___x_2863_);
v___x_2872_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2872_, 0, v___x_2867_);
lean_closure_set(v___x_2872_, 1, v___x_2871_);
lean_inc(v_fst_2832_);
v___x_2873_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2832_, v___x_2872_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
v___x_2876_ = l_Lean_MVarId_assert(v_fst_2832_, v___x_2875_, v_a_2866_, v_a_2874_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2878_ = l_Lean_Meta_intro1Core(v_a_2877_, v___x_2835_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v_fst_2880_; lean_object* v_snd_2881_; lean_object* v___x_2882_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v_fst_2880_ = lean_ctor_get(v_a_2879_, 0);
lean_inc(v_fst_2880_);
v_snd_2881_ = lean_ctor_get(v_a_2879_, 1);
lean_inc(v_snd_2881_);
lean_dec(v_a_2879_);
v___x_2882_ = l_Lean_Meta_substCore(v_snd_2881_, v_fst_2880_, v___x_2830_, v_snd_2833_, v___x_2830_, v___x_2835_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v_fst_2884_ = lean_ctor_get(v_a_2883_, 0);
v_snd_2885_ = lean_ctor_get(v_a_2883_, 1);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_a_2883_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v_a_2883_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_snd_2885_);
lean_inc(v_fst_2884_);
lean_dec(v_a_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v_fst_2884_);
lean_ctor_set(v___x_2887_, 0, v_snd_2885_);
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_snd_2885_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_fst_2884_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
v_a_2826_ = v___x_2890_;
goto v___jp_2825_;
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2882_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2882_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v_snd_2833_);
v_a_2901_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2878_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2878_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec(v_snd_2833_);
v_a_2909_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2876_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2876_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_a_2866_);
lean_dec(v_snd_2833_);
lean_dec(v_fst_2832_);
v_a_2917_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2873_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2873_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2862_);
lean_dec(v_snd_2833_);
lean_dec(v_fst_2832_);
v_a_2925_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2865_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2865_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
v___jp_2825_:
{
size_t v___x_2827_; size_t v___x_2828_; 
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_add(v_i_2818_, v___x_2827_);
v_i_2818_ = v___x_2828_;
v_b_2819_ = v_a_2826_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_2933_, lean_object* v_as_2934_, lean_object* v_sz_2935_, lean_object* v_i_2936_, lean_object* v_b_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
size_t v_sz_boxed_2943_; size_t v_i_boxed_2944_; lean_object* v_res_2945_; 
v_sz_boxed_2943_ = lean_unbox_usize(v_sz_2935_);
lean_dec(v_sz_2935_);
v_i_boxed_2944_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_res_2945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2933_, v_as_2934_, v_sz_boxed_2943_, v_i_boxed_2944_, v_b_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v_as_2934_);
lean_dec(v___x_2933_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_2946_, lean_object* v_as_2947_, size_t v_i_2948_, size_t v_stop_2949_, lean_object* v_b_2950_){
_start:
{
lean_object* v___y_2952_; uint8_t v___x_2956_; 
v___x_2956_ = lean_usize_dec_eq(v_i_2948_, v_stop_2949_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = lean_box(0);
v___x_2958_ = lean_array_uget_borrowed(v_as_2947_, v_i_2948_);
v___x_2959_ = lean_array_get_borrowed(v___x_2957_, v_eqs_2946_, v___x_2958_);
if (lean_obj_tag(v___x_2959_) == 0)
{
v___y_2952_ = v_b_2950_;
goto v___jp_2951_;
}
else
{
lean_object* v_val_2960_; lean_object* v___x_2961_; 
v_val_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_val_2960_);
v___x_2961_ = lean_array_push(v_b_2950_, v_val_2960_);
v___y_2952_ = v___x_2961_;
goto v___jp_2951_;
}
}
else
{
return v_b_2950_;
}
v___jp_2951_:
{
size_t v___x_2953_; size_t v___x_2954_; 
v___x_2953_ = ((size_t)1ULL);
v___x_2954_ = lean_usize_add(v_i_2948_, v___x_2953_);
v_i_2948_ = v___x_2954_;
v_b_2950_ = v___y_2952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_2962_, lean_object* v_as_2963_, lean_object* v_i_2964_, lean_object* v_stop_2965_, lean_object* v_b_2966_){
_start:
{
size_t v_i_boxed_2967_; size_t v_stop_boxed_2968_; lean_object* v_res_2969_; 
v_i_boxed_2967_ = lean_unbox_usize(v_i_2964_);
lean_dec(v_i_2964_);
v_stop_boxed_2968_ = lean_unbox_usize(v_stop_2965_);
lean_dec(v_stop_2965_);
v_res_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2962_, v_as_2963_, v_i_boxed_2967_, v_stop_boxed_2968_, v_b_2966_);
lean_dec_ref(v_as_2963_);
lean_dec_ref(v_eqs_2962_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_2972_, lean_object* v_as_2973_, lean_object* v_start_2974_, lean_object* v_stop_2975_){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_2977_ = lean_nat_dec_lt(v_start_2974_, v_stop_2975_);
if (v___x_2977_ == 0)
{
return v___x_2976_;
}
else
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = lean_array_get_size(v_as_2973_);
v___x_2979_ = lean_nat_dec_le(v_stop_2975_, v___x_2978_);
if (v___x_2979_ == 0)
{
uint8_t v___x_2980_; 
v___x_2980_ = lean_nat_dec_lt(v_start_2974_, v___x_2978_);
if (v___x_2980_ == 0)
{
return v___x_2976_;
}
else
{
size_t v___x_2981_; size_t v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = lean_usize_of_nat(v_start_2974_);
v___x_2982_ = lean_usize_of_nat(v___x_2978_);
v___x_2983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2972_, v_as_2973_, v___x_2981_, v___x_2982_, v___x_2976_);
return v___x_2983_;
}
}
else
{
size_t v___x_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_usize_of_nat(v_start_2974_);
v___x_2985_ = lean_usize_of_nat(v_stop_2975_);
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2972_, v_as_2973_, v___x_2984_, v___x_2985_, v___x_2976_);
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_2987_, lean_object* v_as_2988_, lean_object* v_start_2989_, lean_object* v_stop_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2987_, v_as_2988_, v_start_2989_, v_stop_2990_);
lean_dec(v_stop_2990_);
lean_dec(v_start_2989_);
lean_dec_ref(v_as_2988_);
lean_dec_ref(v_eqs_2987_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_2992_, lean_object* v_type_2993_, lean_object* v_deps_2994_, lean_object* v_eqs_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v_eqs_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = lean_array_get_size(v_deps_2994_);
v_eqs_3003_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2995_, v_deps_2994_, v___x_3001_, v___x_3002_);
v___x_3004_ = lean_array_get_size(v_eqs_3003_);
v___x_3005_ = lean_nat_dec_eq(v___x_3004_, v___x_3001_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_type_2993_);
v___x_3007_ = 0;
v___x_3008_ = lean_box(0);
v___x_3009_ = l_Lean_Meta_mkFreshExprMVar(v___x_3006_, v___x_3007_, v___x_3008_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; size_t v_sz_3014_; size_t v___x_3015_; lean_object* v___x_3016_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = l_Lean_Expr_mvarId_x21(v_a_3010_);
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v_sz_3014_ = lean_array_size(v_eqs_3003_);
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_3004_, v_eqs_3003_, v_sz_3014_, v___x_3015_, v___x_3013_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
lean_dec_ref(v_eqs_3003_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v_fst_3018_; lean_object* v_snd_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v_fst_3018_ = lean_ctor_get(v_a_3017_, 0);
lean_inc(v_fst_3018_);
v_snd_3019_ = lean_ctor_get(v_a_3017_, 1);
lean_inc(v_snd_3019_);
lean_dec(v_a_3017_);
v___x_3020_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_3019_, v_fvarId_2992_);
lean_dec(v_fvarId_2992_);
lean_dec(v_snd_3019_);
v___x_3021_ = l_Lean_mkFVar(v___x_3020_);
v___x_3022_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_3018_, v___x_3021_, v_a_2997_);
lean_dec_ref(v___x_3022_);
v___x_3023_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_3010_, v_a_2997_);
return v___x_3023_;
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v_a_3010_);
lean_dec(v_fvarId_2992_);
v_a_3024_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3016_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3016_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
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
lean_dec_ref(v_eqs_3003_);
lean_dec(v_fvarId_2992_);
return v___x_3009_;
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec_ref(v_eqs_3003_);
lean_dec_ref(v_type_2993_);
v___x_3032_ = l_Lean_mkFVar(v_fvarId_2992_);
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3034_, lean_object* v_type_3035_, lean_object* v_deps_3036_, lean_object* v_eqs_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3034_, v_type_3035_, v_deps_3036_, v_eqs_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec_ref(v_eqs_3037_);
lean_dec_ref(v_deps_3036_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3044_, lean_object* v_val_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3044_, v_val_3045_, v___y_3047_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3052_, lean_object* v_val_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3052_, v_val_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3061_, v_x_3062_, v_x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3065_, lean_object* v_x_3066_, size_t v_x_3067_, size_t v_x_3068_, lean_object* v_x_3069_, lean_object* v_x_3070_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3066_, v_x_3067_, v_x_3068_, v_x_3069_, v_x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3072_, lean_object* v_x_3073_, lean_object* v_x_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v_x_3077_){
_start:
{
size_t v_x_4761__boxed_3078_; size_t v_x_4762__boxed_3079_; lean_object* v_res_3080_; 
v_x_4761__boxed_3078_ = lean_unbox_usize(v_x_3074_);
lean_dec(v_x_3074_);
v_x_4762__boxed_3079_ = lean_unbox_usize(v_x_3075_);
lean_dec(v_x_3075_);
v_res_3080_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3072_, v_x_3073_, v_x_4761__boxed_3078_, v_x_4762__boxed_3079_, v_x_3076_, v_x_3077_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3081_, lean_object* v_n_3082_, lean_object* v_k_3083_, lean_object* v_v_3084_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3082_, v_k_3083_, v_v_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3086_, size_t v_depth_3087_, lean_object* v_keys_3088_, lean_object* v_vals_3089_, lean_object* v_heq_3090_, lean_object* v_i_3091_, lean_object* v_entries_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3087_, v_keys_3088_, v_vals_3089_, v_i_3091_, v_entries_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3094_, lean_object* v_depth_3095_, lean_object* v_keys_3096_, lean_object* v_vals_3097_, lean_object* v_heq_3098_, lean_object* v_i_3099_, lean_object* v_entries_3100_){
_start:
{
size_t v_depth_boxed_3101_; lean_object* v_res_3102_; 
v_depth_boxed_3101_ = lean_unbox_usize(v_depth_3095_);
lean_dec(v_depth_3095_);
v_res_3102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3094_, v_depth_boxed_3101_, v_keys_3096_, v_vals_3097_, v_heq_3098_, v_i_3099_, v_entries_3100_);
lean_dec_ref(v_vals_3097_);
lean_dec_ref(v_keys_3096_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3103_, lean_object* v_x_3104_, lean_object* v_x_3105_, lean_object* v_x_3106_, lean_object* v_x_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3104_, v_x_3105_, v_x_3106_, v_x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___f_3116_; lean_object* v___x_1803__overap_3117_; lean_object* v___x_3118_; 
v___f_3116_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1803__overap_3117_ = lean_panic_fn_borrowed(v___f_3116_, v_msg_3110_);
lean_inc(v___y_3114_);
lean_inc_ref(v___y_3113_);
lean_inc(v___y_3112_);
lean_inc_ref(v___y_3111_);
v___x_3118_ = lean_apply_5(v___x_1803__overap_3117_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, lean_box(0));
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
return v_res_3125_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3129_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3130_ = lean_unsigned_to_nat(34u);
v___x_3131_ = lean_unsigned_to_nat(360u);
v___x_3132_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3133_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3134_ = l_mkPanicMessageWithDecl(v___x_3133_, v___x_3132_, v___x_3131_, v___x_3130_, v___x_3129_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3135_, lean_object* v___x_3136_, lean_object* v___x_3137_, lean_object* v_i_3138_, lean_object* v_kinds_3139_, lean_object* v___x_3140_, lean_object* v_lhs_3141_, lean_object* v_rhs_3142_, lean_object* v_type_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
uint8_t v___x_1990__boxed_3149_; uint8_t v___x_1991__boxed_3150_; lean_object* v_res_3151_; 
v___x_1990__boxed_3149_ = lean_unbox(v___x_3136_);
v___x_1991__boxed_3150_ = lean_unbox(v___x_3137_);
v_res_3151_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3135_, v___x_1990__boxed_3149_, v___x_1991__boxed_3150_, v_i_3138_, v_kinds_3139_, v___x_3140_, v_lhs_3141_, v_rhs_3142_, v_type_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3152_, uint8_t v___x_3153_, uint8_t v___x_3154_, lean_object* v_i_3155_, lean_object* v___x_3156_, lean_object* v_kinds_3157_, lean_object* v_typeSub_3158_, lean_object* v_lhs_3159_, lean_object* v_rhs_3160_, lean_object* v_type_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; uint8_t v___x_3168_; lean_object* v___x_3169_; 
lean_inc_ref(v_rhs_3160_);
v___x_3167_ = lean_array_push(v___x_3152_, v_rhs_3160_);
v___x_3168_ = 1;
v___x_3169_ = l_Lean_Meta_mkLambdaFVars(v___x_3167_, v_type_3161_, v___x_3153_, v___x_3154_, v___x_3153_, v___x_3154_, v___x_3168_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec_ref(v___x_3167_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___x_3169_, 1);
v___x_3171_ = lean_nat_add(v_i_3155_, v___x_3156_);
v___x_3172_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3157_, v___x_3171_, v_typeSub_3158_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
v___x_3174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3175_ = lean_unsigned_to_nat(2u);
v___x_3176_ = lean_mk_empty_array_with_capacity(v___x_3175_);
v___x_3177_ = lean_array_push(v___x_3176_, v_lhs_3159_);
v___x_3178_ = lean_array_push(v___x_3177_, v_rhs_3160_);
lean_inc_ref(v___x_3178_);
v___x_3179_ = l_Lean_Meta_mkAppM(v___x_3174_, v___x_3178_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3181_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3179_, 1);
v___x_3181_ = l_Lean_Meta_mkEqNDRec(v_a_3170_, v_a_3173_, v_a_3180_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = l_Lean_Meta_mkLambdaFVars(v___x_3178_, v_a_3182_, v___x_3153_, v___x_3154_, v___x_3153_, v___x_3154_, v___x_3168_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec_ref(v___x_3178_);
return v___x_3183_;
}
else
{
lean_dec_ref(v___x_3178_);
return v___x_3181_;
}
}
else
{
lean_dec_ref(v___x_3178_);
lean_dec(v_a_3173_);
lean_dec(v_a_3170_);
return v___x_3179_;
}
}
else
{
lean_dec(v_a_3170_);
lean_dec_ref(v_rhs_3160_);
lean_dec_ref(v_lhs_3159_);
return v___x_3172_;
}
}
else
{
lean_dec_ref(v_rhs_3160_);
lean_dec_ref(v_lhs_3159_);
lean_dec_ref(v_typeSub_3158_);
lean_dec_ref(v_kinds_3157_);
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3184_, lean_object* v___x_3185_, lean_object* v___x_3186_, lean_object* v_i_3187_, lean_object* v___x_3188_, lean_object* v_kinds_3189_, lean_object* v_typeSub_3190_, lean_object* v_lhs_3191_, lean_object* v_rhs_3192_, lean_object* v_type_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
uint8_t v___x_2053__boxed_3199_; uint8_t v___x_2054__boxed_3200_; lean_object* v_res_3201_; 
v___x_2053__boxed_3199_ = lean_unbox(v___x_3185_);
v___x_2054__boxed_3200_ = lean_unbox(v___x_3186_);
v_res_3201_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3184_, v___x_2053__boxed_3199_, v___x_2054__boxed_3200_, v_i_3187_, v___x_3188_, v_kinds_3189_, v_typeSub_3190_, v_lhs_3191_, v_rhs_3192_, v_type_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___x_3188_);
lean_dec(v_i_3187_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(lean_object* v_kinds_3202_, lean_object* v_i_3203_, uint8_t v___x_3204_, uint8_t v___x_3205_, lean_object* v_lhs_3206_, lean_object* v_type_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3216_ = 0;
v___x_3217_ = lean_box(v___x_3216_);
v___x_3218_ = lean_array_get(v___x_3217_, v_kinds_3202_, v_i_3203_);
lean_dec(v___x_3217_);
v___x_3219_ = lean_unbox(v___x_3218_);
lean_dec(v___x_3218_);
switch(v___x_3219_)
{
case 1:
{
lean_dec_ref(v_type_3207_);
lean_dec_ref(v_lhs_3206_);
lean_dec(v_i_3203_);
lean_dec_ref(v_kinds_3202_);
goto v___jp_3213_;
}
case 2:
{
lean_object* v___x_3220_; 
lean_inc_ref(v_lhs_3206_);
v___x_3220_ = l_Lean_Meta_mkEqRefl(v_lhs_3206_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___f_3231_; lean_object* v___x_3232_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3222_ = l_Lean_Expr_bindingBody_x21(v_type_3207_);
v___x_3223_ = l_Lean_Expr_bindingBody_x21(v___x_3222_);
lean_dec_ref(v___x_3222_);
v___x_3224_ = lean_unsigned_to_nat(2u);
v___x_3225_ = lean_mk_empty_array_with_capacity(v___x_3224_);
lean_inc_ref(v___x_3225_);
v___x_3226_ = lean_array_push(v___x_3225_, v_a_3221_);
lean_inc_ref(v_lhs_3206_);
v___x_3227_ = lean_array_push(v___x_3226_, v_lhs_3206_);
v___x_3228_ = lean_expr_instantiate(v___x_3223_, v___x_3227_);
lean_dec_ref(v___x_3227_);
lean_dec_ref(v___x_3223_);
v___x_3229_ = lean_box(v___x_3204_);
v___x_3230_ = lean_box(v___x_3205_);
v___f_3231_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3231_, 0, v___x_3225_);
lean_closure_set(v___f_3231_, 1, v___x_3229_);
lean_closure_set(v___f_3231_, 2, v___x_3230_);
lean_closure_set(v___f_3231_, 3, v_i_3203_);
lean_closure_set(v___f_3231_, 4, v_kinds_3202_);
lean_closure_set(v___f_3231_, 5, v___x_3228_);
lean_closure_set(v___f_3231_, 6, v_lhs_3206_);
v___x_3232_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3207_, v___f_3231_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3232_;
}
else
{
lean_dec_ref(v_type_3207_);
lean_dec_ref(v_lhs_3206_);
lean_dec(v_i_3203_);
lean_dec_ref(v_kinds_3202_);
return v___x_3220_;
}
}
case 4:
{
lean_dec_ref(v_type_3207_);
lean_dec_ref(v_lhs_3206_);
lean_dec(v_i_3203_);
lean_dec_ref(v_kinds_3202_);
goto v___jp_3213_;
}
case 5:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v_typeSub_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___f_3240_; lean_object* v___x_3241_; 
v___x_3233_ = l_Lean_Expr_bindingBody_x21(v_type_3207_);
v___x_3234_ = lean_unsigned_to_nat(1u);
v___x_3235_ = lean_mk_empty_array_with_capacity(v___x_3234_);
lean_inc_ref(v_lhs_3206_);
lean_inc_ref(v___x_3235_);
v___x_3236_ = lean_array_push(v___x_3235_, v_lhs_3206_);
v_typeSub_3237_ = lean_expr_instantiate(v___x_3233_, v___x_3236_);
lean_dec_ref(v___x_3236_);
lean_dec_ref(v___x_3233_);
v___x_3238_ = lean_box(v___x_3204_);
v___x_3239_ = lean_box(v___x_3205_);
v___f_3240_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3240_, 0, v___x_3235_);
lean_closure_set(v___f_3240_, 1, v___x_3238_);
lean_closure_set(v___f_3240_, 2, v___x_3239_);
lean_closure_set(v___f_3240_, 3, v_i_3203_);
lean_closure_set(v___f_3240_, 4, v___x_3234_);
lean_closure_set(v___f_3240_, 5, v_kinds_3202_);
lean_closure_set(v___f_3240_, 6, v_typeSub_3237_);
lean_closure_set(v___f_3240_, 7, v_lhs_3206_);
v___x_3241_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3207_, v___f_3240_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3241_;
}
default: 
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_unsigned_to_nat(1u);
v___x_3243_ = lean_nat_add(v_i_3203_, v___x_3242_);
lean_dec(v_i_3203_);
v___x_3244_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3202_, v___x_3243_, v_type_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; lean_object* v___x_3249_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 1);
v___x_3246_ = lean_mk_empty_array_with_capacity(v___x_3242_);
v___x_3247_ = lean_array_push(v___x_3246_, v_lhs_3206_);
v___x_3248_ = 1;
v___x_3249_ = l_Lean_Meta_mkLambdaFVars(v___x_3247_, v_a_3245_, v___x_3204_, v___x_3205_, v___x_3204_, v___x_3205_, v___x_3248_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec_ref(v___x_3247_);
return v___x_3249_;
}
else
{
lean_dec_ref(v_lhs_3206_);
return v___x_3244_;
}
}
}
v___jp_3213_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3215_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3214_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v_kinds_3250_, lean_object* v_i_3251_, lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v_lhs_3254_, lean_object* v_type_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v___x_2090__boxed_3261_; uint8_t v___x_2091__boxed_3262_; lean_object* v_res_3263_; 
v___x_2090__boxed_3261_ = lean_unbox(v___x_3252_);
v___x_2091__boxed_3262_ = lean_unbox(v___x_3253_);
v_res_3263_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v_kinds_3250_, v_i_3251_, v___x_2090__boxed_3261_, v___x_2091__boxed_3262_, v_lhs_3254_, v_type_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
return v_res_3263_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3264_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3265_ = lean_unsigned_to_nat(43u);
v___x_3266_ = lean_unsigned_to_nat(355u);
v___x_3267_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3268_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3269_ = l_mkPanicMessageWithDecl(v___x_3268_, v___x_3267_, v___x_3266_, v___x_3265_, v___x_3264_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3270_, lean_object* v_i_3271_, lean_object* v_type_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3278_ = lean_array_get_size(v_kinds_3270_);
v___x_3279_ = lean_nat_dec_eq(v_i_3271_, v___x_3278_);
if (v___x_3279_ == 0)
{
uint8_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; 
v___x_3280_ = 1;
v___x_3281_ = lean_box(v___x_3279_);
v___x_3282_ = lean_box(v___x_3280_);
v___f_3283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3283_, 0, v_kinds_3270_);
lean_closure_set(v___f_3283_, 1, v_i_3271_);
lean_closure_set(v___f_3283_, 2, v___x_3281_);
lean_closure_set(v___f_3283_, 3, v___x_3282_);
v___x_3284_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3272_, v___f_3283_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3284_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
lean_dec(v_i_3271_);
lean_dec_ref(v_kinds_3270_);
v___x_3285_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3286_ = lean_unsigned_to_nat(3u);
v___x_3287_ = l_Lean_Expr_isAppOfArity(v_type_3272_, v___x_3285_, v___x_3286_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_dec_ref(v_type_3272_);
v___x_3288_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3289_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3288_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3289_;
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = l_Lean_Expr_appFn_x21(v_type_3272_);
lean_dec_ref(v_type_3272_);
v___x_3291_ = l_Lean_Expr_appArg_x21(v___x_3290_);
lean_dec_ref(v___x_3290_);
v___x_3292_ = l_Lean_Meta_mkEqRefl(v___x_3291_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3292_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* v___x_3293_, lean_object* v_rhs_3294_, uint8_t v___x_3295_, uint8_t v___x_3296_, lean_object* v_i_3297_, lean_object* v_kinds_3298_, lean_object* v___x_3299_, lean_object* v_lhs_3300_, lean_object* v_heq_3301_, lean_object* v_type_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; 
lean_inc_ref(v_rhs_3294_);
v___x_3308_ = lean_array_push(v___x_3293_, v_rhs_3294_);
lean_inc_ref(v_heq_3301_);
v___x_3309_ = lean_array_push(v___x_3308_, v_heq_3301_);
v___x_3310_ = 1;
v___x_3311_ = l_Lean_Meta_mkLambdaFVars(v___x_3309_, v_type_3302_, v___x_3295_, v___x_3296_, v___x_3295_, v___x_3296_, v___x_3310_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec_ref(v___x_3309_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = lean_unsigned_to_nat(1u);
v___x_3314_ = lean_nat_add(v_i_3297_, v___x_3313_);
v___x_3315_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3298_, v___x_3314_, v___x_3299_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3317_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v___x_3315_, 1);
lean_inc_ref(v_heq_3301_);
v___x_3317_ = l_Lean_Meta_mkEqRec(v_a_3312_, v_a_3316_, v_heq_3301_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = lean_unsigned_to_nat(3u);
v___x_3320_ = lean_mk_empty_array_with_capacity(v___x_3319_);
v___x_3321_ = lean_array_push(v___x_3320_, v_lhs_3300_);
v___x_3322_ = lean_array_push(v___x_3321_, v_rhs_3294_);
v___x_3323_ = lean_array_push(v___x_3322_, v_heq_3301_);
v___x_3324_ = l_Lean_Meta_mkLambdaFVars(v___x_3323_, v_a_3318_, v___x_3295_, v___x_3296_, v___x_3295_, v___x_3296_, v___x_3310_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec_ref(v___x_3323_);
return v___x_3324_;
}
else
{
lean_dec_ref(v_heq_3301_);
lean_dec_ref(v_lhs_3300_);
lean_dec_ref(v_rhs_3294_);
return v___x_3317_;
}
}
else
{
lean_dec(v_a_3312_);
lean_dec_ref(v_heq_3301_);
lean_dec_ref(v_lhs_3300_);
lean_dec_ref(v_rhs_3294_);
return v___x_3315_;
}
}
else
{
lean_dec_ref(v_heq_3301_);
lean_dec_ref(v_lhs_3300_);
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_kinds_3298_);
lean_dec_ref(v_rhs_3294_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* v___x_3325_, lean_object* v_rhs_3326_, lean_object* v___x_3327_, lean_object* v___x_3328_, lean_object* v_i_3329_, lean_object* v_kinds_3330_, lean_object* v___x_3331_, lean_object* v_lhs_3332_, lean_object* v_heq_3333_, lean_object* v_type_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v___x_2001__boxed_3340_; uint8_t v___x_2002__boxed_3341_; lean_object* v_res_3342_; 
v___x_2001__boxed_3340_ = lean_unbox(v___x_3327_);
v___x_2002__boxed_3341_ = lean_unbox(v___x_3328_);
v_res_3342_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3325_, v_rhs_3326_, v___x_2001__boxed_3340_, v___x_2002__boxed_3341_, v_i_3329_, v_kinds_3330_, v___x_3331_, v_lhs_3332_, v_heq_3333_, v_type_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v_i_3329_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* v___x_3343_, uint8_t v___x_3344_, uint8_t v___x_3345_, lean_object* v_i_3346_, lean_object* v_kinds_3347_, lean_object* v___x_3348_, lean_object* v_lhs_3349_, lean_object* v_rhs_3350_, lean_object* v_type_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___f_3359_; lean_object* v___x_3360_; 
v___x_3357_ = lean_box(v___x_3344_);
v___x_3358_ = lean_box(v___x_3345_);
v___f_3359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3359_, 0, v___x_3343_);
lean_closure_set(v___f_3359_, 1, v_rhs_3350_);
lean_closure_set(v___f_3359_, 2, v___x_3357_);
lean_closure_set(v___f_3359_, 3, v___x_3358_);
lean_closure_set(v___f_3359_, 4, v_i_3346_);
lean_closure_set(v___f_3359_, 5, v_kinds_3347_);
lean_closure_set(v___f_3359_, 6, v___x_3348_);
lean_closure_set(v___f_3359_, 7, v_lhs_3349_);
v___x_3360_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3351_, v___f_3359_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object* v_kinds_3361_, lean_object* v_i_3362_, lean_object* v_type_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3361_, v_i_3362_, v_type_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* v_type_3370_, lean_object* v_kinds_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3371_, v___x_3377_, v_type_3370_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object* v_type_3379_, lean_object* v_kinds_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3379_, v_kinds_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_msg_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___f_3393_; lean_object* v___x_2082__overap_3394_; lean_object* v___x_3395_; 
v___f_3393_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_2082__overap_3394_ = lean_panic_fn_borrowed(v___f_3393_, v_msg_3387_);
lean_inc(v___y_3391_);
lean_inc_ref(v___y_3390_);
lean_inc(v___y_3389_);
lean_inc_ref(v___y_3388_);
v___x_3395_ = lean_apply_5(v___x_2082__overap_3394_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, lean_box(0));
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_msg_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_msg_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(lean_object* v_bs_3403_, lean_object* v_k_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3403_, v_k_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
v_a_3419_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3410_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3410_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg___boxed(lean_object* v_bs_3427_, lean_object* v_k_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3427_, v_k_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec_ref(v_bs_3427_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(lean_object* v_00_u03b1_3435_, lean_object* v_bs_3436_, lean_object* v_k_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v_bs_3436_, v_k_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3444_, lean_object* v_bs_3445_, lean_object* v_k_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1(v_00_u03b1_3444_, v_bs_3445_, v_k_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec_ref(v_bs_3445_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(size_t v_sz_3453_, size_t v_i_3454_, lean_object* v_bs_3455_){
_start:
{
uint8_t v___x_3456_; 
v___x_3456_ = lean_usize_dec_lt(v_i_3454_, v_sz_3453_);
if (v___x_3456_ == 0)
{
return v_bs_3455_;
}
else
{
lean_object* v_v_3457_; lean_object* v___x_3458_; lean_object* v_bs_x27_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; size_t v___x_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v_v_3457_ = lean_array_uget(v_bs_3455_, v_i_3454_);
v___x_3458_ = lean_unsigned_to_nat(0u);
v_bs_x27_3459_ = lean_array_uset(v_bs_3455_, v_i_3454_, v___x_3458_);
v___x_3460_ = l_Lean_Expr_fvarId_x21(v_v_3457_);
lean_dec(v_v_3457_);
v___x_3461_ = 1;
v___x_3462_ = lean_box(v___x_3461_);
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3460_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = ((size_t)1ULL);
v___x_3465_ = lean_usize_add(v_i_3454_, v___x_3464_);
v___x_3466_ = lean_array_uset(v_bs_x27_3459_, v_i_3454_, v___x_3463_);
v_i_3454_ = v___x_3465_;
v_bs_3455_ = v___x_3466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0___boxed(lean_object* v_sz_3468_, lean_object* v_i_3469_, lean_object* v_bs_3470_){
_start:
{
size_t v_sz_boxed_3471_; size_t v_i_boxed_3472_; lean_object* v_res_3473_; 
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3468_);
lean_dec(v_sz_3468_);
v_i_boxed_3472_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_boxed_3471_, v_i_boxed_3472_, v_bs_3470_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(lean_object* v_bs_3474_, lean_object* v_k_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
size_t v_sz_3481_; size_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v_sz_3481_ = lean_array_size(v_bs_3474_);
v___x_3482_ = ((size_t)0ULL);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__0(v_sz_3481_, v___x_3482_, v_bs_3474_);
v___x_3484_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_spec__1___redArg(v___x_3483_, v_k_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec_ref(v___x_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg___boxed(lean_object* v_bs_3485_, lean_object* v_k_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3485_, v_k_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_00_u03b1_3493_, lean_object* v_bs_3494_, lean_object* v_k_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v_bs_3494_, v_k_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3502_, lean_object* v_bs_3503_, lean_object* v_k_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_00_u03b1_3502_, v_bs_3503_, v_k_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3511_, lean_object* v_rhss_3512_, lean_object* v_lhs_3513_, lean_object* v_eqs_3514_, lean_object* v_hyps_3515_, uint8_t v_subsingletonInstImplicitRhs_3516_, lean_object* v_f_3517_, lean_object* v_info_3518_, lean_object* v_kinds_3519_, lean_object* v_lhss_3520_, lean_object* v_b_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3527_ = lean_unsigned_to_nat(1u);
v___x_3528_ = lean_nat_add(v_i_3511_, v___x_3527_);
lean_inc_ref(v_b_3521_);
v___x_3529_ = lean_array_push(v_rhss_3512_, v_b_3521_);
v___x_3530_ = l_Lean_Expr_fvarId_x21(v_lhs_3513_);
v___x_3531_ = l_Lean_Expr_fvarId_x21(v_b_3521_);
v___x_3532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
v___x_3534_ = lean_array_push(v_eqs_3514_, v___x_3533_);
v___x_3535_ = lean_array_push(v_hyps_3515_, v_b_3521_);
v___x_3536_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3516_, v_f_3517_, v_info_3518_, v_kinds_3519_, v_lhss_3520_, v___x_3528_, v___x_3529_, v___x_3534_, v___x_3535_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3537_, lean_object* v_rhss_3538_, lean_object* v_lhs_3539_, lean_object* v_eqs_3540_, lean_object* v_hyps_3541_, lean_object* v_subsingletonInstImplicitRhs_3542_, lean_object* v_f_3543_, lean_object* v_info_3544_, lean_object* v_kinds_3545_, lean_object* v_lhss_3546_, lean_object* v_b_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3553_; lean_object* v_res_3554_; 
v_subsingletonInstImplicitRhs_boxed_3553_ = lean_unbox(v_subsingletonInstImplicitRhs_3542_);
v_res_3554_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3537_, v_rhss_3538_, v_lhs_3539_, v_eqs_3540_, v_hyps_3541_, v_subsingletonInstImplicitRhs_boxed_3553_, v_f_3543_, v_info_3544_, v_kinds_3545_, v_lhss_3546_, v_b_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec_ref(v_lhs_3539_);
lean_dec(v_i_3537_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3555_, lean_object* v_rhss_3556_, lean_object* v_lhs_3557_, lean_object* v_eqs_3558_, lean_object* v_hyps_3559_, uint8_t v_subsingletonInstImplicitRhs_3560_, lean_object* v_f_3561_, lean_object* v_info_3562_, lean_object* v_kinds_3563_, lean_object* v_lhss_3564_, lean_object* v_name_3565_, uint8_t v_bi_3566_, lean_object* v_type_3567_, uint8_t v_kind_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v___x_3574_; lean_object* v___f_3575_; lean_object* v___x_3576_; 
v___x_3574_ = lean_box(v_subsingletonInstImplicitRhs_3560_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3575_, 0, v_i_3555_);
lean_closure_set(v___f_3575_, 1, v_rhss_3556_);
lean_closure_set(v___f_3575_, 2, v_lhs_3557_);
lean_closure_set(v___f_3575_, 3, v_eqs_3558_);
lean_closure_set(v___f_3575_, 4, v_hyps_3559_);
lean_closure_set(v___f_3575_, 5, v___x_3574_);
lean_closure_set(v___f_3575_, 6, v_f_3561_);
lean_closure_set(v___f_3575_, 7, v_info_3562_);
lean_closure_set(v___f_3575_, 8, v_kinds_3563_);
lean_closure_set(v___f_3575_, 9, v_lhss_3564_);
v___x_3576_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3565_, v_bi_3566_, v_type_3567_, v___f_3575_, v_kind_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
v_a_3585_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3576_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3576_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3593_, lean_object* v_rhss_3594_, lean_object* v_lhss_3595_, lean_object* v_i_3596_, lean_object* v_eqs_3597_, lean_object* v_hyps_3598_, uint8_t v_subsingletonInstImplicitRhs_3599_, lean_object* v_f_3600_, lean_object* v_info_3601_, lean_object* v_kinds_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v___x_3608_; 
lean_inc(v___y_3606_);
lean_inc_ref(v___y_3605_);
lean_inc(v___y_3604_);
lean_inc_ref(v___y_3603_);
lean_inc_ref(v_lhs_3593_);
v___x_3608_ = lean_infer_type(v_lhs_3593_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___y_3616_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3610_ = lean_array_get_size(v_rhss_3594_);
v___x_3611_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3595_);
v___x_3612_ = l_Array_toSubarray___redArg(v_lhss_3595_, v___x_3611_, v___x_3610_);
v___x_3613_ = l_Subarray_copy___redArg(v___x_3612_);
v___x_3614_ = l_Lean_Expr_replaceFVars(v_a_3609_, v___x_3613_, v_rhss_3594_);
lean_dec_ref(v___x_3613_);
lean_dec(v_a_3609_);
if (v_subsingletonInstImplicitRhs_3599_ == 0)
{
uint8_t v___x_3631_; 
v___x_3631_ = 1;
v___y_3616_ = v___x_3631_;
goto v___jp_3615_;
}
else
{
uint8_t v___x_3632_; 
v___x_3632_ = 3;
v___y_3616_ = v___x_3632_;
goto v___jp_3615_;
}
v___jp_3615_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = l_Lean_Expr_fvarId_x21(v_lhs_3593_);
v___x_3618_ = l_Lean_FVarId_getDecl___redArg(v___x_3617_, v___y_3603_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3620_ = l_Lean_LocalDecl_userName(v_a_3619_);
lean_dec(v_a_3619_);
v___x_3621_ = 0;
v___x_3622_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3596_, v_rhss_3594_, v_lhs_3593_, v_eqs_3597_, v_hyps_3598_, v_subsingletonInstImplicitRhs_3599_, v_f_3600_, v_info_3601_, v_kinds_3602_, v_lhss_3595_, v___x_3620_, v___y_3616_, v___x_3614_, v___x_3621_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
return v___x_3622_;
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref(v___x_3614_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v_kinds_3602_);
lean_dec_ref(v_info_3601_);
lean_dec_ref(v_f_3600_);
lean_dec_ref(v_hyps_3598_);
lean_dec_ref(v_eqs_3597_);
lean_dec(v_i_3596_);
lean_dec_ref(v_lhss_3595_);
lean_dec_ref(v_rhss_3594_);
lean_dec_ref(v_lhs_3593_);
v_a_3623_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3618_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3618_);
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
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v_kinds_3602_);
lean_dec_ref(v_info_3601_);
lean_dec_ref(v_f_3600_);
lean_dec_ref(v_hyps_3598_);
lean_dec_ref(v_eqs_3597_);
lean_dec(v_i_3596_);
lean_dec_ref(v_lhss_3595_);
lean_dec_ref(v_rhss_3594_);
lean_dec_ref(v_lhs_3593_);
v_a_3633_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3608_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3608_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3641_, lean_object* v_rhss_3642_, lean_object* v_lhss_3643_, lean_object* v_i_3644_, lean_object* v_eqs_3645_, lean_object* v_hyps_3646_, lean_object* v_subsingletonInstImplicitRhs_3647_, lean_object* v_f_3648_, lean_object* v_info_3649_, lean_object* v_kinds_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3656_; lean_object* v_res_3657_; 
v_subsingletonInstImplicitRhs_boxed_3656_ = lean_unbox(v_subsingletonInstImplicitRhs_3647_);
v_res_3657_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3641_, v_rhss_3642_, v_lhss_3643_, v_i_3644_, v_eqs_3645_, v_hyps_3646_, v_subsingletonInstImplicitRhs_boxed_3656_, v_f_3648_, v_info_3649_, v_kinds_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
return v_res_3657_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3659_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3660_ = lean_unsigned_to_nat(38u);
v___x_3661_ = lean_unsigned_to_nat(328u);
v___x_3662_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3663_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3664_ = l_mkPanicMessageWithDecl(v___x_3663_, v___x_3662_, v___x_3661_, v___x_3660_, v___x_3659_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3665_, lean_object* v_f_3666_, lean_object* v_info_3667_, lean_object* v_kinds_3668_, lean_object* v_lhss_3669_, lean_object* v_i_3670_, lean_object* v_rhss_3671_, lean_object* v_eqs_3672_, lean_object* v_hyps_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3679_ = lean_array_get_size(v_kinds_3668_);
v___x_3680_ = lean_nat_dec_eq(v_i_3670_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v_lhs_3682_; lean_object* v_hyps_3683_; uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v___x_3681_ = l_Lean_instInhabitedExpr;
v_lhs_3682_ = lean_array_get_borrowed(v___x_3681_, v_lhss_3669_, v_i_3670_);
lean_inc(v_lhs_3682_);
v_hyps_3683_ = lean_array_push(v_hyps_3673_, v_lhs_3682_);
v___x_3684_ = 0;
v___x_3685_ = lean_box(v___x_3684_);
v___x_3686_ = lean_array_get(v___x_3685_, v_kinds_3668_, v_i_3670_);
lean_dec(v___x_3685_);
v___x_3687_ = lean_unbox(v___x_3686_);
lean_dec(v___x_3686_);
switch(v___x_3687_)
{
case 0:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3688_ = lean_unsigned_to_nat(1u);
v___x_3689_ = lean_nat_add(v_i_3670_, v___x_3688_);
lean_dec(v_i_3670_);
lean_inc(v_lhs_3682_);
v___x_3690_ = lean_array_push(v_rhss_3671_, v_lhs_3682_);
v___x_3691_ = lean_box(0);
v___x_3692_ = lean_array_push(v_eqs_3672_, v___x_3691_);
v_i_3670_ = v___x_3689_;
v_rhss_3671_ = v___x_3690_;
v_eqs_3672_ = v___x_3692_;
v_hyps_3673_ = v_hyps_3683_;
goto _start;
}
case 2:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
lean_inc(v_lhs_3682_);
v___x_3694_ = l_Lean_Expr_fvarId_x21(v_lhs_3682_);
v___x_3695_ = l_Lean_FVarId_getDecl___redArg(v___x_3694_, v_a_3674_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; lean_object* v___x_3701_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3697_ = l_Lean_LocalDecl_userName(v_a_3696_);
v___x_3698_ = l_Lean_LocalDecl_binderInfo(v_a_3696_);
v___x_3699_ = l_Lean_LocalDecl_type(v_a_3696_);
lean_dec(v_a_3696_);
v___x_3700_ = 0;
lean_inc(v___x_3697_);
v___x_3701_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3670_, v_rhss_3671_, v_eqs_3672_, v_hyps_3683_, v_subsingletonInstImplicitRhs_3665_, v_f_3666_, v_info_3667_, v_kinds_3668_, v_lhss_3669_, v_lhs_3682_, v___x_3697_, v___x_3697_, v___x_3698_, v___x_3699_, v___x_3700_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3701_;
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
lean_dec_ref(v_hyps_3683_);
lean_dec(v_lhs_3682_);
lean_dec_ref(v_eqs_3672_);
lean_dec_ref(v_rhss_3671_);
lean_dec(v_i_3670_);
lean_dec_ref(v_lhss_3669_);
lean_dec_ref(v_kinds_3668_);
lean_dec_ref(v_info_3667_);
lean_dec_ref(v_f_3666_);
v_a_3702_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3695_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3695_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
case 3:
{
lean_object* v___x_3710_; 
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
lean_inc(v_a_3675_);
lean_inc_ref(v_a_3674_);
lean_inc(v_lhs_3682_);
v___x_3710_ = lean_infer_type(v_lhs_3682_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v_paramInfo_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v_backDeps_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v_paramInfo_3712_ = lean_ctor_get(v_info_3667_, 0);
v___x_3713_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_3714_ = lean_array_get_borrowed(v___x_3713_, v_paramInfo_3712_, v_i_3670_);
v_backDeps_3715_ = lean_ctor_get(v___x_3714_, 0);
v___x_3716_ = lean_array_get_size(v_rhss_3671_);
v___x_3717_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3669_);
v___x_3718_ = l_Array_toSubarray___redArg(v_lhss_3669_, v___x_3717_, v___x_3716_);
v___x_3719_ = l_Subarray_copy___redArg(v___x_3718_);
v___x_3720_ = l_Lean_Expr_replaceFVars(v_a_3711_, v___x_3719_, v_rhss_3671_);
lean_dec_ref(v___x_3719_);
lean_dec(v_a_3711_);
v___x_3721_ = l_Lean_Expr_fvarId_x21(v_lhs_3682_);
v___x_3722_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3721_, v___x_3720_, v_backDeps_3715_, v_eqs_3672_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v___x_3724_ = lean_unsigned_to_nat(1u);
v___x_3725_ = lean_nat_add(v_i_3670_, v___x_3724_);
lean_dec(v_i_3670_);
v___x_3726_ = lean_array_push(v_rhss_3671_, v_a_3723_);
v___x_3727_ = lean_box(0);
v___x_3728_ = lean_array_push(v_eqs_3672_, v___x_3727_);
v_i_3670_ = v___x_3725_;
v_rhss_3671_ = v___x_3726_;
v_eqs_3672_ = v___x_3728_;
v_hyps_3673_ = v_hyps_3683_;
goto _start;
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v_hyps_3683_);
lean_dec_ref(v_eqs_3672_);
lean_dec_ref(v_rhss_3671_);
lean_dec(v_i_3670_);
lean_dec_ref(v_lhss_3669_);
lean_dec_ref(v_kinds_3668_);
lean_dec_ref(v_info_3667_);
lean_dec_ref(v_f_3666_);
v_a_3730_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3722_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3722_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec_ref(v_hyps_3683_);
lean_dec_ref(v_eqs_3672_);
lean_dec_ref(v_rhss_3671_);
lean_dec(v_i_3670_);
lean_dec_ref(v_lhss_3669_);
lean_dec_ref(v_kinds_3668_);
lean_dec_ref(v_info_3667_);
lean_dec_ref(v_f_3666_);
v_a_3738_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3710_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3710_);
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
case 5:
{
lean_object* v___x_3746_; lean_object* v___f_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_inc_n(v_lhs_3682_, 2);
v___x_3746_ = lean_box(v_subsingletonInstImplicitRhs_3665_);
v___f_3747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3747_, 0, v_lhs_3682_);
lean_closure_set(v___f_3747_, 1, v_rhss_3671_);
lean_closure_set(v___f_3747_, 2, v_lhss_3669_);
lean_closure_set(v___f_3747_, 3, v_i_3670_);
lean_closure_set(v___f_3747_, 4, v_eqs_3672_);
lean_closure_set(v___f_3747_, 5, v_hyps_3683_);
lean_closure_set(v___f_3747_, 6, v___x_3746_);
lean_closure_set(v___f_3747_, 7, v_f_3666_);
lean_closure_set(v___f_3747_, 8, v_info_3667_);
lean_closure_set(v___f_3747_, 9, v_kinds_3668_);
v___x_3748_ = lean_unsigned_to_nat(1u);
v___x_3749_ = lean_mk_empty_array_with_capacity(v___x_3748_);
v___x_3750_ = lean_array_push(v___x_3749_, v_lhs_3682_);
v___x_3751_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___redArg(v___x_3750_, v___f_3747_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3751_;
}
default: 
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_dec_ref(v_hyps_3683_);
lean_dec_ref(v_eqs_3672_);
lean_dec_ref(v_rhss_3671_);
lean_dec(v_i_3670_);
lean_dec_ref(v_lhss_3669_);
lean_dec_ref(v_kinds_3668_);
lean_dec_ref(v_info_3667_);
lean_dec_ref(v_f_3666_);
v___x_3752_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3753_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v___x_3752_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3753_;
}
}
}
else
{
lean_object* v_lhs_3754_; lean_object* v_rhs_3755_; lean_object* v___x_3756_; 
lean_dec_ref(v_eqs_3672_);
lean_dec(v_i_3670_);
lean_dec_ref(v_info_3667_);
lean_inc_ref(v_f_3666_);
v_lhs_3754_ = l_Lean_mkAppN(v_f_3666_, v_lhss_3669_);
lean_dec_ref(v_lhss_3669_);
v_rhs_3755_ = l_Lean_mkAppN(v_f_3666_, v_rhss_3671_);
lean_dec_ref(v_rhss_3671_);
v___x_3756_ = l_Lean_Meta_mkEq(v_lhs_3754_, v_rhs_3755_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; uint8_t v___x_3758_; uint8_t v___x_3759_; lean_object* v___x_3760_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3756_, 1);
v___x_3758_ = 0;
v___x_3759_ = 1;
v___x_3760_ = l_Lean_Meta_mkForallFVars(v_hyps_3673_, v_a_3757_, v___x_3758_, v___x_3680_, v___x_3680_, v___x_3759_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
lean_dec_ref(v_hyps_3673_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3762_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc_n(v_a_3761_, 2);
lean_dec_ref_known(v___x_3760_, 1);
lean_inc_ref(v_kinds_3668_);
v___x_3762_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3761_, v_kinds_3668_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3771_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3765_ = v___x_3762_;
v_isShared_3766_ = v_isSharedCheck_3771_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3762_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3771_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3767_, 0, v_a_3761_);
lean_ctor_set(v___x_3767_, 1, v_a_3763_);
lean_ctor_set(v___x_3767_, 2, v_kinds_3668_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3767_);
v___x_3769_ = v___x_3765_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v_a_3761_);
lean_dec_ref(v_kinds_3668_);
v_a_3772_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3762_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3762_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec_ref(v_kinds_3668_);
v_a_3780_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3760_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3760_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v_hyps_3673_);
lean_dec_ref(v_kinds_3668_);
v_a_3788_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3756_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3756_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3796_, lean_object* v_rhss_3797_, lean_object* v_b_3798_, lean_object* v_eqs_3799_, lean_object* v_hyps_3800_, uint8_t v_subsingletonInstImplicitRhs_3801_, lean_object* v_f_3802_, lean_object* v_info_3803_, lean_object* v_kinds_3804_, lean_object* v_lhss_3805_, lean_object* v_eq_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3812_ = lean_unsigned_to_nat(1u);
v___x_3813_ = lean_nat_add(v_i_3796_, v___x_3812_);
lean_inc_ref(v_b_3798_);
v___x_3814_ = lean_array_push(v_rhss_3797_, v_b_3798_);
v___x_3815_ = l_Lean_Expr_fvarId_x21(v_eq_3806_);
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
v___x_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
v___x_3818_ = lean_array_push(v_eqs_3799_, v___x_3817_);
v___x_3819_ = lean_array_push(v_hyps_3800_, v_b_3798_);
v___x_3820_ = lean_array_push(v___x_3819_, v_eq_3806_);
v___x_3821_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3801_, v_f_3802_, v_info_3803_, v_kinds_3804_, v_lhss_3805_, v___x_3813_, v___x_3814_, v___x_3818_, v___x_3820_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_3822_, lean_object* v_rhss_3823_, lean_object* v_b_3824_, lean_object* v_eqs_3825_, lean_object* v_hyps_3826_, lean_object* v_subsingletonInstImplicitRhs_3827_, lean_object* v_f_3828_, lean_object* v_info_3829_, lean_object* v_kinds_3830_, lean_object* v_lhss_3831_, lean_object* v_eq_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3838_; lean_object* v_res_3839_; 
v_subsingletonInstImplicitRhs_boxed_3838_ = lean_unbox(v_subsingletonInstImplicitRhs_3827_);
v_res_3839_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3822_, v_rhss_3823_, v_b_3824_, v_eqs_3825_, v_hyps_3826_, v_subsingletonInstImplicitRhs_boxed_3838_, v_f_3828_, v_info_3829_, v_kinds_3830_, v_lhss_3831_, v_eq_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v_i_3822_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(lean_object* v_lhs_3841_, lean_object* v_i_3842_, lean_object* v_rhss_3843_, lean_object* v_eqs_3844_, lean_object* v_hyps_3845_, uint8_t v_subsingletonInstImplicitRhs_3846_, lean_object* v_f_3847_, lean_object* v_info_3848_, lean_object* v_kinds_3849_, lean_object* v_lhss_3850_, lean_object* v___x_3851_, lean_object* v_b_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
lean_inc_ref(v_b_3852_);
v___x_3858_ = l_Lean_Meta_mkEq(v_lhs_3841_, v_b_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3860_; lean_object* v___f_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
v___x_3860_ = lean_box(v_subsingletonInstImplicitRhs_3846_);
v___f_3861_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3861_, 0, v_i_3842_);
lean_closure_set(v___f_3861_, 1, v_rhss_3843_);
lean_closure_set(v___f_3861_, 2, v_b_3852_);
lean_closure_set(v___f_3861_, 3, v_eqs_3844_);
lean_closure_set(v___f_3861_, 4, v_hyps_3845_);
lean_closure_set(v___f_3861_, 5, v___x_3860_);
lean_closure_set(v___f_3861_, 6, v_f_3847_);
lean_closure_set(v___f_3861_, 7, v_info_3848_);
lean_closure_set(v___f_3861_, 8, v_kinds_3849_);
lean_closure_set(v___f_3861_, 9, v_lhss_3850_);
v___x_3862_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___closed__0));
v___x_3863_ = lean_name_append_before(v___x_3851_, v___x_3862_);
v___x_3864_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3863_, v_a_3859_, v___f_3861_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
return v___x_3864_;
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v_b_3852_);
lean_dec(v___x_3851_);
lean_dec_ref(v_lhss_3850_);
lean_dec_ref(v_kinds_3849_);
lean_dec_ref(v_info_3848_);
lean_dec_ref(v_f_3847_);
lean_dec_ref(v_hyps_3845_);
lean_dec_ref(v_eqs_3844_);
lean_dec_ref(v_rhss_3843_);
lean_dec(v_i_3842_);
v_a_3865_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3858_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3858_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed(lean_object** _args){
lean_object* v_lhs_3873_ = _args[0];
lean_object* v_i_3874_ = _args[1];
lean_object* v_rhss_3875_ = _args[2];
lean_object* v_eqs_3876_ = _args[3];
lean_object* v_hyps_3877_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3878_ = _args[5];
lean_object* v_f_3879_ = _args[6];
lean_object* v_info_3880_ = _args[7];
lean_object* v_kinds_3881_ = _args[8];
lean_object* v_lhss_3882_ = _args[9];
lean_object* v___x_3883_ = _args[10];
lean_object* v_b_3884_ = _args[11];
lean_object* v___y_3885_ = _args[12];
lean_object* v___y_3886_ = _args[13];
lean_object* v___y_3887_ = _args[14];
lean_object* v___y_3888_ = _args[15];
lean_object* v___y_3889_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3890_; lean_object* v_res_3891_; 
v_subsingletonInstImplicitRhs_boxed_3890_ = lean_unbox(v_subsingletonInstImplicitRhs_3878_);
v_res_3891_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1(v_lhs_3873_, v_i_3874_, v_rhss_3875_, v_eqs_3876_, v_hyps_3877_, v_subsingletonInstImplicitRhs_boxed_3890_, v_f_3879_, v_info_3880_, v_kinds_3881_, v_lhss_3882_, v___x_3883_, v_b_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_3892_, lean_object* v_rhss_3893_, lean_object* v_eqs_3894_, lean_object* v_hyps_3895_, uint8_t v_subsingletonInstImplicitRhs_3896_, lean_object* v_f_3897_, lean_object* v_info_3898_, lean_object* v_kinds_3899_, lean_object* v_lhss_3900_, lean_object* v_lhs_3901_, lean_object* v___x_3902_, lean_object* v_name_3903_, uint8_t v_bi_3904_, lean_object* v_type_3905_, uint8_t v_kind_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v___x_3912_; lean_object* v___f_3913_; lean_object* v___x_3914_; 
v___x_3912_ = lean_box(v_subsingletonInstImplicitRhs_3896_);
v___f_3913_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3913_, 0, v_lhs_3901_);
lean_closure_set(v___f_3913_, 1, v_i_3892_);
lean_closure_set(v___f_3913_, 2, v_rhss_3893_);
lean_closure_set(v___f_3913_, 3, v_eqs_3894_);
lean_closure_set(v___f_3913_, 4, v_hyps_3895_);
lean_closure_set(v___f_3913_, 5, v___x_3912_);
lean_closure_set(v___f_3913_, 6, v_f_3897_);
lean_closure_set(v___f_3913_, 7, v_info_3898_);
lean_closure_set(v___f_3913_, 8, v_kinds_3899_);
lean_closure_set(v___f_3913_, 9, v_lhss_3900_);
lean_closure_set(v___f_3913_, 10, v___x_3902_);
v___x_3914_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3903_, v_bi_3904_, v_type_3905_, v___f_3913_, v_kind_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3914_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3914_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v_a_3923_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3914_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3914_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object** _args){
lean_object* v_i_3931_ = _args[0];
lean_object* v_rhss_3932_ = _args[1];
lean_object* v_eqs_3933_ = _args[2];
lean_object* v_hyps_3934_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3935_ = _args[4];
lean_object* v_f_3936_ = _args[5];
lean_object* v_info_3937_ = _args[6];
lean_object* v_kinds_3938_ = _args[7];
lean_object* v_lhss_3939_ = _args[8];
lean_object* v_lhs_3940_ = _args[9];
lean_object* v___x_3941_ = _args[10];
lean_object* v_name_3942_ = _args[11];
lean_object* v_bi_3943_ = _args[12];
lean_object* v_type_3944_ = _args[13];
lean_object* v_kind_3945_ = _args[14];
lean_object* v___y_3946_ = _args[15];
lean_object* v___y_3947_ = _args[16];
lean_object* v___y_3948_ = _args[17];
lean_object* v___y_3949_ = _args[18];
lean_object* v___y_3950_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3951_; uint8_t v_bi_boxed_3952_; uint8_t v_kind_boxed_3953_; lean_object* v_res_3954_; 
v_subsingletonInstImplicitRhs_boxed_3951_ = lean_unbox(v_subsingletonInstImplicitRhs_3935_);
v_bi_boxed_3952_ = lean_unbox(v_bi_3943_);
v_kind_boxed_3953_ = lean_unbox(v_kind_3945_);
v_res_3954_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3931_, v_rhss_3932_, v_eqs_3933_, v_hyps_3934_, v_subsingletonInstImplicitRhs_boxed_3951_, v_f_3936_, v_info_3937_, v_kinds_3938_, v_lhss_3939_, v_lhs_3940_, v___x_3941_, v_name_3942_, v_bi_boxed_3952_, v_type_3944_, v_kind_boxed_3953_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_3955_ = _args[0];
lean_object* v_rhss_3956_ = _args[1];
lean_object* v_lhs_3957_ = _args[2];
lean_object* v_eqs_3958_ = _args[3];
lean_object* v_hyps_3959_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3960_ = _args[5];
lean_object* v_f_3961_ = _args[6];
lean_object* v_info_3962_ = _args[7];
lean_object* v_kinds_3963_ = _args[8];
lean_object* v_lhss_3964_ = _args[9];
lean_object* v_name_3965_ = _args[10];
lean_object* v_bi_3966_ = _args[11];
lean_object* v_type_3967_ = _args[12];
lean_object* v_kind_3968_ = _args[13];
lean_object* v___y_3969_ = _args[14];
lean_object* v___y_3970_ = _args[15];
lean_object* v___y_3971_ = _args[16];
lean_object* v___y_3972_ = _args[17];
lean_object* v___y_3973_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3974_; uint8_t v_bi_boxed_3975_; uint8_t v_kind_boxed_3976_; lean_object* v_res_3977_; 
v_subsingletonInstImplicitRhs_boxed_3974_ = lean_unbox(v_subsingletonInstImplicitRhs_3960_);
v_bi_boxed_3975_ = lean_unbox(v_bi_3966_);
v_kind_boxed_3976_ = lean_unbox(v_kind_3968_);
v_res_3977_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3955_, v_rhss_3956_, v_lhs_3957_, v_eqs_3958_, v_hyps_3959_, v_subsingletonInstImplicitRhs_boxed_3974_, v_f_3961_, v_info_3962_, v_kinds_3963_, v_lhss_3964_, v_name_3965_, v_bi_boxed_3975_, v_type_3967_, v_kind_boxed_3976_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* v_subsingletonInstImplicitRhs_3978_, lean_object* v_f_3979_, lean_object* v_info_3980_, lean_object* v_kinds_3981_, lean_object* v_lhss_3982_, lean_object* v_i_3983_, lean_object* v_rhss_3984_, lean_object* v_eqs_3985_, lean_object* v_hyps_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3992_; lean_object* v_res_3993_; 
v_subsingletonInstImplicitRhs_boxed_3992_ = lean_unbox(v_subsingletonInstImplicitRhs_3978_);
v_res_3993_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_boxed_3992_, v_f_3979_, v_info_3980_, v_kinds_3981_, v_lhss_3982_, v_i_3983_, v_rhss_3984_, v_eqs_3985_, v_hyps_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* v___x_3994_, uint8_t v_subsingletonInstImplicitRhs_3995_, lean_object* v_f_3996_, lean_object* v_info_3997_, lean_object* v_kinds_3998_, lean_object* v_lhss_3999_, lean_object* v_x_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; uint8_t v___x_4007_; uint8_t v___x_4008_; 
v___x_4006_ = lean_array_get_size(v_lhss_3999_);
v___x_4007_ = lean_nat_dec_eq(v___x_4006_, v___x_3994_);
v___x_4008_ = lean_bool_not(v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4009_ = lean_unsigned_to_nat(0u);
v___x_4010_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_4011_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3995_, v_f_3996_, v_info_3997_, v_kinds_3998_, v_lhss_3999_, v___x_4009_, v___x_4010_, v___x_4010_, v___x_4010_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4020_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4014_ = v___x_4011_;
v_isShared_4015_ = v_isSharedCheck_4020_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4011_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4020_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v_a_4012_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v___x_4016_);
v___x_4018_ = v___x_4014_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
v_a_4021_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4011_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4011_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
else
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
lean_dec_ref(v_lhss_3999_);
lean_dec_ref(v_kinds_3998_);
lean_dec_ref(v_info_3997_);
lean_dec_ref(v_f_3996_);
v___x_4029_ = lean_box(0);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* v___x_4031_, lean_object* v_subsingletonInstImplicitRhs_4032_, lean_object* v_f_4033_, lean_object* v_info_4034_, lean_object* v_kinds_4035_, lean_object* v_lhss_4036_, lean_object* v_x_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4043_; lean_object* v_res_4044_; 
v_subsingletonInstImplicitRhs_boxed_4043_ = lean_unbox(v_subsingletonInstImplicitRhs_4032_);
v_res_4044_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4031_, v_subsingletonInstImplicitRhs_boxed_4043_, v_f_4033_, v_info_4034_, v_kinds_4035_, v_lhss_4036_, v_x_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v_x_4037_);
lean_dec(v___x_4031_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t v_subsingletonInstImplicitRhs_4045_, lean_object* v_f_4046_, lean_object* v_info_4047_, lean_object* v_kinds_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v___y_4055_; uint8_t v___y_4056_; lean_object* v_a_4061_; lean_object* v___x_4064_; 
lean_inc(v_a_4052_);
lean_inc_ref(v_a_4051_);
lean_inc(v_a_4050_);
lean_inc_ref(v_a_4049_);
lean_inc_ref(v_f_4046_);
v___x_4064_ = lean_infer_type(v_f_4046_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4079_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4067_ = v___x_4064_;
v_isShared_4068_ = v_isSharedCheck_4079_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4079_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___f_4071_; lean_object* v___x_4073_; 
v___x_4069_ = lean_array_get_size(v_kinds_4048_);
v___x_4070_ = lean_box(v_subsingletonInstImplicitRhs_4045_);
v___f_4071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4071_, 0, v___x_4069_);
lean_closure_set(v___f_4071_, 1, v___x_4070_);
lean_closure_set(v___f_4071_, 2, v_f_4046_);
lean_closure_set(v___f_4071_, 3, v_info_4047_);
lean_closure_set(v___f_4071_, 4, v_kinds_4048_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set_tag(v___x_4067_, 1);
lean_ctor_set(v___x_4067_, 0, v___x_4069_);
v___x_4073_ = v___x_4067_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4069_);
v___x_4073_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
uint8_t v___x_4074_; uint8_t v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = 1;
v___x_4075_ = 0;
v___x_4076_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_4065_, v___x_4073_, v___f_4071_, v___x_4074_, v___x_4075_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4076_) == 0)
{
return v___x_4076_;
}
else
{
lean_object* v_a_4077_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4076_, 1);
v_a_4061_ = v_a_4077_;
goto v___jp_4060_;
}
}
}
}
else
{
lean_object* v_a_4080_; 
lean_dec_ref(v_kinds_4048_);
lean_dec_ref(v_info_4047_);
lean_dec_ref(v_f_4046_);
v_a_4080_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4064_, 1);
v_a_4061_ = v_a_4080_;
goto v___jp_4060_;
}
v___jp_4054_:
{
if (v___y_4056_ == 0)
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
lean_dec_ref(v___y_4055_);
v___x_4057_ = lean_box(0);
v___x_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
return v___x_4058_;
}
else
{
lean_object* v___x_4059_; 
v___x_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___y_4055_);
return v___x_4059_;
}
}
v___jp_4060_:
{
uint8_t v___x_4062_; 
v___x_4062_ = l_Lean_Exception_isInterrupt(v_a_4061_);
if (v___x_4062_ == 0)
{
uint8_t v___x_4063_; 
lean_inc_ref(v_a_4061_);
v___x_4063_ = l_Lean_Exception_isRuntime(v_a_4061_);
v___y_4055_ = v_a_4061_;
v___y_4056_ = v___x_4063_;
goto v___jp_4054_;
}
else
{
v___y_4055_ = v_a_4061_;
v___y_4056_ = v___x_4062_;
goto v___jp_4054_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* v_subsingletonInstImplicitRhs_4081_, lean_object* v_f_4082_, lean_object* v_info_4083_, lean_object* v_kinds_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4090_; lean_object* v_res_4091_; 
v_subsingletonInstImplicitRhs_boxed_4090_ = lean_unbox(v_subsingletonInstImplicitRhs_4081_);
v_res_4091_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_boxed_4090_, v_f_4082_, v_info_4083_, v_kinds_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
lean_dec(v_a_4088_);
lean_dec_ref(v_a_4087_);
lean_dec(v_a_4086_);
lean_dec_ref(v_a_4085_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t v_sz_4092_, size_t v_i_4093_, lean_object* v_bs_4094_){
_start:
{
uint8_t v___x_4095_; 
v___x_4095_ = lean_usize_dec_lt(v_i_4093_, v_sz_4092_);
if (v___x_4095_ == 0)
{
return v_bs_4094_;
}
else
{
lean_object* v_v_4096_; lean_object* v___x_4097_; lean_object* v_bs_x27_4098_; uint8_t v___y_4100_; uint8_t v___x_4106_; 
v_v_4096_ = lean_array_uget(v_bs_4094_, v_i_4093_);
v___x_4097_ = lean_unsigned_to_nat(0u);
v_bs_x27_4098_ = lean_array_uset(v_bs_4094_, v_i_4093_, v___x_4097_);
v___x_4106_ = lean_unbox(v_v_4096_);
switch(v___x_4106_)
{
case 3:
{
uint8_t v___x_4107_; 
lean_dec(v_v_4096_);
v___x_4107_ = 0;
v___y_4100_ = v___x_4107_;
goto v___jp_4099_;
}
case 5:
{
uint8_t v___x_4108_; 
lean_dec(v_v_4096_);
v___x_4108_ = 0;
v___y_4100_ = v___x_4108_;
goto v___jp_4099_;
}
default: 
{
uint8_t v___x_4109_; 
v___x_4109_ = lean_unbox(v_v_4096_);
lean_dec(v_v_4096_);
v___y_4100_ = v___x_4109_;
goto v___jp_4099_;
}
}
v___jp_4099_:
{
size_t v___x_4101_; size_t v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4101_ = ((size_t)1ULL);
v___x_4102_ = lean_usize_add(v_i_4093_, v___x_4101_);
v___x_4103_ = lean_box(v___y_4100_);
v___x_4104_ = lean_array_uset(v_bs_x27_4098_, v_i_4093_, v___x_4103_);
v_i_4093_ = v___x_4102_;
v_bs_4094_ = v___x_4104_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* v_sz_4110_, lean_object* v_i_4111_, lean_object* v_bs_4112_){
_start:
{
size_t v_sz_boxed_4113_; size_t v_i_boxed_4114_; lean_object* v_res_4115_; 
v_sz_boxed_4113_ = lean_unbox_usize(v_sz_4110_);
lean_dec(v_sz_4110_);
v_i_boxed_4114_ = lean_unbox_usize(v_i_4111_);
lean_dec(v_i_4111_);
v_res_4115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_4113_, v_i_boxed_4114_, v_bs_4112_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* v_f_4116_, lean_object* v_info_4117_, lean_object* v_kinds_4118_, uint8_t v_subsingletonInstImplicitRhs_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4125_; 
lean_inc_ref(v_kinds_4118_);
lean_inc_ref(v_info_4117_);
lean_inc_ref(v_f_4116_);
v___x_4125_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4119_, v_f_4116_, v_info_4117_, v_kinds_4118_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
if (lean_obj_tag(v_a_4126_) == 1)
{
lean_dec_ref_known(v_a_4126_, 1);
lean_dec_ref(v_kinds_4118_);
lean_dec_ref(v_info_4117_);
lean_dec_ref(v_f_4116_);
return v___x_4125_;
}
else
{
lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4139_; 
lean_dec(v_a_4126_);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4139_ == 0)
{
lean_object* v_unused_4140_; 
v_unused_4140_ = lean_ctor_get(v___x_4125_, 0);
lean_dec(v_unused_4140_);
v___x_4128_ = v___x_4125_;
v_isShared_4129_ = v_isSharedCheck_4139_;
goto v_resetjp_4127_;
}
else
{
lean_dec(v___x_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4139_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
uint8_t v___x_4130_; 
v___x_4130_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_4118_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4133_; 
lean_dec_ref(v_kinds_4118_);
lean_dec_ref(v_info_4117_);
lean_dec_ref(v_f_4116_);
v___x_4131_ = lean_box(0);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4131_);
v___x_4133_ = v___x_4128_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
else
{
size_t v_sz_4135_; size_t v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_del_object(v___x_4128_);
v_sz_4135_ = lean_array_size(v_kinds_4118_);
v___x_4136_ = ((size_t)0ULL);
v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4135_, v___x_4136_, v_kinds_4118_);
v___x_4138_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4119_, v_f_4116_, v_info_4117_, v___x_4137_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
return v___x_4138_;
}
}
}
}
else
{
lean_dec_ref(v_kinds_4118_);
lean_dec_ref(v_info_4117_);
lean_dec_ref(v_f_4116_);
return v___x_4125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* v_f_4141_, lean_object* v_info_4142_, lean_object* v_kinds_4143_, lean_object* v_subsingletonInstImplicitRhs_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4150_; lean_object* v_res_4151_; 
v_subsingletonInstImplicitRhs_boxed_4150_ = lean_unbox(v_subsingletonInstImplicitRhs_4144_);
v_res_4151_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4141_, v_info_4142_, v_kinds_4143_, v_subsingletonInstImplicitRhs_boxed_4150_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* v_f_4152_, uint8_t v_subsingletonInstImplicitRhs_4153_, lean_object* v_maxArgs_x3f_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v___x_4160_; lean_object* v_a_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4160_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_4152_, v_a_4156_);
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref(v___x_4160_);
v___x_4162_ = l_Lean_Expr_cleanupAnnotations(v_a_4161_);
lean_inc_ref(v___x_4162_);
v___x_4163_ = l_Lean_Meta_getFunInfo(v___x_4162_, v_maxArgs_x3f_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4165_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4163_, 1);
lean_inc_ref(v___x_4162_);
v___x_4165_ = l_Lean_Meta_getCongrSimpKinds(v___x_4162_, v_a_4164_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4167_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v___x_4167_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4162_, v_a_4164_, v_a_4166_, v_subsingletonInstImplicitRhs_4153_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
return v___x_4167_;
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_a_4164_);
lean_dec_ref(v___x_4162_);
v_a_4168_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4165_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4165_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec_ref(v___x_4162_);
v_a_4176_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4163_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4163_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* v_f_4184_, lean_object* v_subsingletonInstImplicitRhs_4185_, lean_object* v_maxArgs_x3f_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4192_; lean_object* v_res_4193_; 
v_subsingletonInstImplicitRhs_boxed_4192_ = lean_unbox(v_subsingletonInstImplicitRhs_4185_);
v_res_4193_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4184_, v_subsingletonInstImplicitRhs_boxed_4192_, v_maxArgs_x3f_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
return v_res_4193_;
}
}
static lean_object* _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4199_ = lean_string_utf8_byte_size(v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4200_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; 
v___x_4201_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4202_ = lean_string_utf8_byte_size(v_s_4200_);
v___x_4203_ = lean_obj_once(&l_Lean_Meta_isHCongrReservedNameSuffix___closed__0, &l_Lean_Meta_isHCongrReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isHCongrReservedNameSuffix___closed__0);
v___x_4204_ = lean_nat_dec_le(v___x_4203_, v___x_4202_);
if (v___x_4204_ == 0)
{
lean_dec_ref(v_s_4200_);
return v___x_4204_;
}
else
{
lean_object* v___x_4205_; uint8_t v___x_4206_; 
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = lean_string_memcmp(v_s_4200_, v___x_4201_, v___x_4205_, v___x_4205_, v___x_4203_);
if (v___x_4206_ == 0)
{
lean_dec_ref(v_s_4200_);
return v___x_4206_;
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; 
v___x_4207_ = lean_unsigned_to_nat(7u);
lean_inc_ref(v_s_4200_);
v___x_4208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4208_, 0, v_s_4200_);
lean_ctor_set(v___x_4208_, 1, v___x_4205_);
lean_ctor_set(v___x_4208_, 2, v___x_4202_);
v___x_4209_ = l_String_Slice_Pos_nextn(v___x_4208_, v___x_4205_, v___x_4207_);
lean_dec_ref_known(v___x_4208_, 3);
v___x_4210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4210_, 0, v_s_4200_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
lean_ctor_set(v___x_4210_, 2, v___x_4202_);
v___x_4211_ = l_String_Slice_isNat(v___x_4210_);
lean_dec_ref_known(v___x_4210_, 3);
return v___x_4211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* v_s_4212_){
_start:
{
uint8_t v_res_4213_; lean_object* v_r_4214_; 
v_res_4213_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4212_);
v_r_4214_ = lean_box(v_res_4213_);
return v_r_4214_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4264_ = lean_unsigned_to_nat(3482611248u);
v___x_4265_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4266_ = l_Lean_Name_num___override(v___x_4265_, v___x_4264_);
return v___x_4266_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4268_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4269_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4270_ = l_Lean_Name_str___override(v___x_4269_, v___x_4268_);
return v___x_4270_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4272_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4273_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4274_ = l_Lean_Name_str___override(v___x_4273_, v___x_4272_);
return v___x_4274_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = lean_unsigned_to_nat(2u);
v___x_4276_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4277_ = l_Lean_Name_num___override(v___x_4276_, v___x_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4279_; uint8_t v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4279_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4280_ = 0;
v___x_4281_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4282_ = l_Lean_registerTraceClass(v___x_4279_, v___x_4280_, v___x_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4285_, lean_object* v_as_4286_, size_t v_i_4287_, size_t v_stop_4288_, lean_object* v_b_4289_){
_start:
{
lean_object* v___y_4291_; uint8_t v___x_4295_; 
v___x_4295_ = lean_usize_dec_eq(v_i_4287_, v_stop_4288_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v_fst_4297_; uint8_t v___x_4298_; 
v___x_4296_ = lean_array_uget_borrowed(v_as_4286_, v_i_4287_);
v_fst_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_fst_4297_);
lean_inc_ref(v_env_4285_);
v___x_4298_ = l_Lean_Environment_contains(v_env_4285_, v_fst_4297_, v___x_4295_);
if (v___x_4298_ == 0)
{
v___y_4291_ = v_b_4289_;
goto v___jp_4290_;
}
else
{
lean_object* v___x_4299_; 
lean_inc(v___x_4296_);
v___x_4299_ = lean_array_push(v_b_4289_, v___x_4296_);
v___y_4291_ = v___x_4299_;
goto v___jp_4290_;
}
}
else
{
lean_dec_ref(v_env_4285_);
return v_b_4289_;
}
v___jp_4290_:
{
size_t v___x_4292_; size_t v___x_4293_; 
v___x_4292_ = ((size_t)1ULL);
v___x_4293_ = lean_usize_add(v_i_4287_, v___x_4292_);
v_i_4287_ = v___x_4293_;
v_b_4289_ = v___y_4291_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4300_, lean_object* v_as_4301_, lean_object* v_i_4302_, lean_object* v_stop_4303_, lean_object* v_b_4304_){
_start:
{
size_t v_i_boxed_4305_; size_t v_stop_boxed_4306_; lean_object* v_res_4307_; 
v_i_boxed_4305_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_stop_boxed_4306_ = lean_unbox_usize(v_stop_4303_);
lean_dec(v_stop_4303_);
v_res_4307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4300_, v_as_4301_, v_i_boxed_4305_, v_stop_boxed_4306_, v_b_4304_);
lean_dec_ref(v_as_4301_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4308_, lean_object* v_x_4309_){
_start:
{
if (lean_obj_tag(v_x_4309_) == 0)
{
lean_object* v_k_4310_; lean_object* v_v_4311_; lean_object* v_l_4312_; lean_object* v_r_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v_k_4310_ = lean_ctor_get(v_x_4309_, 1);
v_v_4311_ = lean_ctor_get(v_x_4309_, 2);
v_l_4312_ = lean_ctor_get(v_x_4309_, 3);
v_r_4313_ = lean_ctor_get(v_x_4309_, 4);
v___x_4314_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4308_, v_l_4312_);
lean_inc(v_v_4311_);
lean_inc(v_k_4310_);
v___x_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4315_, 0, v_k_4310_);
lean_ctor_set(v___x_4315_, 1, v_v_4311_);
v___x_4316_ = lean_array_push(v___x_4314_, v___x_4315_);
v_init_4308_ = v___x_4316_;
v_x_4309_ = v_r_4313_;
goto _start;
}
else
{
return v_init_4308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4318_, lean_object* v_x_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4318_, v_x_4319_);
lean_dec(v_x_4319_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4327_, lean_object* v_s_4328_){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4331_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4330_, v_s_4328_);
v___x_4332_ = lean_array_get_size(v___x_4331_);
v___x_4333_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4334_ = lean_nat_dec_lt(v___x_4329_, v___x_4332_);
if (v___x_4334_ == 0)
{
lean_object* v___x_4335_; 
lean_dec_ref(v___x_4331_);
lean_dec_ref(v_env_4327_);
v___x_4335_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4335_;
}
else
{
uint8_t v___x_4336_; 
v___x_4336_ = lean_nat_dec_le(v___x_4332_, v___x_4332_);
if (v___x_4336_ == 0)
{
if (v___x_4334_ == 0)
{
lean_object* v___x_4337_; 
lean_dec_ref(v___x_4331_);
lean_dec_ref(v_env_4327_);
v___x_4337_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
return v___x_4337_;
}
else
{
size_t v___x_4338_; size_t v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4338_ = ((size_t)0ULL);
v___x_4339_ = lean_usize_of_nat(v___x_4332_);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4327_, v___x_4331_, v___x_4338_, v___x_4339_, v___x_4333_);
lean_dec_ref(v___x_4331_);
lean_inc_ref_n(v___x_4340_, 2);
v___x_4341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
lean_ctor_set(v___x_4341_, 2, v___x_4340_);
return v___x_4341_;
}
}
else
{
size_t v___x_4342_; size_t v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4342_ = ((size_t)0ULL);
v___x_4343_ = lean_usize_of_nat(v___x_4332_);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4327_, v___x_4331_, v___x_4342_, v___x_4343_, v___x_4333_);
lean_dec_ref(v___x_4331_);
lean_inc_ref_n(v___x_4344_, 2);
v___x_4345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
lean_ctor_set(v___x_4345_, 1, v___x_4344_);
lean_ctor_set(v___x_4345_, 2, v___x_4344_);
return v___x_4345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4346_, lean_object* v_s_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4346_, v_s_4347_);
lean_dec(v_s_4347_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___f_4358_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4359_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4360_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4361_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4359_, v___x_4360_, v___f_4358_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4364_, lean_object* v_t_4365_){
_start:
{
lean_object* v___x_4366_; 
v___x_4366_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4364_, v_t_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4367_, lean_object* v_t_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4367_, v_t_4368_);
lean_dec(v_t_4368_);
return v_res_4369_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object* v_env_4370_, lean_object* v_n_4371_){
_start:
{
if (lean_obj_tag(v_n_4371_) == 1)
{
lean_object* v_pre_4372_; lean_object* v_str_4373_; uint8_t v___y_4375_; uint8_t v___x_4377_; 
v_pre_4372_ = lean_ctor_get(v_n_4371_, 0);
lean_inc(v_pre_4372_);
v_str_4373_ = lean_ctor_get(v_n_4371_, 1);
lean_inc_ref_n(v_str_4373_, 2);
lean_dec_ref_known(v_n_4371_, 2);
v___x_4377_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4373_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4378_; uint8_t v___x_4379_; 
v___x_4378_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4379_ = lean_string_dec_eq(v_str_4373_, v___x_4378_);
lean_dec_ref(v_str_4373_);
v___y_4375_ = v___x_4379_;
goto v___jp_4374_;
}
else
{
lean_dec_ref(v_str_4373_);
v___y_4375_ = v___x_4377_;
goto v___jp_4374_;
}
v___jp_4374_:
{
if (v___y_4375_ == 0)
{
lean_dec(v_pre_4372_);
lean_dec_ref(v_env_4370_);
return v___y_4375_;
}
else
{
uint8_t v___x_4376_; 
v___x_4376_ = l_Lean_Environment_contains(v_env_4370_, v_pre_4372_, v___y_4375_);
return v___x_4376_;
}
}
}
else
{
uint8_t v___x_4380_; 
lean_dec(v_n_4371_);
lean_dec_ref(v_env_4370_);
v___x_4380_ = 0;
return v___x_4380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_env_4381_, lean_object* v_n_4382_){
_start:
{
uint8_t v_res_4383_; lean_object* v_r_4384_; 
v_res_4383_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4381_, v_n_4382_);
v_r_4384_ = lean_box(v_res_4383_);
return v_r_4384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4387_; lean_object* v___x_4388_; 
v___f_4387_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_));
v___x_4388_ = l_Lean_registerReservedNamePredicate(v___f_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_a_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object* v_thm_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4394_; lean_object* v_env_4395_; lean_object* v_toConstantVal_4396_; lean_object* v_value_4397_; lean_object* v_all_4398_; uint8_t v___y_4400_; lean_object* v_type_4408_; uint8_t v___x_4409_; 
v___x_4394_ = lean_st_ref_get(v___y_4392_);
v_env_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc_ref_n(v_env_4395_, 2);
lean_dec(v___x_4394_);
v_toConstantVal_4396_ = lean_ctor_get(v_thm_4391_, 0);
v_value_4397_ = lean_ctor_get(v_thm_4391_, 1);
v_all_4398_ = lean_ctor_get(v_thm_4391_, 2);
v_type_4408_ = lean_ctor_get(v_toConstantVal_4396_, 2);
v___x_4409_ = l_Lean_Environment_hasUnsafe(v_env_4395_, v_type_4408_);
if (v___x_4409_ == 0)
{
uint8_t v___x_4410_; 
v___x_4410_ = l_Lean_Environment_hasUnsafe(v_env_4395_, v_value_4397_);
v___y_4400_ = v___x_4410_;
goto v___jp_4399_;
}
else
{
lean_dec_ref(v_env_4395_);
v___y_4400_ = v___x_4409_;
goto v___jp_4399_;
}
v___jp_4399_:
{
if (v___y_4400_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4401_, 0, v_thm_4391_);
v___x_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4401_);
return v___x_4402_;
}
else
{
lean_object* v___x_4403_; uint8_t v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
lean_inc(v_all_4398_);
lean_inc_ref(v_value_4397_);
lean_inc_ref(v_toConstantVal_4396_);
lean_dec_ref(v_thm_4391_);
v___x_4403_ = lean_box(0);
v___x_4404_ = 0;
v___x_4405_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4405_, 0, v_toConstantVal_4396_);
lean_ctor_set(v___x_4405_, 1, v_value_4397_);
lean_ctor_set(v___x_4405_, 2, v___x_4403_);
lean_ctor_set(v___x_4405_, 3, v_all_4398_);
lean_ctor_set_uint8(v___x_4405_, sizeof(void*)*4, v___x_4404_);
v___x_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
return v___x_4407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_thm_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4411_, v___y_4412_);
lean_dec(v___y_4412_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_thm_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4415_, v___y_4419_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object* v_thm_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
return v_res_4428_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_4429_; double v___x_4430_; 
v___x_4429_ = lean_unsigned_to_nat(0u);
v___x_4430_ = lean_float_of_nat(v___x_4429_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_cls_4434_, lean_object* v_msg_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v_ref_4441_; lean_object* v___x_4442_; lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4487_; 
v_ref_4441_ = lean_ctor_get(v___y_4438_, 5);
v___x_4442_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__2_spec__2(v_msg_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4445_ = v___x_4442_;
v_isShared_4446_ = v_isSharedCheck_4487_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4442_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4487_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4447_; lean_object* v_traceState_4448_; lean_object* v_env_4449_; lean_object* v_nextMacroScope_4450_; lean_object* v_ngen_4451_; lean_object* v_auxDeclNGen_4452_; lean_object* v_cache_4453_; lean_object* v_messages_4454_; lean_object* v_infoState_4455_; lean_object* v_snapshotTasks_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4486_; 
v___x_4447_ = lean_st_ref_take(v___y_4439_);
v_traceState_4448_ = lean_ctor_get(v___x_4447_, 4);
v_env_4449_ = lean_ctor_get(v___x_4447_, 0);
v_nextMacroScope_4450_ = lean_ctor_get(v___x_4447_, 1);
v_ngen_4451_ = lean_ctor_get(v___x_4447_, 2);
v_auxDeclNGen_4452_ = lean_ctor_get(v___x_4447_, 3);
v_cache_4453_ = lean_ctor_get(v___x_4447_, 5);
v_messages_4454_ = lean_ctor_get(v___x_4447_, 6);
v_infoState_4455_ = lean_ctor_get(v___x_4447_, 7);
v_snapshotTasks_4456_ = lean_ctor_get(v___x_4447_, 8);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4458_ = v___x_4447_;
v_isShared_4459_ = v_isSharedCheck_4486_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_snapshotTasks_4456_);
lean_inc(v_infoState_4455_);
lean_inc(v_messages_4454_);
lean_inc(v_cache_4453_);
lean_inc(v_traceState_4448_);
lean_inc(v_auxDeclNGen_4452_);
lean_inc(v_ngen_4451_);
lean_inc(v_nextMacroScope_4450_);
lean_inc(v_env_4449_);
lean_dec(v___x_4447_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4486_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
uint64_t v_tid_4460_; lean_object* v_traces_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4485_; 
v_tid_4460_ = lean_ctor_get_uint64(v_traceState_4448_, sizeof(void*)*1);
v_traces_4461_ = lean_ctor_get(v_traceState_4448_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_traceState_4448_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4463_ = v_traceState_4448_;
v_isShared_4464_ = v_isSharedCheck_4485_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_traces_4461_);
lean_dec(v_traceState_4448_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4485_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; double v___x_4466_; uint8_t v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4465_ = lean_box(0);
v___x_4466_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0);
v___x_4467_ = 0;
v___x_4468_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1));
v___x_4469_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4469_, 0, v_cls_4434_);
lean_ctor_set(v___x_4469_, 1, v___x_4465_);
lean_ctor_set(v___x_4469_, 2, v___x_4468_);
lean_ctor_set_float(v___x_4469_, sizeof(void*)*3, v___x_4466_);
lean_ctor_set_float(v___x_4469_, sizeof(void*)*3 + 8, v___x_4466_);
lean_ctor_set_uint8(v___x_4469_, sizeof(void*)*3 + 16, v___x_4467_);
v___x_4470_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2));
v___x_4471_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4469_);
lean_ctor_set(v___x_4471_, 1, v_a_4443_);
lean_ctor_set(v___x_4471_, 2, v___x_4470_);
lean_inc(v_ref_4441_);
v___x_4472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4472_, 0, v_ref_4441_);
lean_ctor_set(v___x_4472_, 1, v___x_4471_);
v___x_4473_ = l_Lean_PersistentArray_push___redArg(v_traces_4461_, v___x_4472_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4473_);
v___x_4475_ = v___x_4463_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4473_);
lean_ctor_set_uint64(v_reuseFailAlloc_4484_, sizeof(void*)*1, v_tid_4460_);
v___x_4475_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4477_; 
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 4, v___x_4475_);
v___x_4477_ = v___x_4458_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_env_4449_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_nextMacroScope_4450_);
lean_ctor_set(v_reuseFailAlloc_4483_, 2, v_ngen_4451_);
lean_ctor_set(v_reuseFailAlloc_4483_, 3, v_auxDeclNGen_4452_);
lean_ctor_set(v_reuseFailAlloc_4483_, 4, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4483_, 5, v_cache_4453_);
lean_ctor_set(v_reuseFailAlloc_4483_, 6, v_messages_4454_);
lean_ctor_set(v_reuseFailAlloc_4483_, 7, v_infoState_4455_);
lean_ctor_set(v_reuseFailAlloc_4483_, 8, v_snapshotTasks_4456_);
v___x_4477_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4481_; 
v___x_4478_ = lean_st_ref_set(v___y_4439_, v___x_4477_);
v___x_4479_ = lean_box(0);
if (v_isShared_4446_ == 0)
{
lean_ctor_set(v___x_4445_, 0, v___x_4479_);
v___x_4481_ = v___x_4445_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4479_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_4488_, lean_object* v_msg_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4488_, v_msg_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
return v_res_4495_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4496_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
return v___x_4498_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4499_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
lean_ctor_set(v___x_4500_, 1, v___x_4499_);
return v___x_4500_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4504_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4505_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4506_ = l_Lean_Name_append(v___x_4505_, v___x_4504_);
return v___x_4506_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4508_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4509_ = l_Lean_stringToMessageData(v___x_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4510_, uint8_t v___x_4511_, lean_object* v_name_4512_, lean_object* v_argKinds_4513_, lean_object* v___x_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___x_4560_; lean_object* v_a_4561_; lean_object* v___x_4562_; 
v___x_4560_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_4510_, v___y_4518_);
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref(v___x_4560_);
v___x_4562_ = l_Lean_addDecl(v_a_4561_, v___x_4511_, v___y_4517_, v___y_4518_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_options_4563_; uint8_t v_hasTrace_4564_; 
lean_dec_ref_known(v___x_4562_, 1);
v_options_4563_ = lean_ctor_get(v___y_4517_, 2);
v_hasTrace_4564_ = lean_ctor_get_uint8(v_options_4563_, sizeof(void*)*1);
if (v_hasTrace_4564_ == 0)
{
v___y_4521_ = v___y_4516_;
v___y_4522_ = v___y_4518_;
goto v___jp_4520_;
}
else
{
lean_object* v_inheritedTraceOptions_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; 
v_inheritedTraceOptions_4565_ = lean_ctor_get(v___y_4517_, 13);
v___x_4566_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4567_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4565_, v_options_4563_, v___x_4567_);
if (v___x_4568_ == 0)
{
v___y_4521_ = v___y_4516_;
v___y_4522_ = v___y_4518_;
goto v___jp_4520_;
}
else
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4569_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4512_);
v___x_4570_ = l_Lean_MessageData_ofName(v_name_4512_);
v___x_4571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4569_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
v___x_4572_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4571_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_4566_, v___x_4573_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_dec_ref_known(v___x_4574_, 1);
v___y_4521_ = v___y_4516_;
v___y_4522_ = v___y_4518_;
goto v___jp_4520_;
}
else
{
lean_dec_ref(v___x_4514_);
lean_dec_ref(v_argKinds_4513_);
lean_dec(v_name_4512_);
return v___x_4574_;
}
}
}
}
else
{
lean_dec_ref(v___x_4514_);
lean_dec_ref(v_argKinds_4513_);
lean_dec(v_name_4512_);
return v___x_4562_;
}
v___jp_4520_:
{
lean_object* v___x_4523_; lean_object* v_env_4524_; lean_object* v_nextMacroScope_4525_; lean_object* v_ngen_4526_; lean_object* v_auxDeclNGen_4527_; lean_object* v_traceState_4528_; lean_object* v_messages_4529_; lean_object* v_infoState_4530_; lean_object* v_snapshotTasks_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4558_; 
v___x_4523_ = lean_st_ref_take(v___y_4522_);
v_env_4524_ = lean_ctor_get(v___x_4523_, 0);
v_nextMacroScope_4525_ = lean_ctor_get(v___x_4523_, 1);
v_ngen_4526_ = lean_ctor_get(v___x_4523_, 2);
v_auxDeclNGen_4527_ = lean_ctor_get(v___x_4523_, 3);
v_traceState_4528_ = lean_ctor_get(v___x_4523_, 4);
v_messages_4529_ = lean_ctor_get(v___x_4523_, 6);
v_infoState_4530_ = lean_ctor_get(v___x_4523_, 7);
v_snapshotTasks_4531_ = lean_ctor_get(v___x_4523_, 8);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; 
v_unused_4559_ = lean_ctor_get(v___x_4523_, 5);
lean_dec(v_unused_4559_);
v___x_4533_ = v___x_4523_;
v_isShared_4534_ = v_isSharedCheck_4558_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_snapshotTasks_4531_);
lean_inc(v_infoState_4530_);
lean_inc(v_messages_4529_);
lean_inc(v_traceState_4528_);
lean_inc(v_auxDeclNGen_4527_);
lean_inc(v_ngen_4526_);
lean_inc(v_nextMacroScope_4525_);
lean_inc(v_env_4524_);
lean_dec(v___x_4523_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4558_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4539_; 
v___x_4535_ = l_Lean_Meta_congrKindsExt;
v___x_4536_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4535_, v_env_4524_, v_name_4512_, v_argKinds_4513_);
v___x_4537_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 5, v___x_4537_);
lean_ctor_set(v___x_4533_, 0, v___x_4536_);
v___x_4539_ = v___x_4533_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_nextMacroScope_4525_);
lean_ctor_set(v_reuseFailAlloc_4557_, 2, v_ngen_4526_);
lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_auxDeclNGen_4527_);
lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_traceState_4528_);
lean_ctor_set(v_reuseFailAlloc_4557_, 5, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4557_, 6, v_messages_4529_);
lean_ctor_set(v_reuseFailAlloc_4557_, 7, v_infoState_4530_);
lean_ctor_set(v_reuseFailAlloc_4557_, 8, v_snapshotTasks_4531_);
v___x_4539_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v_mctx_4542_; lean_object* v_zetaDeltaFVarIds_4543_; lean_object* v_postponed_4544_; lean_object* v_diag_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4555_; 
v___x_4540_ = lean_st_ref_set(v___y_4522_, v___x_4539_);
v___x_4541_ = lean_st_ref_take(v___y_4521_);
v_mctx_4542_ = lean_ctor_get(v___x_4541_, 0);
v_zetaDeltaFVarIds_4543_ = lean_ctor_get(v___x_4541_, 2);
v_postponed_4544_ = lean_ctor_get(v___x_4541_, 3);
v_diag_4545_ = lean_ctor_get(v___x_4541_, 4);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4555_ == 0)
{
lean_object* v_unused_4556_; 
v_unused_4556_ = lean_ctor_get(v___x_4541_, 1);
lean_dec(v_unused_4556_);
v___x_4547_ = v___x_4541_;
v_isShared_4548_ = v_isSharedCheck_4555_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_diag_4545_);
lean_inc(v_postponed_4544_);
lean_inc(v_zetaDeltaFVarIds_4543_);
lean_inc(v_mctx_4542_);
lean_dec(v___x_4541_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4555_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 1, v___x_4514_);
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_mctx_4542_);
lean_ctor_set(v_reuseFailAlloc_4554_, 1, v___x_4514_);
lean_ctor_set(v_reuseFailAlloc_4554_, 2, v_zetaDeltaFVarIds_4543_);
lean_ctor_set(v_reuseFailAlloc_4554_, 3, v_postponed_4544_);
lean_ctor_set(v_reuseFailAlloc_4554_, 4, v_diag_4545_);
v___x_4550_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4551_ = lean_st_ref_set(v___y_4521_, v___x_4550_);
v___x_4552_ = lean_box(0);
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
return v___x_4553_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4575_, lean_object* v___x_4576_, lean_object* v_name_4577_, lean_object* v_argKinds_4578_, lean_object* v___x_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
uint8_t v___x_15938__boxed_4585_; lean_object* v_res_4586_; 
v___x_15938__boxed_4585_ = lean_unbox(v___x_4576_);
v_res_4586_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4575_, v___x_15938__boxed_4585_, v_name_4577_, v_argKinds_4578_, v___x_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_a_4587_, lean_object* v_a_4588_){
_start:
{
if (lean_obj_tag(v_a_4587_) == 0)
{
lean_object* v___x_4589_; 
v___x_4589_ = l_List_reverse___redArg(v_a_4588_);
return v___x_4589_;
}
else
{
lean_object* v_head_4590_; lean_object* v_tail_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4600_; 
v_head_4590_ = lean_ctor_get(v_a_4587_, 0);
v_tail_4591_ = lean_ctor_get(v_a_4587_, 1);
v_isSharedCheck_4600_ = !lean_is_exclusive(v_a_4587_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4593_ = v_a_4587_;
v_isShared_4594_ = v_isSharedCheck_4600_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_tail_4591_);
lean_inc(v_head_4590_);
lean_dec(v_a_4587_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4600_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4597_; 
v___x_4595_ = l_Lean_mkLevelParam(v_head_4590_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 1, v_a_4588_);
lean_ctor_set(v___x_4593_, 0, v___x_4595_);
v___x_4597_ = v___x_4593_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4595_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v_a_4588_);
v___x_4597_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
v_a_4587_ = v_tail_4591_;
v_a_4588_ = v___x_4597_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4601_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
return v___x_4603_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4604_ = lean_box(1);
v___x_4605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4606_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
lean_ctor_set(v___x_4607_, 1, v___x_4605_);
lean_ctor_set(v___x_4607_, 2, v___x_4604_);
return v___x_4607_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4610_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4611_ = lean_unsigned_to_nat(0u);
v___x_4612_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
lean_ctor_set(v___x_4612_, 1, v___x_4611_);
lean_ctor_set(v___x_4612_, 2, v___x_4611_);
lean_ctor_set(v___x_4612_, 3, v___x_4611_);
lean_ctor_set(v___x_4612_, 4, v___x_4610_);
lean_ctor_set(v___x_4612_, 5, v___x_4610_);
lean_ctor_set(v___x_4612_, 6, v___x_4610_);
lean_ctor_set(v___x_4612_, 7, v___x_4610_);
lean_ctor_set(v___x_4612_, 8, v___x_4610_);
lean_ctor_set(v___x_4612_, 9, v___x_4610_);
return v___x_4612_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4614_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4613_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
lean_ctor_set(v___x_4614_, 2, v___x_4613_);
lean_ctor_set(v___x_4614_, 3, v___x_4613_);
lean_ctor_set(v___x_4614_, 4, v___x_4613_);
lean_ctor_set(v___x_4614_, 5, v___x_4613_);
return v___x_4614_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4615_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
lean_ctor_set(v___x_4616_, 2, v___x_4615_);
lean_ctor_set(v___x_4616_, 3, v___x_4615_);
lean_ctor_set(v___x_4616_, 4, v___x_4615_);
return v___x_4616_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4617_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4619_ = lean_box(1);
v___x_4620_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4621_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
lean_ctor_set(v___x_4622_, 1, v___x_4620_);
lean_ctor_set(v___x_4622_, 2, v___x_4619_);
lean_ctor_set(v___x_4622_, 3, v___x_4618_);
lean_ctor_set(v___x_4622_, 4, v___x_4617_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v_name_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
if (lean_obj_tag(v_name_4623_) == 1)
{
lean_object* v_pre_4627_; lean_object* v_str_4628_; lean_object* v___x_4629_; lean_object* v_env_4630_; uint8_t v___x_4631_; uint8_t v___x_4632_; 
v_pre_4627_ = lean_ctor_get(v_name_4623_, 0);
lean_inc_n(v_pre_4627_, 2);
v_str_4628_ = lean_ctor_get(v_name_4623_, 1);
v___x_4629_ = lean_st_ref_get(v___y_4625_);
v_env_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc_ref(v_env_4630_);
lean_dec(v___x_4629_);
v___x_4631_ = 1;
v___x_4632_ = l_Lean_Environment_contains(v_env_4630_, v_pre_4627_, v___x_4631_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
lean_dec(v_pre_4627_);
lean_dec_ref_known(v_name_4623_, 2);
v___x_4633_ = lean_box(v___x_4632_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
return v___x_4634_;
}
else
{
uint8_t v___x_4635_; lean_object* v___y_4637_; uint8_t v___y_4638_; lean_object* v_a_4643_; 
lean_inc_ref(v_str_4628_);
v___x_4635_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4628_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4646_; uint8_t v___x_4647_; 
v___x_4646_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4647_ = lean_string_dec_eq(v_str_4628_, v___x_4646_);
if (v___x_4647_ == 0)
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
lean_dec(v_pre_4627_);
lean_dec_ref_known(v_name_4623_, 2);
v___x_4648_ = lean_box(v___x_4647_);
v___x_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
return v___x_4649_;
}
else
{
uint8_t v___x_4650_; uint8_t v___x_4651_; uint8_t v___x_4652_; lean_object* v___x_4653_; uint64_t v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; uint8_t v_a_4666_; lean_object* v___x_4670_; 
v___x_4650_ = 1;
v___x_4651_ = 0;
v___x_4652_ = 2;
v___x_4653_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4653_, 0, v___x_4635_);
lean_ctor_set_uint8(v___x_4653_, 1, v___x_4635_);
lean_ctor_set_uint8(v___x_4653_, 2, v___x_4635_);
lean_ctor_set_uint8(v___x_4653_, 3, v___x_4635_);
lean_ctor_set_uint8(v___x_4653_, 4, v___x_4635_);
lean_ctor_set_uint8(v___x_4653_, 5, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 6, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 7, v___x_4635_);
lean_ctor_set_uint8(v___x_4653_, 8, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 9, v___x_4650_);
lean_ctor_set_uint8(v___x_4653_, 10, v___x_4651_);
lean_ctor_set_uint8(v___x_4653_, 11, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 12, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 13, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 14, v___x_4652_);
lean_ctor_set_uint8(v___x_4653_, 15, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 16, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 17, v___x_4647_);
lean_ctor_set_uint8(v___x_4653_, 18, v___x_4647_);
v___x_4654_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4653_);
v___x_4655_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4655_, 0, v___x_4653_);
lean_ctor_set_uint64(v___x_4655_, sizeof(void*)*1, v___x_4654_);
v___x_4656_ = lean_box(1);
v___x_4657_ = lean_unsigned_to_nat(0u);
v___x_4658_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4659_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4660_ = lean_box(0);
v___x_4661_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4661_, 0, v___x_4655_);
lean_ctor_set(v___x_4661_, 1, v___x_4656_);
lean_ctor_set(v___x_4661_, 2, v___x_4658_);
lean_ctor_set(v___x_4661_, 3, v___x_4659_);
lean_ctor_set(v___x_4661_, 4, v___x_4660_);
lean_ctor_set(v___x_4661_, 5, v___x_4657_);
lean_ctor_set(v___x_4661_, 6, v___x_4660_);
lean_ctor_set_uint8(v___x_4661_, sizeof(void*)*7, v___x_4635_);
lean_ctor_set_uint8(v___x_4661_, sizeof(void*)*7 + 1, v___x_4635_);
lean_ctor_set_uint8(v___x_4661_, sizeof(void*)*7 + 2, v___x_4635_);
lean_ctor_set_uint8(v___x_4661_, sizeof(void*)*7 + 3, v___x_4631_);
v___x_4662_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4663_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4664_ = lean_st_mk_ref(v___x_4663_);
lean_inc(v_pre_4627_);
v___x_4670_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4627_, v___x_4661_, v___x_4664_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
v___x_4672_ = l_Lean_ConstantInfo_levelParams(v_a_4671_);
lean_dec(v_a_4671_);
v___x_4673_ = lean_box(0);
lean_inc(v___x_4672_);
v___x_4674_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4672_, v___x_4673_);
lean_inc(v_pre_4627_);
v___x_4675_ = l_Lean_mkConst(v_pre_4627_, v___x_4674_);
lean_inc_ref(v___x_4675_);
v___x_4676_ = l_Lean_Meta_getFunInfo(v___x_4675_, v___x_4660_, v___x_4661_, v___x_4664_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4678_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4676_, 1);
lean_inc_ref(v___x_4675_);
v___x_4678_ = l_Lean_Meta_getCongrSimpKinds(v___x_4675_, v_a_4677_, v___x_4661_, v___x_4664_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4680_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4678_, 1);
v___x_4680_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4675_, v_a_4677_, v_a_4679_, v___x_4631_, v___x_4661_, v___x_4664_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref_known(v___x_4680_, 1);
if (lean_obj_tag(v_a_4681_) == 1)
{
lean_object* v_val_4682_; lean_object* v_type_4683_; lean_object* v_proof_4684_; lean_object* v_argKinds_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4698_; 
v_val_4682_ = lean_ctor_get(v_a_4681_, 0);
lean_inc(v_val_4682_);
lean_dec_ref_known(v_a_4681_, 1);
v_type_4683_ = lean_ctor_get(v_val_4682_, 0);
v_proof_4684_ = lean_ctor_get(v_val_4682_, 1);
v_argKinds_4685_ = lean_ctor_get(v_val_4682_, 2);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_val_4682_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4687_ = v_val_4682_;
v_isShared_4688_ = v_isSharedCheck_4698_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_argKinds_4685_);
lean_inc(v_proof_4684_);
lean_inc(v_type_4683_);
lean_dec(v_val_4682_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4698_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
lean_inc_ref(v_name_4623_);
if (v_isShared_4688_ == 0)
{
lean_ctor_set(v___x_4687_, 2, v_type_4683_);
lean_ctor_set(v___x_4687_, 1, v___x_4672_);
lean_ctor_set(v___x_4687_, 0, v_name_4623_);
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_name_4623_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___x_4672_);
lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_type_4683_);
v___x_4690_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___f_4694_; lean_object* v___x_4695_; 
lean_inc_ref_n(v_name_4623_, 2);
v___x_4691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4691_, 0, v_name_4623_);
lean_ctor_set(v___x_4691_, 1, v___x_4673_);
v___x_4692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v_proof_4684_);
lean_ctor_set(v___x_4692_, 2, v___x_4691_);
v___x_4693_ = lean_box(v___x_4635_);
v___f_4694_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4694_, 0, v___x_4692_);
lean_closure_set(v___f_4694_, 1, v___x_4693_);
lean_closure_set(v___f_4694_, 2, v_name_4623_);
lean_closure_set(v___f_4694_, 3, v_argKinds_4685_);
lean_closure_set(v___f_4694_, 4, v___x_4662_);
v___x_4695_ = l_Lean_Meta_realizeConst(v_pre_4627_, v_name_4623_, v___f_4694_, v___x_4661_, v___x_4664_, v___y_4624_, v___y_4625_);
lean_dec_ref_known(v___x_4661_, 7);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_dec_ref_known(v___x_4695_, 1);
v_a_4666_ = v___x_4631_;
goto v___jp_4665_;
}
else
{
lean_object* v_a_4696_; 
lean_dec(v___x_4664_);
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v_a_4643_ = v_a_4696_;
goto v___jp_4642_;
}
}
}
}
else
{
lean_dec(v_a_4681_);
lean_dec(v___x_4672_);
lean_dec_ref_known(v___x_4661_, 7);
lean_dec(v_pre_4627_);
lean_dec_ref_known(v_name_4623_, 2);
v_a_4666_ = v___x_4635_;
goto v___jp_4665_;
}
}
else
{
lean_object* v_a_4699_; 
lean_dec(v___x_4672_);
lean_dec(v___x_4664_);
lean_dec_ref_known(v___x_4661_, 7);
lean_dec_ref_known(v_name_4623_, 2);
lean_dec(v_pre_4627_);
v_a_4699_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v___x_4680_, 1);
v_a_4643_ = v_a_4699_;
goto v___jp_4642_;
}
}
else
{
lean_object* v_a_4700_; 
lean_dec(v_a_4677_);
lean_dec_ref(v___x_4675_);
lean_dec(v___x_4672_);
lean_dec(v___x_4664_);
lean_dec_ref_known(v___x_4661_, 7);
lean_dec(v_pre_4627_);
lean_dec_ref_known(v_name_4623_, 2);
v_a_4700_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4700_);
lean_dec_ref_known(v___x_4678_, 1);
v_a_4643_ = v_a_4700_;
goto v___jp_4642_;
}
}
else
{
lean_object* v_a_4701_; 
lean_dec_ref(v___x_4675_);
lean_dec(v___x_4672_);
lean_dec(v___x_4664_);
lean_dec_ref_known(v___x_4661_, 7);
lean_dec(v_pre_4627_);
lean_dec_ref_known(v_name_4623_, 2);
v_a_4701_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4676_, 1);
v_a_4643_ = v_a_4701_;
goto v___jp_4642_;
}
}
else
{
lean_object* v_a_4702_; 
lean_dec(v___x_4664_);
lean_dec_ref_known(v___x_4661_, 7);
lean_dec(v_pre_4627_);
lean_dec_ref_known(v_name_4623_, 2);
v_a_4702_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4670_, 1);
v_a_4643_ = v_a_4702_;
goto v___jp_4642_;
}
v___jp_4665_:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4667_ = lean_st_ref_get(v___x_4664_);
lean_dec(v___x_4664_);
lean_dec(v___x_4667_);
v___x_4668_ = lean_box(v_a_4666_);
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4668_);
return v___x_4669_;
}
}
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; lean_object* v___y_4710_; uint8_t v___y_4711_; lean_object* v_a_4716_; uint8_t v___x_4719_; uint8_t v___x_4720_; uint8_t v___x_4721_; lean_object* v___x_4722_; uint64_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4703_ = lean_unsigned_to_nat(7u);
v___x_4704_ = lean_unsigned_to_nat(0u);
v___x_4705_ = lean_string_utf8_byte_size(v_str_4628_);
lean_inc_ref(v_str_4628_);
v___x_4706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4706_, 0, v_str_4628_);
lean_ctor_set(v___x_4706_, 1, v___x_4704_);
lean_ctor_set(v___x_4706_, 2, v___x_4705_);
v___x_4707_ = l_String_Slice_Pos_nextn(v___x_4706_, v___x_4704_, v___x_4703_);
lean_dec_ref_known(v___x_4706_, 3);
v___x_4708_ = 0;
v___x_4719_ = 1;
v___x_4720_ = 0;
v___x_4721_ = 2;
v___x_4722_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4722_, 0, v___x_4708_);
lean_ctor_set_uint8(v___x_4722_, 1, v___x_4708_);
lean_ctor_set_uint8(v___x_4722_, 2, v___x_4708_);
lean_ctor_set_uint8(v___x_4722_, 3, v___x_4708_);
lean_ctor_set_uint8(v___x_4722_, 4, v___x_4708_);
lean_ctor_set_uint8(v___x_4722_, 5, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 6, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 7, v___x_4708_);
lean_ctor_set_uint8(v___x_4722_, 8, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 9, v___x_4719_);
lean_ctor_set_uint8(v___x_4722_, 10, v___x_4720_);
lean_ctor_set_uint8(v___x_4722_, 11, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 12, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 13, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 14, v___x_4721_);
lean_ctor_set_uint8(v___x_4722_, 15, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 16, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 17, v___x_4635_);
lean_ctor_set_uint8(v___x_4722_, 18, v___x_4635_);
v___x_4723_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4722_);
v___x_4724_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4724_, 0, v___x_4722_);
lean_ctor_set_uint64(v___x_4724_, sizeof(void*)*1, v___x_4723_);
v___x_4725_ = lean_box(1);
v___x_4726_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4727_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4728_ = lean_box(0);
v___x_4729_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4729_, 0, v___x_4724_);
lean_ctor_set(v___x_4729_, 1, v___x_4725_);
lean_ctor_set(v___x_4729_, 2, v___x_4726_);
lean_ctor_set(v___x_4729_, 3, v___x_4727_);
lean_ctor_set(v___x_4729_, 4, v___x_4728_);
lean_ctor_set(v___x_4729_, 5, v___x_4704_);
lean_ctor_set(v___x_4729_, 6, v___x_4728_);
lean_ctor_set_uint8(v___x_4729_, sizeof(void*)*7, v___x_4708_);
lean_ctor_set_uint8(v___x_4729_, sizeof(void*)*7 + 1, v___x_4708_);
lean_ctor_set_uint8(v___x_4729_, sizeof(void*)*7 + 2, v___x_4708_);
lean_ctor_set_uint8(v___x_4729_, sizeof(void*)*7 + 3, v___x_4631_);
v___x_4730_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4731_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4732_ = lean_st_mk_ref(v___x_4731_);
lean_inc(v_pre_4627_);
v___x_4733_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4627_, v___x_4729_, v___x_4732_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
lean_inc_ref(v_str_4628_);
v___x_4735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4735_, 0, v_str_4628_);
lean_ctor_set(v___x_4735_, 1, v___x_4707_);
lean_ctor_set(v___x_4735_, 2, v___x_4705_);
v___x_4736_ = l_String_Slice_toNat_x21(v___x_4735_);
lean_dec_ref_known(v___x_4735_, 3);
v___x_4737_ = l_Lean_ConstantInfo_levelParams(v_a_4734_);
lean_dec(v_a_4734_);
v___x_4738_ = lean_box(0);
lean_inc(v___x_4737_);
v___x_4739_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4737_, v___x_4738_);
lean_inc(v_pre_4627_);
v___x_4740_ = l_Lean_mkConst(v_pre_4627_, v___x_4739_);
v___x_4741_ = l_Lean_Meta_mkHCongrWithArity(v___x_4740_, v___x_4736_, v___x_4729_, v___x_4732_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v_type_4743_; lean_object* v_proof_4744_; lean_object* v_argKinds_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4768_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4742_);
lean_dec_ref_known(v___x_4741_, 1);
v_type_4743_ = lean_ctor_get(v_a_4742_, 0);
v_proof_4744_ = lean_ctor_get(v_a_4742_, 1);
v_argKinds_4745_ = lean_ctor_get(v_a_4742_, 2);
v_isSharedCheck_4768_ = !lean_is_exclusive(v_a_4742_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4747_ = v_a_4742_;
v_isShared_4748_ = v_isSharedCheck_4768_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_argKinds_4745_);
lean_inc(v_proof_4744_);
lean_inc(v_type_4743_);
lean_dec(v_a_4742_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4768_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
lean_inc_ref(v_name_4623_);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 2, v_type_4743_);
lean_ctor_set(v___x_4747_, 1, v___x_4737_);
lean_ctor_set(v___x_4747_, 0, v_name_4623_);
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_name_4623_);
lean_ctor_set(v_reuseFailAlloc_4767_, 1, v___x_4737_);
lean_ctor_set(v_reuseFailAlloc_4767_, 2, v_type_4743_);
v___x_4750_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___f_4754_; lean_object* v___x_4755_; 
lean_inc_ref_n(v_name_4623_, 2);
v___x_4751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4751_, 0, v_name_4623_);
lean_ctor_set(v___x_4751_, 1, v___x_4738_);
v___x_4752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4750_);
lean_ctor_set(v___x_4752_, 1, v_proof_4744_);
lean_ctor_set(v___x_4752_, 2, v___x_4751_);
v___x_4753_ = lean_box(v___x_4708_);
v___f_4754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4754_, 0, v___x_4752_);
lean_closure_set(v___f_4754_, 1, v___x_4753_);
lean_closure_set(v___f_4754_, 2, v_name_4623_);
lean_closure_set(v___f_4754_, 3, v_argKinds_4745_);
lean_closure_set(v___f_4754_, 4, v___x_4730_);
v___x_4755_ = l_Lean_Meta_realizeConst(v_pre_4627_, v_name_4623_, v___f_4754_, v___x_4729_, v___x_4732_, v___y_4624_, v___y_4625_);
lean_dec_ref_known(v___x_4729_, 7);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4764_; 
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4764_ == 0)
{
lean_object* v_unused_4765_; 
v_unused_4765_ = lean_ctor_get(v___x_4755_, 0);
lean_dec(v_unused_4765_);
v___x_4757_ = v___x_4755_;
v_isShared_4758_ = v_isSharedCheck_4764_;
goto v_resetjp_4756_;
}
else
{
lean_dec(v___x_4755_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4764_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4762_; 
v___x_4759_ = lean_st_ref_get(v___x_4732_);
lean_dec(v___x_4732_);
lean_dec(v___x_4759_);
v___x_4760_ = lean_box(v___x_4631_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 0, v___x_4760_);
v___x_4762_ = v___x_4757_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4760_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
else
{
lean_object* v_a_4766_; 
lean_dec(v___x_4732_);
v_a_4766_ = lean_ctor_get(v___x_4755_, 0);
lean_inc(v_a_4766_);
lean_dec_ref_known(v___x_4755_, 1);
v_a_4716_ = v_a_4766_;
goto v___jp_4715_;
}
}
}
}
else
{
lean_object* v_a_4769_; 
lean_dec(v___x_4737_);
lean_dec(v___x_4732_);
lean_dec_ref_known(v___x_4729_, 7);
lean_dec_ref_known(v_name_4623_, 2);
lean_dec(v_pre_4627_);
v_a_4769_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v___x_4741_, 1);
v_a_4716_ = v_a_4769_;
goto v___jp_4715_;
}
}
else
{
lean_object* v_a_4770_; 
lean_dec(v___x_4732_);
lean_dec_ref_known(v___x_4729_, 7);
lean_dec(v___x_4707_);
lean_dec_ref_known(v_name_4623_, 2);
lean_dec(v_pre_4627_);
v_a_4770_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4770_);
lean_dec_ref_known(v___x_4733_, 1);
v_a_4716_ = v_a_4770_;
goto v___jp_4715_;
}
v___jp_4709_:
{
if (v___y_4711_ == 0)
{
lean_object* v___x_4712_; lean_object* v___x_4713_; 
lean_dec_ref(v___y_4710_);
v___x_4712_ = lean_box(v___x_4708_);
v___x_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4712_);
return v___x_4713_;
}
else
{
lean_object* v___x_4714_; 
v___x_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4714_, 0, v___y_4710_);
return v___x_4714_;
}
}
v___jp_4715_:
{
uint8_t v___x_4717_; 
v___x_4717_ = l_Lean_Exception_isInterrupt(v_a_4716_);
if (v___x_4717_ == 0)
{
uint8_t v___x_4718_; 
lean_inc_ref(v_a_4716_);
v___x_4718_ = l_Lean_Exception_isRuntime(v_a_4716_);
v___y_4710_ = v_a_4716_;
v___y_4711_ = v___x_4718_;
goto v___jp_4709_;
}
else
{
v___y_4710_ = v_a_4716_;
v___y_4711_ = v___x_4717_;
goto v___jp_4709_;
}
}
}
v___jp_4636_:
{
if (v___y_4638_ == 0)
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
lean_dec_ref(v___y_4637_);
v___x_4639_ = lean_box(v___x_4635_);
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
return v___x_4640_;
}
else
{
lean_object* v___x_4641_; 
v___x_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4641_, 0, v___y_4637_);
return v___x_4641_;
}
}
v___jp_4642_:
{
uint8_t v___x_4644_; 
v___x_4644_ = l_Lean_Exception_isInterrupt(v_a_4643_);
if (v___x_4644_ == 0)
{
uint8_t v___x_4645_; 
lean_inc_ref(v_a_4643_);
v___x_4645_ = l_Lean_Exception_isRuntime(v_a_4643_);
v___y_4637_ = v_a_4643_;
v___y_4638_ = v___x_4645_;
goto v___jp_4636_;
}
else
{
v___y_4637_ = v_a_4643_;
v___y_4638_ = v___x_4644_;
goto v___jp_4636_;
}
}
}
}
else
{
uint8_t v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
lean_dec(v_name_4623_);
v___x_4771_ = 0;
v___x_4772_ = lean_box(v___x_4771_);
v___x_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
return v___x_4773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_name_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4781_; lean_object* v___x_4782_; 
v___f_4781_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4782_ = l_Lean_registerReservedNameAction(v___f_4781_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_a_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* v_msg_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v___f_4791_; lean_object* v___x_1830__overap_4792_; lean_object* v___x_4793_; 
v___f_4791_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1830__overap_4792_ = lean_panic_fn_borrowed(v___f_4791_, v_msg_4785_);
lean_inc(v___y_4789_);
lean_inc_ref(v___y_4788_);
lean_inc(v___y_4787_);
lean_inc_ref(v___y_4786_);
v___x_4793_ = lean_apply_5(v___x_1830__overap_4792_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, lean_box(0));
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___y_4796_);
lean_dec_ref(v___y_4795_);
return v_res_4800_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4802_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4803_ = lean_unsigned_to_nat(8u);
v___x_4804_ = lean_unsigned_to_nat(461u);
v___x_4805_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0));
v___x_4806_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4807_ = l_mkPanicMessageWithDecl(v___x_4806_, v___x_4805_, v___x_4804_, v___x_4803_, v___x_4802_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* v_thmName_4808_, lean_object* v_levels_4809_, lean_object* v___x_4810_, lean_object* v_____r_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; 
lean_inc(v_thmName_4808_);
v___x_4817_ = l_Lean_mkConst(v_thmName_4808_, v_levels_4809_);
lean_inc(v___y_4815_);
lean_inc_ref(v___y_4814_);
lean_inc(v___y_4813_);
lean_inc_ref(v___y_4812_);
lean_inc_ref(v___x_4817_);
v___x_4818_ = lean_infer_type(v___x_4817_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4818_) == 0)
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4862_; 
v_a_4819_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4821_ = v___x_4818_;
v_isShared_4822_ = v_isSharedCheck_4862_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4818_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4862_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4823_; lean_object* v_env_4824_; lean_object* v___x_4825_; lean_object* v_toEnvExtension_4826_; lean_object* v_asyncMode_4827_; uint8_t v___x_4828_; lean_object* v___x_4829_; 
v___x_4823_ = lean_st_ref_get(v___y_4815_);
v_env_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc_ref(v_env_4824_);
lean_dec(v___x_4823_);
v___x_4825_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4826_ = lean_ctor_get(v___x_4825_, 0);
v_asyncMode_4827_ = lean_ctor_get(v_toEnvExtension_4826_, 2);
v___x_4828_ = 0;
v___x_4829_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4810_, v___x_4825_, v_env_4824_, v_thmName_4808_, v_asyncMode_4827_, v___x_4828_);
if (lean_obj_tag(v___x_4829_) == 1)
{
lean_object* v_val_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4842_; 
v_val_4830_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4832_ = v___x_4829_;
v_isShared_4833_ = v_isSharedCheck_4842_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_val_4830_);
lean_dec(v___x_4829_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4842_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4834_; lean_object* v___x_4836_; 
v___x_4834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4834_, 0, v_a_4819_);
lean_ctor_set(v___x_4834_, 1, v___x_4817_);
lean_ctor_set(v___x_4834_, 2, v_val_4830_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 0, v___x_4834_);
v___x_4836_ = v___x_4832_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4834_);
v___x_4836_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v___x_4837_);
v___x_4839_ = v___x_4821_;
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
}
else
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
lean_dec(v___x_4829_);
lean_del_object(v___x_4821_);
lean_dec(v_a_4819_);
lean_dec_ref(v___x_4817_);
v___x_4843_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1);
v___x_4844_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4843_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4853_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4847_ = v___x_4844_;
v_isShared_4848_ = v_isSharedCheck_4853_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4844_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4853_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4849_; lean_object* v___x_4851_; 
v___x_4849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4849_, 0, v_a_4845_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4849_);
v___x_4851_ = v___x_4847_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
v_a_4854_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4844_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4844_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
}
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
lean_dec_ref(v___x_4817_);
lean_dec_ref(v___x_4810_);
lean_dec(v_thmName_4808_);
v_a_4863_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4818_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4818_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* v_thmName_4871_, lean_object* v_levels_4872_, lean_object* v___x_4873_, lean_object* v_____r_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4871_, v_levels_4872_, v___x_4873_, v_____r_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
return v_res_4880_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0(void){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = l_Array_instInhabited(lean_box(0));
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* v_declName_4882_, lean_object* v_levels_4883_, lean_object* v_numArgs_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_){
_start:
{
lean_object* v___y_4891_; uint8_t v___y_4892_; lean_object* v_a_4897_; lean_object* v___y_4901_; lean_object* v___x_4912_; lean_object* v_env_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v_suffix_4917_; lean_object* v_thmName_4918_; uint8_t v___x_4919_; 
v___x_4912_ = lean_st_ref_get(v_a_4888_);
v_env_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc_ref(v_env_4913_);
lean_dec(v___x_4912_);
v___x_4914_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_4915_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4916_ = l_Nat_reprFast(v_numArgs_4884_);
v_suffix_4917_ = lean_string_append(v___x_4915_, v___x_4916_);
lean_dec_ref(v___x_4916_);
v_thmName_4918_ = l_Lean_Name_str___override(v_declName_4882_, v_suffix_4917_);
v___x_4919_ = l_Lean_Environment_containsOnBranch(v_env_4913_, v_thmName_4918_);
lean_dec_ref(v_env_4913_);
if (v___x_4919_ == 0)
{
lean_object* v___x_4920_; 
lean_inc(v_thmName_4918_);
v___x_4920_ = l_Lean_executeReservedNameAction(v_thmName_4918_, v_a_4887_, v_a_4888_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v___x_4921_; lean_object* v___x_4922_; 
lean_dec_ref_known(v___x_4920_, 1);
v___x_4921_ = lean_box(0);
v___x_4922_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4918_, v_levels_4883_, v___x_4914_, v___x_4921_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_);
v___y_4901_ = v___x_4922_;
goto v___jp_4900_;
}
else
{
lean_object* v_a_4923_; 
lean_dec(v_thmName_4918_);
lean_dec(v_levels_4883_);
v_a_4923_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4923_);
lean_dec_ref_known(v___x_4920_, 1);
v_a_4897_ = v_a_4923_;
goto v___jp_4896_;
}
}
else
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = lean_box(0);
v___x_4925_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4918_, v_levels_4883_, v___x_4914_, v___x_4924_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_);
v___y_4901_ = v___x_4925_;
goto v___jp_4900_;
}
v___jp_4890_:
{
if (v___y_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
lean_dec_ref(v___y_4891_);
v___x_4893_ = lean_box(0);
v___x_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4893_);
return v___x_4894_;
}
else
{
lean_object* v___x_4895_; 
v___x_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4895_, 0, v___y_4891_);
return v___x_4895_;
}
}
v___jp_4896_:
{
uint8_t v___x_4898_; 
v___x_4898_ = l_Lean_Exception_isInterrupt(v_a_4897_);
if (v___x_4898_ == 0)
{
uint8_t v___x_4899_; 
lean_inc_ref(v_a_4897_);
v___x_4899_ = l_Lean_Exception_isRuntime(v_a_4897_);
v___y_4891_ = v_a_4897_;
v___y_4892_ = v___x_4899_;
goto v___jp_4890_;
}
else
{
v___y_4891_ = v_a_4897_;
v___y_4892_ = v___x_4898_;
goto v___jp_4890_;
}
}
v___jp_4900_:
{
if (lean_obj_tag(v___y_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4910_; 
v_a_4902_ = lean_ctor_get(v___y_4901_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___y_4901_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4904_ = v___y_4901_;
v_isShared_4905_ = v_isSharedCheck_4910_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___y_4901_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4910_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v_a_4906_; lean_object* v___x_4908_; 
v_a_4906_ = lean_ctor_get(v_a_4902_, 0);
lean_inc(v_a_4906_);
lean_dec(v_a_4902_);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 0, v_a_4906_);
v___x_4908_ = v___x_4904_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4906_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
else
{
lean_object* v_a_4911_; 
v_a_4911_ = lean_ctor_get(v___y_4901_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___y_4901_, 1);
v_a_4897_ = v_a_4911_;
goto v___jp_4896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object* v_declName_4926_, lean_object* v_levels_4927_, lean_object* v_numArgs_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_4926_, v_levels_4927_, v_numArgs_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* v_____r_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4943_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0));
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* v_____r_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec(v___y_4947_);
lean_dec_ref(v___y_4946_);
return v_res_4951_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4953_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4954_ = lean_unsigned_to_nat(8u);
v___x_4955_ = lean_unsigned_to_nat(478u);
v___x_4956_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0));
v___x_4957_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4958_ = l_mkPanicMessageWithDecl(v___x_4957_, v___x_4956_, v___x_4955_, v___x_4954_, v___x_4953_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object* v_thmName_4959_, lean_object* v_levels_4960_, lean_object* v___x_4961_, lean_object* v_____r_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_inc(v_thmName_4959_);
v___x_4968_ = l_Lean_mkConst(v_thmName_4959_, v_levels_4960_);
lean_inc(v___y_4966_);
lean_inc_ref(v___y_4965_);
lean_inc(v___y_4964_);
lean_inc_ref(v___y_4963_);
lean_inc_ref(v___x_4968_);
v___x_4969_ = lean_infer_type(v___x_4968_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_5013_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_4972_ = v___x_4969_;
v_isShared_4973_ = v_isSharedCheck_5013_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4969_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_5013_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; lean_object* v_env_4975_; lean_object* v___x_4976_; lean_object* v_toEnvExtension_4977_; lean_object* v_asyncMode_4978_; uint8_t v___x_4979_; lean_object* v___x_4980_; 
v___x_4974_ = lean_st_ref_get(v___y_4966_);
v_env_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc_ref(v_env_4975_);
lean_dec(v___x_4974_);
v___x_4976_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4977_ = lean_ctor_get(v___x_4976_, 0);
v_asyncMode_4978_ = lean_ctor_get(v_toEnvExtension_4977_, 2);
v___x_4979_ = 0;
v___x_4980_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4961_, v___x_4976_, v_env_4975_, v_thmName_4959_, v_asyncMode_4978_, v___x_4979_);
if (lean_obj_tag(v___x_4980_) == 1)
{
lean_object* v_val_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4993_; 
v_val_4981_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4983_ = v___x_4980_;
v_isShared_4984_ = v_isSharedCheck_4993_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_val_4981_);
lean_dec(v___x_4980_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4993_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4985_; lean_object* v___x_4987_; 
v___x_4985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4985_, 0, v_a_4970_);
lean_ctor_set(v___x_4985_, 1, v___x_4968_);
lean_ctor_set(v___x_4985_, 2, v_val_4981_);
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 0, v___x_4985_);
v___x_4987_ = v___x_4983_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; lean_object* v___x_4990_; 
v___x_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4987_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set(v___x_4972_, 0, v___x_4988_);
v___x_4990_ = v___x_4972_;
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
}
else
{
lean_object* v___x_4994_; lean_object* v___x_4995_; 
lean_dec(v___x_4980_);
lean_del_object(v___x_4972_);
lean_dec(v_a_4970_);
lean_dec_ref(v___x_4968_);
v___x_4994_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1);
v___x_4995_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4994_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5004_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4998_ = v___x_4995_;
v_isShared_4999_ = v_isSharedCheck_5004_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4995_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5004_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5000_; lean_object* v___x_5002_; 
v___x_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5000_, 0, v_a_4996_);
if (v_isShared_4999_ == 0)
{
lean_ctor_set(v___x_4998_, 0, v___x_5000_);
v___x_5002_ = v___x_4998_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_5000_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
v_a_5005_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4995_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4995_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
}
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_dec_ref(v___x_4968_);
lean_dec_ref(v___x_4961_);
lean_dec(v_thmName_4959_);
v_a_5014_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_4969_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_4969_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object* v_thmName_5022_, lean_object* v_levels_5023_, lean_object* v___x_5024_, lean_object* v_____r_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5022_, v_levels_5023_, v___x_5024_, v_____r_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
lean_dec(v___y_5027_);
lean_dec_ref(v___y_5026_);
return v_res_5031_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1(void){
_start:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5033_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0));
v___x_5034_ = l_Lean_stringToMessageData(v___x_5033_);
return v___x_5034_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3(void){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5036_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2));
v___x_5037_ = l_Lean_stringToMessageData(v___x_5036_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* v_declName_5038_, lean_object* v_levels_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v_a_5046_; lean_object* v___y_5064_; lean_object* v___x_5066_; lean_object* v_env_5067_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v_thmName_5073_; lean_object* v___y_5075_; uint8_t v___y_5076_; lean_object* v_a_5103_; lean_object* v___y_5107_; uint8_t v___x_5110_; 
v___x_5066_ = lean_st_ref_get(v_a_5043_);
v_env_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc_ref(v_env_5067_);
lean_dec(v___x_5066_);
v___x_5071_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_5072_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v_thmName_5073_ = l_Lean_Name_str___override(v_declName_5038_, v___x_5072_);
v___x_5110_ = l_Lean_Environment_containsOnBranch(v_env_5067_, v_thmName_5073_);
lean_dec_ref(v_env_5067_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; 
lean_inc(v_thmName_5073_);
v___x_5111_ = l_Lean_executeReservedNameAction(v_thmName_5073_, v_a_5042_, v_a_5043_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v___x_5112_; lean_object* v___x_5113_; 
lean_dec_ref_known(v___x_5111_, 1);
v___x_5112_ = lean_box(0);
lean_inc(v_thmName_5073_);
v___x_5113_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5073_, v_levels_5039_, v___x_5071_, v___x_5112_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_);
v___y_5107_ = v___x_5113_;
goto v___jp_5106_;
}
else
{
lean_object* v_a_5114_; 
lean_dec(v_levels_5039_);
v_a_5114_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5114_);
lean_dec_ref_known(v___x_5111_, 1);
v_a_5103_ = v_a_5114_;
goto v___jp_5102_;
}
}
else
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5115_ = lean_box(0);
lean_inc(v_thmName_5073_);
v___x_5116_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5073_, v_levels_5039_, v___x_5071_, v___x_5115_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_);
v___y_5107_ = v___x_5116_;
goto v___jp_5106_;
}
v___jp_5045_:
{
if (lean_obj_tag(v_a_5046_) == 0)
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
v_a_5047_ = lean_ctor_get(v_a_5046_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v_a_5046_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v_a_5046_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v_a_5046_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
else
{
lean_object* v_a_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5062_; 
v_a_5055_ = lean_ctor_get(v_a_5046_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v_a_5046_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5057_ = v_a_5046_;
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_a_5055_);
lean_dec(v_a_5046_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5060_; 
if (v_isShared_5058_ == 0)
{
lean_ctor_set_tag(v___x_5057_, 0);
v___x_5060_ = v___x_5057_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5055_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
}
v___jp_5063_:
{
lean_object* v_a_5065_; 
v_a_5065_ = lean_ctor_get(v___y_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref(v___y_5064_);
v_a_5046_ = v_a_5065_;
goto v___jp_5045_;
}
v___jp_5068_:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = lean_box(0);
v___x_5070_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v___x_5069_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_);
v___y_5064_ = v___x_5070_;
goto v___jp_5063_;
}
v___jp_5074_:
{
if (v___y_5076_ == 0)
{
lean_object* v_options_5077_; uint8_t v_hasTrace_5078_; 
v_options_5077_ = lean_ctor_get(v_a_5042_, 2);
v_hasTrace_5078_ = lean_ctor_get_uint8(v_options_5077_, sizeof(void*)*1);
if (v_hasTrace_5078_ == 0)
{
lean_dec_ref(v___y_5075_);
lean_dec(v_thmName_5073_);
goto v___jp_5068_;
}
else
{
lean_object* v_inheritedTraceOptions_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; uint8_t v___x_5082_; 
v_inheritedTraceOptions_5079_ = lean_ctor_get(v_a_5042_, 13);
v___x_5080_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_5081_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_5082_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5079_, v_options_5077_, v___x_5081_);
if (v___x_5082_ == 0)
{
lean_dec_ref(v___y_5075_);
lean_dec(v_thmName_5073_);
goto v___jp_5068_;
}
else
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v___x_5083_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1);
v___x_5084_ = l_Lean_MessageData_ofName(v_thmName_5073_);
v___x_5085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5083_);
lean_ctor_set(v___x_5085_, 1, v___x_5084_);
v___x_5086_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3);
v___x_5087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5087_, 0, v___x_5085_);
lean_ctor_set(v___x_5087_, 1, v___x_5086_);
v___x_5088_ = l_Lean_Exception_toMessageData(v___y_5075_);
v___x_5089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5087_);
lean_ctor_set(v___x_5089_, 1, v___x_5088_);
v___x_5090_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_5080_, v___x_5089_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_object* v_a_5091_; lean_object* v___x_5092_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_a_5091_);
lean_dec_ref_known(v___x_5090_, 1);
v___x_5092_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_a_5091_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_);
v___y_5064_ = v___x_5092_;
goto v___jp_5063_;
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
v_a_5093_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5090_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5090_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
}
}
else
{
lean_object* v___x_5101_; 
lean_dec(v_thmName_5073_);
v___x_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5101_, 0, v___y_5075_);
return v___x_5101_;
}
}
v___jp_5102_:
{
uint8_t v___x_5104_; 
v___x_5104_ = l_Lean_Exception_isInterrupt(v_a_5103_);
if (v___x_5104_ == 0)
{
uint8_t v___x_5105_; 
lean_inc_ref(v_a_5103_);
v___x_5105_ = l_Lean_Exception_isRuntime(v_a_5103_);
v___y_5075_ = v_a_5103_;
v___y_5076_ = v___x_5105_;
goto v___jp_5074_;
}
else
{
v___y_5075_ = v_a_5103_;
v___y_5076_ = v___x_5104_;
goto v___jp_5074_;
}
}
v___jp_5106_:
{
if (lean_obj_tag(v___y_5107_) == 0)
{
lean_object* v_a_5108_; 
lean_dec(v_thmName_5073_);
v_a_5108_ = lean_ctor_get(v___y_5107_, 0);
lean_inc(v_a_5108_);
lean_dec_ref_known(v___y_5107_, 1);
v_a_5046_ = v_a_5108_;
goto v___jp_5045_;
}
else
{
lean_object* v_a_5109_; 
v_a_5109_ = lean_ctor_get(v___y_5107_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___y_5107_, 1);
v_a_5103_ = v_a_5109_;
goto v___jp_5102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object* v_declName_5117_, lean_object* v_levels_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_5117_, v_levels_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5121_);
lean_dec(v_a_5120_);
lean_dec_ref(v_a_5119_);
return v_res_5124_;
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
