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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
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
LEAN_EXPORT uint8_t l_Lean_Meta_isCongrReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isCongrReservedNameSuffix___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_isCongrReservedNameSuffix___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.mkHCongrWithArityForConst\?"};
static const lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v_a_413_);
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
lean_dec(v_a_416_);
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
uint8_t v___x_4565__boxed_1093_; uint8_t v___x_4566__boxed_1094_; lean_object* v_res_1095_; 
v___x_4565__boxed_1093_ = lean_unbox(v___x_1084_);
v___x_4566__boxed_1094_ = lean_unbox(v___x_1085_);
v_res_1095_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1081_, v_xs_1082_, v_f_1083_, v___x_4565__boxed_1093_, v___x_4566__boxed_1094_, v_eqs_1086_, v_argKinds_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
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
size_t v___x_1349_; size_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1347_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1345_, v_as_1344_, v___x_1349_, v___x_1350_);
return v___x_1351_;
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
uint8_t v___x_5309__boxed_1705_; lean_object* v_res_1706_; 
v___x_5309__boxed_1705_ = lean_unbox(v___x_1698_);
v_res_1706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1693_, v_val_1694_, v_xs_1695_, v___x_1696_, v___x_1697_, v___x_5309__boxed_1705_, v_a_1699_, v_b_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
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
uint8_t v___x_5396__boxed_1752_; lean_object* v_res_1753_; 
v___x_5396__boxed_1752_ = lean_unbox(v___x_1744_);
v_res_1753_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1742_, v_induct_1743_, v___x_5396__boxed_1752_, v_xs_1745_, v_x_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__20));
v___x_1796_ = l_Lean_stringToMessageData(v___x_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__22));
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__24));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__26));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1806_, lean_object* v_declHint_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v_env_1812_; uint8_t v___x_1813_; 
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_st_ref_get(v___y_1808_);
v_env_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc_ref(v_env_1812_);
lean_dec(v___x_1811_);
v___x_1813_ = l_Lean_Name_isAnonymous(v_declHint_1807_);
if (v___x_1813_ == 0)
{
uint8_t v_isExporting_1814_; 
v_isExporting_1814_ = lean_ctor_get_uint8(v_env_1812_, sizeof(void*)*13);
if (v_isExporting_1814_ == 0)
{
lean_object* v___x_1815_; 
lean_dec_ref(v_env_1812_);
lean_dec(v_declHint_1807_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_msg_1806_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
lean_inc_ref(v_env_1812_);
v___x_1816_ = l_Lean_Environment_setExporting(v_env_1812_, v___x_1813_);
lean_inc(v_declHint_1807_);
lean_inc_ref(v___x_1816_);
v___x_1817_ = l_Lean_Environment_contains(v___x_1816_, v_declHint_1807_, v_isExporting_1814_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec_ref(v___x_1816_);
lean_dec_ref(v_env_1812_);
lean_dec(v_declHint_1807_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_msg_1806_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_c_1824_; lean_object* v___x_1825_; 
v___x_1819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1820_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1821_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1816_);
v___x_1822_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1816_);
lean_ctor_set(v___x_1822_, 1, v___x_1819_);
lean_ctor_set(v___x_1822_, 2, v___x_1820_);
lean_ctor_set(v___x_1822_, 3, v___x_1821_);
lean_inc(v_declHint_1807_);
v___x_1823_ = l_Lean_MessageData_ofConstName(v_declHint_1807_, v___x_1813_);
v_c_1824_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1824_, 0, v___x_1822_);
lean_ctor_set(v_c_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1816_, v_declHint_1807_);
lean_dec_ref(v___x_1816_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v_env_1812_);
lean_dec(v_declHint_1807_);
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
lean_ctor_set(v___x_1831_, 0, v_msg_1806_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
else
{
lean_object* v_val_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1886_; 
v_val_1833_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1835_ = v___x_1825_;
v_isShared_1836_ = v_isSharedCheck_1886_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_val_1833_);
lean_dec(v___x_1825_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1886_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v_modules_1838_; lean_object* v_moduleNames_1839_; lean_object* v_mod_1840_; uint8_t v___x_1855_; 
v___x_1837_ = l_Lean_Environment_header(v_env_1812_);
lean_dec_ref(v_env_1812_);
v_modules_1838_ = lean_ctor_get(v___x_1837_, 3);
lean_inc_ref(v_modules_1838_);
v_moduleNames_1839_ = lean_ctor_get(v___x_1837_, 4);
lean_inc_ref(v_moduleNames_1839_);
lean_dec_ref(v___x_1837_);
v_mod_1840_ = lean_array_get(v___x_1810_, v_moduleNames_1839_, v_val_1833_);
lean_dec_ref(v_moduleNames_1839_);
v___x_1855_ = l_Lean_isPrivateName(v_declHint_1807_);
lean_dec(v_declHint_1807_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = lean_array_get_size(v_modules_1838_);
v___x_1857_ = lean_nat_dec_lt(v_val_1833_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_dec_ref(v_modules_1838_);
lean_dec(v_val_1833_);
goto v___jp_1841_;
}
else
{
lean_object* v___x_1858_; lean_object* v_toImport_1859_; uint8_t v_isExported_1860_; 
v___x_1858_ = lean_array_fget(v_modules_1838_, v_val_1833_);
lean_dec(v_val_1833_);
lean_dec_ref(v_modules_1838_);
v_toImport_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc_ref(v_toImport_1859_);
lean_dec(v___x_1858_);
v_isExported_1860_ = lean_ctor_get_uint8(v_toImport_1859_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1859_);
if (v_isExported_1860_ == 0)
{
goto v___jp_1841_;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_del_object(v___x_1835_);
v___x_1861_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v_c_1824_);
v___x_1863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Lean_MessageData_ofName(v_mod_1840_);
lean_inc_ref(v___x_1865_);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v___x_1865_);
v___x_1870_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = l_Lean_MessageData_note(v___x_1871_);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_msg_1806_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v_modules_1838_);
lean_del_object(v___x_1835_);
lean_dec(v_val_1833_);
v___x_1875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_c_1824_);
v___x_1877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_MessageData_ofName(v_mod_1840_);
v___x_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lean_MessageData_note(v___x_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_msg_1806_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
v___jp_1841_:
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
lean_ctor_set(v___x_1851_, 0, v_msg_1806_);
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
}
}
}
}
}
else
{
lean_object* v___x_1887_; 
lean_dec_ref(v_env_1812_);
lean_dec(v_declHint_1807_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_msg_1806_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1888_, lean_object* v_declHint_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1888_, v_declHint_1889_, v___y_1890_);
lean_dec(v___y_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msg_1893_, lean_object* v_declHint_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1910_; 
v___x_1900_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1893_, v_declHint_1894_, v___y_1898_);
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1910_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1910_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = l_Lean_unknownIdentifierMessageTag;
v___x_1906_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v_a_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1906_);
v___x_1908_ = v___x_1903_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1911_, lean_object* v_declHint_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1911_, v_declHint_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1919_, lean_object* v_msg_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_toCold_1926_; lean_object* v_currRecDepth_1927_; lean_object* v_ref_1928_; uint16_t v_optionFlags_1929_; uint8_t v_suppressElabErrors_1930_; uint8_t v_checkDeprecated_1931_; uint8_t v_isRecordingDeps_1932_; lean_object* v_ref_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_toCold_1926_ = lean_ctor_get(v___y_1923_, 0);
v_currRecDepth_1927_ = lean_ctor_get(v___y_1923_, 1);
v_ref_1928_ = lean_ctor_get(v___y_1923_, 2);
v_optionFlags_1929_ = lean_ctor_get_uint16(v___y_1923_, sizeof(void*)*3);
v_suppressElabErrors_1930_ = lean_ctor_get_uint8(v___y_1923_, sizeof(void*)*3 + 2);
v_checkDeprecated_1931_ = lean_ctor_get_uint8(v___y_1923_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1932_ = lean_ctor_get_uint8(v___y_1923_, sizeof(void*)*3 + 4);
v_ref_1933_ = l_Lean_replaceRef(v_ref_1919_, v_ref_1928_);
lean_inc(v_currRecDepth_1927_);
lean_inc_ref(v_toCold_1926_);
v___x_1934_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1934_, 0, v_toCold_1926_);
lean_ctor_set(v___x_1934_, 1, v_currRecDepth_1927_);
lean_ctor_set(v___x_1934_, 2, v_ref_1933_);
lean_ctor_set_uint16(v___x_1934_, sizeof(void*)*3, v_optionFlags_1929_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*3 + 2, v_suppressElabErrors_1930_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*3 + 3, v_checkDeprecated_1931_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*3 + 4, v_isRecordingDeps_1932_);
v___x_1935_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1920_, v___y_1921_, v___y_1922_, v___x_1934_, v___y_1924_);
lean_dec_ref_known(v___x_1934_, 3);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1936_, lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1936_, v_msg_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v_ref_1936_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_1944_, lean_object* v_msg_1945_, lean_object* v_declHint_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; lean_object* v_a_1953_; lean_object* v___x_1954_; 
v___x_1952_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1945_, v_declHint_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1944_, v_a_1953_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1955_, lean_object* v_msg_1956_, lean_object* v_declHint_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1955_, v_msg_1956_, v_declHint_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_ref_1955_);
return v_res_1963_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1970_, lean_object* v_constName_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1977_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1978_ = 0;
lean_inc(v_constName_1971_);
v___x_1979_ = l_Lean_MessageData_ofConstName(v_constName_1971_, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1977_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1970_, v___x_1982_, v_constName_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1984_, lean_object* v_constName_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1984_, v_constName_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v_ref_1984_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_ref_1998_; lean_object* v___x_1999_; 
v_ref_1998_ = lean_ctor_get(v___y_1995_, 2);
v___x_1999_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1998_, v_constName_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v_env_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2013_ = lean_st_ref_get(v___y_2011_);
v_env_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_ref(v_env_2014_);
lean_dec(v___x_2013_);
v___x_2015_ = 0;
lean_inc(v_constName_2007_);
v___x_2016_ = l_Lean_Environment_find_x3f(v_env_2014_, v_constName_2007_, v___x_2015_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v___x_2017_;
}
else
{
lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_constName_2007_);
v_val_2018_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2016_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 0);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_val_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
if (lean_obj_tag(v_f_2033_) == 4)
{
lean_object* v_declName_2039_; lean_object* v___x_2040_; 
v_declName_2039_ = lean_ctor_get(v_f_2033_, 0);
lean_inc(v_declName_2039_);
lean_dec_ref_known(v_f_2033_, 2);
v___x_2040_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2039_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2064_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2064_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2064_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
if (lean_obj_tag(v_a_2041_) == 6)
{
lean_object* v_val_2045_; lean_object* v___x_2046_; lean_object* v_env_2047_; lean_object* v_toConstantVal_2048_; lean_object* v_induct_2049_; uint8_t v___x_2050_; 
v_val_2045_ = lean_ctor_get(v_a_2041_, 0);
lean_inc_ref(v_val_2045_);
lean_dec_ref_known(v_a_2041_, 1);
v___x_2046_ = lean_st_ref_get(v_a_2037_);
v_env_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_ref(v_env_2047_);
lean_dec(v___x_2046_);
v_toConstantVal_2048_ = lean_ctor_get(v_val_2045_, 0);
v_induct_2049_ = lean_ctor_get(v_val_2045_, 1);
lean_inc(v_induct_2049_);
v___x_2050_ = l_Lean_isClass(v_env_2047_, v_induct_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
lean_dec(v_induct_2049_);
lean_dec_ref(v_val_2045_);
v___x_2051_ = lean_box(0);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2051_);
v___x_2053_ = v___x_2043_;
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
else
{
lean_object* v_type_2055_; lean_object* v___x_2056_; lean_object* v___f_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; 
lean_del_object(v___x_2043_);
v_type_2055_ = lean_ctor_get(v_toConstantVal_2048_, 2);
lean_inc_ref(v_type_2055_);
v___x_2056_ = lean_box(v___x_2050_);
v___f_2057_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2057_, 0, v_val_2045_);
lean_closure_set(v___f_2057_, 1, v_induct_2049_);
lean_closure_set(v___f_2057_, 2, v___x_2056_);
v___x_2058_ = 0;
v___x_2059_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2055_, v___f_2057_, v___x_2050_, v___x_2058_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
return v___x_2059_;
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_dec(v_a_2041_);
v___x_2060_ = lean_box(0);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2060_);
v___x_2062_ = v___x_2043_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_a_2065_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2040_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2040_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_dec_ref(v_f_2033_);
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2082_, lean_object* v_val_2083_, lean_object* v_xs_2084_, lean_object* v___x_2085_, lean_object* v___x_2086_, uint8_t v___x_2087_, lean_object* v_inst_2088_, lean_object* v_R_2089_, lean_object* v_a_2090_, lean_object* v_b_2091_, lean_object* v_c_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2082_, v_val_2083_, v_xs_2084_, v___x_2085_, v___x_2086_, v___x_2087_, v_a_2090_, v_b_2091_, v___y_2093_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2099_, lean_object* v_val_2100_, lean_object* v_xs_2101_, lean_object* v___x_2102_, lean_object* v___x_2103_, lean_object* v___x_2104_, lean_object* v_inst_2105_, lean_object* v_R_2106_, lean_object* v_a_2107_, lean_object* v_b_2108_, lean_object* v_c_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
uint8_t v___x_6044__boxed_2115_; lean_object* v_res_2116_; 
v___x_6044__boxed_2115_ = lean_unbox(v___x_2104_);
v_res_2116_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2099_, v_val_2100_, v_xs_2101_, v___x_2102_, v___x_2103_, v___x_6044__boxed_2115_, v_inst_2105_, v_R_2106_, v_a_2107_, v_b_2108_, v_c_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec_ref(v_xs_2101_);
lean_dec_ref(v_val_2100_);
lean_dec(v_upperBound_2099_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2117_, lean_object* v_constName_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2125_, lean_object* v_constName_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2125_, v_constName_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2133_, lean_object* v_ref_2134_, lean_object* v_constName_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2134_, v_constName_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_ref_2143_, lean_object* v_constName_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2142_, v_ref_2143_, v_constName_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v_ref_2143_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2151_, lean_object* v_ref_2152_, lean_object* v_msg_2153_, lean_object* v_declHint_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2152_, v_msg_2153_, v_declHint_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_ref_2162_, lean_object* v_msg_2163_, lean_object* v_declHint_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2161_, v_ref_2162_, v_msg_2163_, v_declHint_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v_ref_2162_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2171_, lean_object* v_declHint_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2171_, v_declHint_2172_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2179_, lean_object* v_declHint_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2179_, v_declHint_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2187_, lean_object* v_ref_2188_, lean_object* v_msg_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2188_, v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_ref_2197_, lean_object* v_msg_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2196_, v_ref_2197_, v_msg_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v_ref_2197_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2205_, lean_object* v_a_2206_, lean_object* v_____r_2207_, lean_object* v_result_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
uint8_t v___x_2214_; 
v___x_2214_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2205_, v_result_2208_, v_a_2206_);
if (v___x_2214_ == 0)
{
uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2215_ = 0;
v___x_2216_ = lean_box(v___x_2215_);
v___x_2217_ = lean_array_push(v_result_2208_, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
return v___x_2219_;
}
else
{
uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2220_ = 5;
v___x_2221_ = lean_box(v___x_2220_);
v___x_2222_ = lean_array_push(v_result_2208_, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2225_, lean_object* v_a_2226_, lean_object* v_____r_2227_, lean_object* v_result_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2225_, v_a_2226_, v_____r_2227_, v_result_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v_a_2226_);
lean_dec_ref(v_info_2225_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2235_, lean_object* v_upperBound_2236_, lean_object* v___x_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_b_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_a_2247_; lean_object* v___y_2252_; uint8_t v___x_2271_; 
v___x_2271_ = lean_nat_dec_lt(v_a_2239_, v_upperBound_2236_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
lean_dec(v_a_2239_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_b_2240_);
return v___x_2272_;
}
else
{
lean_object* v_resultDeps_2273_; uint8_t v___x_2274_; 
v_resultDeps_2273_ = lean_ctor_get(v_info_2235_, 1);
v___x_2274_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2273_, v_a_2239_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; uint8_t v_isProp_2276_; 
v___x_2275_ = lean_array_fget_borrowed(v___x_2237_, v_a_2239_);
v_isProp_2276_ = lean_ctor_get_uint8(v___x_2275_, sizeof(void*)*1 + 2);
if (v_isProp_2276_ == 0)
{
uint8_t v_isInstance_2277_; 
v_isInstance_2277_ = lean_ctor_get_uint8(v___x_2275_, sizeof(void*)*1 + 4);
if (v_isInstance_2277_ == 0)
{
uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = 2;
v___x_2279_ = lean_box(v___x_2278_);
v___x_2280_ = lean_array_push(v_b_2240_, v___x_2279_);
v_a_2247_ = v___x_2280_;
goto v___jp_2246_;
}
else
{
if (lean_obj_tag(v_a_2238_) == 1)
{
lean_object* v_val_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_val_2281_ = lean_ctor_get(v_a_2238_, 0);
v___x_2282_ = lean_array_get_size(v_val_2281_);
v___x_2283_ = lean_nat_dec_lt(v_a_2239_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2235_, v_a_2239_, v___x_2284_, v_b_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
v___y_2252_ = v___x_2285_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = lean_array_fget_borrowed(v_val_2281_, v_a_2239_);
v___x_2287_ = lean_unbox(v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2235_, v_a_2239_, v___x_2288_, v_b_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
v___y_2252_ = v___x_2289_;
goto v___jp_2251_;
}
else
{
uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = 2;
v___x_2291_ = lean_box(v___x_2290_);
v___x_2292_ = lean_array_push(v_b_2240_, v___x_2291_);
v_a_2247_ = v___x_2292_;
goto v___jp_2246_;
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_box(0);
v___x_2294_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2235_, v_a_2239_, v___x_2293_, v_b_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
v___y_2252_ = v___x_2294_;
goto v___jp_2251_;
}
}
}
else
{
uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = 3;
v___x_2296_ = lean_box(v___x_2295_);
v___x_2297_ = lean_array_push(v_b_2240_, v___x_2296_);
v_a_2247_ = v___x_2297_;
goto v___jp_2246_;
}
}
else
{
uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = 0;
v___x_2299_ = lean_box(v___x_2298_);
v___x_2300_ = lean_array_push(v_b_2240_, v___x_2299_);
v_a_2247_ = v___x_2300_;
goto v___jp_2246_;
}
}
v___jp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_add(v_a_2239_, v___x_2248_);
lean_dec(v_a_2239_);
v_a_2239_ = v___x_2249_;
v_b_2240_ = v_a_2247_;
goto _start;
}
v___jp_2251_:
{
if (lean_obj_tag(v___y_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2262_; 
v_a_2253_ = lean_ctor_get(v___y_2252_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___y_2252_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2255_ = v___y_2252_;
v_isShared_2256_ = v_isSharedCheck_2262_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___y_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2262_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
if (lean_obj_tag(v_a_2253_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; 
lean_dec(v_a_2239_);
v_a_2257_ = lean_ctor_get(v_a_2253_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v_a_2253_, 1);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v_a_2257_);
v___x_2259_ = v___x_2255_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
else
{
lean_object* v_a_2261_; 
lean_del_object(v___x_2255_);
v_a_2261_ = lean_ctor_get(v_a_2253_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v_a_2253_, 1);
v_a_2247_ = v_a_2261_;
goto v___jp_2246_;
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2239_);
v_a_2263_ = lean_ctor_get(v___y_2252_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___y_2252_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___y_2252_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___y_2252_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2301_, lean_object* v_upperBound_2302_, lean_object* v___x_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_b_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2301_, v_upperBound_2302_, v___x_2303_, v_a_2304_, v_a_2305_, v_b_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v_a_2304_);
lean_dec_ref(v___x_2303_);
lean_dec(v_upperBound_2302_);
lean_dec_ref(v_info_2301_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2315_, lean_object* v_info_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v___x_2322_; lean_object* v_result_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_unsigned_to_nat(0u);
v_result_2323_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2324_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2315_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v_paramInfo_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v_paramInfo_2326_ = lean_ctor_get(v_info_2316_, 0);
v___x_2327_ = lean_array_get_size(v_paramInfo_2326_);
v___x_2328_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2316_, v___x_2327_, v_paramInfo_2326_, v_a_2325_, v___x_2322_, v_result_2323_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
lean_dec(v_a_2325_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2337_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2316_, v_a_2329_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
return v___x_2328_;
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
v_a_2338_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2324_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2324_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2346_, lean_object* v_info_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Meta_getCongrSimpKinds(v_f_2346_, v_info_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec_ref(v_info_2347_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2354_, lean_object* v_upperBound_2355_, lean_object* v___x_2356_, lean_object* v_a_2357_, lean_object* v_inst_2358_, lean_object* v_R_2359_, lean_object* v_a_2360_, lean_object* v_b_2361_, lean_object* v_c_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2354_, v_upperBound_2355_, v___x_2356_, v_a_2357_, v_a_2360_, v_b_2361_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2369_, lean_object* v_upperBound_2370_, lean_object* v___x_2371_, lean_object* v_a_2372_, lean_object* v_inst_2373_, lean_object* v_R_2374_, lean_object* v_a_2375_, lean_object* v_b_2376_, lean_object* v_c_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2369_, v_upperBound_2370_, v___x_2371_, v_a_2372_, v_inst_2373_, v_R_2374_, v_a_2375_, v_b_2376_, v_c_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v_a_2372_);
lean_dec_ref(v___x_2371_);
lean_dec(v_upperBound_2370_);
lean_dec_ref(v_info_2369_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2384_, lean_object* v_info_2385_, lean_object* v___x_2386_, lean_object* v_a_2387_, lean_object* v_b_2388_){
_start:
{
lean_object* v_a_2391_; uint8_t v___x_2395_; 
v___x_2395_ = lean_nat_dec_lt(v_a_2387_, v_upperBound_2384_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
lean_dec(v_a_2387_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v_b_2388_);
return v___x_2396_;
}
else
{
lean_object* v_resultDeps_2397_; uint8_t v___x_2398_; 
v_resultDeps_2397_ = lean_ctor_get(v_info_2385_, 1);
v___x_2398_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2397_, v_a_2387_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = lean_nat_dec_eq(v_a_2387_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; uint8_t v_isProp_2402_; 
v___x_2401_ = lean_array_fget_borrowed(v___x_2386_, v_a_2387_);
v_isProp_2402_ = lean_ctor_get_uint8(v___x_2401_, sizeof(void*)*1 + 2);
if (v_isProp_2402_ == 0)
{
uint8_t v_isInstance_2403_; 
v_isInstance_2403_ = lean_ctor_get_uint8(v___x_2401_, sizeof(void*)*1 + 4);
if (v_isInstance_2403_ == 0)
{
uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = 0;
v___x_2405_ = lean_box(v___x_2404_);
v___x_2406_ = lean_array_push(v_b_2388_, v___x_2405_);
v_a_2391_ = v___x_2406_;
goto v___jp_2390_;
}
else
{
uint8_t v___x_2407_; 
v___x_2407_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2385_, v_b_2388_, v_a_2387_);
if (v___x_2407_ == 0)
{
uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = 0;
v___x_2409_ = lean_box(v___x_2408_);
v___x_2410_ = lean_array_push(v_b_2388_, v___x_2409_);
v_a_2391_ = v___x_2410_;
goto v___jp_2390_;
}
else
{
uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = 5;
v___x_2412_ = lean_box(v___x_2411_);
v___x_2413_ = lean_array_push(v_b_2388_, v___x_2412_);
v_a_2391_ = v___x_2413_;
goto v___jp_2390_;
}
}
}
else
{
uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = 3;
v___x_2415_ = lean_box(v___x_2414_);
v___x_2416_ = lean_array_push(v_b_2388_, v___x_2415_);
v_a_2391_ = v___x_2416_;
goto v___jp_2390_;
}
}
else
{
uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = 2;
v___x_2418_ = lean_box(v___x_2417_);
v___x_2419_ = lean_array_push(v_b_2388_, v___x_2418_);
v_a_2391_ = v___x_2419_;
goto v___jp_2390_;
}
}
else
{
uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = 0;
v___x_2421_ = lean_box(v___x_2420_);
v___x_2422_ = lean_array_push(v_b_2388_, v___x_2421_);
v_a_2391_ = v___x_2422_;
goto v___jp_2390_;
}
}
v___jp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_nat_add(v_a_2387_, v___x_2392_);
lean_dec(v_a_2387_);
v_a_2387_ = v___x_2393_;
v_b_2388_ = v_a_2391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2423_, lean_object* v_info_2424_, lean_object* v___x_2425_, lean_object* v_a_2426_, lean_object* v_b_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2423_, v_info_2424_, v___x_2425_, v_a_2426_, v_b_2427_);
lean_dec_ref(v___x_2425_);
lean_dec_ref(v_info_2424_);
lean_dec(v_upperBound_2423_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_paramInfo_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_result_2439_; lean_object* v___x_2440_; 
v_paramInfo_2436_ = lean_ctor_get(v_info_2430_, 0);
v___x_2437_ = lean_array_get_size(v_paramInfo_2436_);
v___x_2438_ = lean_unsigned_to_nat(0u);
v_result_2439_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2440_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2437_, v_info_2430_, v_paramInfo_2436_, v___x_2438_, v_result_2439_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2449_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2445_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2430_, v_a_2441_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2445_);
v___x_2447_ = v___x_2443_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
else
{
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec_ref(v_info_2450_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2457_, lean_object* v_info_2458_, lean_object* v___x_2459_, lean_object* v_inst_2460_, lean_object* v_R_2461_, lean_object* v_a_2462_, lean_object* v_b_2463_, lean_object* v_c_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2457_, v_info_2458_, v___x_2459_, v_a_2462_, v_b_2463_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2471_, lean_object* v_info_2472_, lean_object* v___x_2473_, lean_object* v_inst_2474_, lean_object* v_R_2475_, lean_object* v_a_2476_, lean_object* v_b_2477_, lean_object* v_c_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2471_, v_info_2472_, v___x_2473_, v_inst_2474_, v_R_2475_, v_a_2476_, v_b_2477_, v_c_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v___x_2473_);
lean_dec_ref(v_info_2472_);
lean_dec(v_upperBound_2471_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl(lean_object* v_x_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_obj_tag_nat(v_x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl___boxed(lean_object* v_x_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl(v_x_2487_);
lean_dec_ref(v_x_2487_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2489_, lean_object* v_k_2490_){
_start:
{
if (lean_obj_tag(v_t_2489_) == 0)
{
lean_object* v_fvarId_2491_; lean_object* v___x_2492_; 
v_fvarId_2491_ = lean_ctor_get(v_t_2489_, 0);
lean_inc(v_fvarId_2491_);
lean_dec_ref_known(v_t_2489_, 1);
v___x_2492_ = lean_apply_1(v_k_2490_, v_fvarId_2491_);
return v___x_2492_;
}
else
{
lean_object* v_lhs_2493_; lean_object* v_rhs_2494_; lean_object* v___x_2495_; 
v_lhs_2493_ = lean_ctor_get(v_t_2489_, 0);
lean_inc(v_lhs_2493_);
v_rhs_2494_ = lean_ctor_get(v_t_2489_, 1);
lean_inc(v_rhs_2494_);
lean_dec_ref_known(v_t_2489_, 2);
v___x_2495_ = lean_apply_2(v_k_2490_, v_lhs_2493_, v_rhs_2494_);
return v___x_2495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2496_, lean_object* v_ctorIdx_2497_, lean_object* v_t_2498_, lean_object* v_h_2499_, lean_object* v_k_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2498_, v_k_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2502_, lean_object* v_ctorIdx_2503_, lean_object* v_t_2504_, lean_object* v_h_2505_, lean_object* v_k_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2502_, v_ctorIdx_2503_, v_t_2504_, v_h_2505_, v_k_2506_);
lean_dec(v_ctorIdx_2503_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2508_, lean_object* v_hyp_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2508_, v_hyp_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2511_, lean_object* v_t_2512_, lean_object* v_h_2513_, lean_object* v_hyp_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2512_, v_hyp_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2516_, lean_object* v_decSubsingleton_2517_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2516_, v_decSubsingleton_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2519_, lean_object* v_t_2520_, lean_object* v_h_2521_, lean_object* v_decSubsingleton_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2520_, v_decSubsingleton_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2524_, lean_object* v_fvarId_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2524_, v_fvarId_2525_);
if (lean_obj_tag(v___x_2526_) == 1)
{
lean_object* v_val_2527_; lean_object* v___x_2528_; 
v_val_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_val_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2528_ = l_Lean_Expr_fvarId_x21(v_val_2527_);
lean_dec(v_val_2527_);
return v___x_2528_;
}
else
{
lean_dec(v___x_2526_);
lean_inc(v_fvarId_2525_);
return v_fvarId_2525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2529_, lean_object* v_fvarId_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2529_, v_fvarId_2530_);
lean_dec(v_fvarId_2530_);
lean_dec(v_s_2529_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2532_, v_x_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
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
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
v_a_2548_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2539_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2539_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2556_, lean_object* v_x_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2556_, v_x_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2564_, lean_object* v_mvarId_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2565_, v_x_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_mvarId_2574_, lean_object* v_x_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2573_, v_mvarId_2574_, v_x_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_Expr_hasMVar(v_e_2582_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_e_2582_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; lean_object* v_mctx_2588_; lean_object* v___x_2589_; lean_object* v_fst_2590_; lean_object* v_snd_2591_; lean_object* v___x_2592_; lean_object* v_cache_2593_; lean_object* v_zetaDeltaFVarIds_2594_; lean_object* v_postponed_2595_; lean_object* v_diag_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2605_; 
v___x_2587_ = lean_st_ref_get(v___y_2583_);
v_mctx_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc_ref(v_mctx_2588_);
lean_dec(v___x_2587_);
v___x_2589_ = l_Lean_instantiateMVarsCore(v_mctx_2588_, v_e_2582_);
v_fst_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_fst_2590_);
v_snd_2591_ = lean_ctor_get(v___x_2589_, 1);
lean_inc(v_snd_2591_);
lean_dec_ref(v___x_2589_);
v___x_2592_ = lean_st_ref_take(v___y_2583_);
v_cache_2593_ = lean_ctor_get(v___x_2592_, 1);
v_zetaDeltaFVarIds_2594_ = lean_ctor_get(v___x_2592_, 2);
v_postponed_2595_ = lean_ctor_get(v___x_2592_, 3);
v_diag_2596_ = lean_ctor_get(v___x_2592_, 4);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2592_, 0);
lean_dec(v_unused_2606_);
v___x_2598_ = v___x_2592_;
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_diag_2596_);
lean_inc(v_postponed_2595_);
lean_inc(v_zetaDeltaFVarIds_2594_);
lean_inc(v_cache_2593_);
lean_dec(v___x_2592_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v_snd_2591_);
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_snd_2591_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_cache_2593_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_zetaDeltaFVarIds_2594_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_postponed_2595_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_diag_2596_);
v___x_2601_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_st_ref_put(v___y_2583_, v___x_2601_);
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v_fst_2590_);
return v___x_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2607_, v___y_2608_);
lean_dec(v___y_2608_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2611_, v___y_2613_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_, lean_object* v_x_2628_){
_start:
{
lean_object* v_ks_2629_; lean_object* v_vs_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2654_; 
v_ks_2629_ = lean_ctor_get(v_x_2625_, 0);
v_vs_2630_ = lean_ctor_get(v_x_2625_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_x_2625_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2632_ = v_x_2625_;
v_isShared_2633_ = v_isSharedCheck_2654_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_vs_2630_);
lean_inc(v_ks_2629_);
lean_dec(v_x_2625_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2654_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = lean_array_get_size(v_ks_2629_);
v___x_2635_ = lean_nat_dec_lt(v_x_2626_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_dec(v_x_2626_);
v___x_2636_ = lean_array_push(v_ks_2629_, v_x_2627_);
v___x_2637_ = lean_array_push(v_vs_2630_, v_x_2628_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2637_);
lean_ctor_set(v___x_2632_, 0, v___x_2636_);
v___x_2639_ = v___x_2632_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
else
{
lean_object* v_k_x27_2641_; uint8_t v___x_2642_; 
v_k_x27_2641_ = lean_array_fget_borrowed(v_ks_2629_, v_x_2626_);
v___x_2642_ = l_Lean_instBEqMVarId_beq(v_x_2627_, v_k_x27_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2644_; 
if (v_isShared_2633_ == 0)
{
v___x_2644_ = v___x_2632_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_ks_2629_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_vs_2630_);
v___x_2644_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = lean_unsigned_to_nat(1u);
v___x_2646_ = lean_nat_add(v_x_2626_, v___x_2645_);
lean_dec(v_x_2626_);
v_x_2625_ = v___x_2644_;
v_x_2626_ = v___x_2646_;
goto _start;
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2649_ = lean_array_fset(v_ks_2629_, v_x_2626_, v_x_2627_);
v___x_2650_ = lean_array_fset(v_vs_2630_, v_x_2626_, v_x_2628_);
lean_dec(v_x_2626_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2650_);
lean_ctor_set(v___x_2632_, 0, v___x_2649_);
v___x_2652_ = v___x_2632_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2655_, lean_object* v_k_2656_, lean_object* v_v_2657_){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_unsigned_to_nat(0u);
v___x_2659_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2655_, v___x_2658_, v_k_2656_, v_v_2657_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2661_, size_t v_x_2662_, size_t v_x_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_){
_start:
{
if (lean_obj_tag(v_x_2661_) == 0)
{
lean_object* v_es_2666_; size_t v___x_2667_; size_t v___x_2668_; lean_object* v_j_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_es_2666_ = lean_ctor_get(v_x_2661_, 0);
v___x_2667_ = ((size_t)31ULL);
v___x_2668_ = lean_usize_land(v_x_2662_, v___x_2667_);
v_j_2669_ = lean_usize_to_nat(v___x_2668_);
v___x_2670_ = lean_array_get_size(v_es_2666_);
v___x_2671_ = lean_nat_dec_lt(v_j_2669_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_dec(v_j_2669_);
lean_dec(v_x_2665_);
lean_dec(v_x_2664_);
return v_x_2661_;
}
else
{
lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2710_; 
lean_inc_ref(v_es_2666_);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_x_2661_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; 
v_unused_2711_ = lean_ctor_get(v_x_2661_, 0);
lean_dec(v_unused_2711_);
v___x_2673_ = v_x_2661_;
v_isShared_2674_ = v_isSharedCheck_2710_;
goto v_resetjp_2672_;
}
else
{
lean_dec(v_x_2661_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2710_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v_v_2675_; lean_object* v___x_2676_; lean_object* v_xs_x27_2677_; lean_object* v___y_2679_; 
v_v_2675_ = lean_array_fget(v_es_2666_, v_j_2669_);
v___x_2676_ = lean_box(0);
v_xs_x27_2677_ = lean_array_fset(v_es_2666_, v_j_2669_, v___x_2676_);
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
v___x_2689_ = l_Lean_instBEqMVarId_beq(v_x_2664_, v_key_2684_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_del_object(v___x_2687_);
v___x_2690_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2684_, v_val_2685_, v_x_2664_, v_x_2665_);
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
lean_ctor_set(v___x_2687_, 1, v_x_2665_);
lean_ctor_set(v___x_2687_, 0, v_x_2664_);
v___x_2693_ = v___x_2687_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_x_2664_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_x_2665_);
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
lean_object* v_node_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2708_; 
v_node_2696_ = lean_ctor_get(v_v_2675_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_v_2675_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2698_ = v_v_2675_;
v_isShared_2699_ = v_isSharedCheck_2708_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_node_2696_);
lean_dec(v_v_2675_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2708_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
size_t v___x_2700_; size_t v___x_2701_; size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2700_ = ((size_t)5ULL);
v___x_2701_ = lean_usize_shift_right(v_x_2662_, v___x_2700_);
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_add(v_x_2663_, v___x_2702_);
v___x_2704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2696_, v___x_2701_, v___x_2703_, v_x_2664_, v_x_2665_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2704_);
v___x_2706_ = v___x_2698_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
v___y_2679_ = v___x_2706_;
goto v___jp_2678_;
}
}
}
default: 
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_x_2664_);
lean_ctor_set(v___x_2709_, 1, v_x_2665_);
v___y_2679_ = v___x_2709_;
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
lean_object* v_ks_2712_; lean_object* v_vs_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2731_; 
v_ks_2712_ = lean_ctor_get(v_x_2661_, 0);
v_vs_2713_ = lean_ctor_get(v_x_2661_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_x_2661_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2715_ = v_x_2661_;
v_isShared_2716_ = v_isSharedCheck_2731_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_vs_2713_);
lean_inc(v_ks_2712_);
lean_dec(v_x_2661_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2731_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_ks_2712_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_vs_2713_);
v___x_2718_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v_newNode_2719_; size_t v___x_2720_; uint8_t v___x_2721_; 
v_newNode_2719_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2718_, v_x_2664_, v_x_2665_);
v___x_2720_ = ((size_t)7ULL);
v___x_2721_ = lean_usize_dec_le(v___x_2720_, v_x_2663_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2722_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2719_);
v___x_2723_ = lean_unsigned_to_nat(4u);
v___x_2724_ = lean_nat_dec_lt(v___x_2722_, v___x_2723_);
lean_dec(v___x_2722_);
if (v___x_2724_ == 0)
{
lean_object* v_ks_2725_; lean_object* v_vs_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_ks_2725_ = lean_ctor_get(v_newNode_2719_, 0);
lean_inc_ref(v_ks_2725_);
v_vs_2726_ = lean_ctor_get(v_newNode_2719_, 1);
lean_inc_ref(v_vs_2726_);
lean_dec_ref(v_newNode_2719_);
v___x_2727_ = lean_unsigned_to_nat(0u);
v___x_2728_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2663_, v_ks_2725_, v_vs_2726_, v___x_2727_, v___x_2728_);
lean_dec_ref(v_vs_2726_);
lean_dec_ref(v_ks_2725_);
return v___x_2729_;
}
else
{
return v_newNode_2719_;
}
}
else
{
return v_newNode_2719_;
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
size_t v_x_3883__boxed_2764_; size_t v_x_3884__boxed_2765_; lean_object* v_res_2766_; 
v_x_3883__boxed_2764_ = lean_unbox_usize(v_x_2760_);
lean_dec(v_x_2760_);
v_x_3884__boxed_2765_ = lean_unbox_usize(v_x_2761_);
lean_dec(v_x_2761_);
v_res_2766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2759_, v_x_3883__boxed_2764_, v_x_3884__boxed_2765_, v_x_2762_, v_x_2763_);
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
lean_object* v___x_2778_; lean_object* v_mctx_2779_; lean_object* v_cache_2780_; lean_object* v_zetaDeltaFVarIds_2781_; lean_object* v_postponed_2782_; lean_object* v_diag_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2812_; 
v___x_2778_ = lean_st_ref_take(v___y_2776_);
v_mctx_2779_ = lean_ctor_get(v___x_2778_, 0);
v_cache_2780_ = lean_ctor_get(v___x_2778_, 1);
v_zetaDeltaFVarIds_2781_ = lean_ctor_get(v___x_2778_, 2);
v_postponed_2782_ = lean_ctor_get(v___x_2778_, 3);
v_diag_2783_ = lean_ctor_get(v___x_2778_, 4);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2785_ = v___x_2778_;
v_isShared_2786_ = v_isSharedCheck_2812_;
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
v_isShared_2786_ = v_isSharedCheck_2812_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v_depth_2787_; lean_object* v_levelAssignDepth_2788_; lean_object* v_lmvarCounter_2789_; lean_object* v_mvarCounter_2790_; lean_object* v_lDecls_2791_; lean_object* v_decls_2792_; lean_object* v_userNames_2793_; lean_object* v_lAssignment_2794_; lean_object* v_eAssignment_2795_; lean_object* v_dAssignment_2796_; lean_object* v_instanceTypedMVars_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2811_; 
v_depth_2787_ = lean_ctor_get(v_mctx_2779_, 0);
v_levelAssignDepth_2788_ = lean_ctor_get(v_mctx_2779_, 1);
v_lmvarCounter_2789_ = lean_ctor_get(v_mctx_2779_, 2);
v_mvarCounter_2790_ = lean_ctor_get(v_mctx_2779_, 3);
v_lDecls_2791_ = lean_ctor_get(v_mctx_2779_, 4);
v_decls_2792_ = lean_ctor_get(v_mctx_2779_, 5);
v_userNames_2793_ = lean_ctor_get(v_mctx_2779_, 6);
v_lAssignment_2794_ = lean_ctor_get(v_mctx_2779_, 7);
v_eAssignment_2795_ = lean_ctor_get(v_mctx_2779_, 8);
v_dAssignment_2796_ = lean_ctor_get(v_mctx_2779_, 9);
v_instanceTypedMVars_2797_ = lean_ctor_get(v_mctx_2779_, 10);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_mctx_2779_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2799_ = v_mctx_2779_;
v_isShared_2800_ = v_isSharedCheck_2811_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_instanceTypedMVars_2797_);
lean_inc(v_dAssignment_2796_);
lean_inc(v_eAssignment_2795_);
lean_inc(v_lAssignment_2794_);
lean_inc(v_userNames_2793_);
lean_inc(v_decls_2792_);
lean_inc(v_lDecls_2791_);
lean_inc(v_mvarCounter_2790_);
lean_inc(v_lmvarCounter_2789_);
lean_inc(v_levelAssignDepth_2788_);
lean_inc(v_depth_2787_);
lean_dec(v_mctx_2779_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2811_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2795_, v_mvarId_2774_, v_val_2775_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 8, v___x_2802_);
v___x_2804_ = v___x_2799_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_depth_2787_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_levelAssignDepth_2788_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_lmvarCounter_2789_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v_mvarCounter_2790_);
lean_ctor_set(v_reuseFailAlloc_2810_, 4, v_lDecls_2791_);
lean_ctor_set(v_reuseFailAlloc_2810_, 5, v_decls_2792_);
lean_ctor_set(v_reuseFailAlloc_2810_, 6, v_userNames_2793_);
lean_ctor_set(v_reuseFailAlloc_2810_, 7, v_lAssignment_2794_);
lean_ctor_set(v_reuseFailAlloc_2810_, 8, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2810_, 9, v_dAssignment_2796_);
lean_ctor_set(v_reuseFailAlloc_2810_, 10, v_instanceTypedMVars_2797_);
v___x_2804_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2806_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2804_);
v___x_2806_ = v___x_2785_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_cache_2780_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_zetaDeltaFVarIds_2781_);
lean_ctor_set(v_reuseFailAlloc_2809_, 3, v_postponed_2782_);
lean_ctor_set(v_reuseFailAlloc_2809_, 4, v_diag_2783_);
v___x_2806_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = lean_st_ref_put(v___y_2776_, v___x_2806_);
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2801_);
return v___x_2808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2813_, lean_object* v_val_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2813_, v_val_2814_, v___y_2815_);
lean_dec(v___y_2815_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2826_, lean_object* v_as_2827_, size_t v_sz_2828_, size_t v_i_2829_, lean_object* v_b_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_a_2837_; uint8_t v___x_2841_; 
v___x_2841_ = lean_usize_dec_lt(v_i_2829_, v_sz_2828_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_b_2830_);
return v___x_2842_;
}
else
{
lean_object* v_fst_2843_; lean_object* v_snd_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v_a_2847_; 
v_fst_2843_ = lean_ctor_get(v_b_2830_, 0);
lean_inc(v_fst_2843_);
v_snd_2844_ = lean_ctor_get(v_b_2830_, 1);
lean_inc(v_snd_2844_);
lean_dec_ref(v_b_2830_);
v___x_2845_ = lean_unsigned_to_nat(0u);
v___x_2846_ = lean_nat_dec_eq(v___x_2826_, v___x_2845_);
v_a_2847_ = lean_array_uget_borrowed(v_as_2827_, v_i_2829_);
if (lean_obj_tag(v_a_2847_) == 0)
{
lean_object* v_fvarId_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_fvarId_2848_ = lean_ctor_get(v_a_2847_, 0);
v___x_2849_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2844_, v_fvarId_2848_);
v___x_2850_ = l_Lean_Meta_substCore(v_fst_2843_, v___x_2849_, v___x_2841_, v_snd_2844_, v___x_2841_, v___x_2846_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v_fst_2852_; lean_object* v_snd_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v_fst_2852_ = lean_ctor_get(v_a_2851_, 0);
v_snd_2853_ = lean_ctor_get(v_a_2851_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_a_2851_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v_a_2851_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_snd_2853_);
lean_inc(v_fst_2852_);
lean_dec(v_a_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v_fst_2852_);
lean_ctor_set(v___x_2855_, 0, v_snd_2853_);
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_snd_2853_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_fst_2852_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
v_a_2837_ = v___x_2858_;
goto v___jp_2836_;
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
v_a_2861_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2850_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2850_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_object* v_lhs_2869_; lean_object* v_rhs_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_lhs_2869_ = lean_ctor_get(v_a_2847_, 0);
v_rhs_2870_ = lean_ctor_get(v_a_2847_, 1);
v___x_2871_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2844_, v_lhs_2869_);
v___x_2872_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2844_, v_rhs_2870_);
v___x_2873_ = l_Lean_mkFVar(v___x_2871_);
v___x_2874_ = l_Lean_mkFVar(v___x_2872_);
lean_inc_ref(v___x_2874_);
lean_inc_ref(v___x_2873_);
v___x_2875_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2875_, 0, v___x_2873_);
lean_closure_set(v___x_2875_, 1, v___x_2874_);
lean_inc(v_fst_2843_);
v___x_2876_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2843_, v___x_2875_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2879_ = lean_unsigned_to_nat(2u);
v___x_2880_ = lean_mk_empty_array_with_capacity(v___x_2879_);
v___x_2881_ = lean_array_push(v___x_2880_, v___x_2873_);
v___x_2882_ = lean_array_push(v___x_2881_, v___x_2874_);
v___x_2883_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2883_, 0, v___x_2878_);
lean_closure_set(v___x_2883_, 1, v___x_2882_);
lean_inc(v_fst_2843_);
v___x_2884_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2843_, v___x_2883_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
v___x_2887_ = l_Lean_MVarId_assert(v_fst_2843_, v___x_2886_, v_a_2877_, v_a_2885_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = l_Lean_Meta_intro1Core(v_a_2888_, v___x_2846_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v_fst_2891_; lean_object* v_snd_2892_; lean_object* v___x_2893_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v_fst_2891_ = lean_ctor_get(v_a_2890_, 0);
lean_inc(v_fst_2891_);
v_snd_2892_ = lean_ctor_get(v_a_2890_, 1);
lean_inc(v_snd_2892_);
lean_dec(v_a_2890_);
v___x_2893_ = l_Lean_Meta_substCore(v_snd_2892_, v_fst_2891_, v___x_2841_, v_snd_2844_, v___x_2841_, v___x_2846_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v_fst_2895_; lean_object* v_snd_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v_fst_2895_ = lean_ctor_get(v_a_2894_, 0);
v_snd_2896_ = lean_ctor_get(v_a_2894_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_a_2894_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v_a_2894_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_snd_2896_);
lean_inc(v_fst_2895_);
lean_dec(v_a_2894_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 1, v_fst_2895_);
lean_ctor_set(v___x_2898_, 0, v_snd_2896_);
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_snd_2896_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_fst_2895_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
v_a_2837_ = v___x_2901_;
goto v___jp_2836_;
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
v_a_2904_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2893_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2893_);
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
lean_dec(v_snd_2844_);
v_a_2912_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2889_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2889_);
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
lean_dec(v_snd_2844_);
v_a_2920_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2887_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2887_);
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
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_a_2877_);
lean_dec(v_snd_2844_);
lean_dec(v_fst_2843_);
v_a_2928_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2884_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2884_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_dec(v_snd_2844_);
lean_dec(v_fst_2843_);
v_a_2936_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2876_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2876_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
v___jp_2836_:
{
size_t v___x_2838_; size_t v___x_2839_; 
v___x_2838_ = ((size_t)1ULL);
v___x_2839_ = lean_usize_add(v_i_2829_, v___x_2838_);
v_i_2829_ = v___x_2839_;
v_b_2830_ = v_a_2837_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_2944_, lean_object* v_as_2945_, lean_object* v_sz_2946_, lean_object* v_i_2947_, lean_object* v_b_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
size_t v_sz_boxed_2954_; size_t v_i_boxed_2955_; lean_object* v_res_2956_; 
v_sz_boxed_2954_ = lean_unbox_usize(v_sz_2946_);
lean_dec(v_sz_2946_);
v_i_boxed_2955_ = lean_unbox_usize(v_i_2947_);
lean_dec(v_i_2947_);
v_res_2956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2944_, v_as_2945_, v_sz_boxed_2954_, v_i_boxed_2955_, v_b_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v_as_2945_);
lean_dec(v___x_2944_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_2957_, lean_object* v_as_2958_, size_t v_i_2959_, size_t v_stop_2960_, lean_object* v_b_2961_){
_start:
{
lean_object* v___y_2963_; uint8_t v___x_2967_; 
v___x_2967_ = lean_usize_dec_eq(v_i_2959_, v_stop_2960_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_array_uget_borrowed(v_as_2958_, v_i_2959_);
v___x_2970_ = lean_array_get_borrowed(v___x_2968_, v_eqs_2957_, v___x_2969_);
if (lean_obj_tag(v___x_2970_) == 0)
{
v___y_2963_ = v_b_2961_;
goto v___jp_2962_;
}
else
{
lean_object* v_val_2971_; lean_object* v___x_2972_; 
v_val_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_val_2971_);
v___x_2972_ = lean_array_push(v_b_2961_, v_val_2971_);
v___y_2963_ = v___x_2972_;
goto v___jp_2962_;
}
}
else
{
return v_b_2961_;
}
v___jp_2962_:
{
size_t v___x_2964_; size_t v___x_2965_; 
v___x_2964_ = ((size_t)1ULL);
v___x_2965_ = lean_usize_add(v_i_2959_, v___x_2964_);
v_i_2959_ = v___x_2965_;
v_b_2961_ = v___y_2963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_2973_, lean_object* v_as_2974_, lean_object* v_i_2975_, lean_object* v_stop_2976_, lean_object* v_b_2977_){
_start:
{
size_t v_i_boxed_2978_; size_t v_stop_boxed_2979_; lean_object* v_res_2980_; 
v_i_boxed_2978_ = lean_unbox_usize(v_i_2975_);
lean_dec(v_i_2975_);
v_stop_boxed_2979_ = lean_unbox_usize(v_stop_2976_);
lean_dec(v_stop_2976_);
v_res_2980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2973_, v_as_2974_, v_i_boxed_2978_, v_stop_boxed_2979_, v_b_2977_);
lean_dec_ref(v_as_2974_);
lean_dec_ref(v_eqs_2973_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_2983_, lean_object* v_as_2984_, lean_object* v_start_2985_, lean_object* v_stop_2986_){
_start:
{
lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2987_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_2988_ = lean_nat_dec_lt(v_start_2985_, v_stop_2986_);
if (v___x_2988_ == 0)
{
return v___x_2987_;
}
else
{
lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2989_ = lean_array_get_size(v_as_2984_);
v___x_2990_ = lean_nat_dec_le(v_stop_2986_, v___x_2989_);
if (v___x_2990_ == 0)
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_nat_dec_lt(v_start_2985_, v___x_2989_);
if (v___x_2991_ == 0)
{
return v___x_2987_;
}
else
{
size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = lean_usize_of_nat(v_start_2985_);
v___x_2993_ = lean_usize_of_nat(v___x_2989_);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2983_, v_as_2984_, v___x_2992_, v___x_2993_, v___x_2987_);
return v___x_2994_;
}
}
else
{
size_t v___x_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_usize_of_nat(v_start_2985_);
v___x_2996_ = lean_usize_of_nat(v_stop_2986_);
v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_2983_, v_as_2984_, v___x_2995_, v___x_2996_, v___x_2987_);
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_2998_, lean_object* v_as_2999_, lean_object* v_start_3000_, lean_object* v_stop_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_2998_, v_as_2999_, v_start_3000_, v_stop_3001_);
lean_dec(v_stop_3001_);
lean_dec(v_start_3000_);
lean_dec_ref(v_as_2999_);
lean_dec_ref(v_eqs_2998_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_3003_, lean_object* v_type_3004_, lean_object* v_deps_3005_, lean_object* v_eqs_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v_eqs_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_array_get_size(v_deps_3005_);
v_eqs_3014_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_3006_, v_deps_3005_, v___x_3012_, v___x_3013_);
v___x_3015_ = lean_array_get_size(v_eqs_3014_);
v___x_3016_ = lean_nat_dec_eq(v___x_3015_, v___x_3012_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_type_3004_);
v___x_3018_ = 0;
v___x_3019_ = lean_box(0);
v___x_3020_ = l_Lean_Meta_mkFreshExprMVar(v___x_3017_, v___x_3018_, v___x_3019_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; size_t v_sz_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = l_Lean_Expr_mvarId_x21(v_a_3021_);
v___x_3023_ = lean_box(0);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v_sz_3025_ = lean_array_size(v_eqs_3014_);
v___x_3026_ = ((size_t)0ULL);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_3015_, v_eqs_3014_, v_sz_3025_, v___x_3026_, v___x_3024_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec_ref(v_eqs_3014_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v_fst_3029_; lean_object* v_snd_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v_fst_3029_ = lean_ctor_get(v_a_3028_, 0);
lean_inc(v_fst_3029_);
v_snd_3030_ = lean_ctor_get(v_a_3028_, 1);
lean_inc(v_snd_3030_);
lean_dec(v_a_3028_);
v___x_3031_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_3030_, v_fvarId_3003_);
lean_dec(v_fvarId_3003_);
lean_dec(v_snd_3030_);
v___x_3032_ = l_Lean_mkFVar(v___x_3031_);
v___x_3033_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_3029_, v___x_3032_, v_a_3008_);
lean_dec_ref(v___x_3033_);
v___x_3034_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_3021_, v_a_3008_);
return v___x_3034_;
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_a_3021_);
lean_dec(v_fvarId_3003_);
v_a_3035_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3027_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3027_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_dec_ref(v_eqs_3014_);
lean_dec(v_fvarId_3003_);
return v___x_3020_;
}
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_dec_ref(v_eqs_3014_);
lean_dec_ref(v_type_3004_);
v___x_3043_ = l_Lean_mkFVar(v_fvarId_3003_);
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3045_, lean_object* v_type_3046_, lean_object* v_deps_3047_, lean_object* v_eqs_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3045_, v_type_3046_, v_deps_3047_, v_eqs_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec_ref(v_eqs_3048_);
lean_dec_ref(v_deps_3047_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3055_, lean_object* v_val_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3055_, v_val_3056_, v___y_3058_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3063_, lean_object* v_val_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3063_, v_val_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3071_, lean_object* v_x_3072_, lean_object* v_x_3073_, lean_object* v_x_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3072_, v_x_3073_, v_x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3076_, lean_object* v_x_3077_, size_t v_x_3078_, size_t v_x_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3077_, v_x_3078_, v_x_3079_, v_x_3080_, v_x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3083_, lean_object* v_x_3084_, lean_object* v_x_3085_, lean_object* v_x_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_){
_start:
{
size_t v_x_4484__boxed_3089_; size_t v_x_4485__boxed_3090_; lean_object* v_res_3091_; 
v_x_4484__boxed_3089_ = lean_unbox_usize(v_x_3085_);
lean_dec(v_x_3085_);
v_x_4485__boxed_3090_ = lean_unbox_usize(v_x_3086_);
lean_dec(v_x_3086_);
v_res_3091_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3083_, v_x_3084_, v_x_4484__boxed_3089_, v_x_4485__boxed_3090_, v_x_3087_, v_x_3088_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3092_, lean_object* v_n_3093_, lean_object* v_k_3094_, lean_object* v_v_3095_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3093_, v_k_3094_, v_v_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3097_, size_t v_depth_3098_, lean_object* v_keys_3099_, lean_object* v_vals_3100_, lean_object* v_heq_3101_, lean_object* v_i_3102_, lean_object* v_entries_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3098_, v_keys_3099_, v_vals_3100_, v_i_3102_, v_entries_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3105_, lean_object* v_depth_3106_, lean_object* v_keys_3107_, lean_object* v_vals_3108_, lean_object* v_heq_3109_, lean_object* v_i_3110_, lean_object* v_entries_3111_){
_start:
{
size_t v_depth_boxed_3112_; lean_object* v_res_3113_; 
v_depth_boxed_3112_ = lean_unbox_usize(v_depth_3106_);
lean_dec(v_depth_3106_);
v_res_3113_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3105_, v_depth_boxed_3112_, v_keys_3107_, v_vals_3108_, v_heq_3109_, v_i_3110_, v_entries_3111_);
lean_dec_ref(v_vals_3108_);
lean_dec_ref(v_keys_3107_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3114_, lean_object* v_x_3115_, lean_object* v_x_3116_, lean_object* v_x_3117_, lean_object* v_x_3118_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3115_, v_x_3116_, v_x_3117_, v_x_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___f_3127_; lean_object* v___x_1366__overap_3128_; lean_object* v___x_3129_; 
v___f_3127_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1366__overap_3128_ = lean_panic_fn_borrowed(v___f_3127_, v_msg_3121_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3124_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
v___x_3129_ = lean_apply_5(v___x_1366__overap_3128_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, lean_box(0));
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
return v_res_3136_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3140_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3141_ = lean_unsigned_to_nat(34u);
v___x_3142_ = lean_unsigned_to_nat(360u);
v___x_3143_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3144_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3145_ = l_mkPanicMessageWithDecl(v___x_3144_, v___x_3143_, v___x_3142_, v___x_3141_, v___x_3140_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3146_, lean_object* v___x_3147_, lean_object* v___x_3148_, lean_object* v_i_3149_, lean_object* v_kinds_3150_, lean_object* v___x_3151_, lean_object* v_lhs_3152_, lean_object* v_rhs_3153_, lean_object* v_type_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
uint8_t v___x_1560__boxed_3160_; uint8_t v___x_1561__boxed_3161_; lean_object* v_res_3162_; 
v___x_1560__boxed_3160_ = lean_unbox(v___x_3147_);
v___x_1561__boxed_3161_ = lean_unbox(v___x_3148_);
v_res_3162_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3146_, v___x_1560__boxed_3160_, v___x_1561__boxed_3161_, v_i_3149_, v_kinds_3150_, v___x_3151_, v_lhs_3152_, v_rhs_3153_, v_type_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3163_, uint8_t v___x_3164_, uint8_t v___x_3165_, lean_object* v_i_3166_, lean_object* v___x_3167_, lean_object* v_kinds_3168_, lean_object* v_typeSub_3169_, lean_object* v_lhs_3170_, lean_object* v_rhs_3171_, lean_object* v_type_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; uint8_t v___x_3179_; lean_object* v___x_3180_; 
lean_inc_ref(v_rhs_3171_);
v___x_3178_ = lean_array_push(v___x_3163_, v_rhs_3171_);
v___x_3179_ = 1;
v___x_3180_ = l_Lean_Meta_mkLambdaFVars(v___x_3178_, v_type_3172_, v___x_3164_, v___x_3165_, v___x_3164_, v___x_3165_, v___x_3179_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec_ref(v___x_3178_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref_known(v___x_3180_, 1);
v___x_3182_ = lean_nat_add(v_i_3166_, v___x_3167_);
v___x_3183_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3168_, v___x_3182_, v_typeSub_3169_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3186_ = lean_unsigned_to_nat(2u);
v___x_3187_ = lean_mk_empty_array_with_capacity(v___x_3186_);
v___x_3188_ = lean_array_push(v___x_3187_, v_lhs_3170_);
v___x_3189_ = lean_array_push(v___x_3188_, v_rhs_3171_);
lean_inc_ref(v___x_3189_);
v___x_3190_ = l_Lean_Meta_mkAppM(v___x_3185_, v___x_3189_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = l_Lean_Meta_mkEqNDRec(v_a_3181_, v_a_3184_, v_a_3191_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
v___x_3194_ = l_Lean_Meta_mkLambdaFVars(v___x_3189_, v_a_3193_, v___x_3164_, v___x_3165_, v___x_3164_, v___x_3165_, v___x_3179_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec_ref(v___x_3189_);
return v___x_3194_;
}
else
{
lean_dec_ref(v___x_3189_);
return v___x_3192_;
}
}
else
{
lean_dec_ref(v___x_3189_);
lean_dec(v_a_3184_);
lean_dec(v_a_3181_);
return v___x_3190_;
}
}
else
{
lean_dec(v_a_3181_);
lean_dec_ref(v_rhs_3171_);
lean_dec_ref(v_lhs_3170_);
return v___x_3183_;
}
}
else
{
lean_dec_ref(v_rhs_3171_);
lean_dec_ref(v_lhs_3170_);
lean_dec_ref(v_typeSub_3169_);
lean_dec_ref(v_kinds_3168_);
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3195_, lean_object* v___x_3196_, lean_object* v___x_3197_, lean_object* v_i_3198_, lean_object* v___x_3199_, lean_object* v_kinds_3200_, lean_object* v_typeSub_3201_, lean_object* v_lhs_3202_, lean_object* v_rhs_3203_, lean_object* v_type_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
uint8_t v___x_1624__boxed_3210_; uint8_t v___x_1625__boxed_3211_; lean_object* v_res_3212_; 
v___x_1624__boxed_3210_ = lean_unbox(v___x_3196_);
v___x_1625__boxed_3211_ = lean_unbox(v___x_3197_);
v_res_3212_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3195_, v___x_1624__boxed_3210_, v___x_1625__boxed_3211_, v_i_3198_, v___x_3199_, v_kinds_3200_, v_typeSub_3201_, v_lhs_3202_, v_rhs_3203_, v_type_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___x_3199_);
lean_dec(v_i_3198_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(uint8_t v___x_3213_, lean_object* v_kinds_3214_, lean_object* v_i_3215_, uint8_t v___x_3216_, uint8_t v___x_3217_, lean_object* v_lhs_3218_, lean_object* v_type_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3228_ = lean_box(v___x_3213_);
v___x_3229_ = lean_array_get(v___x_3228_, v_kinds_3214_, v_i_3215_);
lean_dec(v___x_3228_);
v___x_3230_ = lean_unbox(v___x_3229_);
lean_dec(v___x_3229_);
switch(v___x_3230_)
{
case 1:
{
lean_dec_ref(v_type_3219_);
lean_dec_ref(v_lhs_3218_);
lean_dec(v_i_3215_);
lean_dec_ref(v_kinds_3214_);
goto v___jp_3225_;
}
case 2:
{
lean_object* v___x_3231_; 
lean_inc_ref(v_lhs_3218_);
v___x_3231_ = l_Lean_Meta_mkEqRefl(v_lhs_3218_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = l_Lean_Expr_bindingBody_x21(v_type_3219_);
v___x_3234_ = l_Lean_Expr_bindingBody_x21(v___x_3233_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = lean_unsigned_to_nat(2u);
v___x_3236_ = lean_mk_empty_array_with_capacity(v___x_3235_);
lean_inc_ref(v___x_3236_);
v___x_3237_ = lean_array_push(v___x_3236_, v_a_3232_);
lean_inc_ref(v_lhs_3218_);
v___x_3238_ = lean_array_push(v___x_3237_, v_lhs_3218_);
v___x_3239_ = lean_expr_instantiate(v___x_3234_, v___x_3238_);
lean_dec_ref(v___x_3238_);
lean_dec_ref(v___x_3234_);
v___x_3240_ = lean_box(v___x_3216_);
v___x_3241_ = lean_box(v___x_3217_);
v___f_3242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3242_, 0, v___x_3236_);
lean_closure_set(v___f_3242_, 1, v___x_3240_);
lean_closure_set(v___f_3242_, 2, v___x_3241_);
lean_closure_set(v___f_3242_, 3, v_i_3215_);
lean_closure_set(v___f_3242_, 4, v_kinds_3214_);
lean_closure_set(v___f_3242_, 5, v___x_3239_);
lean_closure_set(v___f_3242_, 6, v_lhs_3218_);
v___x_3243_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3219_, v___f_3242_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
return v___x_3243_;
}
else
{
lean_dec_ref(v_type_3219_);
lean_dec_ref(v_lhs_3218_);
lean_dec(v_i_3215_);
lean_dec_ref(v_kinds_3214_);
return v___x_3231_;
}
}
case 4:
{
lean_dec_ref(v_type_3219_);
lean_dec_ref(v_lhs_3218_);
lean_dec(v_i_3215_);
lean_dec_ref(v_kinds_3214_);
goto v___jp_3225_;
}
case 5:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v_typeSub_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___f_3251_; lean_object* v___x_3252_; 
v___x_3244_ = l_Lean_Expr_bindingBody_x21(v_type_3219_);
v___x_3245_ = lean_unsigned_to_nat(1u);
v___x_3246_ = lean_mk_empty_array_with_capacity(v___x_3245_);
lean_inc_ref(v_lhs_3218_);
lean_inc_ref(v___x_3246_);
v___x_3247_ = lean_array_push(v___x_3246_, v_lhs_3218_);
v_typeSub_3248_ = lean_expr_instantiate(v___x_3244_, v___x_3247_);
lean_dec_ref(v___x_3247_);
lean_dec_ref(v___x_3244_);
v___x_3249_ = lean_box(v___x_3216_);
v___x_3250_ = lean_box(v___x_3217_);
v___f_3251_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3251_, 0, v___x_3246_);
lean_closure_set(v___f_3251_, 1, v___x_3249_);
lean_closure_set(v___f_3251_, 2, v___x_3250_);
lean_closure_set(v___f_3251_, 3, v_i_3215_);
lean_closure_set(v___f_3251_, 4, v___x_3245_);
lean_closure_set(v___f_3251_, 5, v_kinds_3214_);
lean_closure_set(v___f_3251_, 6, v_typeSub_3248_);
lean_closure_set(v___f_3251_, 7, v_lhs_3218_);
v___x_3252_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3219_, v___f_3251_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
return v___x_3252_;
}
default: 
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_unsigned_to_nat(1u);
v___x_3254_ = lean_nat_add(v_i_3215_, v___x_3253_);
lean_dec(v_i_3215_);
v___x_3255_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3214_, v___x_3254_, v_type_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; lean_object* v___x_3260_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
v___x_3257_ = lean_mk_empty_array_with_capacity(v___x_3253_);
v___x_3258_ = lean_array_push(v___x_3257_, v_lhs_3218_);
v___x_3259_ = 1;
v___x_3260_ = l_Lean_Meta_mkLambdaFVars(v___x_3258_, v_a_3256_, v___x_3216_, v___x_3217_, v___x_3216_, v___x_3217_, v___x_3259_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec_ref(v___x_3258_);
return v___x_3260_;
}
else
{
lean_dec_ref(v_lhs_3218_);
return v___x_3255_;
}
}
}
v___jp_3225_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3227_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3226_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v___x_3261_, lean_object* v_kinds_3262_, lean_object* v_i_3263_, lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_lhs_3266_, lean_object* v_type_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v___x_1661__boxed_3273_; uint8_t v___x_1662__boxed_3274_; uint8_t v___x_1663__boxed_3275_; lean_object* v_res_3276_; 
v___x_1661__boxed_3273_ = lean_unbox(v___x_3261_);
v___x_1662__boxed_3274_ = lean_unbox(v___x_3264_);
v___x_1663__boxed_3275_ = lean_unbox(v___x_3265_);
v_res_3276_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v___x_1661__boxed_3273_, v_kinds_3262_, v_i_3263_, v___x_1662__boxed_3274_, v___x_1663__boxed_3275_, v_lhs_3266_, v_type_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3276_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3277_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3278_ = lean_unsigned_to_nat(43u);
v___x_3279_ = lean_unsigned_to_nat(355u);
v___x_3280_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3281_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3282_ = l_mkPanicMessageWithDecl(v___x_3281_, v___x_3280_, v___x_3279_, v___x_3278_, v___x_3277_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3283_, lean_object* v_i_3284_, lean_object* v_type_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = lean_array_get_size(v_kinds_3283_);
v___x_3292_ = lean_nat_dec_eq(v_i_3284_, v___x_3291_);
if (v___x_3292_ == 0)
{
uint8_t v___x_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; 
v___x_3293_ = 0;
v___x_3294_ = 1;
v___x_3295_ = lean_box(v___x_3293_);
v___x_3296_ = lean_box(v___x_3292_);
v___x_3297_ = lean_box(v___x_3294_);
v___f_3298_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 12, 5);
lean_closure_set(v___f_3298_, 0, v___x_3295_);
lean_closure_set(v___f_3298_, 1, v_kinds_3283_);
lean_closure_set(v___f_3298_, 2, v_i_3284_);
lean_closure_set(v___f_3298_, 3, v___x_3296_);
lean_closure_set(v___f_3298_, 4, v___x_3297_);
v___x_3299_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3285_, v___f_3298_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
lean_dec(v_i_3284_);
lean_dec_ref(v_kinds_3283_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3301_ = lean_unsigned_to_nat(3u);
v___x_3302_ = l_Lean_Expr_isAppOfArity(v_type_3285_, v___x_3300_, v___x_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec_ref(v_type_3285_);
v___x_3303_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3304_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3303_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
return v___x_3304_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = l_Lean_Expr_appFn_x21(v_type_3285_);
lean_dec_ref(v_type_3285_);
v___x_3306_ = l_Lean_Expr_appArg_x21(v___x_3305_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = l_Lean_Meta_mkEqRefl(v___x_3306_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
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
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = lean_unsigned_to_nat(1u);
v___x_3329_ = lean_nat_add(v_i_3312_, v___x_3328_);
v___x_3330_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3313_, v___x_3329_, v___x_3314_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3330_, 1);
lean_inc_ref(v_heq_3316_);
v___x_3332_ = l_Lean_Meta_mkEqRec(v_a_3327_, v_a_3331_, v_heq_3316_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v___x_3334_ = lean_unsigned_to_nat(3u);
v___x_3335_ = lean_mk_empty_array_with_capacity(v___x_3334_);
v___x_3336_ = lean_array_push(v___x_3335_, v_lhs_3315_);
v___x_3337_ = lean_array_push(v___x_3336_, v_rhs_3309_);
v___x_3338_ = lean_array_push(v___x_3337_, v_heq_3316_);
v___x_3339_ = l_Lean_Meta_mkLambdaFVars(v___x_3338_, v_a_3333_, v___x_3310_, v___x_3311_, v___x_3310_, v___x_3311_, v___x_3325_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec_ref(v___x_3338_);
return v___x_3339_;
}
else
{
lean_dec_ref(v_heq_3316_);
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v_rhs_3309_);
return v___x_3332_;
}
}
else
{
lean_dec(v_a_3327_);
lean_dec_ref(v_heq_3316_);
lean_dec_ref(v_lhs_3315_);
lean_dec_ref(v_rhs_3309_);
return v___x_3330_;
}
}
else
{
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
uint8_t v___x_1571__boxed_3355_; uint8_t v___x_1572__boxed_3356_; lean_object* v_res_3357_; 
v___x_1571__boxed_3355_ = lean_unbox(v___x_3342_);
v___x_1572__boxed_3356_ = lean_unbox(v___x_3343_);
v_res_3357_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3340_, v_rhs_3341_, v___x_1571__boxed_3355_, v___x_1572__boxed_3356_, v_i_3344_, v_kinds_3345_, v___x_3346_, v_lhs_3347_, v_heq_3348_, v_type_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
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
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
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
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_msg_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___f_3408_; lean_object* v___x_1532__overap_3409_; lean_object* v___x_3410_; 
v___f_3408_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1532__overap_3409_ = lean_panic_fn_borrowed(v___f_3408_, v_msg_3402_);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3405_);
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3403_);
v___x_3410_ = lean_apply_5(v___x_1532__overap_3409_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, lean_box(0));
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_msg_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_msg_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(lean_object* v_bs_3418_, lean_object* v_k_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg___boxed(lean_object* v_bs_3442_, lean_object* v_k_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v_bs_3442_, v_k_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec_ref(v_bs_3442_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(lean_object* v_00_u03b1_3450_, lean_object* v_bs_3451_, lean_object* v_k_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v_bs_3451_, v_k_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3459_, lean_object* v_bs_3460_, lean_object* v_k_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(v_00_u03b1_3459_, v_bs_3460_, v_k_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v_bs_3460_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(size_t v_sz_3468_, size_t v_i_3469_, lean_object* v_bs_3470_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1___boxed(lean_object* v_sz_3483_, lean_object* v_i_3484_, lean_object* v_bs_3485_){
_start:
{
size_t v_sz_boxed_3486_; size_t v_i_boxed_3487_; lean_object* v_res_3488_; 
v_sz_boxed_3486_ = lean_unbox_usize(v_sz_3483_);
lean_dec(v_sz_3483_);
v_i_boxed_3487_ = lean_unbox_usize(v_i_3484_);
lean_dec(v_i_3484_);
v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(v_sz_boxed_3486_, v_i_boxed_3487_, v_bs_3485_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(lean_object* v_bs_3489_, lean_object* v_k_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
size_t v_sz_3496_; size_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_sz_3496_ = lean_array_size(v_bs_3489_);
v___x_3497_ = ((size_t)0ULL);
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(v_sz_3496_, v___x_3497_, v_bs_3489_);
v___x_3499_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v___x_3498_, v_k_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec_ref(v___x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg___boxed(lean_object* v_bs_3500_, lean_object* v_k_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v_bs_3500_, v_k_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_00_u03b1_3508_, lean_object* v_bs_3509_, lean_object* v_k_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v_bs_3509_, v_k_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_00_u03b1_3517_, lean_object* v_bs_3518_, lean_object* v_k_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_00_u03b1_3517_, v_bs_3518_, v_k_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
return v_res_3525_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3527_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3528_ = lean_unsigned_to_nat(38u);
v___x_3529_ = lean_unsigned_to_nat(328u);
v___x_3530_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3531_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3532_ = l_mkPanicMessageWithDecl(v___x_3531_, v___x_3530_, v___x_3529_, v___x_3528_, v___x_3527_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3533_, lean_object* v_rhss_3534_, lean_object* v_b_3535_, lean_object* v_eqs_3536_, lean_object* v_hyps_3537_, uint8_t v_subsingletonInstImplicitRhs_3538_, lean_object* v_f_3539_, lean_object* v_info_3540_, lean_object* v_kinds_3541_, lean_object* v_lhss_3542_, lean_object* v_eq_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3549_ = lean_unsigned_to_nat(1u);
v___x_3550_ = lean_nat_add(v_i_3533_, v___x_3549_);
lean_inc_ref(v_b_3535_);
v___x_3551_ = lean_array_push(v_rhss_3534_, v_b_3535_);
v___x_3552_ = l_Lean_Expr_fvarId_x21(v_eq_3543_);
v___x_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
v___x_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
v___x_3555_ = lean_array_push(v_eqs_3536_, v___x_3554_);
v___x_3556_ = lean_array_push(v_hyps_3537_, v_b_3535_);
v___x_3557_ = lean_array_push(v___x_3556_, v_eq_3543_);
v___x_3558_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3538_, v_f_3539_, v_info_3540_, v_kinds_3541_, v_lhss_3542_, v___x_3550_, v___x_3551_, v___x_3555_, v___x_3557_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3559_, lean_object* v_rhss_3560_, lean_object* v_b_3561_, lean_object* v_eqs_3562_, lean_object* v_hyps_3563_, lean_object* v_subsingletonInstImplicitRhs_3564_, lean_object* v_f_3565_, lean_object* v_info_3566_, lean_object* v_kinds_3567_, lean_object* v_lhss_3568_, lean_object* v_eq_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3575_; lean_object* v_res_3576_; 
v_subsingletonInstImplicitRhs_boxed_3575_ = lean_unbox(v_subsingletonInstImplicitRhs_3564_);
v_res_3576_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3559_, v_rhss_3560_, v_b_3561_, v_eqs_3562_, v_hyps_3563_, v_subsingletonInstImplicitRhs_boxed_3575_, v_f_3565_, v_info_3566_, v_kinds_3567_, v_lhss_3568_, v_eq_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v_i_3559_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(lean_object* v_i_3578_, lean_object* v_rhss_3579_, lean_object* v_eqs_3580_, lean_object* v_hyps_3581_, uint8_t v_subsingletonInstImplicitRhs_3582_, lean_object* v_f_3583_, lean_object* v_info_3584_, lean_object* v_kinds_3585_, lean_object* v_lhss_3586_, lean_object* v_lhs_3587_, lean_object* v___x_3588_, lean_object* v_b_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; lean_object* v___f_3596_; lean_object* v___x_3597_; 
v___x_3595_ = lean_box(v_subsingletonInstImplicitRhs_3582_);
lean_inc_ref(v_b_3589_);
v___f_3596_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3596_, 0, v_i_3578_);
lean_closure_set(v___f_3596_, 1, v_rhss_3579_);
lean_closure_set(v___f_3596_, 2, v_b_3589_);
lean_closure_set(v___f_3596_, 3, v_eqs_3580_);
lean_closure_set(v___f_3596_, 4, v_hyps_3581_);
lean_closure_set(v___f_3596_, 5, v___x_3595_);
lean_closure_set(v___f_3596_, 6, v_f_3583_);
lean_closure_set(v___f_3596_, 7, v_info_3584_);
lean_closure_set(v___f_3596_, 8, v_kinds_3585_);
lean_closure_set(v___f_3596_, 9, v_lhss_3586_);
v___x_3597_ = l_Lean_Meta_mkEq(v_lhs_3587_, v_b_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3599_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0));
v___x_3600_ = l_Lean_Name_appendBefore(v___x_3588_, v___x_3599_);
v___x_3601_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3600_, v_a_3598_, v___f_3596_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v___x_3601_;
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec_ref(v___f_3596_);
lean_dec(v___x_3588_);
v_a_3602_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3597_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3597_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed(lean_object** _args){
lean_object* v_i_3610_ = _args[0];
lean_object* v_rhss_3611_ = _args[1];
lean_object* v_eqs_3612_ = _args[2];
lean_object* v_hyps_3613_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3614_ = _args[4];
lean_object* v_f_3615_ = _args[5];
lean_object* v_info_3616_ = _args[6];
lean_object* v_kinds_3617_ = _args[7];
lean_object* v_lhss_3618_ = _args[8];
lean_object* v_lhs_3619_ = _args[9];
lean_object* v___x_3620_ = _args[10];
lean_object* v_b_3621_ = _args[11];
lean_object* v___y_3622_ = _args[12];
lean_object* v___y_3623_ = _args[13];
lean_object* v___y_3624_ = _args[14];
lean_object* v___y_3625_ = _args[15];
lean_object* v___y_3626_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3627_; lean_object* v_res_3628_; 
v_subsingletonInstImplicitRhs_boxed_3627_ = lean_unbox(v_subsingletonInstImplicitRhs_3614_);
v_res_3628_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(v_i_3610_, v_rhss_3611_, v_eqs_3612_, v_hyps_3613_, v_subsingletonInstImplicitRhs_boxed_3627_, v_f_3615_, v_info_3616_, v_kinds_3617_, v_lhss_3618_, v_lhs_3619_, v___x_3620_, v_b_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3629_, lean_object* v_rhss_3630_, lean_object* v_eqs_3631_, lean_object* v_hyps_3632_, uint8_t v_subsingletonInstImplicitRhs_3633_, lean_object* v_f_3634_, lean_object* v_info_3635_, lean_object* v_kinds_3636_, lean_object* v_lhss_3637_, lean_object* v_lhs_3638_, lean_object* v___x_3639_, lean_object* v_name_3640_, uint8_t v_bi_3641_, lean_object* v_type_3642_, uint8_t v_kind_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; 
v___x_3649_ = lean_box(v_subsingletonInstImplicitRhs_3633_);
v___f_3650_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3650_, 0, v_i_3629_);
lean_closure_set(v___f_3650_, 1, v_rhss_3630_);
lean_closure_set(v___f_3650_, 2, v_eqs_3631_);
lean_closure_set(v___f_3650_, 3, v_hyps_3632_);
lean_closure_set(v___f_3650_, 4, v___x_3649_);
lean_closure_set(v___f_3650_, 5, v_f_3634_);
lean_closure_set(v___f_3650_, 6, v_info_3635_);
lean_closure_set(v___f_3650_, 7, v_kinds_3636_);
lean_closure_set(v___f_3650_, 8, v_lhss_3637_);
lean_closure_set(v___f_3650_, 9, v_lhs_3638_);
lean_closure_set(v___f_3650_, 10, v___x_3639_);
v___x_3651_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3640_, v_bi_3641_, v_type_3642_, v___f_3650_, v_kind_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
v_a_3660_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3651_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3651_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3668_, lean_object* v_rhss_3669_, lean_object* v_lhss_3670_, lean_object* v_i_3671_, lean_object* v_eqs_3672_, lean_object* v_hyps_3673_, uint8_t v_subsingletonInstImplicitRhs_3674_, lean_object* v_f_3675_, lean_object* v_info_3676_, lean_object* v_kinds_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v___x_3683_; 
lean_inc(v___y_3681_);
lean_inc_ref(v___y_3680_);
lean_inc(v___y_3679_);
lean_inc_ref(v___y_3678_);
lean_inc_ref(v_lhs_3668_);
v___x_3683_ = lean_infer_type(v_lhs_3668_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___y_3691_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v___x_3685_ = lean_array_get_size(v_rhss_3669_);
v___x_3686_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3670_);
v___x_3687_ = l_Array_toSubarray___redArg(v_lhss_3670_, v___x_3686_, v___x_3685_);
v___x_3688_ = l_Subarray_copy___redArg(v___x_3687_);
v___x_3689_ = l_Lean_Expr_replaceFVars(v_a_3684_, v___x_3688_, v_rhss_3669_);
lean_dec_ref(v___x_3688_);
lean_dec(v_a_3684_);
if (v_subsingletonInstImplicitRhs_3674_ == 0)
{
uint8_t v___x_3706_; 
v___x_3706_ = 1;
v___y_3691_ = v___x_3706_;
goto v___jp_3690_;
}
else
{
uint8_t v___x_3707_; 
v___x_3707_ = 3;
v___y_3691_ = v___x_3707_;
goto v___jp_3690_;
}
v___jp_3690_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = l_Lean_Expr_fvarId_x21(v_lhs_3668_);
v___x_3693_ = l_Lean_FVarId_getDecl___redArg(v___x_3692_, v___y_3678_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; lean_object* v___x_3697_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v___x_3695_ = l_Lean_LocalDecl_userName(v_a_3694_);
lean_dec(v_a_3694_);
v___x_3696_ = 0;
v___x_3697_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3671_, v_rhss_3669_, v_lhs_3668_, v_eqs_3672_, v_hyps_3673_, v_subsingletonInstImplicitRhs_3674_, v_f_3675_, v_info_3676_, v_kinds_3677_, v_lhss_3670_, v___x_3695_, v___y_3691_, v___x_3689_, v___x_3696_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
return v___x_3697_;
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec_ref(v___x_3689_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec_ref(v_kinds_3677_);
lean_dec_ref(v_info_3676_);
lean_dec_ref(v_f_3675_);
lean_dec_ref(v_hyps_3673_);
lean_dec_ref(v_eqs_3672_);
lean_dec(v_i_3671_);
lean_dec_ref(v_lhss_3670_);
lean_dec_ref(v_rhss_3669_);
lean_dec_ref(v_lhs_3668_);
v_a_3698_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3693_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3693_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec_ref(v_kinds_3677_);
lean_dec_ref(v_info_3676_);
lean_dec_ref(v_f_3675_);
lean_dec_ref(v_hyps_3673_);
lean_dec_ref(v_eqs_3672_);
lean_dec(v_i_3671_);
lean_dec_ref(v_lhss_3670_);
lean_dec_ref(v_rhss_3669_);
lean_dec_ref(v_lhs_3668_);
v_a_3708_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3683_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3683_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3716_, lean_object* v_rhss_3717_, lean_object* v_lhss_3718_, lean_object* v_i_3719_, lean_object* v_eqs_3720_, lean_object* v_hyps_3721_, lean_object* v_subsingletonInstImplicitRhs_3722_, lean_object* v_f_3723_, lean_object* v_info_3724_, lean_object* v_kinds_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3731_; lean_object* v_res_3732_; 
v_subsingletonInstImplicitRhs_boxed_3731_ = lean_unbox(v_subsingletonInstImplicitRhs_3722_);
v_res_3732_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3716_, v_rhss_3717_, v_lhss_3718_, v_i_3719_, v_eqs_3720_, v_hyps_3721_, v_subsingletonInstImplicitRhs_boxed_3731_, v_f_3723_, v_info_3724_, v_kinds_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3733_, lean_object* v_f_3734_, lean_object* v_info_3735_, lean_object* v_kinds_3736_, lean_object* v_lhss_3737_, lean_object* v_i_3738_, lean_object* v_rhss_3739_, lean_object* v_eqs_3740_, lean_object* v_hyps_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = lean_array_get_size(v_kinds_3736_);
v___x_3755_ = lean_nat_dec_eq(v_i_3738_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; uint8_t v___x_3757_; lean_object* v_lhs_3758_; lean_object* v_hyps_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v___x_3756_ = l_Lean_instInhabitedExpr;
v___x_3757_ = 0;
v_lhs_3758_ = lean_array_get_borrowed(v___x_3756_, v_lhss_3737_, v_i_3738_);
lean_inc(v_lhs_3758_);
v_hyps_3759_ = lean_array_push(v_hyps_3741_, v_lhs_3758_);
v___x_3760_ = lean_box(v___x_3757_);
v___x_3761_ = lean_array_get(v___x_3760_, v_kinds_3736_, v_i_3738_);
lean_dec(v___x_3760_);
v___x_3762_ = lean_unbox(v___x_3761_);
lean_dec(v___x_3761_);
switch(v___x_3762_)
{
case 0:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3763_ = lean_unsigned_to_nat(1u);
v___x_3764_ = lean_nat_add(v_i_3738_, v___x_3763_);
lean_dec(v_i_3738_);
lean_inc(v_lhs_3758_);
v___x_3765_ = lean_array_push(v_rhss_3739_, v_lhs_3758_);
v___x_3766_ = lean_box(0);
v___x_3767_ = lean_array_push(v_eqs_3740_, v___x_3766_);
v_i_3738_ = v___x_3764_;
v_rhss_3739_ = v___x_3765_;
v_eqs_3740_ = v___x_3767_;
v_hyps_3741_ = v_hyps_3759_;
goto _start;
}
case 2:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
lean_inc(v_lhs_3758_);
v___x_3769_ = l_Lean_Expr_fvarId_x21(v_lhs_3758_);
v___x_3770_ = l_Lean_FVarId_getDecl___redArg(v___x_3769_, v_a_3742_, v_a_3744_, v_a_3745_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; lean_object* v___x_3776_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = l_Lean_LocalDecl_userName(v_a_3771_);
v___x_3773_ = l_Lean_LocalDecl_binderInfo(v_a_3771_);
v___x_3774_ = l_Lean_LocalDecl_type(v_a_3771_);
lean_dec(v_a_3771_);
v___x_3775_ = 0;
lean_inc(v___x_3772_);
v___x_3776_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3738_, v_rhss_3739_, v_eqs_3740_, v_hyps_3759_, v_subsingletonInstImplicitRhs_3733_, v_f_3734_, v_info_3735_, v_kinds_3736_, v_lhss_3737_, v_lhs_3758_, v___x_3772_, v___x_3772_, v___x_3773_, v___x_3774_, v___x_3775_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
return v___x_3776_;
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v_hyps_3759_);
lean_dec(v_lhs_3758_);
lean_dec_ref(v_eqs_3740_);
lean_dec_ref(v_rhss_3739_);
lean_dec(v_i_3738_);
lean_dec_ref(v_lhss_3737_);
lean_dec_ref(v_kinds_3736_);
lean_dec_ref(v_info_3735_);
lean_dec_ref(v_f_3734_);
v_a_3777_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3770_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3770_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
case 3:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = l_Lean_Meta_instInhabitedParamInfo_default;
lean_inc(v_a_3745_);
lean_inc_ref(v_a_3744_);
lean_inc(v_a_3743_);
lean_inc_ref(v_a_3742_);
lean_inc(v_lhs_3758_);
v___x_3786_ = lean_infer_type(v_lhs_3758_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v_paramInfo_3788_; lean_object* v___x_3789_; lean_object* v_backDeps_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___x_3786_, 1);
v_paramInfo_3788_ = lean_ctor_get(v_info_3735_, 0);
v___x_3789_ = lean_array_get_borrowed(v___x_3785_, v_paramInfo_3788_, v_i_3738_);
v_backDeps_3790_ = lean_ctor_get(v___x_3789_, 0);
v___x_3791_ = lean_array_get_size(v_rhss_3739_);
v___x_3792_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3737_);
v___x_3793_ = l_Array_toSubarray___redArg(v_lhss_3737_, v___x_3792_, v___x_3791_);
v___x_3794_ = l_Subarray_copy___redArg(v___x_3793_);
v___x_3795_ = l_Lean_Expr_replaceFVars(v_a_3787_, v___x_3794_, v_rhss_3739_);
lean_dec_ref(v___x_3794_);
lean_dec(v_a_3787_);
v___x_3796_ = l_Lean_Expr_fvarId_x21(v_lhs_3758_);
v___x_3797_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3796_, v___x_3795_, v_backDeps_3790_, v_eqs_3740_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v___x_3799_ = lean_unsigned_to_nat(1u);
v___x_3800_ = lean_nat_add(v_i_3738_, v___x_3799_);
lean_dec(v_i_3738_);
v___x_3801_ = lean_array_push(v_rhss_3739_, v_a_3798_);
v___x_3802_ = lean_box(0);
v___x_3803_ = lean_array_push(v_eqs_3740_, v___x_3802_);
v_i_3738_ = v___x_3800_;
v_rhss_3739_ = v___x_3801_;
v_eqs_3740_ = v___x_3803_;
v_hyps_3741_ = v_hyps_3759_;
goto _start;
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec_ref(v_hyps_3759_);
lean_dec_ref(v_eqs_3740_);
lean_dec_ref(v_rhss_3739_);
lean_dec(v_i_3738_);
lean_dec_ref(v_lhss_3737_);
lean_dec_ref(v_kinds_3736_);
lean_dec_ref(v_info_3735_);
lean_dec_ref(v_f_3734_);
v_a_3805_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3797_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3797_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v_hyps_3759_);
lean_dec_ref(v_eqs_3740_);
lean_dec_ref(v_rhss_3739_);
lean_dec(v_i_3738_);
lean_dec_ref(v_lhss_3737_);
lean_dec_ref(v_kinds_3736_);
lean_dec_ref(v_info_3735_);
lean_dec_ref(v_f_3734_);
v_a_3813_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3786_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3786_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
case 5:
{
lean_object* v___x_3821_; lean_object* v___f_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_inc_n(v_lhs_3758_, 2);
v___x_3821_ = lean_box(v_subsingletonInstImplicitRhs_3733_);
v___f_3822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3822_, 0, v_lhs_3758_);
lean_closure_set(v___f_3822_, 1, v_rhss_3739_);
lean_closure_set(v___f_3822_, 2, v_lhss_3737_);
lean_closure_set(v___f_3822_, 3, v_i_3738_);
lean_closure_set(v___f_3822_, 4, v_eqs_3740_);
lean_closure_set(v___f_3822_, 5, v_hyps_3759_);
lean_closure_set(v___f_3822_, 6, v___x_3821_);
lean_closure_set(v___f_3822_, 7, v_f_3734_);
lean_closure_set(v___f_3822_, 8, v_info_3735_);
lean_closure_set(v___f_3822_, 9, v_kinds_3736_);
v___x_3823_ = lean_unsigned_to_nat(1u);
v___x_3824_ = lean_mk_empty_array_with_capacity(v___x_3823_);
v___x_3825_ = lean_array_push(v___x_3824_, v_lhs_3758_);
v___x_3826_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v___x_3825_, v___f_3822_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
return v___x_3826_;
}
default: 
{
lean_dec_ref(v_hyps_3759_);
lean_dec_ref(v_eqs_3740_);
lean_dec_ref(v_rhss_3739_);
lean_dec(v_i_3738_);
lean_dec_ref(v_lhss_3737_);
lean_dec_ref(v_kinds_3736_);
lean_dec_ref(v_info_3735_);
lean_dec_ref(v_f_3734_);
v___y_3748_ = v_a_3742_;
v___y_3749_ = v_a_3743_;
v___y_3750_ = v_a_3744_;
v___y_3751_ = v_a_3745_;
goto v___jp_3747_;
}
}
}
else
{
lean_object* v_lhs_3827_; lean_object* v_rhs_3828_; lean_object* v___x_3829_; 
lean_dec_ref(v_eqs_3740_);
lean_dec(v_i_3738_);
lean_dec_ref(v_info_3735_);
lean_inc_ref(v_f_3734_);
v_lhs_3827_ = l_Lean_mkAppN(v_f_3734_, v_lhss_3737_);
lean_dec_ref(v_lhss_3737_);
v_rhs_3828_ = l_Lean_mkAppN(v_f_3734_, v_rhss_3739_);
lean_dec_ref(v_rhss_3739_);
v___x_3829_ = l_Lean_Meta_mkEq(v_lhs_3827_, v_rhs_3828_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; uint8_t v___x_3831_; uint8_t v___x_3832_; lean_object* v___x_3833_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3829_, 1);
v___x_3831_ = 0;
v___x_3832_ = 1;
v___x_3833_ = l_Lean_Meta_mkForallFVars(v_hyps_3741_, v_a_3830_, v___x_3831_, v___x_3755_, v___x_3755_, v___x_3832_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
lean_dec_ref(v_hyps_3741_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3835_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc_n(v_a_3834_, 2);
lean_dec_ref_known(v___x_3833_, 1);
lean_inc_ref(v_kinds_3736_);
v___x_3835_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3834_, v_kinds_3736_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3844_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3838_ = v___x_3835_;
v_isShared_3839_ = v_isSharedCheck_3844_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3835_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3844_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3840_, 0, v_a_3834_);
lean_ctor_set(v___x_3840_, 1, v_a_3836_);
lean_ctor_set(v___x_3840_, 2, v_kinds_3736_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3840_);
v___x_3842_ = v___x_3838_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v_a_3834_);
lean_dec_ref(v_kinds_3736_);
v_a_3845_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3835_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3835_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec_ref(v_kinds_3736_);
v_a_3853_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3833_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3833_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_hyps_3741_);
lean_dec_ref(v_kinds_3736_);
v_a_3861_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3829_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3829_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
v___jp_3747_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3753_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v___x_3752_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3869_, lean_object* v_rhss_3870_, lean_object* v_lhs_3871_, lean_object* v_eqs_3872_, lean_object* v_hyps_3873_, uint8_t v_subsingletonInstImplicitRhs_3874_, lean_object* v_f_3875_, lean_object* v_info_3876_, lean_object* v_kinds_3877_, lean_object* v_lhss_3878_, lean_object* v_b_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = lean_nat_add(v_i_3869_, v___x_3885_);
lean_inc_ref(v_b_3879_);
v___x_3887_ = lean_array_push(v_rhss_3870_, v_b_3879_);
v___x_3888_ = l_Lean_Expr_fvarId_x21(v_lhs_3871_);
v___x_3889_ = l_Lean_Expr_fvarId_x21(v_b_3879_);
v___x_3890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
v___x_3892_ = lean_array_push(v_eqs_3872_, v___x_3891_);
v___x_3893_ = lean_array_push(v_hyps_3873_, v_b_3879_);
v___x_3894_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3874_, v_f_3875_, v_info_3876_, v_kinds_3877_, v_lhss_3878_, v___x_3886_, v___x_3887_, v___x_3892_, v___x_3893_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_3895_, lean_object* v_rhss_3896_, lean_object* v_lhs_3897_, lean_object* v_eqs_3898_, lean_object* v_hyps_3899_, lean_object* v_subsingletonInstImplicitRhs_3900_, lean_object* v_f_3901_, lean_object* v_info_3902_, lean_object* v_kinds_3903_, lean_object* v_lhss_3904_, lean_object* v_b_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3911_; lean_object* v_res_3912_; 
v_subsingletonInstImplicitRhs_boxed_3911_ = lean_unbox(v_subsingletonInstImplicitRhs_3900_);
v_res_3912_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3895_, v_rhss_3896_, v_lhs_3897_, v_eqs_3898_, v_hyps_3899_, v_subsingletonInstImplicitRhs_boxed_3911_, v_f_3901_, v_info_3902_, v_kinds_3903_, v_lhss_3904_, v_b_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec_ref(v_lhs_3897_);
lean_dec(v_i_3895_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_3913_, lean_object* v_rhss_3914_, lean_object* v_lhs_3915_, lean_object* v_eqs_3916_, lean_object* v_hyps_3917_, uint8_t v_subsingletonInstImplicitRhs_3918_, lean_object* v_f_3919_, lean_object* v_info_3920_, lean_object* v_kinds_3921_, lean_object* v_lhss_3922_, lean_object* v_name_3923_, uint8_t v_bi_3924_, lean_object* v_type_3925_, uint8_t v_kind_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; lean_object* v___f_3933_; lean_object* v___x_3934_; 
v___x_3932_ = lean_box(v_subsingletonInstImplicitRhs_3918_);
v___f_3933_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3933_, 0, v_i_3913_);
lean_closure_set(v___f_3933_, 1, v_rhss_3914_);
lean_closure_set(v___f_3933_, 2, v_lhs_3915_);
lean_closure_set(v___f_3933_, 3, v_eqs_3916_);
lean_closure_set(v___f_3933_, 4, v_hyps_3917_);
lean_closure_set(v___f_3933_, 5, v___x_3932_);
lean_closure_set(v___f_3933_, 6, v_f_3919_);
lean_closure_set(v___f_3933_, 7, v_info_3920_);
lean_closure_set(v___f_3933_, 8, v_kinds_3921_);
lean_closure_set(v___f_3933_, 9, v_lhss_3922_);
v___x_3934_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3923_, v_bi_3924_, v_type_3925_, v___f_3933_, v_kind_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
v_a_3943_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3934_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3934_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object** _args){
lean_object* v_i_3951_ = _args[0];
lean_object* v_rhss_3952_ = _args[1];
lean_object* v_lhs_3953_ = _args[2];
lean_object* v_eqs_3954_ = _args[3];
lean_object* v_hyps_3955_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_3956_ = _args[5];
lean_object* v_f_3957_ = _args[6];
lean_object* v_info_3958_ = _args[7];
lean_object* v_kinds_3959_ = _args[8];
lean_object* v_lhss_3960_ = _args[9];
lean_object* v_name_3961_ = _args[10];
lean_object* v_bi_3962_ = _args[11];
lean_object* v_type_3963_ = _args[12];
lean_object* v_kind_3964_ = _args[13];
lean_object* v___y_3965_ = _args[14];
lean_object* v___y_3966_ = _args[15];
lean_object* v___y_3967_ = _args[16];
lean_object* v___y_3968_ = _args[17];
lean_object* v___y_3969_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3970_; uint8_t v_bi_boxed_3971_; uint8_t v_kind_boxed_3972_; lean_object* v_res_3973_; 
v_subsingletonInstImplicitRhs_boxed_3970_ = lean_unbox(v_subsingletonInstImplicitRhs_3956_);
v_bi_boxed_3971_ = lean_unbox(v_bi_3962_);
v_kind_boxed_3972_ = lean_unbox(v_kind_3964_);
v_res_3973_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3951_, v_rhss_3952_, v_lhs_3953_, v_eqs_3954_, v_hyps_3955_, v_subsingletonInstImplicitRhs_boxed_3970_, v_f_3957_, v_info_3958_, v_kinds_3959_, v_lhss_3960_, v_name_3961_, v_bi_boxed_3971_, v_type_3963_, v_kind_boxed_3972_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_3974_ = _args[0];
lean_object* v_rhss_3975_ = _args[1];
lean_object* v_eqs_3976_ = _args[2];
lean_object* v_hyps_3977_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3978_ = _args[4];
lean_object* v_f_3979_ = _args[5];
lean_object* v_info_3980_ = _args[6];
lean_object* v_kinds_3981_ = _args[7];
lean_object* v_lhss_3982_ = _args[8];
lean_object* v_lhs_3983_ = _args[9];
lean_object* v___x_3984_ = _args[10];
lean_object* v_name_3985_ = _args[11];
lean_object* v_bi_3986_ = _args[12];
lean_object* v_type_3987_ = _args[13];
lean_object* v_kind_3988_ = _args[14];
lean_object* v___y_3989_ = _args[15];
lean_object* v___y_3990_ = _args[16];
lean_object* v___y_3991_ = _args[17];
lean_object* v___y_3992_ = _args[18];
lean_object* v___y_3993_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3994_; uint8_t v_bi_boxed_3995_; uint8_t v_kind_boxed_3996_; lean_object* v_res_3997_; 
v_subsingletonInstImplicitRhs_boxed_3994_ = lean_unbox(v_subsingletonInstImplicitRhs_3978_);
v_bi_boxed_3995_ = lean_unbox(v_bi_3986_);
v_kind_boxed_3996_ = lean_unbox(v_kind_3988_);
v_res_3997_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3974_, v_rhss_3975_, v_eqs_3976_, v_hyps_3977_, v_subsingletonInstImplicitRhs_boxed_3994_, v_f_3979_, v_info_3980_, v_kinds_3981_, v_lhss_3982_, v_lhs_3983_, v___x_3984_, v_name_3985_, v_bi_boxed_3995_, v_type_3987_, v_kind_boxed_3996_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* v_subsingletonInstImplicitRhs_3998_, lean_object* v_f_3999_, lean_object* v_info_4000_, lean_object* v_kinds_4001_, lean_object* v_lhss_4002_, lean_object* v_i_4003_, lean_object* v_rhss_4004_, lean_object* v_eqs_4005_, lean_object* v_hyps_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4012_; lean_object* v_res_4013_; 
v_subsingletonInstImplicitRhs_boxed_4012_ = lean_unbox(v_subsingletonInstImplicitRhs_3998_);
v_res_4013_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_boxed_4012_, v_f_3999_, v_info_4000_, v_kinds_4001_, v_lhss_4002_, v_i_4003_, v_rhss_4004_, v_eqs_4005_, v_hyps_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* v___x_4014_, uint8_t v_subsingletonInstImplicitRhs_4015_, lean_object* v_f_4016_, lean_object* v_info_4017_, lean_object* v_kinds_4018_, lean_object* v_lhss_4019_, lean_object* v_x_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; uint8_t v___x_4027_; 
v___x_4026_ = lean_array_get_size(v_lhss_4019_);
v___x_4027_ = lean_nat_dec_eq(v___x_4026_, v___x_4014_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
lean_dec_ref(v_lhss_4019_);
lean_dec_ref(v_kinds_4018_);
lean_dec_ref(v_info_4017_);
lean_dec_ref(v_f_4016_);
v___x_4028_ = lean_box(0);
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
return v___x_4029_;
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = lean_unsigned_to_nat(0u);
v___x_4031_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_4032_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_4015_, v_f_4016_, v_info_4017_, v_kinds_4018_, v_lhss_4019_, v___x_4030_, v___x_4031_, v___x_4031_, v___x_4031_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4041_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4041_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4041_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
v___x_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4037_, 0, v_a_4033_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4037_);
v___x_4039_ = v___x_4035_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4032_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4032_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* v___x_4050_, lean_object* v_subsingletonInstImplicitRhs_4051_, lean_object* v_f_4052_, lean_object* v_info_4053_, lean_object* v_kinds_4054_, lean_object* v_lhss_4055_, lean_object* v_x_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4062_; lean_object* v_res_4063_; 
v_subsingletonInstImplicitRhs_boxed_4062_ = lean_unbox(v_subsingletonInstImplicitRhs_4051_);
v_res_4063_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4050_, v_subsingletonInstImplicitRhs_boxed_4062_, v_f_4052_, v_info_4053_, v_kinds_4054_, v_lhss_4055_, v_x_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec_ref(v_x_4056_);
lean_dec(v___x_4050_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t v_subsingletonInstImplicitRhs_4064_, lean_object* v_f_4065_, lean_object* v_info_4066_, lean_object* v_kinds_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_a_4074_; lean_object* v___x_4081_; 
lean_inc(v_a_4071_);
lean_inc_ref(v_a_4070_);
lean_inc(v_a_4069_);
lean_inc_ref(v_a_4068_);
lean_inc_ref(v_f_4065_);
v___x_4081_ = lean_infer_type(v_f_4065_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4096_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4096_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4096_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___f_4088_; lean_object* v___x_4090_; 
v___x_4086_ = lean_array_get_size(v_kinds_4067_);
v___x_4087_ = lean_box(v_subsingletonInstImplicitRhs_4064_);
v___f_4088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4088_, 0, v___x_4086_);
lean_closure_set(v___f_4088_, 1, v___x_4087_);
lean_closure_set(v___f_4088_, 2, v_f_4065_);
lean_closure_set(v___f_4088_, 3, v_info_4066_);
lean_closure_set(v___f_4088_, 4, v_kinds_4067_);
if (v_isShared_4085_ == 0)
{
lean_ctor_set_tag(v___x_4084_, 1);
lean_ctor_set(v___x_4084_, 0, v___x_4086_);
v___x_4090_ = v___x_4084_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4086_);
v___x_4090_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
uint8_t v___x_4091_; uint8_t v___x_4092_; lean_object* v___x_4093_; 
v___x_4091_ = 1;
v___x_4092_ = 0;
v___x_4093_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_4082_, v___x_4090_, v___f_4088_, v___x_4091_, v___x_4092_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
if (lean_obj_tag(v___x_4093_) == 0)
{
return v___x_4093_;
}
else
{
lean_object* v_a_4094_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4093_, 1);
v_a_4074_ = v_a_4094_;
goto v___jp_4073_;
}
}
}
}
else
{
lean_object* v_a_4097_; 
lean_dec_ref(v_kinds_4067_);
lean_dec_ref(v_info_4066_);
lean_dec_ref(v_f_4065_);
v_a_4097_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4081_, 1);
v_a_4074_ = v_a_4097_;
goto v___jp_4073_;
}
v___jp_4073_:
{
uint8_t v___x_4075_; 
v___x_4075_ = l_Lean_Exception_isInterrupt(v_a_4074_);
if (v___x_4075_ == 0)
{
uint8_t v___x_4076_; 
lean_inc_ref(v_a_4074_);
v___x_4076_ = l_Lean_Exception_isRuntime(v_a_4074_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_dec_ref(v_a_4074_);
v___x_4077_ = lean_box(0);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
return v___x_4078_;
}
else
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4079_, 0, v_a_4074_);
return v___x_4079_;
}
}
else
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4080_, 0, v_a_4074_);
return v___x_4080_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* v_subsingletonInstImplicitRhs_4098_, lean_object* v_f_4099_, lean_object* v_info_4100_, lean_object* v_kinds_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4107_; lean_object* v_res_4108_; 
v_subsingletonInstImplicitRhs_boxed_4107_ = lean_unbox(v_subsingletonInstImplicitRhs_4098_);
v_res_4108_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_boxed_4107_, v_f_4099_, v_info_4100_, v_kinds_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t v_sz_4109_, size_t v_i_4110_, lean_object* v_bs_4111_){
_start:
{
uint8_t v___x_4112_; 
v___x_4112_ = lean_usize_dec_lt(v_i_4110_, v_sz_4109_);
if (v___x_4112_ == 0)
{
return v_bs_4111_;
}
else
{
lean_object* v_v_4113_; lean_object* v___x_4114_; lean_object* v_bs_x27_4115_; uint8_t v___y_4117_; uint8_t v___x_4123_; 
v_v_4113_ = lean_array_uget(v_bs_4111_, v_i_4110_);
v___x_4114_ = lean_unsigned_to_nat(0u);
v_bs_x27_4115_ = lean_array_uset(v_bs_4111_, v_i_4110_, v___x_4114_);
v___x_4123_ = lean_unbox(v_v_4113_);
switch(v___x_4123_)
{
case 3:
{
uint8_t v___x_4124_; 
lean_dec(v_v_4113_);
v___x_4124_ = 0;
v___y_4117_ = v___x_4124_;
goto v___jp_4116_;
}
case 5:
{
uint8_t v___x_4125_; 
lean_dec(v_v_4113_);
v___x_4125_ = 0;
v___y_4117_ = v___x_4125_;
goto v___jp_4116_;
}
default: 
{
uint8_t v___x_4126_; 
v___x_4126_ = lean_unbox(v_v_4113_);
lean_dec(v_v_4113_);
v___y_4117_ = v___x_4126_;
goto v___jp_4116_;
}
}
v___jp_4116_:
{
size_t v___x_4118_; size_t v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4118_ = ((size_t)1ULL);
v___x_4119_ = lean_usize_add(v_i_4110_, v___x_4118_);
v___x_4120_ = lean_box(v___y_4117_);
v___x_4121_ = lean_array_uset(v_bs_x27_4115_, v_i_4110_, v___x_4120_);
v_i_4110_ = v___x_4119_;
v_bs_4111_ = v___x_4121_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* v_sz_4127_, lean_object* v_i_4128_, lean_object* v_bs_4129_){
_start:
{
size_t v_sz_boxed_4130_; size_t v_i_boxed_4131_; lean_object* v_res_4132_; 
v_sz_boxed_4130_ = lean_unbox_usize(v_sz_4127_);
lean_dec(v_sz_4127_);
v_i_boxed_4131_ = lean_unbox_usize(v_i_4128_);
lean_dec(v_i_4128_);
v_res_4132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_4130_, v_i_boxed_4131_, v_bs_4129_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* v_f_4133_, lean_object* v_info_4134_, lean_object* v_kinds_4135_, uint8_t v_subsingletonInstImplicitRhs_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
lean_object* v___x_4142_; 
lean_inc_ref(v_kinds_4135_);
lean_inc_ref(v_info_4134_);
lean_inc_ref(v_f_4133_);
v___x_4142_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4136_, v_f_4133_, v_info_4134_, v_kinds_4135_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
if (lean_obj_tag(v_a_4143_) == 1)
{
lean_dec_ref(v_kinds_4135_);
lean_dec_ref(v_info_4134_);
lean_dec_ref(v_f_4133_);
return v___x_4142_;
}
else
{
lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4156_; 
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; 
v_unused_4157_ = lean_ctor_get(v___x_4142_, 0);
lean_dec(v_unused_4157_);
v___x_4145_ = v___x_4142_;
v_isShared_4146_ = v_isSharedCheck_4156_;
goto v_resetjp_4144_;
}
else
{
lean_dec(v___x_4142_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4156_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
uint8_t v___x_4147_; 
v___x_4147_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_4135_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4150_; 
lean_dec_ref(v_kinds_4135_);
lean_dec_ref(v_info_4134_);
lean_dec_ref(v_f_4133_);
v___x_4148_ = lean_box(0);
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 0, v___x_4148_);
v___x_4150_ = v___x_4145_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_4148_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
else
{
size_t v_sz_4152_; size_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_del_object(v___x_4145_);
v_sz_4152_ = lean_array_size(v_kinds_4135_);
v___x_4153_ = ((size_t)0ULL);
v___x_4154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4152_, v___x_4153_, v_kinds_4135_);
v___x_4155_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4136_, v_f_4133_, v_info_4134_, v___x_4154_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
return v___x_4155_;
}
}
}
}
else
{
lean_dec_ref(v_kinds_4135_);
lean_dec_ref(v_info_4134_);
lean_dec_ref(v_f_4133_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* v_f_4158_, lean_object* v_info_4159_, lean_object* v_kinds_4160_, lean_object* v_subsingletonInstImplicitRhs_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4167_; lean_object* v_res_4168_; 
v_subsingletonInstImplicitRhs_boxed_4167_ = lean_unbox(v_subsingletonInstImplicitRhs_4161_);
v_res_4168_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4158_, v_info_4159_, v_kinds_4160_, v_subsingletonInstImplicitRhs_boxed_4167_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* v_f_4169_, uint8_t v_subsingletonInstImplicitRhs_4170_, lean_object* v_maxArgs_x3f_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v___x_4177_; lean_object* v_a_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4177_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_4169_, v_a_4173_);
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref(v___x_4177_);
v___x_4179_ = l_Lean_Expr_cleanupAnnotations(v_a_4178_);
lean_dec(v_a_4178_);
lean_inc_ref(v___x_4179_);
v___x_4180_ = l_Lean_Meta_getFunInfo(v___x_4179_, v_maxArgs_x3f_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4182_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4180_, 1);
lean_inc_ref(v___x_4179_);
v___x_4182_ = l_Lean_Meta_getCongrSimpKinds(v___x_4179_, v_a_4181_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4184_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4182_, 1);
v___x_4184_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4179_, v_a_4181_, v_a_4183_, v_subsingletonInstImplicitRhs_4170_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
return v___x_4184_;
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec(v_a_4181_);
lean_dec_ref(v___x_4179_);
v_a_4185_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4182_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4182_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
lean_dec_ref(v___x_4179_);
v_a_4193_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4180_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4180_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* v_f_4201_, lean_object* v_subsingletonInstImplicitRhs_4202_, lean_object* v_maxArgs_x3f_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4209_; lean_object* v_res_4210_; 
v_subsingletonInstImplicitRhs_boxed_4209_ = lean_unbox(v_subsingletonInstImplicitRhs_4202_);
v_res_4210_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4201_, v_subsingletonInstImplicitRhs_boxed_4209_, v_maxArgs_x3f_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
return v_res_4210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4215_){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4216_ = lean_string_utf8_byte_size(v_s_4215_);
v___x_4217_ = lean_unsigned_to_nat(7u);
v___x_4218_ = lean_nat_dec_le(v___x_4217_, v___x_4216_);
if (v___x_4218_ == 0)
{
lean_dec_ref(v_s_4215_);
return v___x_4218_;
}
else
{
lean_object* v___x_4219_; lean_object* v___x_4220_; uint8_t v___x_4221_; 
v___x_4219_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4220_ = lean_unsigned_to_nat(0u);
v___x_4221_ = lean_string_memcmp(v_s_4215_, v___x_4219_, v___x_4220_, v___x_4220_, v___x_4217_);
if (v___x_4221_ == 0)
{
lean_dec_ref(v_s_4215_);
return v___x_4221_;
}
else
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
lean_inc_ref(v_s_4215_);
v___x_4222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4222_, 0, v_s_4215_);
lean_ctor_set(v___x_4222_, 1, v___x_4220_);
lean_ctor_set(v___x_4222_, 2, v___x_4216_);
v___x_4223_ = l_String_Slice_Pos_nextn(v___x_4222_, v___x_4220_, v___x_4217_);
lean_dec_ref_known(v___x_4222_, 3);
v___x_4224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4224_, 0, v_s_4215_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
lean_ctor_set(v___x_4224_, 2, v___x_4216_);
v___x_4225_ = l_String_Slice_isNat(v___x_4224_);
lean_dec_ref_known(v___x_4224_, 3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(lean_object* v_env_4299_, lean_object* v_as_4300_, size_t v_i_4301_, size_t v_stop_4302_, lean_object* v_b_4303_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_4314_, lean_object* v_as_4315_, lean_object* v_i_4316_, lean_object* v_stop_4317_, lean_object* v_b_4318_){
_start:
{
size_t v_i_boxed_4319_; size_t v_stop_boxed_4320_; lean_object* v_res_4321_; 
v_i_boxed_4319_ = lean_unbox_usize(v_i_4316_);
lean_dec(v_i_4316_);
v_stop_boxed_4320_ = lean_unbox_usize(v_stop_4317_);
lean_dec(v_stop_4317_);
v_res_4321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(v_env_4314_, v_as_4315_, v_i_boxed_4319_, v_stop_boxed_4320_, v_b_4318_);
lean_dec_ref(v_as_4315_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4322_, lean_object* v_as_4323_, size_t v_i_4324_, size_t v_stop_4325_, lean_object* v_b_4326_){
_start:
{
lean_object* v___y_4328_; uint8_t v___x_4332_; 
v___x_4332_ = lean_usize_dec_eq(v_i_4324_, v_stop_4325_);
if (v___x_4332_ == 0)
{
lean_object* v___x_4333_; lean_object* v_fst_4334_; uint8_t v___x_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4333_ = lean_array_uget_borrowed(v_as_4323_, v_i_4324_);
v_fst_4334_ = lean_ctor_get(v___x_4333_, 0);
v___x_4335_ = 1;
lean_inc_ref(v_env_4322_);
v___x_4336_ = l_Lean_Environment_setExporting(v_env_4322_, v___x_4335_);
lean_inc(v_fst_4334_);
v___x_4337_ = l_Lean_Environment_contains(v___x_4336_, v_fst_4334_, v___x_4335_);
if (v___x_4337_ == 0)
{
v___y_4328_ = v_b_4326_;
goto v___jp_4327_;
}
else
{
lean_object* v___x_4338_; 
lean_inc(v___x_4333_);
v___x_4338_ = lean_array_push(v_b_4326_, v___x_4333_);
v___y_4328_ = v___x_4338_;
goto v___jp_4327_;
}
}
else
{
lean_dec_ref(v_env_4322_);
return v_b_4326_;
}
v___jp_4327_:
{
size_t v___x_4329_; size_t v___x_4330_; 
v___x_4329_ = ((size_t)1ULL);
v___x_4330_ = lean_usize_add(v_i_4324_, v___x_4329_);
v_i_4324_ = v___x_4330_;
v_b_4326_ = v___y_4328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4339_, lean_object* v_as_4340_, lean_object* v_i_4341_, lean_object* v_stop_4342_, lean_object* v_b_4343_){
_start:
{
size_t v_i_boxed_4344_; size_t v_stop_boxed_4345_; lean_object* v_res_4346_; 
v_i_boxed_4344_ = lean_unbox_usize(v_i_4341_);
lean_dec(v_i_4341_);
v_stop_boxed_4345_ = lean_unbox_usize(v_stop_4342_);
lean_dec(v_stop_4342_);
v_res_4346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4339_, v_as_4340_, v_i_boxed_4344_, v_stop_boxed_4345_, v_b_4343_);
lean_dec_ref(v_as_4340_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4347_, lean_object* v_x_4348_){
_start:
{
if (lean_obj_tag(v_x_4348_) == 0)
{
lean_object* v_k_4349_; lean_object* v_v_4350_; lean_object* v_l_4351_; lean_object* v_r_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_k_4349_ = lean_ctor_get(v_x_4348_, 1);
v_v_4350_ = lean_ctor_get(v_x_4348_, 2);
v_l_4351_ = lean_ctor_get(v_x_4348_, 3);
v_r_4352_ = lean_ctor_get(v_x_4348_, 4);
v___x_4353_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4347_, v_l_4351_);
lean_inc(v_v_4350_);
lean_inc(v_k_4349_);
v___x_4354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4354_, 0, v_k_4349_);
lean_ctor_set(v___x_4354_, 1, v_v_4350_);
v___x_4355_ = lean_array_push(v___x_4353_, v___x_4354_);
v_init_4347_ = v___x_4355_;
v_x_4348_ = v_r_4352_;
goto _start;
}
else
{
return v_init_4347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4357_, lean_object* v_x_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4357_, v_x_4358_);
lean_dec(v_x_4358_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4364_, lean_object* v_s_4365_){
_start:
{
lean_object* v___x_4366_; lean_object* v___y_4368_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4377_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4378_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4377_, v_s_4365_);
v___x_4379_ = lean_array_get_size(v___x_4378_);
v___x_4380_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4381_ = lean_nat_dec_lt(v___x_4366_, v___x_4379_);
if (v___x_4381_ == 0)
{
lean_dec_ref(v___x_4378_);
v___y_4368_ = v___x_4380_;
goto v___jp_4367_;
}
else
{
size_t v___x_4382_; size_t v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = ((size_t)0ULL);
v___x_4383_ = lean_usize_of_nat(v___x_4379_);
lean_inc_ref(v_env_4364_);
v___x_4384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(v_env_4364_, v___x_4378_, v___x_4382_, v___x_4383_, v___x_4380_);
lean_dec_ref(v___x_4378_);
v___y_4368_ = v___x_4384_;
goto v___jp_4367_;
}
v___jp_4367_:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v___x_4369_ = lean_array_get_size(v___y_4368_);
v___x_4370_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4371_ = lean_nat_dec_lt(v___x_4366_, v___x_4369_);
if (v___x_4371_ == 0)
{
lean_object* v___x_4372_; 
lean_dec_ref(v_env_4364_);
v___x_4372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set(v___x_4372_, 1, v___x_4370_);
lean_ctor_set(v___x_4372_, 2, v___y_4368_);
return v___x_4372_;
}
else
{
size_t v___x_4373_; size_t v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4373_ = ((size_t)0ULL);
v___x_4374_ = lean_usize_of_nat(v___x_4369_);
v___x_4375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4364_, v___y_4368_, v___x_4373_, v___x_4374_, v___x_4370_);
lean_inc_ref(v___x_4375_);
v___x_4376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
lean_ctor_set(v___x_4376_, 2, v___y_4368_);
return v___x_4376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4385_, lean_object* v_s_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4385_, v_s_4386_);
lean_dec(v_s_4386_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; lean_object* v___x_4401_; 
v___f_4397_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4398_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4399_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4400_ = 0;
v___x_4401_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4398_, v___x_4399_, v___x_4400_, v___f_4397_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4404_, lean_object* v_t_4405_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4404_, v_t_4405_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4407_, lean_object* v_t_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4407_, v_t_4408_);
lean_dec(v_t_4408_);
return v_res_4409_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isCongrReservedNameSuffix(lean_object* v_s_4410_){
_start:
{
uint8_t v___x_4411_; 
lean_inc_ref(v_s_4410_);
v___x_4411_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4410_);
if (v___x_4411_ == 0)
{
lean_object* v___x_4412_; uint8_t v___x_4413_; 
v___x_4412_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4413_ = lean_string_dec_eq(v_s_4410_, v___x_4412_);
lean_dec_ref(v_s_4410_);
return v___x_4413_;
}
else
{
lean_dec_ref(v_s_4410_);
return v___x_4411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isCongrReservedNameSuffix___boxed(lean_object* v_s_4414_){
_start:
{
uint8_t v_res_4415_; lean_object* v_r_4416_; 
v_res_4415_ = l_Lean_Meta_isCongrReservedNameSuffix(v_s_4414_);
v_r_4416_ = lean_box(v_res_4415_);
return v_r_4416_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_(lean_object* v_env_4417_, lean_object* v_n_4418_){
_start:
{
if (lean_obj_tag(v_n_4418_) == 1)
{
lean_object* v_pre_4419_; lean_object* v_str_4420_; uint8_t v___x_4421_; 
v_pre_4419_ = lean_ctor_get(v_n_4418_, 0);
lean_inc(v_pre_4419_);
v_str_4420_ = lean_ctor_get(v_n_4418_, 1);
lean_inc_ref(v_str_4420_);
lean_dec_ref_known(v_n_4418_, 2);
v___x_4421_ = l_Lean_Meta_isCongrReservedNameSuffix(v_str_4420_);
if (v___x_4421_ == 0)
{
lean_dec(v_pre_4419_);
lean_dec_ref(v_env_4417_);
return v___x_4421_;
}
else
{
uint8_t v___x_4422_; 
v___x_4422_ = l_Lean_Environment_contains(v_env_4417_, v_pre_4419_, v___x_4421_);
return v___x_4422_;
}
}
else
{
uint8_t v___x_4423_; 
lean_dec(v_n_4418_);
lean_dec_ref(v_env_4417_);
v___x_4423_ = 0;
return v___x_4423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2____boxed(lean_object* v_env_4424_, lean_object* v_n_4425_){
_start:
{
uint8_t v_res_4426_; lean_object* v_r_4427_; 
v_res_4426_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_(v_env_4424_, v_n_4425_);
v_r_4427_ = lean_box(v_res_4426_);
return v_r_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___f_4431_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_));
v___x_4432_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_));
v___x_4433_ = l_Lean_registerReservedNamePredicate(v___x_4432_, v___f_4431_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2____boxed(lean_object* v_a_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_();
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(lean_object* v_thm_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; lean_object* v_env_4440_; lean_object* v_toConstantVal_4441_; lean_object* v_value_4442_; lean_object* v_all_4443_; lean_object* v_type_4450_; uint8_t v___x_4451_; 
v___x_4439_ = lean_st_ref_get(v___y_4437_);
v_env_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc_ref_n(v_env_4440_, 2);
lean_dec(v___x_4439_);
v_toConstantVal_4441_ = lean_ctor_get(v_thm_4436_, 0);
v_value_4442_ = lean_ctor_get(v_thm_4436_, 1);
v_all_4443_ = lean_ctor_get(v_thm_4436_, 2);
v_type_4450_ = lean_ctor_get(v_toConstantVal_4441_, 2);
v___x_4451_ = l_Lean_Environment_hasUnsafe(v_env_4440_, v_type_4450_);
if (v___x_4451_ == 0)
{
uint8_t v___x_4452_; 
v___x_4452_ = l_Lean_Environment_hasUnsafe(v_env_4440_, v_value_4442_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4453_, 0, v_thm_4436_);
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
return v___x_4454_;
}
else
{
lean_inc(v_all_4443_);
lean_inc_ref(v_value_4442_);
lean_inc_ref(v_toConstantVal_4441_);
lean_dec_ref(v_thm_4436_);
goto v___jp_4444_;
}
}
else
{
lean_inc(v_all_4443_);
lean_inc_ref(v_value_4442_);
lean_inc_ref(v_toConstantVal_4441_);
lean_dec_ref(v_env_4440_);
lean_dec_ref(v_thm_4436_);
goto v___jp_4444_;
}
v___jp_4444_:
{
lean_object* v___x_4445_; uint8_t v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4445_ = lean_box(0);
v___x_4446_ = 0;
v___x_4447_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4447_, 0, v_toConstantVal_4441_);
lean_ctor_set(v___x_4447_, 1, v_value_4442_);
lean_ctor_set(v___x_4447_, 2, v___x_4445_);
lean_ctor_set(v___x_4447_, 3, v_all_4443_);
lean_ctor_set_uint8(v___x_4447_, sizeof(void*)*4, v___x_4446_);
v___x_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_thm_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v_thm_4455_, v___y_4456_);
lean_dec(v___y_4456_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_thm_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v_thm_4459_, v___y_4463_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_thm_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_thm_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
return v_res_4472_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0(void){
_start:
{
lean_object* v___x_4473_; double v___x_4474_; 
v___x_4473_ = lean_unsigned_to_nat(0u);
v___x_4474_ = lean_float_of_nat(v___x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(lean_object* v_cls_4478_, lean_object* v_msg_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_ref_4485_; lean_object* v___x_4486_; lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4532_; 
v_ref_4485_ = lean_ctor_get(v___y_4482_, 2);
v___x_4486_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4489_ = v___x_4486_;
v_isShared_4490_ = v_isSharedCheck_4532_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4486_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4532_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v_traceState_4492_; lean_object* v_env_4493_; lean_object* v_nextMacroScope_4494_; lean_object* v_ngen_4495_; lean_object* v_auxDeclNGen_4496_; lean_object* v_cache_4497_; lean_object* v_recordedDeps_4498_; lean_object* v_messages_4499_; lean_object* v_infoState_4500_; lean_object* v_snapshotTasks_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4531_; 
v___x_4491_ = lean_st_ref_take(v___y_4483_);
v_traceState_4492_ = lean_ctor_get(v___x_4491_, 4);
v_env_4493_ = lean_ctor_get(v___x_4491_, 0);
v_nextMacroScope_4494_ = lean_ctor_get(v___x_4491_, 1);
v_ngen_4495_ = lean_ctor_get(v___x_4491_, 2);
v_auxDeclNGen_4496_ = lean_ctor_get(v___x_4491_, 3);
v_cache_4497_ = lean_ctor_get(v___x_4491_, 5);
v_recordedDeps_4498_ = lean_ctor_get(v___x_4491_, 6);
v_messages_4499_ = lean_ctor_get(v___x_4491_, 7);
v_infoState_4500_ = lean_ctor_get(v___x_4491_, 8);
v_snapshotTasks_4501_ = lean_ctor_get(v___x_4491_, 9);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4503_ = v___x_4491_;
v_isShared_4504_ = v_isSharedCheck_4531_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_snapshotTasks_4501_);
lean_inc(v_infoState_4500_);
lean_inc(v_messages_4499_);
lean_inc(v_recordedDeps_4498_);
lean_inc(v_cache_4497_);
lean_inc(v_traceState_4492_);
lean_inc(v_auxDeclNGen_4496_);
lean_inc(v_ngen_4495_);
lean_inc(v_nextMacroScope_4494_);
lean_inc(v_env_4493_);
lean_dec(v___x_4491_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4531_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
uint64_t v_tid_4505_; lean_object* v_traces_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4530_; 
v_tid_4505_ = lean_ctor_get_uint64(v_traceState_4492_, sizeof(void*)*1);
v_traces_4506_ = lean_ctor_get(v_traceState_4492_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v_traceState_4492_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4508_ = v_traceState_4492_;
v_isShared_4509_ = v_isSharedCheck_4530_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_traces_4506_);
lean_dec(v_traceState_4492_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4530_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; double v___x_4512_; uint8_t v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4521_; 
v___x_4510_ = lean_box(0);
v___x_4511_ = lean_box(0);
v___x_4512_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__0);
v___x_4513_ = 0;
v___x_4514_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__1));
v___x_4515_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4515_, 0, v_cls_4478_);
lean_ctor_set(v___x_4515_, 1, v___x_4511_);
lean_ctor_set(v___x_4515_, 2, v___x_4514_);
lean_ctor_set_float(v___x_4515_, sizeof(void*)*3, v___x_4512_);
lean_ctor_set_float(v___x_4515_, sizeof(void*)*3 + 8, v___x_4512_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*3 + 16, v___x_4513_);
v___x_4516_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3___closed__2));
v___x_4517_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4515_);
lean_ctor_set(v___x_4517_, 1, v_a_4487_);
lean_ctor_set(v___x_4517_, 2, v___x_4516_);
lean_inc(v_ref_4485_);
v___x_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4518_, 0, v_ref_4485_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
v___x_4519_ = l_Lean_PersistentArray_push___redArg(v_traces_4506_, v___x_4518_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v___x_4519_);
v___x_4521_ = v___x_4508_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4519_);
lean_ctor_set_uint64(v_reuseFailAlloc_4529_, sizeof(void*)*1, v_tid_4505_);
v___x_4521_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_object* v___x_4523_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 4, v___x_4521_);
v___x_4523_ = v___x_4503_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_env_4493_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v_nextMacroScope_4494_);
lean_ctor_set(v_reuseFailAlloc_4528_, 2, v_ngen_4495_);
lean_ctor_set(v_reuseFailAlloc_4528_, 3, v_auxDeclNGen_4496_);
lean_ctor_set(v_reuseFailAlloc_4528_, 4, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4528_, 5, v_cache_4497_);
lean_ctor_set(v_reuseFailAlloc_4528_, 6, v_recordedDeps_4498_);
lean_ctor_set(v_reuseFailAlloc_4528_, 7, v_messages_4499_);
lean_ctor_set(v_reuseFailAlloc_4528_, 8, v_infoState_4500_);
lean_ctor_set(v_reuseFailAlloc_4528_, 9, v_snapshotTasks_4501_);
v___x_4523_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4524_; lean_object* v___x_4526_; 
v___x_4524_ = lean_st_ref_put(v___y_4483_, v___x_4523_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v___x_4510_);
v___x_4526_ = v___x_4489_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4510_);
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
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4543_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
lean_ctor_set(v___x_4544_, 1, v___x_4543_);
return v___x_4544_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4548_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4549_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4550_ = l_Lean_Name_append(v___x_4549_, v___x_4548_);
return v___x_4550_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4552_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4553_ = l_Lean_stringToMessageData(v___x_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v_name_4554_, lean_object* v_argKinds_4555_, uint8_t v___x_4556_, lean_object* v___x_4557_, lean_object* v___x_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v___x_4603_; lean_object* v_a_4604_; lean_object* v___x_4605_; 
v___x_4603_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___redArg(v___x_4558_, v___y_4562_);
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
lean_inc(v_a_4604_);
lean_dec_ref(v___x_4603_);
v___x_4605_ = l_Lean_addDecl(v_a_4604_, v___x_4556_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_toCold_4606_; lean_object* v_options_4607_; uint8_t v_hasTrace_4608_; 
lean_dec_ref_known(v___x_4605_, 1);
v_toCold_4606_ = lean_ctor_get(v___y_4561_, 0);
v_options_4607_ = lean_ctor_get(v_toCold_4606_, 2);
v_hasTrace_4608_ = lean_ctor_get_uint8(v_options_4607_, sizeof(void*)*1);
if (v_hasTrace_4608_ == 0)
{
goto v___jp_4564_;
}
else
{
lean_object* v_inheritedTraceOptions_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
v_inheritedTraceOptions_4609_ = lean_ctor_get(v_toCold_4606_, 11);
v___x_4610_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4611_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4609_, v_options_4607_, v___x_4611_);
if (v___x_4612_ == 0)
{
goto v___jp_4564_;
}
else
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4613_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4554_);
v___x_4614_ = l_Lean_MessageData_ofName(v_name_4554_);
v___x_4615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4613_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
v___x_4616_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4615_);
lean_ctor_set(v___x_4617_, 1, v___x_4616_);
v___x_4618_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(v___x_4610_, v___x_4617_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_dec_ref_known(v___x_4618_, 1);
goto v___jp_4564_;
}
else
{
lean_dec_ref(v___x_4557_);
lean_dec_ref(v_argKinds_4555_);
lean_dec(v_name_4554_);
return v___x_4618_;
}
}
}
}
else
{
lean_dec_ref(v___x_4557_);
lean_dec_ref(v_argKinds_4555_);
lean_dec(v_name_4554_);
return v___x_4605_;
}
v___jp_4564_:
{
lean_object* v___x_4565_; lean_object* v_env_4566_; lean_object* v_nextMacroScope_4567_; lean_object* v_ngen_4568_; lean_object* v_auxDeclNGen_4569_; lean_object* v_traceState_4570_; lean_object* v_recordedDeps_4571_; lean_object* v_messages_4572_; lean_object* v_infoState_4573_; lean_object* v_snapshotTasks_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4601_; 
v___x_4565_ = lean_st_ref_take(v___y_4562_);
v_env_4566_ = lean_ctor_get(v___x_4565_, 0);
v_nextMacroScope_4567_ = lean_ctor_get(v___x_4565_, 1);
v_ngen_4568_ = lean_ctor_get(v___x_4565_, 2);
v_auxDeclNGen_4569_ = lean_ctor_get(v___x_4565_, 3);
v_traceState_4570_ = lean_ctor_get(v___x_4565_, 4);
v_recordedDeps_4571_ = lean_ctor_get(v___x_4565_, 6);
v_messages_4572_ = lean_ctor_get(v___x_4565_, 7);
v_infoState_4573_ = lean_ctor_get(v___x_4565_, 8);
v_snapshotTasks_4574_ = lean_ctor_get(v___x_4565_, 9);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4601_ == 0)
{
lean_object* v_unused_4602_; 
v_unused_4602_ = lean_ctor_get(v___x_4565_, 5);
lean_dec(v_unused_4602_);
v___x_4576_ = v___x_4565_;
v_isShared_4577_ = v_isSharedCheck_4601_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_snapshotTasks_4574_);
lean_inc(v_infoState_4573_);
lean_inc(v_messages_4572_);
lean_inc(v_recordedDeps_4571_);
lean_inc(v_traceState_4570_);
lean_inc(v_auxDeclNGen_4569_);
lean_inc(v_ngen_4568_);
lean_inc(v_nextMacroScope_4567_);
lean_inc(v_env_4566_);
lean_dec(v___x_4565_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4601_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
v___x_4578_ = l_Lean_Meta_congrKindsExt;
v___x_4579_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4578_, v_env_4566_, v_name_4554_, v_argKinds_4555_, v___x_4556_);
v___x_4580_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 5, v___x_4580_);
lean_ctor_set(v___x_4576_, 0, v___x_4579_);
v___x_4582_ = v___x_4576_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_nextMacroScope_4567_);
lean_ctor_set(v_reuseFailAlloc_4600_, 2, v_ngen_4568_);
lean_ctor_set(v_reuseFailAlloc_4600_, 3, v_auxDeclNGen_4569_);
lean_ctor_set(v_reuseFailAlloc_4600_, 4, v_traceState_4570_);
lean_ctor_set(v_reuseFailAlloc_4600_, 5, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4600_, 6, v_recordedDeps_4571_);
lean_ctor_set(v_reuseFailAlloc_4600_, 7, v_messages_4572_);
lean_ctor_set(v_reuseFailAlloc_4600_, 8, v_infoState_4573_);
lean_ctor_set(v_reuseFailAlloc_4600_, 9, v_snapshotTasks_4574_);
v___x_4582_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v_mctx_4585_; lean_object* v_zetaDeltaFVarIds_4586_; lean_object* v_postponed_4587_; lean_object* v_diag_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4598_; 
v___x_4583_ = lean_st_ref_put(v___y_4562_, v___x_4582_);
v___x_4584_ = lean_st_ref_take(v___y_4560_);
v_mctx_4585_ = lean_ctor_get(v___x_4584_, 0);
v_zetaDeltaFVarIds_4586_ = lean_ctor_get(v___x_4584_, 2);
v_postponed_4587_ = lean_ctor_get(v___x_4584_, 3);
v_diag_4588_ = lean_ctor_get(v___x_4584_, 4);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4598_ == 0)
{
lean_object* v_unused_4599_; 
v_unused_4599_ = lean_ctor_get(v___x_4584_, 1);
lean_dec(v_unused_4599_);
v___x_4590_ = v___x_4584_;
v_isShared_4591_ = v_isSharedCheck_4598_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_diag_4588_);
lean_inc(v_postponed_4587_);
lean_inc(v_zetaDeltaFVarIds_4586_);
lean_inc(v_mctx_4585_);
lean_dec(v___x_4584_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4598_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4592_; lean_object* v___x_4594_; 
v___x_4592_ = lean_box(0);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 1, v___x_4557_);
v___x_4594_ = v___x_4590_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_mctx_4585_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v___x_4557_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_zetaDeltaFVarIds_4586_);
lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_postponed_4587_);
lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_diag_4588_);
v___x_4594_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_st_ref_put(v___y_4560_, v___x_4594_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4592_);
return v___x_4596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_name_4619_, lean_object* v_argKinds_4620_, lean_object* v___x_4621_, lean_object* v___x_4622_, lean_object* v___x_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
uint8_t v___x_12662__boxed_4629_; lean_object* v_res_4630_; 
v___x_12662__boxed_4629_ = lean_unbox(v___x_4621_);
v_res_4630_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_4619_, v_argKinds_4620_, v___x_12662__boxed_4629_, v___x_4622_, v___x_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
return v_res_4630_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v___dummy_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg();
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
if (lean_obj_tag(v_a_4637_) == 0)
{
lean_object* v___x_4639_; 
v___x_4639_ = l_List_reverse___redArg(v_a_4638_);
return v___x_4639_;
}
else
{
lean_object* v_head_4640_; lean_object* v_tail_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4650_; 
v_head_4640_ = lean_ctor_get(v_a_4637_, 0);
v_tail_4641_ = lean_ctor_get(v_a_4637_, 1);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_a_4637_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4643_ = v_a_4637_;
v_isShared_4644_ = v_isSharedCheck_4650_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_tail_4641_);
lean_inc(v_head_4640_);
lean_dec(v_a_4637_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4650_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4645_; lean_object* v___x_4647_; 
v___x_4645_ = l_Lean_mkLevelParam(v_head_4640_);
if (v_isShared_4644_ == 0)
{
lean_ctor_set(v___x_4643_, 1, v_a_4638_);
lean_ctor_set(v___x_4643_, 0, v___x_4645_);
v___x_4647_ = v___x_4643_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_a_4638_);
v___x_4647_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
v_a_4637_ = v_tail_4641_;
v_a_4638_ = v___x_4647_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
return v___x_4652_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4653_ = lean_box(1);
v___x_4654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4655_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
lean_ctor_set(v___x_4656_, 1, v___x_4654_);
lean_ctor_set(v___x_4656_, 2, v___x_4653_);
return v___x_4656_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4659_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4660_ = lean_unsigned_to_nat(0u);
v___x_4661_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4660_);
lean_ctor_set(v___x_4661_, 1, v___x_4660_);
lean_ctor_set(v___x_4661_, 2, v___x_4660_);
lean_ctor_set(v___x_4661_, 3, v___x_4660_);
lean_ctor_set(v___x_4661_, 4, v___x_4659_);
lean_ctor_set(v___x_4661_, 5, v___x_4659_);
lean_ctor_set(v___x_4661_, 6, v___x_4659_);
lean_ctor_set(v___x_4661_, 7, v___x_4659_);
lean_ctor_set(v___x_4661_, 8, v___x_4659_);
lean_ctor_set(v___x_4661_, 9, v___x_4659_);
lean_ctor_set(v___x_4661_, 10, v___x_4659_);
return v___x_4661_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0___redArg();
return v___x_4662_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4663_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
lean_ctor_set(v___x_4664_, 1, v___x_4663_);
return v___x_4664_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = lean_unsigned_to_nat(0u);
v___x_4666_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
lean_ctor_set(v___x_4667_, 1, v___x_4666_);
lean_ctor_set(v___x_4667_, 2, v___x_4665_);
return v___x_4667_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4668_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4669_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4670_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4671_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4672_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4671_);
lean_ctor_set(v___x_4672_, 1, v___x_4670_);
lean_ctor_set(v___x_4672_, 2, v___x_4669_);
lean_ctor_set(v___x_4672_, 3, v___x_4670_);
lean_ctor_set(v___x_4672_, 4, v___x_4670_);
lean_ctor_set(v___x_4672_, 5, v___x_4670_);
lean_ctor_set(v___x_4672_, 6, v___x_4668_);
return v___x_4672_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
lean_ctor_set(v___x_4674_, 2, v___x_4673_);
lean_ctor_set(v___x_4674_, 3, v___x_4673_);
lean_ctor_set(v___x_4674_, 4, v___x_4673_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4675_, lean_object* v_name_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
if (lean_obj_tag(v_name_4676_) == 1)
{
lean_object* v_pre_4680_; lean_object* v_str_4681_; lean_object* v___x_4682_; lean_object* v_env_4683_; uint8_t v___x_4684_; uint8_t v___x_4685_; 
v_pre_4680_ = lean_ctor_get(v_name_4676_, 0);
lean_inc_n(v_pre_4680_, 2);
v_str_4681_ = lean_ctor_get(v_name_4676_, 1);
v___x_4682_ = lean_st_ref_get(v___y_4678_);
v_env_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc_ref(v_env_4683_);
lean_dec(v___x_4682_);
v___x_4684_ = 1;
v___x_4685_ = l_Lean_Environment_contains(v_env_4683_, v_pre_4680_, v___x_4684_);
if (v___x_4685_ == 0)
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
lean_dec(v_pre_4680_);
lean_dec_ref_known(v_name_4676_, 2);
lean_dec(v___x_4675_);
v___x_4686_ = lean_box(v___x_4685_);
v___x_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
return v___x_4687_;
}
else
{
uint8_t v___x_4688_; lean_object* v_a_4690_; 
lean_inc_ref(v_str_4681_);
v___x_4688_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4681_);
if (v___x_4688_ == 0)
{
lean_object* v___x_4697_; uint8_t v___x_4698_; 
v___x_4697_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4698_ = lean_string_dec_eq(v_str_4681_, v___x_4697_);
if (v___x_4698_ == 0)
{
lean_object* v___x_4699_; lean_object* v___x_4700_; 
lean_dec(v_pre_4680_);
lean_dec_ref_known(v_name_4676_, 2);
lean_dec(v___x_4675_);
v___x_4699_ = lean_box(v___x_4698_);
v___x_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4699_);
return v___x_4700_;
}
else
{
uint8_t v___x_4701_; uint8_t v___x_4702_; uint8_t v___x_4703_; lean_object* v___x_4704_; uint64_t v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; uint8_t v_a_4719_; lean_object* v___x_4723_; 
v___x_4701_ = 1;
v___x_4702_ = 0;
v___x_4703_ = 2;
v___x_4704_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_4704_, 0, v___x_4688_);
lean_ctor_set_uint8(v___x_4704_, 1, v___x_4688_);
lean_ctor_set_uint8(v___x_4704_, 2, v___x_4688_);
lean_ctor_set_uint8(v___x_4704_, 3, v___x_4688_);
lean_ctor_set_uint8(v___x_4704_, 4, v___x_4688_);
lean_ctor_set_uint8(v___x_4704_, 5, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 6, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 7, v___x_4688_);
lean_ctor_set_uint8(v___x_4704_, 8, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 9, v___x_4701_);
lean_ctor_set_uint8(v___x_4704_, 10, v___x_4702_);
lean_ctor_set_uint8(v___x_4704_, 11, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 12, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 13, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 14, v___x_4703_);
lean_ctor_set_uint8(v___x_4704_, 15, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 16, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 17, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 18, v___x_4698_);
lean_ctor_set_uint8(v___x_4704_, 19, v___x_4688_);
lean_ctor_set_uint8(v___x_4704_, 20, v___x_4698_);
v___x_4705_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4704_);
v___x_4706_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4706_, 0, v___x_4704_);
lean_ctor_set_uint64(v___x_4706_, sizeof(void*)*1, v___x_4705_);
v___x_4707_ = lean_unsigned_to_nat(0u);
v___x_4708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4709_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4710_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4711_ = lean_box(0);
lean_inc(v___x_4675_);
v___x_4712_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4712_, 0, v___x_4706_);
lean_ctor_set(v___x_4712_, 1, v___x_4675_);
lean_ctor_set(v___x_4712_, 2, v___x_4709_);
lean_ctor_set(v___x_4712_, 3, v___x_4710_);
lean_ctor_set(v___x_4712_, 4, v___x_4711_);
lean_ctor_set(v___x_4712_, 5, v___x_4707_);
lean_ctor_set(v___x_4712_, 6, v___x_4711_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*7, v___x_4688_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*7 + 1, v___x_4688_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*7 + 2, v___x_4688_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*7 + 3, v___x_4684_);
v___x_4713_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4714_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4715_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4713_);
lean_ctor_set(v___x_4716_, 1, v___x_4714_);
lean_ctor_set(v___x_4716_, 2, v___x_4675_);
lean_ctor_set(v___x_4716_, 3, v___x_4708_);
lean_ctor_set(v___x_4716_, 4, v___x_4715_);
v___x_4717_ = lean_st_mk_ref(v___x_4716_);
lean_inc(v_pre_4680_);
v___x_4723_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4680_, v___x_4712_, v___x_4717_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v___x_4725_ = l_Lean_ConstantInfo_levelParams(v_a_4724_);
lean_dec(v_a_4724_);
v___x_4726_ = lean_box(0);
lean_inc(v___x_4725_);
v___x_4727_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v___x_4725_, v___x_4726_);
lean_inc(v_pre_4680_);
v___x_4728_ = l_Lean_mkConst(v_pre_4680_, v___x_4727_);
lean_inc_ref(v___x_4728_);
v___x_4729_ = l_Lean_Meta_getFunInfo(v___x_4728_, v___x_4711_, v___x_4712_, v___x_4717_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4731_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v___x_4729_, 1);
lean_inc_ref(v___x_4728_);
v___x_4731_ = l_Lean_Meta_getCongrSimpKinds(v___x_4728_, v_a_4730_, v___x_4712_, v___x_4717_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4733_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4732_);
lean_dec_ref_known(v___x_4731_, 1);
v___x_4733_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4728_, v_a_4730_, v_a_4732_, v___x_4684_, v___x_4712_, v___x_4717_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
if (lean_obj_tag(v_a_4734_) == 1)
{
lean_object* v_val_4735_; lean_object* v_type_4736_; lean_object* v_proof_4737_; lean_object* v_argKinds_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4751_; 
v_val_4735_ = lean_ctor_get(v_a_4734_, 0);
lean_inc(v_val_4735_);
lean_dec_ref_known(v_a_4734_, 1);
v_type_4736_ = lean_ctor_get(v_val_4735_, 0);
v_proof_4737_ = lean_ctor_get(v_val_4735_, 1);
v_argKinds_4738_ = lean_ctor_get(v_val_4735_, 2);
v_isSharedCheck_4751_ = !lean_is_exclusive(v_val_4735_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4740_ = v_val_4735_;
v_isShared_4741_ = v_isSharedCheck_4751_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_argKinds_4738_);
lean_inc(v_proof_4737_);
lean_inc(v_type_4736_);
lean_dec(v_val_4735_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4751_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
lean_inc_ref(v_name_4676_);
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 2, v_type_4736_);
lean_ctor_set(v___x_4740_, 1, v___x_4725_);
lean_ctor_set(v___x_4740_, 0, v_name_4676_);
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_name_4676_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v___x_4725_);
lean_ctor_set(v_reuseFailAlloc_4750_, 2, v_type_4736_);
v___x_4743_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___f_4747_; lean_object* v___x_4748_; 
lean_inc_ref_n(v_name_4676_, 2);
v___x_4744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4744_, 0, v_name_4676_);
lean_ctor_set(v___x_4744_, 1, v___x_4726_);
v___x_4745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4743_);
lean_ctor_set(v___x_4745_, 1, v_proof_4737_);
lean_ctor_set(v___x_4745_, 2, v___x_4744_);
v___x_4746_ = lean_box(v___x_4688_);
v___f_4747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4747_, 0, v_name_4676_);
lean_closure_set(v___f_4747_, 1, v_argKinds_4738_);
lean_closure_set(v___f_4747_, 2, v___x_4746_);
lean_closure_set(v___f_4747_, 3, v___x_4714_);
lean_closure_set(v___f_4747_, 4, v___x_4745_);
v___x_4748_ = l_Lean_Meta_realizeConst(v_pre_4680_, v_name_4676_, v___f_4747_, v___x_4712_, v___x_4717_, v___y_4677_, v___y_4678_);
lean_dec_ref_known(v___x_4712_, 7);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_dec_ref_known(v___x_4748_, 1);
v_a_4719_ = v___x_4684_;
goto v___jp_4718_;
}
else
{
lean_object* v_a_4749_; 
lean_dec(v___x_4717_);
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
lean_inc(v_a_4749_);
lean_dec_ref_known(v___x_4748_, 1);
v_a_4690_ = v_a_4749_;
goto v___jp_4689_;
}
}
}
}
else
{
lean_dec(v_a_4734_);
lean_dec(v___x_4725_);
lean_dec_ref_known(v___x_4712_, 7);
lean_dec_ref_known(v_name_4676_, 2);
lean_dec(v_pre_4680_);
v_a_4719_ = v___x_4688_;
goto v___jp_4718_;
}
}
else
{
lean_object* v_a_4752_; 
lean_dec(v___x_4725_);
lean_dec(v___x_4717_);
lean_dec_ref_known(v___x_4712_, 7);
lean_dec_ref_known(v_name_4676_, 2);
lean_dec(v_pre_4680_);
v_a_4752_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4752_);
lean_dec_ref_known(v___x_4733_, 1);
v_a_4690_ = v_a_4752_;
goto v___jp_4689_;
}
}
else
{
lean_object* v_a_4753_; 
lean_dec(v_a_4730_);
lean_dec_ref(v___x_4728_);
lean_dec(v___x_4725_);
lean_dec(v___x_4717_);
lean_dec_ref_known(v___x_4712_, 7);
lean_dec(v_pre_4680_);
lean_dec_ref_known(v_name_4676_, 2);
v_a_4753_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4753_);
lean_dec_ref_known(v___x_4731_, 1);
v_a_4690_ = v_a_4753_;
goto v___jp_4689_;
}
}
else
{
lean_object* v_a_4754_; 
lean_dec_ref(v___x_4728_);
lean_dec(v___x_4725_);
lean_dec(v___x_4717_);
lean_dec_ref_known(v___x_4712_, 7);
lean_dec_ref_known(v_name_4676_, 2);
lean_dec(v_pre_4680_);
v_a_4754_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4754_);
lean_dec_ref_known(v___x_4729_, 1);
v_a_4690_ = v_a_4754_;
goto v___jp_4689_;
}
}
else
{
lean_object* v_a_4755_; 
lean_dec(v___x_4717_);
lean_dec_ref_known(v___x_4712_, 7);
lean_dec_ref_known(v_name_4676_, 2);
lean_dec(v_pre_4680_);
v_a_4755_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4723_, 1);
v_a_4690_ = v_a_4755_;
goto v___jp_4689_;
}
v___jp_4718_:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4720_ = lean_st_ref_get(v___x_4717_);
lean_dec(v___x_4717_);
lean_dec(v___x_4720_);
v___x_4721_ = lean_box(v_a_4719_);
v___x_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4721_);
return v___x_4722_;
}
}
}
else
{
lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; lean_object* v_a_4765_; uint8_t v___x_4772_; uint8_t v___x_4773_; uint8_t v___x_4774_; lean_object* v___x_4775_; uint64_t v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4756_ = lean_unsigned_to_nat(7u);
v___x_4757_ = lean_unsigned_to_nat(0u);
v___x_4758_ = lean_string_utf8_byte_size(v_str_4681_);
lean_inc_ref_n(v_str_4681_, 2);
v___x_4759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4759_, 0, v_str_4681_);
lean_ctor_set(v___x_4759_, 1, v___x_4757_);
lean_ctor_set(v___x_4759_, 2, v___x_4758_);
v___x_4760_ = l_String_Slice_Pos_nextn(v___x_4759_, v___x_4757_, v___x_4756_);
lean_dec_ref_known(v___x_4759_, 3);
v___x_4761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4761_, 0, v_str_4681_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
lean_ctor_set(v___x_4761_, 2, v___x_4758_);
v___x_4762_ = l_String_Slice_toNat_x21(v___x_4761_);
lean_dec_ref_known(v___x_4761_, 3);
v___x_4763_ = 0;
v___x_4772_ = 1;
v___x_4773_ = 0;
v___x_4774_ = 2;
v___x_4775_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_4775_, 0, v___x_4763_);
lean_ctor_set_uint8(v___x_4775_, 1, v___x_4763_);
lean_ctor_set_uint8(v___x_4775_, 2, v___x_4763_);
lean_ctor_set_uint8(v___x_4775_, 3, v___x_4763_);
lean_ctor_set_uint8(v___x_4775_, 4, v___x_4763_);
lean_ctor_set_uint8(v___x_4775_, 5, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 6, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 7, v___x_4763_);
lean_ctor_set_uint8(v___x_4775_, 8, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 9, v___x_4772_);
lean_ctor_set_uint8(v___x_4775_, 10, v___x_4773_);
lean_ctor_set_uint8(v___x_4775_, 11, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 12, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 13, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 14, v___x_4774_);
lean_ctor_set_uint8(v___x_4775_, 15, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 16, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 17, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 18, v___x_4688_);
lean_ctor_set_uint8(v___x_4775_, 19, v___x_4763_);
lean_ctor_set_uint8(v___x_4775_, 20, v___x_4688_);
v___x_4776_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4775_);
v___x_4777_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4777_, 0, v___x_4775_);
lean_ctor_set_uint64(v___x_4777_, sizeof(void*)*1, v___x_4776_);
v___x_4778_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4779_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4780_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4781_ = lean_box(0);
lean_inc(v___x_4675_);
v___x_4782_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4782_, 0, v___x_4777_);
lean_ctor_set(v___x_4782_, 1, v___x_4675_);
lean_ctor_set(v___x_4782_, 2, v___x_4779_);
lean_ctor_set(v___x_4782_, 3, v___x_4780_);
lean_ctor_set(v___x_4782_, 4, v___x_4781_);
lean_ctor_set(v___x_4782_, 5, v___x_4757_);
lean_ctor_set(v___x_4782_, 6, v___x_4781_);
lean_ctor_set_uint8(v___x_4782_, sizeof(void*)*7, v___x_4763_);
lean_ctor_set_uint8(v___x_4782_, sizeof(void*)*7 + 1, v___x_4763_);
lean_ctor_set_uint8(v___x_4782_, sizeof(void*)*7 + 2, v___x_4763_);
lean_ctor_set_uint8(v___x_4782_, sizeof(void*)*7 + 3, v___x_4684_);
v___x_4783_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4784_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4785_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4783_);
lean_ctor_set(v___x_4786_, 1, v___x_4784_);
lean_ctor_set(v___x_4786_, 2, v___x_4675_);
lean_ctor_set(v___x_4786_, 3, v___x_4778_);
lean_ctor_set(v___x_4786_, 4, v___x_4785_);
v___x_4787_ = lean_st_mk_ref(v___x_4786_);
lean_inc(v_pre_4680_);
v___x_4788_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4680_, v___x_4782_, v___x_4787_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc(v_a_4789_);
lean_dec_ref_known(v___x_4788_, 1);
v___x_4790_ = l_Lean_ConstantInfo_levelParams(v_a_4789_);
lean_dec(v_a_4789_);
v___x_4791_ = lean_box(0);
lean_inc(v___x_4790_);
v___x_4792_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v___x_4790_, v___x_4791_);
lean_inc(v_pre_4680_);
v___x_4793_ = l_Lean_mkConst(v_pre_4680_, v___x_4792_);
v___x_4794_ = l_Lean_Meta_mkHCongrWithArity(v___x_4793_, v___x_4762_, v___x_4782_, v___x_4787_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v_type_4796_; lean_object* v_proof_4797_; lean_object* v_argKinds_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4821_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
lean_inc(v_a_4795_);
lean_dec_ref_known(v___x_4794_, 1);
v_type_4796_ = lean_ctor_get(v_a_4795_, 0);
v_proof_4797_ = lean_ctor_get(v_a_4795_, 1);
v_argKinds_4798_ = lean_ctor_get(v_a_4795_, 2);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_a_4795_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4800_ = v_a_4795_;
v_isShared_4801_ = v_isSharedCheck_4821_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_argKinds_4798_);
lean_inc(v_proof_4797_);
lean_inc(v_type_4796_);
lean_dec(v_a_4795_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4821_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
lean_inc_ref(v_name_4676_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 2, v_type_4796_);
lean_ctor_set(v___x_4800_, 1, v___x_4790_);
lean_ctor_set(v___x_4800_, 0, v_name_4676_);
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_name_4676_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4820_, 2, v_type_4796_);
v___x_4803_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___f_4807_; lean_object* v___x_4808_; 
lean_inc_ref_n(v_name_4676_, 2);
v___x_4804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4804_, 0, v_name_4676_);
lean_ctor_set(v___x_4804_, 1, v___x_4791_);
v___x_4805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4803_);
lean_ctor_set(v___x_4805_, 1, v_proof_4797_);
lean_ctor_set(v___x_4805_, 2, v___x_4804_);
v___x_4806_ = lean_box(v___x_4763_);
v___f_4807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4807_, 0, v_name_4676_);
lean_closure_set(v___f_4807_, 1, v_argKinds_4798_);
lean_closure_set(v___f_4807_, 2, v___x_4806_);
lean_closure_set(v___f_4807_, 3, v___x_4784_);
lean_closure_set(v___f_4807_, 4, v___x_4805_);
v___x_4808_ = l_Lean_Meta_realizeConst(v_pre_4680_, v_name_4676_, v___f_4807_, v___x_4782_, v___x_4787_, v___y_4677_, v___y_4678_);
lean_dec_ref_known(v___x_4782_, 7);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4817_; 
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4817_ == 0)
{
lean_object* v_unused_4818_; 
v_unused_4818_ = lean_ctor_get(v___x_4808_, 0);
lean_dec(v_unused_4818_);
v___x_4810_ = v___x_4808_;
v_isShared_4811_ = v_isSharedCheck_4817_;
goto v_resetjp_4809_;
}
else
{
lean_dec(v___x_4808_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4817_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4815_; 
v___x_4812_ = lean_st_ref_get(v___x_4787_);
lean_dec(v___x_4787_);
lean_dec(v___x_4812_);
v___x_4813_ = lean_box(v___x_4684_);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v___x_4813_);
v___x_4815_ = v___x_4810_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
else
{
lean_object* v_a_4819_; 
lean_dec(v___x_4787_);
v_a_4819_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_a_4819_);
lean_dec_ref_known(v___x_4808_, 1);
v_a_4765_ = v_a_4819_;
goto v___jp_4764_;
}
}
}
}
else
{
lean_object* v_a_4822_; 
lean_dec(v___x_4790_);
lean_dec(v___x_4787_);
lean_dec_ref_known(v___x_4782_, 7);
lean_dec_ref_known(v_name_4676_, 2);
lean_dec(v_pre_4680_);
v_a_4822_ = lean_ctor_get(v___x_4794_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4794_, 1);
v_a_4765_ = v_a_4822_;
goto v___jp_4764_;
}
}
else
{
lean_object* v_a_4823_; 
lean_dec(v___x_4787_);
lean_dec_ref_known(v___x_4782_, 7);
lean_dec(v___x_4762_);
lean_dec_ref_known(v_name_4676_, 2);
lean_dec(v_pre_4680_);
v_a_4823_ = lean_ctor_get(v___x_4788_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4788_, 1);
v_a_4765_ = v_a_4823_;
goto v___jp_4764_;
}
v___jp_4764_:
{
uint8_t v___x_4766_; 
v___x_4766_ = l_Lean_Exception_isInterrupt(v_a_4765_);
if (v___x_4766_ == 0)
{
uint8_t v___x_4767_; 
lean_inc_ref(v_a_4765_);
v___x_4767_ = l_Lean_Exception_isRuntime(v_a_4765_);
if (v___x_4767_ == 0)
{
lean_object* v___x_4768_; lean_object* v___x_4769_; 
lean_dec_ref(v_a_4765_);
v___x_4768_ = lean_box(v___x_4763_);
v___x_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4768_);
return v___x_4769_;
}
else
{
lean_object* v___x_4770_; 
v___x_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4770_, 0, v_a_4765_);
return v___x_4770_;
}
}
else
{
lean_object* v___x_4771_; 
v___x_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4771_, 0, v_a_4765_);
return v___x_4771_;
}
}
}
v___jp_4689_:
{
uint8_t v___x_4691_; 
v___x_4691_ = l_Lean_Exception_isInterrupt(v_a_4690_);
if (v___x_4691_ == 0)
{
uint8_t v___x_4692_; 
lean_inc_ref(v_a_4690_);
v___x_4692_ = l_Lean_Exception_isRuntime(v_a_4690_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; lean_object* v___x_4694_; 
lean_dec_ref(v_a_4690_);
v___x_4693_ = lean_box(v___x_4688_);
v___x_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4693_);
return v___x_4694_;
}
else
{
lean_object* v___x_4695_; 
v___x_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4695_, 0, v_a_4690_);
return v___x_4695_;
}
}
else
{
lean_object* v___x_4696_; 
v___x_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4696_, 0, v_a_4690_);
return v___x_4696_;
}
}
}
}
else
{
uint8_t v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
lean_dec(v_name_4676_);
lean_dec(v___x_4675_);
v___x_4824_ = 0;
v___x_4825_ = lean_box(v___x_4824_);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4827_, lean_object* v_name_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4827_, v_name_4828_, v___y_4829_, v___y_4830_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4836_; lean_object* v___x_4837_; 
v___f_4836_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4837_ = l_Lean_registerReservedNameAction(v___f_4836_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4840_){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0___redArg(){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___dummy_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0___redArg();
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_4846_){
_start:
{
lean_object* v___x_4847_; 
v___x_4847_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* v_msg_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v___f_4854_; lean_object* v___x_1736__overap_4855_; lean_object* v___x_4856_; 
v___f_4854_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1736__overap_4855_ = lean_panic_fn_borrowed(v___f_4854_, v_msg_4848_);
lean_inc(v___y_4852_);
lean_inc_ref(v___y_4851_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
v___x_4856_ = lean_apply_5(v___x_1736__overap_4855_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, lean_box(0));
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
return v_res_4863_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4865_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4866_ = lean_unsigned_to_nat(8u);
v___x_4867_ = lean_unsigned_to_nat(464u);
v___x_4868_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0));
v___x_4869_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4870_ = l_mkPanicMessageWithDecl(v___x_4869_, v___x_4868_, v___x_4867_, v___x_4866_, v___x_4865_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* v_thmName_4871_, lean_object* v_levels_4872_, lean_object* v_____r_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
lean_inc(v_thmName_4871_);
v___x_4879_ = l_Lean_mkConst(v_thmName_4871_, v_levels_4872_);
lean_inc(v___y_4877_);
lean_inc_ref(v___y_4876_);
lean_inc(v___y_4875_);
lean_inc_ref(v___y_4874_);
lean_inc_ref(v___x_4879_);
v___x_4880_ = lean_infer_type(v___x_4879_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4924_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4883_ = v___x_4880_;
v_isShared_4884_ = v_isSharedCheck_4924_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4924_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v_env_4886_; lean_object* v___x_4887_; lean_object* v_toEnvExtension_4888_; lean_object* v_asyncMode_4889_; uint8_t v___x_4890_; lean_object* v___x_4891_; 
v___x_4885_ = lean_st_ref_get(v___y_4877_);
v_env_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc_ref(v_env_4886_);
lean_dec(v___x_4885_);
v___x_4887_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_4888_ = lean_ctor_get(v___x_4887_, 0);
v_asyncMode_4889_ = lean_ctor_get(v_toEnvExtension_4888_, 2);
v___x_4890_ = 0;
v___x_4891_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4887_, v_env_4886_, v_thmName_4871_, v_asyncMode_4889_, v___x_4890_);
if (lean_obj_tag(v___x_4891_) == 1)
{
lean_object* v_val_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4904_; 
v_val_4892_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4894_ = v___x_4891_;
v_isShared_4895_ = v_isSharedCheck_4904_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_val_4892_);
lean_dec(v___x_4891_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4904_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4896_; lean_object* v___x_4898_; 
v___x_4896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4896_, 0, v_a_4881_);
lean_ctor_set(v___x_4896_, 1, v___x_4879_);
lean_ctor_set(v___x_4896_, 2, v_val_4892_);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4896_);
v___x_4898_ = v___x_4894_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4896_);
v___x_4898_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
lean_object* v___x_4899_; lean_object* v___x_4901_; 
v___x_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4898_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4899_);
v___x_4901_ = v___x_4883_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
else
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
lean_dec(v___x_4891_);
lean_del_object(v___x_4883_);
lean_dec(v_a_4881_);
lean_dec_ref(v___x_4879_);
v___x_4905_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1);
v___x_4906_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_4905_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4915_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4909_ = v___x_4906_;
v_isShared_4910_ = v_isSharedCheck_4915_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4906_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4915_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4911_; lean_object* v___x_4913_; 
v___x_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4911_, 0, v_a_4907_);
if (v_isShared_4910_ == 0)
{
lean_ctor_set(v___x_4909_, 0, v___x_4911_);
v___x_4913_ = v___x_4909_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4911_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
v_a_4916_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4906_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4906_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec_ref(v___x_4879_);
lean_dec(v_thmName_4871_);
v_a_4925_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4880_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4880_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* v_thmName_4933_, lean_object* v_levels_4934_, lean_object* v_____r_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4933_, v_levels_4934_, v_____r_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* v_declName_4942_, lean_object* v_levels_4943_, lean_object* v_numArgs_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v_a_4951_; lean_object* v___y_4959_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v_suffix_4972_; lean_object* v_thmName_4973_; lean_object* v___x_4974_; lean_object* v_env_4975_; uint8_t v___x_4976_; 
v___x_4970_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4971_ = l_Nat_reprFast(v_numArgs_4944_);
v_suffix_4972_ = lean_string_append(v___x_4970_, v___x_4971_);
lean_dec_ref(v___x_4971_);
v_thmName_4973_ = l_Lean_Name_str___override(v_declName_4942_, v_suffix_4972_);
v___x_4974_ = lean_st_ref_get(v_a_4948_);
v_env_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc_ref(v_env_4975_);
lean_dec(v___x_4974_);
v___x_4976_ = l_Lean_Environment_containsOnBranch(v_env_4975_, v_thmName_4973_);
lean_dec_ref(v_env_4975_);
if (v___x_4976_ == 0)
{
lean_object* v___x_4977_; 
lean_inc(v_thmName_4973_);
v___x_4977_ = l_Lean_executeReservedNameAction(v_thmName_4973_, v_a_4947_, v_a_4948_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
lean_dec_ref_known(v___x_4977_, 1);
v___x_4978_ = lean_box(0);
v___x_4979_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4973_, v_levels_4943_, v___x_4978_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_);
v___y_4959_ = v___x_4979_;
goto v___jp_4958_;
}
else
{
lean_object* v_a_4980_; 
lean_dec(v_thmName_4973_);
lean_dec(v_levels_4943_);
v_a_4980_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4980_);
lean_dec_ref_known(v___x_4977_, 1);
v_a_4951_ = v_a_4980_;
goto v___jp_4950_;
}
}
else
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4981_ = lean_box(0);
v___x_4982_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4973_, v_levels_4943_, v___x_4981_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_);
v___y_4959_ = v___x_4982_;
goto v___jp_4958_;
}
v___jp_4950_:
{
uint8_t v___x_4952_; 
v___x_4952_ = l_Lean_Exception_isInterrupt(v_a_4951_);
if (v___x_4952_ == 0)
{
uint8_t v___x_4953_; 
lean_inc_ref(v_a_4951_);
v___x_4953_ = l_Lean_Exception_isRuntime(v_a_4951_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4954_; lean_object* v___x_4955_; 
lean_dec_ref(v_a_4951_);
v___x_4954_ = lean_box(0);
v___x_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
return v___x_4955_;
}
else
{
lean_object* v___x_4956_; 
v___x_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4956_, 0, v_a_4951_);
return v___x_4956_;
}
}
else
{
lean_object* v___x_4957_; 
v___x_4957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_a_4951_);
return v___x_4957_;
}
}
v___jp_4958_:
{
if (lean_obj_tag(v___y_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4968_; 
v_a_4960_ = lean_ctor_get(v___y_4959_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___y_4959_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4962_ = v___y_4959_;
v_isShared_4963_ = v_isSharedCheck_4968_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___y_4959_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4968_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v_a_4964_; lean_object* v___x_4966_; 
v_a_4964_ = lean_ctor_get(v_a_4960_, 0);
lean_inc(v_a_4964_);
lean_dec(v_a_4960_);
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 0, v_a_4964_);
v___x_4966_ = v___x_4962_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
else
{
lean_object* v_a_4969_; 
v_a_4969_ = lean_ctor_get(v___y_4959_, 0);
lean_inc(v_a_4969_);
lean_dec_ref_known(v___y_4959_, 1);
v_a_4951_ = v_a_4969_;
goto v___jp_4950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object* v_declName_4983_, lean_object* v_levels_4984_, lean_object* v_numArgs_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_4983_, v_levels_4984_, v_numArgs_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v_a_4986_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* v_____r_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_5000_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0));
v___x_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5001_, 0, v___x_5000_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* v_____r_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
return v_res_5008_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5010_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_5011_ = lean_unsigned_to_nat(8u);
v___x_5012_ = lean_unsigned_to_nat(481u);
v___x_5013_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0));
v___x_5014_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_5015_ = l_mkPanicMessageWithDecl(v___x_5014_, v___x_5013_, v___x_5012_, v___x_5011_, v___x_5010_);
return v___x_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object* v_thmName_5016_, lean_object* v_levels_5017_, lean_object* v_____r_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; 
lean_inc(v_thmName_5016_);
v___x_5024_ = l_Lean_mkConst(v_thmName_5016_, v_levels_5017_);
lean_inc(v___y_5022_);
lean_inc_ref(v___y_5021_);
lean_inc(v___y_5020_);
lean_inc_ref(v___y_5019_);
lean_inc_ref(v___x_5024_);
v___x_5025_ = lean_infer_type(v___x_5024_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_);
if (lean_obj_tag(v___x_5025_) == 0)
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5069_; 
v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5025_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5028_ = v___x_5025_;
v_isShared_5029_ = v_isSharedCheck_5069_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_5025_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5069_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5030_; lean_object* v_env_5031_; lean_object* v___x_5032_; lean_object* v_toEnvExtension_5033_; lean_object* v_asyncMode_5034_; uint8_t v___x_5035_; lean_object* v___x_5036_; 
v___x_5030_ = lean_st_ref_get(v___y_5022_);
v_env_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc_ref(v_env_5031_);
lean_dec(v___x_5030_);
v___x_5032_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_5033_ = lean_ctor_get(v___x_5032_, 0);
v_asyncMode_5034_ = lean_ctor_get(v_toEnvExtension_5033_, 2);
v___x_5035_ = 0;
v___x_5036_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_5032_, v_env_5031_, v_thmName_5016_, v_asyncMode_5034_, v___x_5035_);
if (lean_obj_tag(v___x_5036_) == 1)
{
lean_object* v_val_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5049_; 
v_val_5037_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5039_ = v___x_5036_;
v_isShared_5040_ = v_isSharedCheck_5049_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_val_5037_);
lean_dec(v___x_5036_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5049_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5041_; lean_object* v___x_5043_; 
v___x_5041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5041_, 0, v_a_5026_);
lean_ctor_set(v___x_5041_, 1, v___x_5024_);
lean_ctor_set(v___x_5041_, 2, v_val_5037_);
if (v_isShared_5040_ == 0)
{
lean_ctor_set(v___x_5039_, 0, v___x_5041_);
v___x_5043_ = v___x_5039_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5044_; lean_object* v___x_5046_; 
v___x_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 0, v___x_5044_);
v___x_5046_ = v___x_5028_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5044_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
else
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
lean_dec(v___x_5036_);
lean_del_object(v___x_5028_);
lean_dec(v_a_5026_);
lean_dec_ref(v___x_5024_);
v___x_5050_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1);
v___x_5051_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_5050_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5060_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5054_ = v___x_5051_;
v_isShared_5055_ = v_isSharedCheck_5060_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5051_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5060_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5056_, 0, v_a_5052_);
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5056_);
v___x_5058_ = v___x_5054_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___x_5056_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
return v___x_5058_;
}
}
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5068_; 
v_a_5061_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5063_ = v___x_5051_;
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5051_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
}
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5077_; 
lean_dec_ref(v___x_5024_);
lean_dec(v_thmName_5016_);
v_a_5070_ = lean_ctor_get(v___x_5025_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5025_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5072_ = v___x_5025_;
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v___x_5025_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object* v_thmName_5078_, lean_object* v_levels_5079_, lean_object* v_____r_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5078_, v_levels_5079_, v_____r_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
return v_res_5086_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1(void){
_start:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5088_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0));
v___x_5089_ = l_Lean_stringToMessageData(v___x_5088_);
return v___x_5089_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3(void){
_start:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; 
v___x_5091_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2));
v___x_5092_ = l_Lean_stringToMessageData(v___x_5091_);
return v___x_5092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* v_declName_5093_, lean_object* v_levels_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_){
_start:
{
lean_object* v_a_5101_; lean_object* v___y_5119_; lean_object* v___x_5124_; lean_object* v_thmName_5125_; lean_object* v_a_5127_; lean_object* v___y_5158_; lean_object* v___x_5161_; lean_object* v_env_5162_; uint8_t v___x_5163_; 
v___x_5124_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v_thmName_5125_ = l_Lean_Name_str___override(v_declName_5093_, v___x_5124_);
v___x_5161_ = lean_st_ref_get(v_a_5098_);
v_env_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc_ref(v_env_5162_);
lean_dec(v___x_5161_);
v___x_5163_ = l_Lean_Environment_containsOnBranch(v_env_5162_, v_thmName_5125_);
lean_dec_ref(v_env_5162_);
if (v___x_5163_ == 0)
{
lean_object* v___x_5164_; 
lean_inc(v_thmName_5125_);
v___x_5164_ = l_Lean_executeReservedNameAction(v_thmName_5125_, v_a_5097_, v_a_5098_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
lean_dec_ref_known(v___x_5164_, 1);
v___x_5165_ = lean_box(0);
lean_inc(v_thmName_5125_);
v___x_5166_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5125_, v_levels_5094_, v___x_5165_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_);
v___y_5158_ = v___x_5166_;
goto v___jp_5157_;
}
else
{
lean_object* v_a_5167_; 
lean_dec(v_levels_5094_);
v_a_5167_ = lean_ctor_get(v___x_5164_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5164_, 1);
v_a_5127_ = v_a_5167_;
goto v___jp_5126_;
}
}
else
{
lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5168_ = lean_box(0);
lean_inc(v_thmName_5125_);
v___x_5169_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5125_, v_levels_5094_, v___x_5168_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_);
v___y_5158_ = v___x_5169_;
goto v___jp_5157_;
}
v___jp_5100_:
{
if (lean_obj_tag(v_a_5101_) == 0)
{
lean_object* v_a_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5109_; 
v_a_5102_ = lean_ctor_get(v_a_5101_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v_a_5101_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5104_ = v_a_5101_;
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_a_5102_);
lean_dec(v_a_5101_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5107_; 
if (v_isShared_5105_ == 0)
{
v___x_5107_ = v___x_5104_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_a_5102_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
v_a_5110_ = lean_ctor_get(v_a_5101_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v_a_5101_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v_a_5101_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v_a_5101_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
lean_ctor_set_tag(v___x_5112_, 0);
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
v___jp_5118_:
{
lean_object* v_a_5120_; 
v_a_5120_ = lean_ctor_get(v___y_5119_, 0);
lean_inc(v_a_5120_);
lean_dec_ref(v___y_5119_);
v_a_5101_ = v_a_5120_;
goto v___jp_5100_;
}
v___jp_5121_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; 
v___x_5122_ = lean_box(0);
v___x_5123_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v___x_5122_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_);
v___y_5119_ = v___x_5123_;
goto v___jp_5118_;
}
v___jp_5126_:
{
uint8_t v___x_5128_; 
v___x_5128_ = l_Lean_Exception_isInterrupt(v_a_5127_);
if (v___x_5128_ == 0)
{
uint8_t v___x_5129_; 
lean_inc_ref(v_a_5127_);
v___x_5129_ = l_Lean_Exception_isRuntime(v_a_5127_);
if (v___x_5129_ == 0)
{
lean_object* v_toCold_5130_; lean_object* v_options_5131_; uint8_t v_hasTrace_5132_; 
v_toCold_5130_ = lean_ctor_get(v_a_5097_, 0);
v_options_5131_ = lean_ctor_get(v_toCold_5130_, 2);
v_hasTrace_5132_ = lean_ctor_get_uint8(v_options_5131_, sizeof(void*)*1);
if (v_hasTrace_5132_ == 0)
{
lean_dec_ref(v_a_5127_);
lean_dec(v_thmName_5125_);
goto v___jp_5121_;
}
else
{
lean_object* v_inheritedTraceOptions_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; uint8_t v___x_5136_; 
v_inheritedTraceOptions_5133_ = lean_ctor_get(v_toCold_5130_, 11);
v___x_5134_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_5135_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_5136_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5133_, v_options_5131_, v___x_5135_);
if (v___x_5136_ == 0)
{
lean_dec_ref(v_a_5127_);
lean_dec(v_thmName_5125_);
goto v___jp_5121_;
}
else
{
lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5137_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1);
v___x_5138_ = l_Lean_MessageData_ofName(v_thmName_5125_);
v___x_5139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5139_, 0, v___x_5137_);
lean_ctor_set(v___x_5139_, 1, v___x_5138_);
v___x_5140_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3);
v___x_5141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
lean_ctor_set(v___x_5141_, 1, v___x_5140_);
v___x_5142_ = l_Lean_Exception_toMessageData(v_a_5127_);
v___x_5143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5141_);
lean_ctor_set(v___x_5143_, 1, v___x_5142_);
v___x_5144_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__3(v___x_5134_, v___x_5143_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v___x_5146_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5144_, 1);
v___x_5146_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_a_5145_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_);
v___y_5119_ = v___x_5146_;
goto v___jp_5118_;
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
v_a_5147_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5144_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5144_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
}
else
{
lean_object* v___x_5155_; 
lean_dec(v_thmName_5125_);
v___x_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5155_, 0, v_a_5127_);
return v___x_5155_;
}
}
else
{
lean_object* v___x_5156_; 
lean_dec(v_thmName_5125_);
v___x_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5156_, 0, v_a_5127_);
return v___x_5156_;
}
}
v___jp_5157_:
{
if (lean_obj_tag(v___y_5158_) == 0)
{
lean_object* v_a_5159_; 
lean_dec(v_thmName_5125_);
v_a_5159_ = lean_ctor_get(v___y_5158_, 0);
lean_inc(v_a_5159_);
lean_dec_ref_known(v___y_5158_, 1);
v_a_5101_ = v_a_5159_;
goto v___jp_5100_;
}
else
{
lean_object* v_a_5160_; 
v_a_5160_ = lean_ctor_get(v___y_5158_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___y_5158_, 1);
v_a_5127_ = v_a_5160_;
goto v___jp_5126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object* v_declName_5170_, lean_object* v_levels_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_5170_, v_levels_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
lean_dec(v_a_5175_);
lean_dec_ref(v_a_5174_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
return v_res_5177_;
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
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1460259042____hygCtx___hyg_2_();
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
