// Lean compiler output
// Module: Lean.LocalContext
// Imports: public import Init.Data.Nat.Control public import Lean.Data.PersistentArray public import Lean.Expr import Init.Data.ToString.Macro import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getSanitizeNames(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LocalDeclKind.default"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__0 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__1 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__1_value;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.LocalDeclKind.implDetail"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__2 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__3 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__3_value;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LocalDeclKind.auxDecl"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__4 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__5 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__5_value;
static lean_once_cell_t l_Lean_instReprLocalDeclKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLocalDeclKind_repr___closed__6;
static lean_once_cell_t l_Lean_instReprLocalDeclKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLocalDeclKind_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLocalDeclKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLocalDeclKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLocalDeclKind___closed__0 = (const lean_object*)&l_Lean_instReprLocalDeclKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLocalDeclKind = (const lean_object*)&l_Lean_instReprLocalDeclKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableLocalDeclKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableLocalDeclKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableLocalDeclKind___closed__0 = (const lean_object*)&l_Lean_instHashableLocalDeclKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableLocalDeclKind = (const lean_object*)&l_Lean_instHashableLocalDeclKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedLocalDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedLocalDecl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedLocalDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedLocalDecl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedLocalDecl_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalDecl_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedLocalDecl_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalDecl_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl;
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object*);
static const lean_string_object l_Lean_LocalDecl_value___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.LocalContext"};
static const lean_object* l_Lean_LocalDecl_value___closed__0 = (const lean_object*)&l_Lean_LocalDecl_value___closed__0_value;
static const lean_string_object l_Lean_LocalDecl_value___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.LocalDecl.value"};
static const lean_object* l_Lean_LocalDecl_value___closed__1 = (const lean_object*)&l_Lean_LocalDecl_value___closed__1_value;
static const lean_string_object l_Lean_LocalDecl_value___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "let declaration expected"};
static const lean_object* l_Lean_LocalDecl_value___closed__2 = (const lean_object*)&l_Lean_LocalDecl_value___closed__2_value;
static lean_once_cell_t l_Lean_LocalDecl_value___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_value___closed__3;
static const lean_string_object l_Lean_LocalDecl_value___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "dependent let declaration expected"};
static const lean_object* l_Lean_LocalDecl_value___closed__4 = (const lean_object*)&l_Lean_LocalDecl_value___closed__4_value;
static lean_once_cell_t l_Lean_LocalDecl_value___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_value___closed__5;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object*);
static const lean_string_object l_Lean_LocalDecl_setBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.LocalDecl.setBinderInfo"};
static const lean_object* l_Lean_LocalDecl_setBinderInfo___closed__0 = (const lean_object*)&l_Lean_LocalDecl_setBinderInfo___closed__0_value;
static const lean_string_object l_Lean_LocalDecl_setBinderInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected let declaration"};
static const lean_object* l_Lean_LocalDecl_setBinderInfo___closed__1 = (const lean_object*)&l_Lean_LocalDecl_setBinderInfo___closed__1_value;
static lean_once_cell_t l_Lean_LocalDecl_setBinderInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_setBinderInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__3;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext;
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.LocalContext.get!"};
static const lean_object* l_Lean_LocalContext_get_x21___closed__0 = (const lean_object*)&l_Lean_LocalContext_get_x21___closed__0_value;
static const lean_string_object l_Lean_LocalContext_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown free variable"};
static const lean_object* l_Lean_LocalContext_get_x21___closed__1 = (const lean_object*)&l_Lean_LocalContext_get_x21___closed__1_value;
static lean_once_cell_t l_Lean_LocalContext_get_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_get_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_LocalContext_getFVarIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LocalContext_getFVarIds___closed__0 = (const lean_object*)&l_Lean_LocalContext_getFVarIds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.LocalContext.getFromUserName!"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__0 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__0_value;
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unknown local declaration `"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__1 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__1_value;
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__2 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LocalContext_modifyLocalDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_modifyLocalDecl___closed__0 = (const lean_object*)&l_Lean_LocalContext_modifyLocalDecl___closed__0_value;
static const lean_closure_object l_Lean_LocalContext_modifyLocalDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_modifyLocalDecl___closed__1 = (const lean_object*)&l_Lean_LocalContext_modifyLocalDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__0 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__0_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__1 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__1_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__2 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__2_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__3 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__3_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__4 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__4_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__5 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__5_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__6 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__0_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__1_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__7 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__7_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__2_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__3_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__4_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__5_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__8 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__8_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__6_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__9 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_mkBinding___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.LocalContext.mkBinding"};
static const lean_object* l_Lean_LocalContext_mkBinding___lam__0___closed__0 = (const lean_object*)&l_Lean_LocalContext_mkBinding___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_LocalContext_mkBinding___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkBinding___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_LocalContext_findFromUserNames___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LocalContext_findFromUserNames___redArg___closed__0 = (const lean_object*)&l_Lean_LocalContext_findFromUserNames___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___redArg___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t v_x_1_){
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
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_LocalDeclKind_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_LocalDeclKind_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_LocalDeclKind_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_LocalDeclKind_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_LocalDeclKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_28_){
_start:
{
lean_inc(v_default_28_);
return v_default_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_29_);
lean_dec(v_default_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_default_34_){
_start:
{
lean_inc(v_default_34_);
return v_default_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_default_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_LocalDeclKind_default_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_default_38_);
lean_dec(v_default_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_41_){
_start:
{
lean_inc(v_implDetail_41_);
return v_implDetail_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_42_);
lean_dec(v_implDetail_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_implDetail_47_){
_start:
{
lean_inc(v_implDetail_47_);
return v_implDetail_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_implDetail_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_implDetail_51_);
lean_dec(v_implDetail_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_54_){
_start:
{
lean_inc(v_auxDecl_54_);
return v_auxDecl_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_55_);
lean_dec(v_auxDecl_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_auxDecl_60_){
_start:
{
lean_inc(v_auxDecl_60_);
return v_auxDecl_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_auxDecl_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_auxDecl_64_);
lean_dec(v_auxDecl_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_82_, lean_object* v_prec_83_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_92_; lean_object* v___y_99_; 
switch(v_x_82_)
{
case 0:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_83_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_85_ = v___x_107_;
goto v___jp_84_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_85_ = v___x_108_;
goto v___jp_84_;
}
}
case 1:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1024u);
v___x_110_ = lean_nat_dec_le(v___x_109_, v_prec_83_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_92_ = v___x_111_;
goto v___jp_91_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_92_ = v___x_112_;
goto v___jp_91_;
}
}
default: 
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1024u);
v___x_114_ = lean_nat_dec_le(v___x_113_, v_prec_83_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_99_ = v___x_115_;
goto v___jp_98_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_99_ = v___x_116_;
goto v___jp_98_;
}
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_83_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_83_);
return v___x_97_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___y_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = 0;
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v_prec_83_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
uint8_t v_x_177__boxed_119_; lean_object* v_res_120_; 
v_x_177__boxed_119_ = lean_unbox(v_x_117_);
v_res_120_ = l_Lean_instReprLocalDeclKind_repr(v_x_177__boxed_119_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_123_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_nat_dec_le(v_n_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_dec_le(v_n_123_, v___x_126_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 2;
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_LocalDeclKind_ofNat(v_n_131_);
lean_dec(v_n_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_134_, uint8_t v_y_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = l_Lean_LocalDeclKind_ctorIdx(v_x_134_);
v___x_137_ = l_Lean_LocalDeclKind_ctorIdx(v_y_135_);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
lean_dec(v___x_137_);
lean_dec(v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_139_, lean_object* v_y_140_){
_start:
{
uint8_t v_x_13__boxed_141_; uint8_t v_y_14__boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v_x_13__boxed_141_ = lean_unbox(v_x_139_);
v_y_14__boxed_142_ = lean_unbox(v_y_140_);
v_res_143_ = l_Lean_instDecidableEqLocalDeclKind(v_x_13__boxed_141_, v_y_14__boxed_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_145_){
_start:
{
switch(v_x_145_)
{
case 0:
{
uint64_t v___x_146_; 
v___x_146_ = 0ULL;
return v___x_146_;
}
case 1:
{
uint64_t v___x_147_; 
v___x_147_ = 1ULL;
return v___x_147_;
}
default: 
{
uint64_t v___x_148_; 
v___x_148_ = 2ULL;
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_40__boxed_150_; uint64_t v_res_151_; lean_object* v_r_152_; 
v_x_40__boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_150_);
v_r_152_ = lean_box_uint64(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(0u);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_unsigned_to_nat(1u);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_LocalDecl_ctorIdx(v_x_158_);
lean_dec_ref(v_x_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_160_, lean_object* v_k_161_){
_start:
{
if (lean_obj_tag(v_t_160_) == 0)
{
lean_object* v_index_162_; lean_object* v_fvarId_163_; lean_object* v_userName_164_; lean_object* v_type_165_; uint8_t v_bi_166_; uint8_t v_kind_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_index_162_ = lean_ctor_get(v_t_160_, 0);
lean_inc(v_index_162_);
v_fvarId_163_ = lean_ctor_get(v_t_160_, 1);
lean_inc(v_fvarId_163_);
v_userName_164_ = lean_ctor_get(v_t_160_, 2);
lean_inc(v_userName_164_);
v_type_165_ = lean_ctor_get(v_t_160_, 3);
lean_inc_ref(v_type_165_);
v_bi_166_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*4);
v_kind_167_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*4 + 1);
lean_dec_ref(v_t_160_);
v___x_168_ = lean_box(v_bi_166_);
v___x_169_ = lean_box(v_kind_167_);
v___x_170_ = lean_apply_6(v_k_161_, v_index_162_, v_fvarId_163_, v_userName_164_, v_type_165_, v___x_168_, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v_index_171_; lean_object* v_fvarId_172_; lean_object* v_userName_173_; lean_object* v_type_174_; lean_object* v_value_175_; uint8_t v_nondep_176_; uint8_t v_kind_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_index_171_ = lean_ctor_get(v_t_160_, 0);
lean_inc(v_index_171_);
v_fvarId_172_ = lean_ctor_get(v_t_160_, 1);
lean_inc(v_fvarId_172_);
v_userName_173_ = lean_ctor_get(v_t_160_, 2);
lean_inc(v_userName_173_);
v_type_174_ = lean_ctor_get(v_t_160_, 3);
lean_inc_ref(v_type_174_);
v_value_175_ = lean_ctor_get(v_t_160_, 4);
lean_inc_ref(v_value_175_);
v_nondep_176_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*5);
v_kind_177_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*5 + 1);
lean_dec_ref(v_t_160_);
v___x_178_ = lean_box(v_nondep_176_);
v___x_179_ = lean_box(v_kind_177_);
v___x_180_ = lean_apply_7(v_k_161_, v_index_171_, v_fvarId_172_, v_userName_173_, v_type_174_, v_value_175_, v___x_178_, v___x_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_181_, lean_object* v_ctorIdx_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_k_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_183_, v_k_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_LocalDecl_ctorElim(v_motive_187_, v_ctorIdx_188_, v_t_189_, v_h_190_, v_k_191_);
lean_dec(v_ctorIdx_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_193_, lean_object* v_cdecl_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_193_, v_cdecl_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_cdecl_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_197_, v_cdecl_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_201_, lean_object* v_ldecl_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_201_, v_ldecl_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_ldecl_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_205_, v_ldecl_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_box(0);
v___x_213_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_214_ = l_Lean_Expr_const___override(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_215_ = 0;
v___x_216_ = 0;
v___x_217_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_218_ = lean_box(0);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_218_);
lean_ctor_set(v___x_220_, 3, v___x_217_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*4, v___x_216_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*4 + 1, v___x_215_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_223_, lean_object* v_fvarId_224_, lean_object* v_userName_225_, lean_object* v_type_226_, uint8_t v_bi_227_){
_start:
{
uint8_t v___x_228_; lean_object* v___x_229_; 
v___x_228_ = 0;
v___x_229_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_229_, 0, v_index_223_);
lean_ctor_set(v___x_229_, 1, v_fvarId_224_);
lean_ctor_set(v___x_229_, 2, v_userName_225_);
lean_ctor_set(v___x_229_, 3, v_type_226_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*4, v_bi_227_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*4 + 1, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_230_, lean_object* v_fvarId_231_, lean_object* v_userName_232_, lean_object* v_type_233_, lean_object* v_bi_234_){
_start:
{
uint8_t v_bi_boxed_235_; lean_object* v_res_236_; 
v_bi_boxed_235_ = lean_unbox(v_bi_234_);
v_res_236_ = lean_mk_local_decl(v_index_230_, v_fvarId_231_, v_userName_232_, v_type_233_, v_bi_boxed_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_237_, lean_object* v_fvarId_238_, lean_object* v_userName_239_, lean_object* v_type_240_, lean_object* v_val_241_){
_start:
{
uint8_t v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; 
v___x_242_ = 0;
v___x_243_ = 0;
v___x_244_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_244_, 0, v_index_237_);
lean_ctor_set(v___x_244_, 1, v_fvarId_238_);
lean_ctor_set(v___x_244_, 2, v_userName_239_);
lean_ctor_set(v___x_244_, 3, v_type_240_);
lean_ctor_set(v___x_244_, 4, v_val_241_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5, v___x_242_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5 + 1, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
uint8_t v_bi_246_; 
v_bi_246_ = lean_ctor_get_uint8(v_x_245_, sizeof(void*)*4);
lean_dec_ref(v_x_245_);
return v_bi_246_;
}
else
{
uint8_t v___x_247_; 
lean_dec_ref(v_x_245_);
v___x_247_ = 0;
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = lean_local_decl_binder_info(v_x_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_251_, uint8_t v_x_252_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
else
{
uint8_t v_nondep_254_; 
v_nondep_254_ = lean_ctor_get_uint8(v_x_251_, sizeof(void*)*5);
if (v_nondep_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
else
{
return v_x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_x_53__boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v_x_53__boxed_258_ = lean_unbox(v_x_257_);
v_res_259_ = l_Lean_LocalDecl_isLet(v_x_256_, v_x_53__boxed_258_);
lean_dec_ref(v_x_256_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_261_){
_start:
{
lean_object* v_index_262_; 
v_index_262_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_index_262_);
return v_index_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_LocalDecl_index(v_x_263_);
lean_dec_ref(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_object* v_fvarId_267_; lean_object* v_userName_268_; lean_object* v_type_269_; uint8_t v_bi_270_; uint8_t v_kind_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_fvarId_267_ = lean_ctor_get(v_x_265_, 1);
v_userName_268_ = lean_ctor_get(v_x_265_, 2);
v_type_269_ = lean_ctor_get(v_x_265_, 3);
v_bi_270_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*4);
v_kind_271_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*4 + 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_x_265_, 0);
lean_dec(v_unused_279_);
v___x_273_ = v_x_265_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_type_269_);
lean_inc(v_userName_268_);
lean_inc(v_fvarId_267_);
lean_dec(v_x_265_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v_x_266_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_x_266_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_fvarId_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_userName_268_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_type_269_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*4, v_bi_270_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*4 + 1, v_kind_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v_fvarId_280_; lean_object* v_userName_281_; lean_object* v_type_282_; lean_object* v_value_283_; uint8_t v_nondep_284_; uint8_t v_kind_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_fvarId_280_ = lean_ctor_get(v_x_265_, 1);
v_userName_281_ = lean_ctor_get(v_x_265_, 2);
v_type_282_ = lean_ctor_get(v_x_265_, 3);
v_value_283_ = lean_ctor_get(v_x_265_, 4);
v_nondep_284_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*5);
v_kind_285_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*5 + 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_x_265_, 0);
lean_dec(v_unused_293_);
v___x_287_ = v_x_265_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_value_283_);
lean_inc(v_type_282_);
lean_inc(v_userName_281_);
lean_inc(v_fvarId_280_);
lean_dec(v_x_265_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v_x_266_);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_x_266_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_fvarId_280_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_userName_281_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_type_282_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_value_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*5, v_nondep_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*5 + 1, v_kind_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_294_){
_start:
{
lean_object* v_fvarId_295_; 
v_fvarId_295_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_fvarId_295_);
return v_fvarId_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_LocalDecl_fvarId(v_x_296_);
lean_dec_ref(v_x_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_298_){
_start:
{
lean_object* v_userName_299_; 
v_userName_299_ = lean_ctor_get(v_x_298_, 2);
lean_inc(v_userName_299_);
return v_userName_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_LocalDecl_userName(v_x_300_);
lean_dec_ref(v_x_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_302_){
_start:
{
lean_object* v_type_303_; 
v_type_303_ = lean_ctor_get(v_x_302_, 3);
lean_inc_ref(v_type_303_);
return v_type_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_LocalDecl_type(v_x_304_);
lean_dec_ref(v_x_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_object* v_index_308_; lean_object* v_fvarId_309_; lean_object* v_userName_310_; uint8_t v_bi_311_; uint8_t v_kind_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_index_308_ = lean_ctor_get(v_x_306_, 0);
v_fvarId_309_ = lean_ctor_get(v_x_306_, 1);
v_userName_310_ = lean_ctor_get(v_x_306_, 2);
v_bi_311_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*4);
v_kind_312_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*4 + 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_x_306_, 3);
lean_dec(v_unused_320_);
v___x_314_ = v_x_306_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_userName_310_);
lean_inc(v_fvarId_309_);
lean_inc(v_index_308_);
lean_dec(v_x_306_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 3, v_x_307_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_index_308_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_fvarId_309_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_userName_310_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_x_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*4, v_bi_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*4 + 1, v_kind_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_index_321_; lean_object* v_fvarId_322_; lean_object* v_userName_323_; lean_object* v_value_324_; uint8_t v_nondep_325_; uint8_t v_kind_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_index_321_ = lean_ctor_get(v_x_306_, 0);
v_fvarId_322_ = lean_ctor_get(v_x_306_, 1);
v_userName_323_ = lean_ctor_get(v_x_306_, 2);
v_value_324_ = lean_ctor_get(v_x_306_, 4);
v_nondep_325_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*5);
v_kind_326_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*5 + 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_x_306_, 3);
lean_dec(v_unused_334_);
v___x_328_ = v_x_306_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_value_324_);
lean_inc(v_userName_323_);
lean_inc(v_fvarId_322_);
lean_inc(v_index_321_);
lean_dec(v_x_306_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 3, v_x_307_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_index_321_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_fvarId_322_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_userName_323_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_x_307_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_value_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_332_, sizeof(void*)*5, v_nondep_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_332_, sizeof(void*)*5 + 1, v_kind_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
uint8_t v_bi_336_; 
v_bi_336_ = lean_ctor_get_uint8(v_x_335_, sizeof(void*)*4);
return v_bi_336_;
}
else
{
uint8_t v___x_337_; 
v___x_337_ = 0;
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Lean_LocalDecl_binderInfo(v_x_338_);
lean_dec_ref(v_x_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
uint8_t v_kind_342_; 
v_kind_342_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*4 + 1);
return v_kind_342_;
}
else
{
uint8_t v_kind_343_; 
v_kind_343_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*5 + 1);
return v_kind_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Lean_LocalDecl_kind(v_x_344_);
lean_dec_ref(v_x_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_347_){
_start:
{
uint8_t v___y_349_; 
if (lean_obj_tag(v_d_347_) == 0)
{
uint8_t v_kind_352_; 
v_kind_352_ = lean_ctor_get_uint8(v_d_347_, sizeof(void*)*4 + 1);
v___y_349_ = v_kind_352_;
goto v___jp_348_;
}
else
{
uint8_t v_kind_353_; 
v_kind_353_ = lean_ctor_get_uint8(v_d_347_, sizeof(void*)*5 + 1);
v___y_349_ = v_kind_353_;
goto v___jp_348_;
}
v___jp_348_:
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 2;
v___x_351_ = l_Lean_instDecidableEqLocalDeclKind(v___y_349_, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_LocalDecl_isAuxDecl(v_d_354_);
lean_dec_ref(v_d_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_357_){
_start:
{
uint8_t v___y_359_; 
if (lean_obj_tag(v_d_357_) == 0)
{
uint8_t v_kind_364_; 
v_kind_364_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*4 + 1);
v___y_359_ = v_kind_364_;
goto v___jp_358_;
}
else
{
uint8_t v_kind_365_; 
v_kind_365_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*5 + 1);
v___y_359_ = v_kind_365_;
goto v___jp_358_;
}
v___jp_358_:
{
uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_360_ = 0;
v___x_361_ = l_Lean_instDecidableEqLocalDeclKind(v___y_359_, v___x_360_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; 
v___x_362_ = 1;
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Lean_LocalDecl_isImplementationDetail(v_d_366_);
lean_dec_ref(v_d_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_369_, uint8_t v_x_370_){
_start:
{
if (lean_obj_tag(v_x_369_) == 1)
{
uint8_t v_nondep_371_; 
v_nondep_371_ = lean_ctor_get_uint8(v_x_369_, sizeof(void*)*5);
if (v_nondep_371_ == 0)
{
lean_object* v_value_372_; lean_object* v___x_373_; 
v_value_372_ = lean_ctor_get(v_x_369_, 4);
lean_inc_ref(v_value_372_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_value_372_);
return v___x_373_;
}
else
{
if (v_x_370_ == 1)
{
lean_object* v_value_374_; lean_object* v___x_375_; 
v_value_374_ = lean_ctor_get(v_x_369_, 4);
lean_inc_ref(v_value_374_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v_value_374_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_x_57__boxed_380_; lean_object* v_res_381_; 
v_x_57__boxed_380_ = lean_unbox(v_x_379_);
v_res_381_ = l_Lean_LocalDecl_value_x3f(v_x_378_, v_x_57__boxed_380_);
lean_dec_ref(v_x_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = l_Lean_instInhabitedExpr;
v___x_384_ = lean_panic_fn_borrowed(v___x_383_, v_msg_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_388_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_389_ = lean_unsigned_to_nat(54u);
v___x_390_ = lean_unsigned_to_nat(172u);
v___x_391_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_392_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_393_ = l_mkPanicMessageWithDecl(v___x_392_, v___x_391_, v___x_390_, v___x_389_, v___x_388_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_395_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_396_ = lean_unsigned_to_nat(54u);
v___x_397_ = lean_unsigned_to_nat(175u);
v___x_398_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_399_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_400_ = l_mkPanicMessageWithDecl(v___x_399_, v___x_398_, v___x_397_, v___x_396_, v___x_395_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_401_, uint8_t v_x_402_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_404_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_403_);
return v___x_404_;
}
else
{
uint8_t v_nondep_405_; 
v_nondep_405_ = lean_ctor_get_uint8(v_x_401_, sizeof(void*)*5);
if (v_nondep_405_ == 0)
{
lean_object* v_value_406_; 
v_value_406_ = lean_ctor_get(v_x_401_, 4);
lean_inc_ref(v_value_406_);
return v_value_406_;
}
else
{
if (v_x_402_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_408_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_407_);
return v___x_408_;
}
else
{
lean_object* v_value_409_; 
v_value_409_ = lean_ctor_get(v_x_401_, 4);
lean_inc_ref(v_value_409_);
return v_value_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
uint8_t v_x_143__boxed_412_; lean_object* v_res_413_; 
v_x_143__boxed_412_ = lean_unbox(v_x_411_);
v_res_413_ = l_Lean_LocalDecl_value(v_x_410_, v_x_143__boxed_412_);
lean_dec_ref(v_x_410_);
return v_res_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_414_, uint8_t v_x_415_){
_start:
{
if (lean_obj_tag(v_x_414_) == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
else
{
uint8_t v_nondep_417_; 
v_nondep_417_ = lean_ctor_get_uint8(v_x_414_, sizeof(void*)*5);
if (v_nondep_417_ == 0)
{
uint8_t v___x_418_; 
v___x_418_ = 1;
return v___x_418_;
}
else
{
return v_x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_x_72__boxed_421_; uint8_t v_res_422_; lean_object* v_r_423_; 
v_x_72__boxed_421_ = lean_unbox(v_x_420_);
v_res_422_ = l_Lean_LocalDecl_hasValue(v_x_419_, v_x_72__boxed_421_);
lean_dec_ref(v_x_419_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_424_) == 1)
{
lean_object* v_index_426_; lean_object* v_fvarId_427_; lean_object* v_userName_428_; lean_object* v_type_429_; uint8_t v_nondep_430_; uint8_t v_kind_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_index_426_ = lean_ctor_get(v_x_424_, 0);
v_fvarId_427_ = lean_ctor_get(v_x_424_, 1);
v_userName_428_ = lean_ctor_get(v_x_424_, 2);
v_type_429_ = lean_ctor_get(v_x_424_, 3);
v_nondep_430_ = lean_ctor_get_uint8(v_x_424_, sizeof(void*)*5);
v_kind_431_ = lean_ctor_get_uint8(v_x_424_, sizeof(void*)*5 + 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v_x_424_, 4);
lean_dec(v_unused_439_);
v___x_433_ = v_x_424_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_type_429_);
lean_inc(v_userName_428_);
lean_inc(v_fvarId_427_);
lean_inc(v_index_426_);
lean_dec(v_x_424_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 4, v_x_425_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_index_426_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_fvarId_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_userName_428_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_type_429_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_x_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*5, v_nondep_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*5 + 1, v_kind_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_dec_ref(v_x_425_);
return v_x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_440_, uint8_t v_x_441_){
_start:
{
if (lean_obj_tag(v_x_440_) == 1)
{
lean_object* v_index_442_; lean_object* v_fvarId_443_; lean_object* v_userName_444_; lean_object* v_type_445_; lean_object* v_value_446_; uint8_t v_kind_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_index_442_ = lean_ctor_get(v_x_440_, 0);
v_fvarId_443_ = lean_ctor_get(v_x_440_, 1);
v_userName_444_ = lean_ctor_get(v_x_440_, 2);
v_type_445_ = lean_ctor_get(v_x_440_, 3);
v_value_446_ = lean_ctor_get(v_x_440_, 4);
v_kind_447_ = lean_ctor_get_uint8(v_x_440_, sizeof(void*)*5 + 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v_x_440_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_value_446_);
lean_inc(v_type_445_);
lean_inc(v_userName_444_);
lean_inc(v_fvarId_443_);
lean_inc(v_index_442_);
lean_dec(v_x_440_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_index_442_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_fvarId_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_userName_444_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_type_445_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_value_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*5 + 1, v_kind_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*5, v_x_441_);
return v___x_452_;
}
}
}
else
{
return v_x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_x_27__boxed_457_; lean_object* v_res_458_; 
v_x_27__boxed_457_ = lean_unbox(v_x_456_);
v_res_458_ = l_Lean_LocalDecl_setNondep(v_x_455_, v_x_27__boxed_457_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 1)
{
uint8_t v_nondep_460_; 
v_nondep_460_ = lean_ctor_get_uint8(v_x_459_, sizeof(void*)*5);
return v_nondep_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Lean_LocalDecl_isNondep(v_x_462_);
lean_dec_ref(v_x_462_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v_index_467_; lean_object* v_fvarId_468_; lean_object* v_type_469_; uint8_t v_bi_470_; uint8_t v_kind_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_index_467_ = lean_ctor_get(v_x_465_, 0);
v_fvarId_468_ = lean_ctor_get(v_x_465_, 1);
v_type_469_ = lean_ctor_get(v_x_465_, 3);
v_bi_470_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*4);
v_kind_471_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*4 + 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v_x_465_, 2);
lean_dec(v_unused_479_);
v___x_473_ = v_x_465_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_type_469_);
lean_inc(v_fvarId_468_);
lean_inc(v_index_467_);
lean_dec(v_x_465_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 2, v_x_466_);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_index_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_fvarId_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_x_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_type_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*4, v_bi_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*4 + 1, v_kind_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_index_480_; lean_object* v_fvarId_481_; lean_object* v_type_482_; lean_object* v_value_483_; uint8_t v_nondep_484_; uint8_t v_kind_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_index_480_ = lean_ctor_get(v_x_465_, 0);
v_fvarId_481_ = lean_ctor_get(v_x_465_, 1);
v_type_482_ = lean_ctor_get(v_x_465_, 3);
v_value_483_ = lean_ctor_get(v_x_465_, 4);
v_nondep_484_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*5);
v_kind_485_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*5 + 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_x_465_, 2);
lean_dec(v_unused_493_);
v___x_487_ = v_x_465_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_value_483_);
lean_inc(v_type_482_);
lean_inc(v_fvarId_481_);
lean_inc(v_index_480_);
lean_dec(v_x_465_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 2, v_x_466_);
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_index_480_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_fvarId_481_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_x_466_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_type_482_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_value_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5, v_nondep_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5 + 1, v_kind_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = l_Lean_instInhabitedLocalDecl_default;
v___x_496_ = lean_panic_fn_borrowed(v___x_495_, v_msg_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_500_ = lean_unsigned_to_nat(38u);
v___x_501_ = lean_unsigned_to_nat(237u);
v___x_502_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_503_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_504_ = l_mkPanicMessageWithDecl(v___x_503_, v___x_502_, v___x_501_, v___x_500_, v___x_499_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_505_, uint8_t v_x_506_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v_index_507_; lean_object* v_fvarId_508_; lean_object* v_userName_509_; lean_object* v_type_510_; uint8_t v_kind_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_index_507_ = lean_ctor_get(v_x_505_, 0);
v_fvarId_508_ = lean_ctor_get(v_x_505_, 1);
v_userName_509_ = lean_ctor_get(v_x_505_, 2);
v_type_510_ = lean_ctor_get(v_x_505_, 3);
v_kind_511_ = lean_ctor_get_uint8(v_x_505_, sizeof(void*)*4 + 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v_x_505_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_type_510_);
lean_inc(v_userName_509_);
lean_inc(v_fvarId_508_);
lean_inc(v_index_507_);
lean_dec(v_x_505_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_index_507_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_fvarId_508_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_userName_509_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_type_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_517_, sizeof(void*)*4 + 1, v_kind_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*4, v_x_506_);
return v___x_516_;
}
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref(v_x_505_);
v___x_519_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_520_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
uint8_t v_x_84__boxed_523_; lean_object* v_res_524_; 
v_x_84__boxed_523_ = lean_unbox(v_x_522_);
v_res_524_ = l_Lean_LocalDecl_setBinderInfo(v_x_521_, v_x_84__boxed_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_525_){
_start:
{
lean_object* v_fvarId_526_; lean_object* v___x_527_; 
v_fvarId_526_ = lean_ctor_get(v_decl_525_, 1);
lean_inc(v_fvarId_526_);
lean_dec_ref(v_decl_525_);
v___x_527_ = l_Lean_mkFVar(v_fvarId_526_);
return v___x_527_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_type_529_; uint8_t v___x_530_; 
v_type_529_ = lean_ctor_get(v_x_528_, 3);
v___x_530_ = l_Lean_Expr_hasExprMVar(v_type_529_);
return v___x_530_;
}
else
{
lean_object* v_type_531_; lean_object* v_value_532_; uint8_t v___x_533_; 
v_type_531_ = lean_ctor_get(v_x_528_, 3);
v_value_532_ = lean_ctor_get(v_x_528_, 4);
v___x_533_ = l_Lean_Expr_hasExprMVar(v_type_531_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
v___x_534_ = l_Lean_Expr_hasExprMVar(v_value_532_);
return v___x_534_;
}
else
{
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Lean_LocalDecl_hasExprMVar(v_x_535_);
lean_dec_ref(v_x_535_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_538_, uint8_t v_x_539_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v_index_540_; lean_object* v_fvarId_541_; lean_object* v_userName_542_; lean_object* v_type_543_; uint8_t v_bi_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_index_540_ = lean_ctor_get(v_x_538_, 0);
v_fvarId_541_ = lean_ctor_get(v_x_538_, 1);
v_userName_542_ = lean_ctor_get(v_x_538_, 2);
v_type_543_ = lean_ctor_get(v_x_538_, 3);
v_bi_544_ = lean_ctor_get_uint8(v_x_538_, sizeof(void*)*4);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v_x_538_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_type_543_);
lean_inc(v_userName_542_);
lean_inc(v_fvarId_541_);
lean_inc(v_index_540_);
lean_dec(v_x_538_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_index_540_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_fvarId_541_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_userName_542_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_type_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*4, v_bi_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*4 + 1, v_x_539_);
return v___x_549_;
}
}
}
else
{
lean_object* v_index_552_; lean_object* v_fvarId_553_; lean_object* v_userName_554_; lean_object* v_type_555_; lean_object* v_value_556_; uint8_t v_nondep_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_index_552_ = lean_ctor_get(v_x_538_, 0);
v_fvarId_553_ = lean_ctor_get(v_x_538_, 1);
v_userName_554_ = lean_ctor_get(v_x_538_, 2);
v_type_555_ = lean_ctor_get(v_x_538_, 3);
v_value_556_ = lean_ctor_get(v_x_538_, 4);
v_nondep_557_ = lean_ctor_get_uint8(v_x_538_, sizeof(void*)*5);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v_x_538_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_value_556_);
lean_inc(v_type_555_);
lean_inc(v_userName_554_);
lean_inc(v_fvarId_553_);
lean_inc(v_index_552_);
lean_dec(v_x_538_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_index_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_fvarId_553_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_userName_554_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_type_555_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_value_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*5, v_nondep_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*5 + 1, v_x_539_);
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
uint8_t v_x_31__boxed_567_; lean_object* v_res_568_; 
v_x_31__boxed_567_ = lean_unbox(v_x_566_);
v_res_568_ = l_Lean_LocalDecl_setKind(v_x_565_, v_x_31__boxed_567_);
return v_res_568_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_569_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(32u);
v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_575_ = ((size_t)5ULL);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_unsigned_to_nat(32u);
v___x_578_ = lean_mk_empty_array_with_capacity(v___x_577_);
v___x_579_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_580_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_576_);
lean_ctor_set(v___x_580_, 3, v___x_576_);
lean_ctor_set_usize(v___x_580_, 4, v___x_575_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_box(1);
v___x_582_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_583_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
lean_ctor_set(v___x_584_, 2, v___x_581_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_instInhabitedLocalContext_default;
return v___x_586_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(32u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
lean_dec_ref(v___x_589_);
v___x_590_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_unsigned_to_nat(32u);
v___x_592_ = lean_mk_empty_array_with_capacity(v___x_591_);
lean_dec_ref(v___x_592_);
v___x_593_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_596_);
lean_dec_ref(v_x_596_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_599_, lean_object* v_x_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_602_, lean_object* v_x_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_602_, v_x_603_);
lean_dec_ref(v_x_603_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* v_lctx_606_){
_start:
{
lean_object* v_fvarIdToDecl_607_; uint8_t v___x_608_; 
v_fvarIdToDecl_607_ = lean_ctor_get(v_lctx_606_, 0);
lean_inc_ref(v_fvarIdToDecl_607_);
lean_dec_ref(v_lctx_606_);
v___x_608_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_607_);
lean_dec_ref(v_fvarIdToDecl_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = lean_local_ctx_is_empty(v_lctx_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_ks_616_; lean_object* v_vs_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_641_; 
v_ks_616_ = lean_ctor_get(v_x_612_, 0);
v_vs_617_ = lean_ctor_get(v_x_612_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_641_ == 0)
{
v___x_619_ = v_x_612_;
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_vs_617_);
lean_inc(v_ks_616_);
lean_dec(v_x_612_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_get_size(v_ks_616_);
v___x_622_ = lean_nat_dec_lt(v_x_613_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
lean_dec(v_x_613_);
v___x_623_ = lean_array_push(v_ks_616_, v_x_614_);
v___x_624_ = lean_array_push(v_vs_617_, v_x_615_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_624_);
lean_ctor_set(v___x_619_, 0, v___x_623_);
v___x_626_ = v___x_619_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v_k_x27_628_; uint8_t v___x_629_; 
v_k_x27_628_ = lean_array_fget_borrowed(v_ks_616_, v_x_613_);
v___x_629_ = l_Lean_instBEqFVarId_beq(v_x_614_, v_k_x27_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_631_; 
if (v_isShared_620_ == 0)
{
v___x_631_ = v___x_619_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_ks_616_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_vs_617_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_add(v_x_613_, v___x_632_);
lean_dec(v_x_613_);
v_x_612_ = v___x_631_;
v_x_613_ = v___x_633_;
goto _start;
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = lean_array_fset(v_ks_616_, v_x_613_, v_x_614_);
v___x_637_ = lean_array_fset(v_vs_617_, v_x_613_, v_x_615_);
lean_dec(v_x_613_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_637_);
lean_ctor_set(v___x_619_, 0, v___x_636_);
v___x_639_ = v___x_619_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_642_, lean_object* v_k_643_, lean_object* v_v_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_642_, v___x_645_, v_k_643_, v_v_644_);
return v___x_646_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; 
v___x_647_ = ((size_t)5ULL);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_shift_left(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; 
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_652_ = lean_usize_sub(v___x_651_, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_654_, size_t v_x_655_, size_t v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_es_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; lean_object* v_j_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_es_659_ = lean_ctor_get(v_x_654_, 0);
v___x_660_ = ((size_t)5ULL);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_663_ = lean_usize_land(v_x_655_, v___x_662_);
v_j_664_ = lean_usize_to_nat(v___x_663_);
v___x_665_ = lean_array_get_size(v_es_659_);
v___x_666_ = lean_nat_dec_lt(v_j_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec(v_j_664_);
lean_dec(v_x_658_);
lean_dec(v_x_657_);
return v_x_654_;
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_703_; 
lean_inc_ref(v_es_659_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_x_654_, 0);
lean_dec(v_unused_704_);
v___x_668_ = v_x_654_;
v_isShared_669_ = v_isSharedCheck_703_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_x_654_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_703_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v_xs_x27_672_; lean_object* v___y_674_; 
v_v_670_ = lean_array_fget(v_es_659_, v_j_664_);
v___x_671_ = lean_box(0);
v_xs_x27_672_ = lean_array_fset(v_es_659_, v_j_664_, v___x_671_);
switch(lean_obj_tag(v_v_670_))
{
case 0:
{
lean_object* v_key_679_; lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_690_; 
v_key_679_ = lean_ctor_get(v_v_670_, 0);
v_val_680_ = lean_ctor_get(v_v_670_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_690_ == 0)
{
v___x_682_ = v_v_670_;
v_isShared_683_ = v_isSharedCheck_690_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_inc(v_key_679_);
lean_dec(v_v_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_690_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_instBEqFVarId_beq(v_x_657_, v_key_679_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_del_object(v___x_682_);
v___x_685_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_679_, v_val_680_, v_x_657_, v_x_658_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___y_674_ = v___x_686_;
goto v___jp_673_;
}
else
{
lean_object* v___x_688_; 
lean_dec(v_val_680_);
lean_dec(v_key_679_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_x_658_);
lean_ctor_set(v___x_682_, 0, v_x_657_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_x_657_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_x_658_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v___y_674_ = v___x_688_;
goto v___jp_673_;
}
}
}
}
case 1:
{
lean_object* v_node_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_701_; 
v_node_691_ = lean_ctor_get(v_v_670_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_701_ == 0)
{
v___x_693_ = v_v_670_;
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_node_691_);
lean_dec(v_v_670_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_695_ = lean_usize_shift_right(v_x_655_, v___x_660_);
v___x_696_ = lean_usize_add(v_x_656_, v___x_661_);
v___x_697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_691_, v___x_695_, v___x_696_, v_x_657_, v_x_658_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_697_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v___y_674_ = v___x_699_;
goto v___jp_673_;
}
}
}
default: 
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_x_657_);
lean_ctor_set(v___x_702_, 1, v_x_658_);
v___y_674_ = v___x_702_;
goto v___jp_673_;
}
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_array_fset(v_xs_x27_672_, v_j_664_, v___y_674_);
lean_dec(v_j_664_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_675_);
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
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
else
{
lean_object* v_ks_705_; lean_object* v_vs_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_726_; 
v_ks_705_ = lean_ctor_get(v_x_654_, 0);
v_vs_706_ = lean_ctor_get(v_x_654_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_726_ == 0)
{
v___x_708_ = v_x_654_;
v_isShared_709_ = v_isSharedCheck_726_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_vs_706_);
lean_inc(v_ks_705_);
lean_dec(v_x_654_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_726_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_ks_705_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_vs_706_);
v___x_711_ = v_reuseFailAlloc_725_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v_newNode_712_; uint8_t v___y_714_; size_t v___x_720_; uint8_t v___x_721_; 
v_newNode_712_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_711_, v_x_657_, v_x_658_);
v___x_720_ = ((size_t)7ULL);
v___x_721_ = lean_usize_dec_le(v___x_720_, v_x_656_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_712_);
v___x_723_ = lean_unsigned_to_nat(4u);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
v___y_714_ = v___x_724_;
goto v___jp_713_;
}
else
{
v___y_714_ = v___x_721_;
goto v___jp_713_;
}
v___jp_713_:
{
if (v___y_714_ == 0)
{
lean_object* v_ks_715_; lean_object* v_vs_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_ks_715_ = lean_ctor_get(v_newNode_712_, 0);
lean_inc_ref(v_ks_715_);
v_vs_716_ = lean_ctor_get(v_newNode_712_, 1);
lean_inc_ref(v_vs_716_);
lean_dec_ref(v_newNode_712_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2);
v___x_719_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_656_, v_ks_715_, v_vs_716_, v___x_717_, v___x_718_);
lean_dec_ref(v_vs_716_);
lean_dec_ref(v_ks_715_);
return v___x_719_;
}
else
{
return v_newNode_712_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_727_, lean_object* v_keys_728_, lean_object* v_vals_729_, lean_object* v_i_730_, lean_object* v_entries_731_){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_array_get_size(v_keys_728_);
v___x_733_ = lean_nat_dec_lt(v_i_730_, v___x_732_);
if (v___x_733_ == 0)
{
lean_dec(v_i_730_);
return v_entries_731_;
}
else
{
lean_object* v_k_734_; lean_object* v_v_735_; uint64_t v___x_736_; size_t v_h_737_; size_t v___x_738_; lean_object* v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v_h_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_k_734_ = lean_array_fget_borrowed(v_keys_728_, v_i_730_);
v_v_735_ = lean_array_fget_borrowed(v_vals_729_, v_i_730_);
v___x_736_ = l_Lean_instHashableFVarId_hash(v_k_734_);
v_h_737_ = lean_uint64_to_usize(v___x_736_);
v___x_738_ = ((size_t)5ULL);
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_sub(v_depth_727_, v___x_740_);
v___x_742_ = lean_usize_mul(v___x_738_, v___x_741_);
v_h_743_ = lean_usize_shift_right(v_h_737_, v___x_742_);
v___x_744_ = lean_nat_add(v_i_730_, v___x_739_);
lean_dec(v_i_730_);
lean_inc(v_v_735_);
lean_inc(v_k_734_);
v___x_745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_731_, v_h_743_, v_depth_727_, v_k_734_, v_v_735_);
v_i_730_ = v___x_744_;
v_entries_731_ = v___x_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_747_, lean_object* v_keys_748_, lean_object* v_vals_749_, lean_object* v_i_750_, lean_object* v_entries_751_){
_start:
{
size_t v_depth_boxed_752_; lean_object* v_res_753_; 
v_depth_boxed_752_ = lean_unbox_usize(v_depth_747_);
lean_dec(v_depth_747_);
v_res_753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_752_, v_keys_748_, v_vals_749_, v_i_750_, v_entries_751_);
lean_dec_ref(v_vals_749_);
lean_dec_ref(v_keys_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
size_t v_x_371__boxed_759_; size_t v_x_372__boxed_760_; lean_object* v_res_761_; 
v_x_371__boxed_759_ = lean_unbox_usize(v_x_755_);
lean_dec(v_x_755_);
v_x_372__boxed_760_ = lean_unbox_usize(v_x_756_);
lean_dec(v_x_756_);
v_res_761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_754_, v_x_371__boxed_759_, v_x_372__boxed_760_, v_x_757_, v_x_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
uint64_t v___x_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_765_ = l_Lean_instHashableFVarId_hash(v_x_763_);
v___x_766_ = lean_uint64_to_usize(v___x_765_);
v___x_767_ = ((size_t)1ULL);
v___x_768_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_762_, v___x_766_, v___x_767_, v_x_763_, v_x_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_769_, lean_object* v_fvarId_770_, lean_object* v_userName_771_, lean_object* v_type_772_, uint8_t v_bi_773_, uint8_t v_kind_774_){
_start:
{
lean_object* v_decls_775_; lean_object* v_fvarIdToDecl_776_; lean_object* v_auxDeclToFullName_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_789_; 
v_decls_775_ = lean_ctor_get(v_lctx_769_, 1);
v_fvarIdToDecl_776_ = lean_ctor_get(v_lctx_769_, 0);
v_auxDeclToFullName_777_ = lean_ctor_get(v_lctx_769_, 2);
v_isSharedCheck_789_ = !lean_is_exclusive(v_lctx_769_);
if (v_isSharedCheck_789_ == 0)
{
v___x_779_ = v_lctx_769_;
v_isShared_780_ = v_isSharedCheck_789_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_auxDeclToFullName_777_);
lean_inc(v_decls_775_);
lean_inc(v_fvarIdToDecl_776_);
lean_dec(v_lctx_769_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_789_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_size_781_; lean_object* v_decl_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v_size_781_ = lean_ctor_get(v_decls_775_, 2);
lean_inc(v_fvarId_770_);
lean_inc(v_size_781_);
v_decl_782_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_782_, 0, v_size_781_);
lean_ctor_set(v_decl_782_, 1, v_fvarId_770_);
lean_ctor_set(v_decl_782_, 2, v_userName_771_);
lean_ctor_set(v_decl_782_, 3, v_type_772_);
lean_ctor_set_uint8(v_decl_782_, sizeof(void*)*4, v_bi_773_);
lean_ctor_set_uint8(v_decl_782_, sizeof(void*)*4 + 1, v_kind_774_);
lean_inc_ref(v_decl_782_);
v___x_783_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_776_, v_fvarId_770_, v_decl_782_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_decl_782_);
v___x_785_ = l_Lean_PersistentArray_push___redArg(v_decls_775_, v___x_784_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_785_);
lean_ctor_set(v___x_779_, 0, v___x_783_);
v___x_787_ = v___x_779_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_auxDeclToFullName_777_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_790_, lean_object* v_fvarId_791_, lean_object* v_userName_792_, lean_object* v_type_793_, lean_object* v_bi_794_, lean_object* v_kind_795_){
_start:
{
uint8_t v_bi_boxed_796_; uint8_t v_kind_boxed_797_; lean_object* v_res_798_; 
v_bi_boxed_796_ = lean_unbox(v_bi_794_);
v_kind_boxed_797_ = lean_unbox(v_kind_795_);
v_res_798_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_790_, v_fvarId_791_, v_userName_792_, v_type_793_, v_bi_boxed_796_, v_kind_boxed_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_800_, v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, size_t v_x_806_, size_t v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_805_, v_x_806_, v_x_807_, v_x_808_, v_x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
size_t v_x_581__boxed_817_; size_t v_x_582__boxed_818_; lean_object* v_res_819_; 
v_x_581__boxed_817_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_x_582__boxed_818_ = lean_unbox_usize(v_x_814_);
lean_dec(v_x_814_);
v_res_819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_811_, v_x_812_, v_x_581__boxed_817_, v_x_582__boxed_818_, v_x_815_, v_x_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_820_, lean_object* v_n_821_, lean_object* v_k_822_, lean_object* v_v_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_821_, v_k_822_, v_v_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_825_, size_t v_depth_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_entries_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_826_, v_keys_827_, v_vals_828_, v_i_830_, v_entries_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_833_, lean_object* v_depth_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_heq_837_, lean_object* v_i_838_, lean_object* v_entries_839_){
_start:
{
size_t v_depth_boxed_840_; lean_object* v_res_841_; 
v_depth_boxed_840_ = lean_unbox_usize(v_depth_834_);
lean_dec(v_depth_834_);
v_res_841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_833_, v_depth_boxed_840_, v_keys_835_, v_vals_836_, v_heq_837_, v_i_838_, v_entries_839_);
lean_dec_ref(v_vals_836_);
lean_dec_ref(v_keys_835_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_843_, v_x_844_, v_x_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_848_, lean_object* v_fvarId_849_, lean_object* v_userName_850_, lean_object* v_type_851_, uint8_t v_bi_852_){
_start:
{
uint8_t v___x_853_; lean_object* v___x_854_; 
v___x_853_ = 0;
v___x_854_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_848_, v_fvarId_849_, v_userName_850_, v_type_851_, v_bi_852_, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_855_, lean_object* v_fvarId_856_, lean_object* v_userName_857_, lean_object* v_type_858_, lean_object* v_bi_859_){
_start:
{
uint8_t v_bi_boxed_860_; lean_object* v_res_861_; 
v_bi_boxed_860_ = lean_unbox(v_bi_859_);
v_res_861_ = lean_local_ctx_mk_local_decl(v_lctx_855_, v_fvarId_856_, v_userName_857_, v_type_858_, v_bi_boxed_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_862_, lean_object* v_fvarId_863_, lean_object* v_userName_864_, lean_object* v_type_865_, lean_object* v_value_866_, uint8_t v_nondep_867_, uint8_t v_kind_868_){
_start:
{
lean_object* v_decls_869_; lean_object* v_fvarIdToDecl_870_; lean_object* v_auxDeclToFullName_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_883_; 
v_decls_869_ = lean_ctor_get(v_lctx_862_, 1);
v_fvarIdToDecl_870_ = lean_ctor_get(v_lctx_862_, 0);
v_auxDeclToFullName_871_ = lean_ctor_get(v_lctx_862_, 2);
v_isSharedCheck_883_ = !lean_is_exclusive(v_lctx_862_);
if (v_isSharedCheck_883_ == 0)
{
v___x_873_ = v_lctx_862_;
v_isShared_874_ = v_isSharedCheck_883_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_auxDeclToFullName_871_);
lean_inc(v_decls_869_);
lean_inc(v_fvarIdToDecl_870_);
lean_dec(v_lctx_862_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_883_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_size_875_; lean_object* v_decl_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v_size_875_ = lean_ctor_get(v_decls_869_, 2);
lean_inc(v_fvarId_863_);
lean_inc(v_size_875_);
v_decl_876_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_876_, 0, v_size_875_);
lean_ctor_set(v_decl_876_, 1, v_fvarId_863_);
lean_ctor_set(v_decl_876_, 2, v_userName_864_);
lean_ctor_set(v_decl_876_, 3, v_type_865_);
lean_ctor_set(v_decl_876_, 4, v_value_866_);
lean_ctor_set_uint8(v_decl_876_, sizeof(void*)*5, v_nondep_867_);
lean_ctor_set_uint8(v_decl_876_, sizeof(void*)*5 + 1, v_kind_868_);
lean_inc_ref(v_decl_876_);
v___x_877_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_870_, v_fvarId_863_, v_decl_876_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_decl_876_);
v___x_879_ = l_Lean_PersistentArray_push___redArg(v_decls_869_, v___x_878_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 1, v___x_879_);
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_881_ = v___x_873_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_auxDeclToFullName_871_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_884_, lean_object* v_fvarId_885_, lean_object* v_userName_886_, lean_object* v_type_887_, lean_object* v_value_888_, lean_object* v_nondep_889_, lean_object* v_kind_890_){
_start:
{
uint8_t v_nondep_boxed_891_; uint8_t v_kind_boxed_892_; lean_object* v_res_893_; 
v_nondep_boxed_891_ = lean_unbox(v_nondep_889_);
v_kind_boxed_892_ = lean_unbox(v_kind_890_);
v_res_893_ = l_Lean_LocalContext_mkLetDecl(v_lctx_884_, v_fvarId_885_, v_userName_886_, v_type_887_, v_value_888_, v_nondep_boxed_891_, v_kind_boxed_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_894_, lean_object* v_fvarId_895_, lean_object* v_userName_896_, lean_object* v_type_897_, lean_object* v_value_898_, uint8_t v_nondep_899_){
_start:
{
uint8_t v___x_900_; lean_object* v___x_901_; 
v___x_900_ = 0;
v___x_901_ = l_Lean_LocalContext_mkLetDecl(v_lctx_894_, v_fvarId_895_, v_userName_896_, v_type_897_, v_value_898_, v_nondep_899_, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_902_, lean_object* v_fvarId_903_, lean_object* v_userName_904_, lean_object* v_type_905_, lean_object* v_value_906_, lean_object* v_nondep_907_){
_start:
{
uint8_t v_nondep_boxed_908_; lean_object* v_res_909_; 
v_nondep_boxed_908_ = lean_unbox(v_nondep_907_);
v_res_909_ = lean_local_ctx_mk_let_decl(v_lctx_902_, v_fvarId_903_, v_userName_904_, v_type_905_, v_value_906_, v_nondep_boxed_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_910_, lean_object* v_fvarId_911_, lean_object* v_userName_912_, lean_object* v_type_913_, lean_object* v_fullName_914_){
_start:
{
lean_object* v_decls_915_; lean_object* v_fvarIdToDecl_916_; lean_object* v_auxDeclToFullName_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_932_; 
v_decls_915_ = lean_ctor_get(v_lctx_910_, 1);
v_fvarIdToDecl_916_ = lean_ctor_get(v_lctx_910_, 0);
v_auxDeclToFullName_917_ = lean_ctor_get(v_lctx_910_, 2);
v_isSharedCheck_932_ = !lean_is_exclusive(v_lctx_910_);
if (v_isSharedCheck_932_ == 0)
{
v___x_919_ = v_lctx_910_;
v_isShared_920_ = v_isSharedCheck_932_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_auxDeclToFullName_917_);
lean_inc(v_decls_915_);
lean_inc(v_fvarIdToDecl_916_);
lean_dec(v_lctx_910_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_932_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_size_921_; uint8_t v___x_922_; uint8_t v___x_923_; lean_object* v_decl_924_; lean_object* v_auxDeclToFullName_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v_size_921_ = lean_ctor_get(v_decls_915_, 2);
v___x_922_ = 0;
v___x_923_ = 2;
lean_inc_n(v_fvarId_911_, 2);
lean_inc(v_size_921_);
v_decl_924_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_924_, 0, v_size_921_);
lean_ctor_set(v_decl_924_, 1, v_fvarId_911_);
lean_ctor_set(v_decl_924_, 2, v_userName_912_);
lean_ctor_set(v_decl_924_, 3, v_type_913_);
lean_ctor_set_uint8(v_decl_924_, sizeof(void*)*4, v___x_922_);
lean_ctor_set_uint8(v_decl_924_, sizeof(void*)*4 + 1, v___x_923_);
v_auxDeclToFullName_925_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_911_, v_fullName_914_, v_auxDeclToFullName_917_);
lean_inc_ref(v_decl_924_);
v___x_926_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_916_, v_fvarId_911_, v_decl_924_);
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v_decl_924_);
v___x_928_ = l_Lean_PersistentArray_push___redArg(v_decls_915_, v___x_927_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 2, v_auxDeclToFullName_925_);
lean_ctor_set(v___x_919_, 1, v___x_928_);
lean_ctor_set(v___x_919_, 0, v___x_926_);
v___x_930_ = v___x_919_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_auxDeclToFullName_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_933_, lean_object* v_newDecl_934_){
_start:
{
lean_object* v_decls_935_; lean_object* v_fvarIdToDecl_936_; lean_object* v_auxDeclToFullName_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_952_; 
v_decls_935_ = lean_ctor_get(v_lctx_933_, 1);
v_fvarIdToDecl_936_ = lean_ctor_get(v_lctx_933_, 0);
v_auxDeclToFullName_937_ = lean_ctor_get(v_lctx_933_, 2);
v_isSharedCheck_952_ = !lean_is_exclusive(v_lctx_933_);
if (v_isSharedCheck_952_ == 0)
{
v___x_939_ = v_lctx_933_;
v_isShared_940_ = v_isSharedCheck_952_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_auxDeclToFullName_937_);
lean_inc(v_decls_935_);
lean_inc(v_fvarIdToDecl_936_);
lean_dec(v_lctx_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_952_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_size_941_; lean_object* v_newDecl_942_; lean_object* v___y_944_; lean_object* v_fvarId_951_; 
v_size_941_ = lean_ctor_get(v_decls_935_, 2);
lean_inc(v_size_941_);
v_newDecl_942_ = l_Lean_LocalDecl_setIndex(v_newDecl_934_, v_size_941_);
v_fvarId_951_ = lean_ctor_get(v_newDecl_942_, 1);
lean_inc(v_fvarId_951_);
v___y_944_ = v_fvarId_951_;
goto v___jp_943_;
v___jp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
lean_inc_ref(v_newDecl_942_);
v___x_945_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_936_, v___y_944_, v_newDecl_942_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v_newDecl_942_);
v___x_947_ = l_Lean_PersistentArray_push___redArg(v_decls_935_, v___x_946_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_947_);
lean_ctor_set(v___x_939_, 0, v___x_945_);
v___x_949_ = v___x_939_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_auxDeclToFullName_937_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_953_, lean_object* v_vals_954_, lean_object* v_i_955_, lean_object* v_k_956_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_array_get_size(v_keys_953_);
v___x_958_ = lean_nat_dec_lt(v_i_955_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec(v_i_955_);
v___x_959_ = lean_box(0);
return v___x_959_;
}
else
{
lean_object* v_k_x27_960_; uint8_t v___x_961_; 
v_k_x27_960_ = lean_array_fget_borrowed(v_keys_953_, v_i_955_);
v___x_961_ = l_Lean_instBEqFVarId_beq(v_k_956_, v_k_x27_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_i_955_, v___x_962_);
lean_dec(v_i_955_);
v_i_955_ = v___x_963_;
goto _start;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_array_fget_borrowed(v_vals_954_, v_i_955_);
lean_dec(v_i_955_);
lean_inc(v___x_965_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_967_, lean_object* v_vals_968_, lean_object* v_i_969_, lean_object* v_k_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_967_, v_vals_968_, v_i_969_, v_k_970_);
lean_dec(v_k_970_);
lean_dec_ref(v_vals_968_);
lean_dec_ref(v_keys_967_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_972_, size_t v_x_973_, lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_972_) == 0)
{
lean_object* v_es_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_996_; 
v_es_975_ = lean_ctor_get(v_x_972_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_996_ == 0)
{
v___x_977_ = v_x_972_;
v_isShared_978_ = v_isSharedCheck_996_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_es_975_);
lean_dec(v_x_972_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_996_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; lean_object* v_j_983_; lean_object* v___x_984_; 
v___x_979_ = lean_box(2);
v___x_980_ = ((size_t)5ULL);
v___x_981_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_982_ = lean_usize_land(v_x_973_, v___x_981_);
v_j_983_ = lean_usize_to_nat(v___x_982_);
v___x_984_ = lean_array_get(v___x_979_, v_es_975_, v_j_983_);
lean_dec(v_j_983_);
lean_dec_ref(v_es_975_);
switch(lean_obj_tag(v___x_984_))
{
case 0:
{
lean_object* v_key_985_; lean_object* v_val_986_; uint8_t v___x_987_; 
v_key_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_key_985_);
v_val_986_ = lean_ctor_get(v___x_984_, 1);
lean_inc(v_val_986_);
lean_dec_ref(v___x_984_);
v___x_987_ = l_Lean_instBEqFVarId_beq(v_x_974_, v_key_985_);
lean_dec(v_key_985_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec(v_val_986_);
lean_del_object(v___x_977_);
v___x_988_ = lean_box(0);
return v___x_988_;
}
else
{
lean_object* v___x_990_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 1);
lean_ctor_set(v___x_977_, 0, v_val_986_);
v___x_990_ = v___x_977_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_val_986_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
case 1:
{
lean_object* v_node_992_; size_t v___x_993_; 
lean_del_object(v___x_977_);
v_node_992_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_node_992_);
lean_dec_ref(v___x_984_);
v___x_993_ = lean_usize_shift_right(v_x_973_, v___x_980_);
v_x_972_ = v_node_992_;
v_x_973_ = v___x_993_;
goto _start;
}
default: 
{
lean_object* v___x_995_; 
lean_del_object(v___x_977_);
v___x_995_ = lean_box(0);
return v___x_995_;
}
}
}
}
else
{
lean_object* v_ks_997_; lean_object* v_vs_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_ks_997_ = lean_ctor_get(v_x_972_, 0);
lean_inc_ref(v_ks_997_);
v_vs_998_ = lean_ctor_get(v_x_972_, 1);
lean_inc_ref(v_vs_998_);
lean_dec_ref(v_x_972_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_997_, v_vs_998_, v___x_999_, v_x_974_);
lean_dec_ref(v_vs_998_);
lean_dec_ref(v_ks_997_);
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
size_t v_x_143__boxed_1004_; lean_object* v_res_1005_; 
v_x_143__boxed_1004_ = lean_unbox_usize(v_x_1002_);
lean_dec(v_x_1002_);
v_res_1005_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1001_, v_x_143__boxed_1004_, v_x_1003_);
lean_dec(v_x_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
uint64_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = l_Lean_instHashableFVarId_hash(v_x_1007_);
v___x_1009_ = lean_uint64_to_usize(v___x_1008_);
v___x_1010_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1006_, v___x_1009_, v_x_1007_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1011_, v_x_1012_);
lean_dec(v_x_1012_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1014_, lean_object* v_fvarId_1015_){
_start:
{
lean_object* v_fvarIdToDecl_1016_; lean_object* v___x_1017_; 
v_fvarIdToDecl_1016_ = lean_ctor_get(v_lctx_1014_, 0);
lean_inc_ref(v_fvarIdToDecl_1016_);
lean_dec_ref(v_lctx_1014_);
v___x_1017_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1016_, v_fvarId_1015_);
lean_dec(v_fvarId_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1019_, v_x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1022_, v_x_1023_, v_x_1024_);
lean_dec(v_x_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1026_, lean_object* v_x_1027_, size_t v_x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1027_, v_x_1028_, v_x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
size_t v_x_226__boxed_1035_; lean_object* v_res_1036_; 
v_x_226__boxed_1035_ = lean_unbox_usize(v_x_1033_);
lean_dec(v_x_1033_);
v_res_1036_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1031_, v_x_1032_, v_x_226__boxed_1035_, v_x_1034_);
lean_dec(v_x_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1037_, lean_object* v_keys_1038_, lean_object* v_vals_1039_, lean_object* v_heq_1040_, lean_object* v_i_1041_, lean_object* v_k_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1038_, v_vals_1039_, v_i_1041_, v_k_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1044_, lean_object* v_keys_1045_, lean_object* v_vals_1046_, lean_object* v_heq_1047_, lean_object* v_i_1048_, lean_object* v_k_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1044_, v_keys_1045_, v_vals_1046_, v_heq_1047_, v_i_1048_, v_k_1049_);
lean_dec(v_k_1049_);
lean_dec_ref(v_vals_1046_);
lean_dec_ref(v_keys_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1051_, lean_object* v_e_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = l_Lean_Expr_fvarId_x21(v_e_1052_);
v___x_1054_ = lean_local_ctx_find(v_lctx_1051_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1055_, lean_object* v_e_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1055_, v_e_1056_);
lean_dec_ref(v_e_1056_);
return v_res_1057_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1060_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1061_ = lean_unsigned_to_nat(14u);
v___x_1062_ = lean_unsigned_to_nat(340u);
v___x_1063_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1064_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1065_ = l_mkPanicMessageWithDecl(v___x_1064_, v___x_1063_, v___x_1062_, v___x_1061_, v___x_1060_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1066_, lean_object* v_fvarId_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_local_ctx_find(v_lctx_1066_, v_fvarId_1067_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1070_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1069_);
return v___x_1070_;
}
else
{
lean_object* v_val_1071_; 
v_val_1071_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_val_1071_);
lean_dec_ref(v___x_1068_);
return v_val_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1072_, lean_object* v_e_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = l_Lean_Expr_fvarId_x21(v_e_1073_);
v___x_1075_ = l_Lean_LocalContext_get_x21(v_lctx_1072_, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1076_, lean_object* v_e_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1076_, v_e_1077_);
lean_dec_ref(v_e_1077_);
return v_res_1078_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1079_, lean_object* v_i_1080_, lean_object* v_k_1081_){
_start:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_array_get_size(v_keys_1079_);
v___x_1083_ = lean_nat_dec_lt(v_i_1080_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec(v_i_1080_);
return v___x_1083_;
}
else
{
lean_object* v_k_x27_1084_; uint8_t v___x_1085_; 
v_k_x27_1084_ = lean_array_fget_borrowed(v_keys_1079_, v_i_1080_);
v___x_1085_ = l_Lean_instBEqFVarId_beq(v_k_1081_, v_k_x27_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_add(v_i_1080_, v___x_1086_);
lean_dec(v_i_1080_);
v_i_1080_ = v___x_1087_;
goto _start;
}
else
{
lean_dec(v_i_1080_);
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1089_, lean_object* v_i_1090_, lean_object* v_k_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1089_, v_i_1090_, v_k_1091_);
lean_dec(v_k_1091_);
lean_dec_ref(v_keys_1089_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1094_, size_t v_x_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1094_) == 0)
{
lean_object* v_es_1097_; lean_object* v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; lean_object* v_j_1102_; lean_object* v___x_1103_; 
v_es_1097_ = lean_ctor_get(v_x_1094_, 0);
v___x_1098_ = lean_box(2);
v___x_1099_ = ((size_t)5ULL);
v___x_1100_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_1101_ = lean_usize_land(v_x_1095_, v___x_1100_);
v_j_1102_ = lean_usize_to_nat(v___x_1101_);
v___x_1103_ = lean_array_get_borrowed(v___x_1098_, v_es_1097_, v_j_1102_);
lean_dec(v_j_1102_);
switch(lean_obj_tag(v___x_1103_))
{
case 0:
{
lean_object* v_key_1104_; uint8_t v___x_1105_; 
v_key_1104_ = lean_ctor_get(v___x_1103_, 0);
v___x_1105_ = l_Lean_instBEqFVarId_beq(v_x_1096_, v_key_1104_);
return v___x_1105_;
}
case 1:
{
lean_object* v_node_1106_; size_t v___x_1107_; 
v_node_1106_ = lean_ctor_get(v___x_1103_, 0);
v___x_1107_ = lean_usize_shift_right(v_x_1095_, v___x_1099_);
v_x_1094_ = v_node_1106_;
v_x_1095_ = v___x_1107_;
goto _start;
}
default: 
{
uint8_t v___x_1109_; 
v___x_1109_ = 0;
return v___x_1109_;
}
}
}
else
{
lean_object* v_ks_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_ks_1110_ = lean_ctor_get(v_x_1094_, 0);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1110_, v___x_1111_, v_x_1096_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
size_t v_x_129__boxed_1116_; uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_x_129__boxed_1116_ = lean_unbox_usize(v_x_1114_);
lean_dec(v_x_1114_);
v_res_1117_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1113_, v_x_129__boxed_1116_, v_x_1115_);
lean_dec(v_x_1115_);
lean_dec_ref(v_x_1113_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
uint64_t v___x_1121_; size_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1121_ = l_Lean_instHashableFVarId_hash(v_x_1120_);
v___x_1122_ = lean_uint64_to_usize(v___x_1121_);
v___x_1123_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1119_, v___x_1122_, v_x_1120_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1124_, v_x_1125_);
lean_dec(v_x_1125_);
lean_dec_ref(v_x_1124_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1128_, lean_object* v_fvarId_1129_){
_start:
{
lean_object* v_fvarIdToDecl_1130_; uint8_t v___x_1131_; 
v_fvarIdToDecl_1130_ = lean_ctor_get(v_lctx_1128_, 0);
v___x_1131_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1130_, v_fvarId_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1132_, lean_object* v_fvarId_1133_){
_start:
{
uint8_t v_res_1134_; lean_object* v_r_1135_; 
v_res_1134_ = l_Lean_LocalContext_contains(v_lctx_1132_, v_fvarId_1133_);
lean_dec(v_fvarId_1133_);
lean_dec_ref(v_lctx_1132_);
v_r_1135_ = lean_box(v_res_1134_);
return v_r_1135_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1137_, v_x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
uint8_t v_res_1143_; lean_object* v_r_1144_; 
v_res_1143_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1140_, v_x_1141_, v_x_1142_);
lean_dec(v_x_1142_);
lean_dec_ref(v_x_1141_);
v_r_1144_ = lean_box(v_res_1143_);
return v_r_1144_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1145_, lean_object* v_x_1146_, size_t v_x_1147_, lean_object* v_x_1148_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1146_, v_x_1147_, v_x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_){
_start:
{
size_t v_x_194__boxed_1154_; uint8_t v_res_1155_; lean_object* v_r_1156_; 
v_x_194__boxed_1154_ = lean_unbox_usize(v_x_1152_);
lean_dec(v_x_1152_);
v_res_1155_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1150_, v_x_1151_, v_x_194__boxed_1154_, v_x_1153_);
lean_dec(v_x_1153_);
lean_dec_ref(v_x_1151_);
v_r_1156_ = lean_box(v_res_1155_);
return v_r_1156_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1157_, lean_object* v_keys_1158_, lean_object* v_vals_1159_, lean_object* v_heq_1160_, lean_object* v_i_1161_, lean_object* v_k_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1158_, v_i_1161_, v_k_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1164_, lean_object* v_keys_1165_, lean_object* v_vals_1166_, lean_object* v_heq_1167_, lean_object* v_i_1168_, lean_object* v_k_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1164_, v_keys_1165_, v_vals_1166_, v_heq_1167_, v_i_1168_, v_k_1169_);
lean_dec(v_k_1169_);
lean_dec_ref(v_vals_1166_);
lean_dec_ref(v_keys_1165_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1172_, lean_object* v_e_1173_){
_start:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = l_Lean_Expr_fvarId_x21(v_e_1173_);
v___x_1175_ = l_Lean_LocalContext_contains(v_lctx_1172_, v___x_1174_);
lean_dec(v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1176_, lean_object* v_e_1177_){
_start:
{
uint8_t v_res_1178_; lean_object* v_r_1179_; 
v_res_1178_ = l_Lean_LocalContext_containsFVar(v_lctx_1176_, v_e_1177_);
lean_dec_ref(v_e_1177_);
lean_dec_ref(v_lctx_1176_);
v_r_1179_ = lean_box(v_res_1178_);
return v_r_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1180_, size_t v_i_1181_, size_t v_stop_1182_, lean_object* v_b_1183_){
_start:
{
lean_object* v___y_1185_; uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_eq(v_i_1181_, v_stop_1182_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_array_uget_borrowed(v_as_1180_, v_i_1181_);
if (lean_obj_tag(v___x_1190_) == 0)
{
v___y_1185_ = v_b_1183_;
goto v___jp_1184_;
}
else
{
lean_object* v_val_1191_; lean_object* v_fvarId_1192_; lean_object* v___x_1193_; 
v_val_1191_ = lean_ctor_get(v___x_1190_, 0);
v_fvarId_1192_ = lean_ctor_get(v_val_1191_, 1);
lean_inc(v_fvarId_1192_);
v___x_1193_ = lean_array_push(v_b_1183_, v_fvarId_1192_);
v___y_1185_ = v___x_1193_;
goto v___jp_1184_;
}
}
else
{
return v_b_1183_;
}
v___jp_1184_:
{
size_t v___x_1186_; size_t v___x_1187_; 
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1181_, v___x_1186_);
v_i_1181_ = v___x_1187_;
v_b_1183_ = v___y_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1194_, lean_object* v_i_1195_, lean_object* v_stop_1196_, lean_object* v_b_1197_){
_start:
{
size_t v_i_boxed_1198_; size_t v_stop_boxed_1199_; lean_object* v_res_1200_; 
v_i_boxed_1198_ = lean_unbox_usize(v_i_1195_);
lean_dec(v_i_1195_);
v_stop_boxed_1199_ = lean_unbox_usize(v_stop_1196_);
lean_dec(v_stop_1196_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1194_, v_i_boxed_1198_, v_stop_boxed_1199_, v_b_1197_);
lean_dec_ref(v_as_1194_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1201_) == 0)
{
lean_object* v_cs_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_cs_1203_ = lean_ctor_get(v_x_1201_, 0);
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_array_get_size(v_cs_1203_);
v___x_1206_ = lean_nat_dec_lt(v___x_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
return v_x_1202_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_nat_dec_le(v___x_1205_, v___x_1205_);
if (v___x_1207_ == 0)
{
if (v___x_1206_ == 0)
{
return v_x_1202_;
}
else
{
size_t v___x_1208_; size_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = ((size_t)0ULL);
v___x_1209_ = lean_usize_of_nat(v___x_1205_);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1203_, v___x_1208_, v___x_1209_, v_x_1202_);
return v___x_1210_;
}
}
else
{
size_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = lean_usize_of_nat(v___x_1205_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1203_, v___x_1211_, v___x_1212_, v_x_1202_);
return v___x_1213_;
}
}
}
else
{
lean_object* v_vs_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_vs_1214_ = lean_ctor_get(v_x_1201_, 0);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_array_get_size(v_vs_1214_);
v___x_1217_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
return v_x_1202_;
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = lean_nat_dec_le(v___x_1216_, v___x_1216_);
if (v___x_1218_ == 0)
{
if (v___x_1217_ == 0)
{
return v_x_1202_;
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = lean_usize_of_nat(v___x_1216_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1214_, v___x_1219_, v___x_1220_, v_x_1202_);
return v___x_1221_;
}
}
else
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = ((size_t)0ULL);
v___x_1223_ = lean_usize_of_nat(v___x_1216_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1214_, v___x_1222_, v___x_1223_, v_x_1202_);
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1225_, size_t v_i_1226_, size_t v_stop_1227_, lean_object* v_b_1228_){
_start:
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_usize_dec_eq(v_i_1226_, v_stop_1227_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; 
v___x_1230_ = lean_array_uget_borrowed(v_as_1225_, v_i_1226_);
v___x_1231_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1230_, v_b_1228_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_i_1226_, v___x_1232_);
v_i_1226_ = v___x_1233_;
v_b_1228_ = v___x_1231_;
goto _start;
}
else
{
return v_b_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1235_, lean_object* v_i_1236_, lean_object* v_stop_1237_, lean_object* v_b_1238_){
_start:
{
size_t v_i_boxed_1239_; size_t v_stop_boxed_1240_; lean_object* v_res_1241_; 
v_i_boxed_1239_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_stop_boxed_1240_ = lean_unbox_usize(v_stop_1237_);
lean_dec(v_stop_1237_);
v_res_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1235_, v_i_boxed_1239_, v_stop_boxed_1240_, v_b_1238_);
lean_dec_ref(v_as_1235_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1242_, v_x_1243_);
lean_dec_ref(v_x_1242_);
return v_res_1244_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1246_, size_t v_x_1247_, size_t v_x_1248_, lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v_cs_1250_; lean_object* v___x_1251_; size_t v___x_1252_; lean_object* v_j_1253_; lean_object* v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_cs_1250_ = lean_ctor_get(v_x_1246_, 0);
v___x_1251_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1252_ = lean_usize_shift_right(v_x_1247_, v_x_1248_);
v_j_1253_ = lean_usize_to_nat(v___x_1252_);
v___x_1254_ = lean_array_get_borrowed(v___x_1251_, v_cs_1250_, v_j_1253_);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_shift_left(v___x_1255_, v_x_1248_);
v___x_1257_ = lean_usize_sub(v___x_1256_, v___x_1255_);
v___x_1258_ = lean_usize_land(v_x_1247_, v___x_1257_);
v___x_1259_ = ((size_t)5ULL);
v___x_1260_ = lean_usize_sub(v_x_1248_, v___x_1259_);
v___x_1261_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1254_, v___x_1258_, v___x_1260_, v_x_1249_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_add(v_j_1253_, v___x_1262_);
lean_dec(v_j_1253_);
v___x_1264_ = lean_array_get_size(v_cs_1250_);
v___x_1265_ = lean_nat_dec_lt(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec(v___x_1263_);
return v___x_1261_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_nat_dec_le(v___x_1264_, v___x_1264_);
if (v___x_1266_ == 0)
{
if (v___x_1265_ == 0)
{
lean_dec(v___x_1263_);
return v___x_1261_;
}
else
{
size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_usize_of_nat(v___x_1263_);
lean_dec(v___x_1263_);
v___x_1268_ = lean_usize_of_nat(v___x_1264_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1250_, v___x_1267_, v___x_1268_, v___x_1261_);
return v___x_1269_;
}
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_usize_of_nat(v___x_1263_);
lean_dec(v___x_1263_);
v___x_1271_ = lean_usize_of_nat(v___x_1264_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1250_, v___x_1270_, v___x_1271_, v___x_1261_);
return v___x_1272_;
}
}
}
else
{
lean_object* v_vs_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_vs_1273_ = lean_ctor_get(v_x_1246_, 0);
v___x_1274_ = lean_usize_to_nat(v_x_1247_);
v___x_1275_ = lean_array_get_size(v_vs_1273_);
v___x_1276_ = lean_nat_dec_lt(v___x_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec(v___x_1274_);
return v_x_1249_;
}
else
{
uint8_t v___x_1277_; 
v___x_1277_ = lean_nat_dec_le(v___x_1275_, v___x_1275_);
if (v___x_1277_ == 0)
{
if (v___x_1276_ == 0)
{
lean_dec(v___x_1274_);
return v_x_1249_;
}
else
{
size_t v___x_1278_; size_t v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_usize_of_nat(v___x_1274_);
lean_dec(v___x_1274_);
v___x_1279_ = lean_usize_of_nat(v___x_1275_);
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1273_, v___x_1278_, v___x_1279_, v_x_1249_);
return v___x_1280_;
}
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_usize_of_nat(v___x_1274_);
lean_dec(v___x_1274_);
v___x_1282_ = lean_usize_of_nat(v___x_1275_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1273_, v___x_1281_, v___x_1282_, v_x_1249_);
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_){
_start:
{
size_t v_x_1632__boxed_1288_; size_t v_x_1633__boxed_1289_; lean_object* v_res_1290_; 
v_x_1632__boxed_1288_ = lean_unbox_usize(v_x_1285_);
lean_dec(v_x_1285_);
v_x_1633__boxed_1289_ = lean_unbox_usize(v_x_1286_);
lean_dec(v_x_1286_);
v_res_1290_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1284_, v_x_1632__boxed_1288_, v_x_1633__boxed_1289_, v_x_1287_);
lean_dec_ref(v_x_1284_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1291_, lean_object* v_init_1292_, lean_object* v_start_1293_){
_start:
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = lean_nat_dec_eq(v_start_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v_root_1296_; lean_object* v_tail_1297_; size_t v_shift_1298_; lean_object* v_tailOff_1299_; uint8_t v___x_1300_; 
v_root_1296_ = lean_ctor_get(v_t_1291_, 0);
v_tail_1297_ = lean_ctor_get(v_t_1291_, 1);
v_shift_1298_ = lean_ctor_get_usize(v_t_1291_, 4);
v_tailOff_1299_ = lean_ctor_get(v_t_1291_, 3);
v___x_1300_ = lean_nat_dec_le(v_tailOff_1299_, v_start_1293_);
if (v___x_1300_ == 0)
{
size_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1301_ = lean_usize_of_nat(v_start_1293_);
v___x_1302_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1296_, v___x_1301_, v_shift_1298_, v_init_1292_);
v___x_1303_ = lean_array_get_size(v_tail_1297_);
v___x_1304_ = lean_nat_dec_lt(v___x_1294_, v___x_1303_);
if (v___x_1304_ == 0)
{
return v___x_1302_;
}
else
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_nat_dec_le(v___x_1303_, v___x_1303_);
if (v___x_1305_ == 0)
{
if (v___x_1304_ == 0)
{
return v___x_1302_;
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = lean_usize_of_nat(v___x_1303_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1297_, v___x_1306_, v___x_1307_, v___x_1302_);
return v___x_1308_;
}
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((size_t)0ULL);
v___x_1310_ = lean_usize_of_nat(v___x_1303_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1297_, v___x_1309_, v___x_1310_, v___x_1302_);
return v___x_1311_;
}
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_nat_sub(v_start_1293_, v_tailOff_1299_);
v___x_1313_ = lean_array_get_size(v_tail_1297_);
v___x_1314_ = lean_nat_dec_lt(v___x_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_dec(v___x_1312_);
return v_init_1292_;
}
else
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_nat_dec_le(v___x_1313_, v___x_1313_);
if (v___x_1315_ == 0)
{
if (v___x_1314_ == 0)
{
lean_dec(v___x_1312_);
return v_init_1292_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_usize_of_nat(v___x_1312_);
lean_dec(v___x_1312_);
v___x_1317_ = lean_usize_of_nat(v___x_1313_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1297_, v___x_1316_, v___x_1317_, v_init_1292_);
return v___x_1318_;
}
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_usize_of_nat(v___x_1312_);
lean_dec(v___x_1312_);
v___x_1320_ = lean_usize_of_nat(v___x_1313_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1297_, v___x_1319_, v___x_1320_, v_init_1292_);
return v___x_1321_;
}
}
}
}
else
{
lean_object* v_root_1322_; lean_object* v_tail_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_root_1322_ = lean_ctor_get(v_t_1291_, 0);
v_tail_1323_ = lean_ctor_get(v_t_1291_, 1);
v___x_1324_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1322_, v_init_1292_);
v___x_1325_ = lean_array_get_size(v_tail_1323_);
v___x_1326_ = lean_nat_dec_lt(v___x_1294_, v___x_1325_);
if (v___x_1326_ == 0)
{
return v___x_1324_;
}
else
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_nat_dec_le(v___x_1325_, v___x_1325_);
if (v___x_1327_ == 0)
{
if (v___x_1326_ == 0)
{
return v___x_1324_;
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1325_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1323_, v___x_1328_, v___x_1329_, v___x_1324_);
return v___x_1330_;
}
}
else
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = lean_usize_of_nat(v___x_1325_);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1323_, v___x_1331_, v___x_1332_, v___x_1324_);
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1334_, lean_object* v_init_1335_, lean_object* v_start_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1334_, v_init_1335_, v_start_1336_);
lean_dec(v_start_1336_);
lean_dec_ref(v_t_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1340_){
_start:
{
lean_object* v_decls_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_decls_1341_ = lean_ctor_get(v_lctx_1340_, 1);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1344_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1341_, v___x_1343_, v___x_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_LocalContext_getFVarIds(v_lctx_1345_);
lean_dec_ref(v_lctx_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1347_, size_t v_i_1348_, lean_object* v_bs_1349_){
_start:
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_usize_dec_lt(v_i_1348_, v_sz_1347_);
if (v___x_1350_ == 0)
{
return v_bs_1349_;
}
else
{
lean_object* v_v_1351_; lean_object* v___x_1352_; lean_object* v_bs_x27_1353_; lean_object* v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v_v_1351_ = lean_array_uget(v_bs_1349_, v_i_1348_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v_bs_x27_1353_ = lean_array_uset(v_bs_1349_, v_i_1348_, v___x_1352_);
v___x_1354_ = l_Lean_mkFVar(v_v_1351_);
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_add(v_i_1348_, v___x_1355_);
v___x_1357_ = lean_array_uset(v_bs_x27_1353_, v_i_1348_, v___x_1354_);
v_i_1348_ = v___x_1356_;
v_bs_1349_ = v___x_1357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1359_, lean_object* v_i_1360_, lean_object* v_bs_1361_){
_start:
{
size_t v_sz_boxed_1362_; size_t v_i_boxed_1363_; lean_object* v_res_1364_; 
v_sz_boxed_1362_ = lean_unbox_usize(v_sz_1359_);
lean_dec(v_sz_1359_);
v_i_boxed_1363_ = lean_unbox_usize(v_i_1360_);
lean_dec(v_i_1360_);
v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1362_, v_i_boxed_1363_, v_bs_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1365_){
_start:
{
lean_object* v___x_1366_; size_t v_sz_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1366_ = l_Lean_LocalContext_getFVarIds(v_lctx_1365_);
v_sz_1367_ = lean_array_size(v___x_1366_);
v___x_1368_ = ((size_t)0ULL);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1367_, v___x_1368_, v___x_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_LocalContext_getFVars(v_lctx_1370_);
lean_dec_ref(v_lctx_1370_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1372_){
_start:
{
lean_object* v_size_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v_size_1373_ = lean_ctor_get(v_a_1372_, 2);
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = lean_nat_dec_eq(v_size_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_unsigned_to_nat(1u);
v___x_1378_ = lean_nat_sub(v_size_1373_, v___x_1377_);
v___x_1379_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1376_, v_a_1372_, v___x_1378_);
lean_dec(v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_PersistentArray_pop___redArg(v_a_1372_);
v_a_1372_ = v___x_1380_;
goto _start;
}
else
{
lean_dec_ref(v___x_1379_);
return v_a_1372_;
}
}
else
{
return v_a_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1382_, lean_object* v_t_1383_){
_start:
{
if (lean_obj_tag(v_t_1383_) == 0)
{
lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v_l_1386_; lean_object* v_r_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_2041_; 
v_k_1384_ = lean_ctor_get(v_t_1383_, 1);
v_v_1385_ = lean_ctor_get(v_t_1383_, 2);
v_l_1386_ = lean_ctor_get(v_t_1383_, 3);
v_r_1387_ = lean_ctor_get(v_t_1383_, 4);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_t_1383_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_t_1383_, 0);
lean_dec(v_unused_2042_);
v___x_1389_ = v_t_1383_;
v_isShared_1390_ = v_isSharedCheck_2041_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_r_1387_);
lean_inc(v_l_1386_);
lean_inc(v_v_1385_);
lean_inc(v_k_1384_);
lean_dec(v_t_1383_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_2041_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
uint8_t v___x_1391_; 
v___x_1391_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1382_, v_k_1384_);
switch(v___x_1391_)
{
case 0:
{
lean_object* v_impl_1392_; lean_object* v___x_1393_; 
v_impl_1392_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1382_, v_l_1386_);
v___x_1393_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1392_) == 0)
{
if (lean_obj_tag(v_r_1387_) == 0)
{
lean_object* v_size_1394_; lean_object* v_size_1395_; lean_object* v_k_1396_; lean_object* v_v_1397_; lean_object* v_l_1398_; lean_object* v_r_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_size_1394_ = lean_ctor_get(v_impl_1392_, 0);
lean_inc(v_size_1394_);
v_size_1395_ = lean_ctor_get(v_r_1387_, 0);
v_k_1396_ = lean_ctor_get(v_r_1387_, 1);
v_v_1397_ = lean_ctor_get(v_r_1387_, 2);
v_l_1398_ = lean_ctor_get(v_r_1387_, 3);
lean_inc(v_l_1398_);
v_r_1399_ = lean_ctor_get(v_r_1387_, 4);
v___x_1400_ = lean_unsigned_to_nat(3u);
v___x_1401_ = lean_nat_mul(v___x_1400_, v_size_1394_);
v___x_1402_ = lean_nat_dec_lt(v___x_1401_, v_size_1395_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_dec(v_l_1398_);
v___x_1403_ = lean_nat_add(v___x_1393_, v_size_1394_);
lean_dec(v_size_1394_);
v___x_1404_ = lean_nat_add(v___x_1403_, v_size_1395_);
lean_dec(v___x_1403_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 3, v_impl_1392_);
lean_ctor_set(v___x_1389_, 0, v___x_1404_);
v___x_1406_ = v___x_1389_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_impl_1392_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v_r_1387_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1471_; 
lean_inc(v_r_1399_);
lean_inc(v_v_1397_);
lean_inc(v_k_1396_);
lean_inc(v_size_1395_);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; 
v_unused_1472_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_r_1387_, 2);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_r_1387_, 1);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_r_1387_, 0);
lean_dec(v_unused_1476_);
v___x_1409_ = v_r_1387_;
v_isShared_1410_ = v_isSharedCheck_1471_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_r_1387_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1471_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_size_1411_; lean_object* v_k_1412_; lean_object* v_v_1413_; lean_object* v_l_1414_; lean_object* v_r_1415_; lean_object* v_size_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_size_1411_ = lean_ctor_get(v_l_1398_, 0);
v_k_1412_ = lean_ctor_get(v_l_1398_, 1);
v_v_1413_ = lean_ctor_get(v_l_1398_, 2);
v_l_1414_ = lean_ctor_get(v_l_1398_, 3);
v_r_1415_ = lean_ctor_get(v_l_1398_, 4);
v_size_1416_ = lean_ctor_get(v_r_1399_, 0);
v___x_1417_ = lean_unsigned_to_nat(2u);
v___x_1418_ = lean_nat_mul(v___x_1417_, v_size_1416_);
v___x_1419_ = lean_nat_dec_lt(v_size_1411_, v___x_1418_);
lean_dec(v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1447_; 
lean_inc(v_r_1415_);
lean_inc(v_l_1414_);
lean_inc(v_v_1413_);
lean_inc(v_k_1412_);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_l_1398_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1448_ = lean_ctor_get(v_l_1398_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1398_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_l_1398_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_l_1398_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1398_, 0);
lean_dec(v_unused_1452_);
v___x_1421_ = v_l_1398_;
v_isShared_1422_ = v_isSharedCheck_1447_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v_l_1398_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1447_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1437_; 
v___x_1423_ = lean_nat_add(v___x_1393_, v_size_1394_);
lean_dec(v_size_1394_);
v___x_1424_ = lean_nat_add(v___x_1423_, v_size_1395_);
lean_dec(v_size_1395_);
if (lean_obj_tag(v_l_1414_) == 0)
{
lean_object* v_size_1445_; 
v_size_1445_ = lean_ctor_get(v_l_1414_, 0);
lean_inc(v_size_1445_);
v___y_1437_ = v_size_1445_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___y_1437_ = v___x_1446_;
goto v___jp_1436_;
}
v___jp_1425_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_nat_add(v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec(v___y_1427_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 4, v_r_1399_);
lean_ctor_set(v___x_1421_, 3, v_r_1415_);
lean_ctor_set(v___x_1421_, 2, v_v_1397_);
lean_ctor_set(v___x_1421_, 1, v_k_1396_);
lean_ctor_set(v___x_1421_, 0, v___x_1429_);
v___x_1431_ = v___x_1421_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_k_1396_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_v_1397_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_r_1415_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v_r_1399_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_1431_);
lean_ctor_set(v___x_1409_, 3, v___y_1426_);
lean_ctor_set(v___x_1409_, 2, v_v_1413_);
lean_ctor_set(v___x_1409_, 1, v_k_1412_);
lean_ctor_set(v___x_1409_, 0, v___x_1424_);
v___x_1433_ = v___x_1409_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1412_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1413_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v___y_1426_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
v___jp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_nat_add(v___x_1423_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec(v___x_1423_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_l_1414_);
lean_ctor_set(v___x_1389_, 3, v_impl_1392_);
lean_ctor_set(v___x_1389_, 0, v___x_1438_);
v___x_1440_ = v___x_1389_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_impl_1392_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_l_1414_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_nat_add(v___x_1393_, v_size_1416_);
if (lean_obj_tag(v_r_1415_) == 0)
{
lean_object* v_size_1442_; 
v_size_1442_ = lean_ctor_get(v_r_1415_, 0);
lean_inc(v_size_1442_);
v___y_1426_ = v___x_1440_;
v___y_1427_ = v___x_1441_;
v___y_1428_ = v_size_1442_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___y_1426_ = v___x_1440_;
v___y_1427_ = v___x_1441_;
v___y_1428_ = v___x_1443_;
goto v___jp_1425_;
}
}
}
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_del_object(v___x_1389_);
v___x_1453_ = lean_nat_add(v___x_1393_, v_size_1394_);
lean_dec(v_size_1394_);
v___x_1454_ = lean_nat_add(v___x_1453_, v_size_1395_);
lean_dec(v_size_1395_);
v___x_1455_ = lean_nat_add(v___x_1453_, v_size_1411_);
lean_dec(v___x_1453_);
lean_inc_ref(v_impl_1392_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_l_1398_);
lean_ctor_set(v___x_1409_, 3, v_impl_1392_);
lean_ctor_set(v___x_1409_, 2, v_v_1385_);
lean_ctor_set(v___x_1409_, 1, v_k_1384_);
lean_ctor_set(v___x_1409_, 0, v___x_1455_);
v___x_1457_ = v___x_1409_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_impl_1392_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v_l_1398_);
v___x_1457_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v_impl_1392_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1465_ = lean_ctor_get(v_impl_1392_, 4);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_impl_1392_, 3);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_impl_1392_, 2);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_impl_1392_, 1);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_impl_1392_, 0);
lean_dec(v_unused_1469_);
v___x_1459_ = v_impl_1392_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_impl_1392_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v_r_1399_);
lean_ctor_set(v___x_1459_, 3, v___x_1457_);
lean_ctor_set(v___x_1459_, 2, v_v_1397_);
lean_ctor_set(v___x_1459_, 1, v_k_1396_);
lean_ctor_set(v___x_1459_, 0, v___x_1454_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1396_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1397_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_r_1399_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v_size_1477_ = lean_ctor_get(v_impl_1392_, 0);
lean_inc(v_size_1477_);
v___x_1478_ = lean_nat_add(v___x_1393_, v_size_1477_);
lean_dec(v_size_1477_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 3, v_impl_1392_);
lean_ctor_set(v___x_1389_, 0, v___x_1478_);
v___x_1480_ = v___x_1389_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_impl_1392_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_r_1387_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
if (lean_obj_tag(v_r_1387_) == 0)
{
lean_object* v_l_1482_; 
v_l_1482_ = lean_ctor_get(v_r_1387_, 3);
lean_inc(v_l_1482_);
if (lean_obj_tag(v_l_1482_) == 0)
{
lean_object* v_r_1483_; 
v_r_1483_ = lean_ctor_get(v_r_1387_, 4);
lean_inc(v_r_1483_);
if (lean_obj_tag(v_r_1483_) == 0)
{
lean_object* v_size_1484_; lean_object* v_k_1485_; lean_object* v_v_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1499_; 
v_size_1484_ = lean_ctor_get(v_r_1387_, 0);
v_k_1485_ = lean_ctor_get(v_r_1387_, 1);
v_v_1486_ = lean_ctor_get(v_r_1387_, 2);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; lean_object* v_unused_1501_; 
v_unused_1500_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1501_);
v___x_1488_ = v_r_1387_;
v_isShared_1489_ = v_isSharedCheck_1499_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_v_1486_);
lean_inc(v_k_1485_);
lean_inc(v_size_1484_);
lean_dec(v_r_1387_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1499_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_size_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v_size_1490_ = lean_ctor_get(v_l_1482_, 0);
v___x_1491_ = lean_nat_add(v___x_1393_, v_size_1484_);
lean_dec(v_size_1484_);
v___x_1492_ = lean_nat_add(v___x_1393_, v_size_1490_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 4, v_l_1482_);
lean_ctor_set(v___x_1488_, 3, v_impl_1392_);
lean_ctor_set(v___x_1488_, 2, v_v_1385_);
lean_ctor_set(v___x_1488_, 1, v_k_1384_);
lean_ctor_set(v___x_1488_, 0, v___x_1492_);
v___x_1494_ = v___x_1488_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_impl_1392_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_l_1482_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_r_1483_);
lean_ctor_set(v___x_1389_, 3, v___x_1494_);
lean_ctor_set(v___x_1389_, 2, v_v_1486_);
lean_ctor_set(v___x_1389_, 1, v_k_1485_);
lean_ctor_set(v___x_1389_, 0, v___x_1491_);
v___x_1496_ = v___x_1389_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1485_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1486_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_r_1483_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_k_1502_; lean_object* v_v_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1526_; 
v_k_1502_ = lean_ctor_get(v_r_1387_, 1);
v_v_1503_ = lean_ctor_get(v_r_1387_, 2);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; lean_object* v_unused_1528_; lean_object* v_unused_1529_; 
v_unused_1527_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_r_1387_, 0);
lean_dec(v_unused_1529_);
v___x_1505_ = v_r_1387_;
v_isShared_1506_ = v_isSharedCheck_1526_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_v_1503_);
lean_inc(v_k_1502_);
lean_dec(v_r_1387_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1526_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_k_1507_; lean_object* v_v_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1522_; 
v_k_1507_ = lean_ctor_get(v_l_1482_, 1);
v_v_1508_ = lean_ctor_get(v_l_1482_, 2);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_l_1482_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; 
v_unused_1523_ = lean_ctor_get(v_l_1482_, 4);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_l_1482_, 3);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_l_1482_, 0);
lean_dec(v_unused_1525_);
v___x_1510_ = v_l_1482_;
v_isShared_1511_ = v_isSharedCheck_1522_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_v_1508_);
lean_inc(v_k_1507_);
lean_dec(v_l_1482_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1522_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_unsigned_to_nat(3u);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_r_1483_);
lean_ctor_set(v___x_1510_, 3, v_r_1483_);
lean_ctor_set(v___x_1510_, 2, v_v_1385_);
lean_ctor_set(v___x_1510_, 1, v_k_1384_);
lean_ctor_set(v___x_1510_, 0, v___x_1393_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_r_1483_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_r_1483_);
v___x_1514_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 3, v_r_1483_);
lean_ctor_set(v___x_1505_, 0, v___x_1393_);
v___x_1516_ = v___x_1505_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1502_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1503_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_r_1483_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_r_1483_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_1516_);
lean_ctor_set(v___x_1389_, 3, v___x_1514_);
lean_ctor_set(v___x_1389_, 2, v_v_1508_);
lean_ctor_set(v___x_1389_, 1, v_k_1507_);
lean_ctor_set(v___x_1389_, 0, v___x_1512_);
v___x_1518_ = v___x_1389_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1507_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1508_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1530_; 
v_r_1530_ = lean_ctor_get(v_r_1387_, 4);
lean_inc(v_r_1530_);
if (lean_obj_tag(v_r_1530_) == 0)
{
lean_object* v_k_1531_; lean_object* v_v_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1543_; 
v_k_1531_ = lean_ctor_get(v_r_1387_, 1);
v_v_1532_ = lean_ctor_get(v_r_1387_, 2);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; lean_object* v_unused_1545_; lean_object* v_unused_1546_; 
v_unused_1544_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_r_1387_, 0);
lean_dec(v_unused_1546_);
v___x_1534_ = v_r_1387_;
v_isShared_1535_ = v_isSharedCheck_1543_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_dec(v_r_1387_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1543_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = lean_unsigned_to_nat(3u);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 4, v_l_1482_);
lean_ctor_set(v___x_1534_, 2, v_v_1385_);
lean_ctor_set(v___x_1534_, 1, v_k_1384_);
lean_ctor_set(v___x_1534_, 0, v___x_1393_);
v___x_1538_ = v___x_1534_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_l_1482_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_l_1482_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_r_1530_);
lean_ctor_set(v___x_1389_, 3, v___x_1538_);
lean_ctor_set(v___x_1389_, 2, v_v_1532_);
lean_ctor_set(v___x_1389_, 1, v_k_1531_);
lean_ctor_set(v___x_1389_, 0, v___x_1536_);
v___x_1540_ = v___x_1389_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_r_1530_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_size_1547_; lean_object* v_k_1548_; lean_object* v_v_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1560_; 
v_size_1547_ = lean_ctor_get(v_r_1387_, 0);
v_k_1548_ = lean_ctor_get(v_r_1387_, 1);
v_v_1549_ = lean_ctor_get(v_r_1387_, 2);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1561_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1562_);
v___x_1551_ = v_r_1387_;
v_isShared_1552_ = v_isSharedCheck_1560_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_v_1549_);
lean_inc(v_k_1548_);
lean_inc(v_size_1547_);
lean_dec(v_r_1387_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1560_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 3, v_r_1530_);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_size_1547_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1548_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1549_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_r_1530_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_r_1530_);
v___x_1554_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = lean_unsigned_to_nat(2u);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_1554_);
lean_ctor_set(v___x_1389_, 3, v_r_1530_);
lean_ctor_set(v___x_1389_, 0, v___x_1555_);
v___x_1557_ = v___x_1389_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1530_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v___x_1554_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
else
{
lean_object* v___x_1564_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 3, v_r_1387_);
lean_ctor_set(v___x_1389_, 0, v___x_1393_);
v___x_1564_ = v___x_1389_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_r_1387_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_r_1387_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1389_);
lean_dec(v_v_1385_);
lean_dec(v_k_1384_);
if (lean_obj_tag(v_l_1386_) == 0)
{
if (lean_obj_tag(v_r_1387_) == 0)
{
lean_object* v_size_1566_; lean_object* v_k_1567_; lean_object* v_v_1568_; lean_object* v_l_1569_; lean_object* v_r_1570_; lean_object* v_size_1571_; lean_object* v_k_1572_; lean_object* v_v_1573_; lean_object* v_l_1574_; lean_object* v_r_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_size_1566_ = lean_ctor_get(v_l_1386_, 0);
v_k_1567_ = lean_ctor_get(v_l_1386_, 1);
v_v_1568_ = lean_ctor_get(v_l_1386_, 2);
v_l_1569_ = lean_ctor_get(v_l_1386_, 3);
v_r_1570_ = lean_ctor_get(v_l_1386_, 4);
lean_inc(v_r_1570_);
v_size_1571_ = lean_ctor_get(v_r_1387_, 0);
v_k_1572_ = lean_ctor_get(v_r_1387_, 1);
v_v_1573_ = lean_ctor_get(v_r_1387_, 2);
v_l_1574_ = lean_ctor_get(v_r_1387_, 3);
lean_inc(v_l_1574_);
v_r_1575_ = lean_ctor_get(v_r_1387_, 4);
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_dec_lt(v_size_1566_, v_size_1571_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1713_; 
lean_inc(v_l_1569_);
lean_inc(v_v_1568_);
lean_inc(v_k_1567_);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; lean_object* v_unused_1715_; lean_object* v_unused_1716_; lean_object* v_unused_1717_; lean_object* v_unused_1718_; 
v_unused_1714_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1715_);
v_unused_1716_ = lean_ctor_get(v_l_1386_, 2);
lean_dec(v_unused_1716_);
v_unused_1717_ = lean_ctor_get(v_l_1386_, 1);
lean_dec(v_unused_1717_);
v_unused_1718_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1718_);
v___x_1579_ = v_l_1386_;
v_isShared_1580_ = v_isSharedCheck_1713_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v_l_1386_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1713_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v_tree_1582_; 
v___x_1581_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1567_, v_v_1568_, v_l_1569_, v_r_1570_);
v_tree_1582_ = lean_ctor_get(v___x_1581_, 2);
lean_inc(v_tree_1582_);
if (lean_obj_tag(v_tree_1582_) == 0)
{
lean_object* v_k_1583_; lean_object* v_v_1584_; lean_object* v_size_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_k_1583_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_k_1583_);
v_v_1584_ = lean_ctor_get(v___x_1581_, 1);
lean_inc(v_v_1584_);
lean_dec_ref(v___x_1581_);
v_size_1585_ = lean_ctor_get(v_tree_1582_, 0);
v___x_1586_ = lean_unsigned_to_nat(3u);
v___x_1587_ = lean_nat_mul(v___x_1586_, v_size_1585_);
v___x_1588_ = lean_nat_dec_lt(v___x_1587_, v_size_1571_);
lean_dec(v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
lean_dec(v_l_1574_);
v___x_1589_ = lean_nat_add(v___x_1576_, v_size_1585_);
v___x_1590_ = lean_nat_add(v___x_1589_, v_size_1571_);
lean_dec(v___x_1589_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_r_1387_);
lean_ctor_set(v___x_1579_, 3, v_tree_1582_);
lean_ctor_set(v___x_1579_, 2, v_v_1584_);
lean_ctor_set(v___x_1579_, 1, v_k_1583_);
lean_ctor_set(v___x_1579_, 0, v___x_1590_);
v___x_1592_ = v___x_1579_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_k_1583_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_v_1584_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_tree_1582_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_r_1387_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
else
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1648_; 
lean_inc(v_r_1575_);
lean_inc(v_v_1573_);
lean_inc(v_k_1572_);
lean_inc(v_size_1571_);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; lean_object* v_unused_1653_; 
v_unused_1649_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_r_1387_, 2);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_r_1387_, 1);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_r_1387_, 0);
lean_dec(v_unused_1653_);
v___x_1595_ = v_r_1387_;
v_isShared_1596_ = v_isSharedCheck_1648_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_r_1387_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1648_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_size_1597_; lean_object* v_k_1598_; lean_object* v_v_1599_; lean_object* v_l_1600_; lean_object* v_r_1601_; lean_object* v_size_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_size_1597_ = lean_ctor_get(v_l_1574_, 0);
v_k_1598_ = lean_ctor_get(v_l_1574_, 1);
v_v_1599_ = lean_ctor_get(v_l_1574_, 2);
v_l_1600_ = lean_ctor_get(v_l_1574_, 3);
v_r_1601_ = lean_ctor_get(v_l_1574_, 4);
v_size_1602_ = lean_ctor_get(v_r_1575_, 0);
v___x_1603_ = lean_unsigned_to_nat(2u);
v___x_1604_ = lean_nat_mul(v___x_1603_, v_size_1602_);
v___x_1605_ = lean_nat_dec_lt(v_size_1597_, v___x_1604_);
lean_dec(v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1633_; 
lean_inc(v_r_1601_);
lean_inc(v_l_1600_);
lean_inc(v_v_1599_);
lean_inc(v_k_1598_);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_l_1574_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; 
v_unused_1634_ = lean_ctor_get(v_l_1574_, 4);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_l_1574_, 3);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_l_1574_, 2);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_l_1574_, 1);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_l_1574_, 0);
lean_dec(v_unused_1638_);
v___x_1607_ = v_l_1574_;
v_isShared_1608_ = v_isSharedCheck_1633_;
goto v_resetjp_1606_;
}
else
{
lean_dec(v_l_1574_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1633_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1623_; 
v___x_1609_ = lean_nat_add(v___x_1576_, v_size_1585_);
v___x_1610_ = lean_nat_add(v___x_1609_, v_size_1571_);
lean_dec(v_size_1571_);
if (lean_obj_tag(v_l_1600_) == 0)
{
lean_object* v_size_1631_; 
v_size_1631_ = lean_ctor_get(v_l_1600_, 0);
lean_inc(v_size_1631_);
v___y_1623_ = v_size_1631_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
v___y_1623_ = v___x_1632_;
goto v___jp_1622_;
}
v___jp_1611_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_nat_add(v___y_1612_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec(v___y_1612_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 4, v_r_1575_);
lean_ctor_set(v___x_1607_, 3, v_r_1601_);
lean_ctor_set(v___x_1607_, 2, v_v_1573_);
lean_ctor_set(v___x_1607_, 1, v_k_1572_);
lean_ctor_set(v___x_1607_, 0, v___x_1615_);
v___x_1617_ = v___x_1607_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v_r_1601_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v_r_1575_);
v___x_1617_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1619_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 4, v___x_1617_);
lean_ctor_set(v___x_1595_, 3, v___y_1613_);
lean_ctor_set(v___x_1595_, 2, v_v_1599_);
lean_ctor_set(v___x_1595_, 1, v_k_1598_);
lean_ctor_set(v___x_1595_, 0, v___x_1610_);
v___x_1619_ = v___x_1595_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1598_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1599_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v___y_1613_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
v___jp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_nat_add(v___x_1609_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec(v___x_1609_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_l_1600_);
lean_ctor_set(v___x_1579_, 3, v_tree_1582_);
lean_ctor_set(v___x_1579_, 2, v_v_1584_);
lean_ctor_set(v___x_1579_, 1, v_k_1583_);
lean_ctor_set(v___x_1579_, 0, v___x_1624_);
v___x_1626_ = v___x_1579_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1583_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1584_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_tree_1582_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_l_1600_);
v___x_1626_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_nat_add(v___x_1576_, v_size_1602_);
if (lean_obj_tag(v_r_1601_) == 0)
{
lean_object* v_size_1628_; 
v_size_1628_ = lean_ctor_get(v_r_1601_, 0);
lean_inc(v_size_1628_);
v___y_1612_ = v___x_1627_;
v___y_1613_ = v___x_1626_;
v___y_1614_ = v_size_1628_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_unsigned_to_nat(0u);
v___y_1612_ = v___x_1627_;
v___y_1613_ = v___x_1626_;
v___y_1614_ = v___x_1629_;
goto v___jp_1611_;
}
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1639_ = lean_nat_add(v___x_1576_, v_size_1585_);
v___x_1640_ = lean_nat_add(v___x_1639_, v_size_1571_);
lean_dec(v_size_1571_);
v___x_1641_ = lean_nat_add(v___x_1639_, v_size_1597_);
lean_dec(v___x_1639_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 4, v_l_1574_);
lean_ctor_set(v___x_1595_, 3, v_tree_1582_);
lean_ctor_set(v___x_1595_, 2, v_v_1584_);
lean_ctor_set(v___x_1595_, 1, v_k_1583_);
lean_ctor_set(v___x_1595_, 0, v___x_1641_);
v___x_1643_ = v___x_1595_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1583_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1584_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_tree_1582_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_l_1574_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_r_1575_);
lean_ctor_set(v___x_1579_, 3, v___x_1643_);
lean_ctor_set(v___x_1579_, 2, v_v_1573_);
lean_ctor_set(v___x_1579_, 1, v_k_1572_);
lean_ctor_set(v___x_1579_, 0, v___x_1640_);
v___x_1645_ = v___x_1579_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_r_1575_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
}
else
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1707_; 
lean_inc(v_r_1575_);
lean_inc(v_v_1573_);
lean_inc(v_k_1572_);
lean_inc(v_size_1571_);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; 
v_unused_1708_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_r_1387_, 2);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_r_1387_, 1);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v_r_1387_, 0);
lean_dec(v_unused_1712_);
v___x_1655_ = v_r_1387_;
v_isShared_1656_ = v_isSharedCheck_1707_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v_r_1387_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1707_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
if (lean_obj_tag(v_l_1574_) == 0)
{
if (lean_obj_tag(v_r_1575_) == 0)
{
lean_object* v_k_1657_; lean_object* v_v_1658_; lean_object* v_size_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v_k_1657_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_k_1657_);
v_v_1658_ = lean_ctor_get(v___x_1581_, 1);
lean_inc(v_v_1658_);
lean_dec_ref(v___x_1581_);
v_size_1659_ = lean_ctor_get(v_l_1574_, 0);
v___x_1660_ = lean_nat_add(v___x_1576_, v_size_1571_);
lean_dec(v_size_1571_);
v___x_1661_ = lean_nat_add(v___x_1576_, v_size_1659_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 4, v_l_1574_);
lean_ctor_set(v___x_1655_, 3, v_tree_1582_);
lean_ctor_set(v___x_1655_, 2, v_v_1658_);
lean_ctor_set(v___x_1655_, 1, v_k_1657_);
lean_ctor_set(v___x_1655_, 0, v___x_1661_);
v___x_1663_ = v___x_1655_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1657_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1658_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_tree_1582_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_l_1574_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_r_1575_);
lean_ctor_set(v___x_1579_, 3, v___x_1663_);
lean_ctor_set(v___x_1579_, 2, v_v_1573_);
lean_ctor_set(v___x_1579_, 1, v_k_1572_);
lean_ctor_set(v___x_1579_, 0, v___x_1660_);
v___x_1665_ = v___x_1579_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_r_1575_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_k_1668_; lean_object* v_v_1669_; lean_object* v_k_1670_; lean_object* v_v_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_size_1571_);
v_k_1668_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_k_1668_);
v_v_1669_ = lean_ctor_get(v___x_1581_, 1);
lean_inc(v_v_1669_);
lean_dec_ref(v___x_1581_);
v_k_1670_ = lean_ctor_get(v_l_1574_, 1);
v_v_1671_ = lean_ctor_get(v_l_1574_, 2);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_l_1574_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; lean_object* v_unused_1687_; lean_object* v_unused_1688_; 
v_unused_1686_ = lean_ctor_get(v_l_1574_, 4);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_l_1574_, 3);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_l_1574_, 0);
lean_dec(v_unused_1688_);
v___x_1673_ = v_l_1574_;
v_isShared_1674_ = v_isSharedCheck_1685_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_v_1671_);
lean_inc(v_k_1670_);
lean_dec(v_l_1574_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1685_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = lean_unsigned_to_nat(3u);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 4, v_r_1575_);
lean_ctor_set(v___x_1673_, 3, v_r_1575_);
lean_ctor_set(v___x_1673_, 2, v_v_1669_);
lean_ctor_set(v___x_1673_, 1, v_k_1668_);
lean_ctor_set(v___x_1673_, 0, v___x_1576_);
v___x_1677_ = v___x_1673_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1668_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1669_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_r_1575_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_r_1575_);
v___x_1677_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1679_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 3, v_r_1575_);
lean_ctor_set(v___x_1655_, 0, v___x_1576_);
v___x_1679_ = v___x_1655_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_r_1575_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v_r_1575_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v___x_1679_);
lean_ctor_set(v___x_1579_, 3, v___x_1677_);
lean_ctor_set(v___x_1579_, 2, v_v_1671_);
lean_ctor_set(v___x_1579_, 1, v_k_1670_);
lean_ctor_set(v___x_1579_, 0, v___x_1675_);
v___x_1681_ = v___x_1579_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_k_1670_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_v_1671_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1575_) == 0)
{
lean_object* v_k_1689_; lean_object* v_v_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_dec(v_size_1571_);
v_k_1689_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_k_1689_);
v_v_1690_ = lean_ctor_get(v___x_1581_, 1);
lean_inc(v_v_1690_);
lean_dec_ref(v___x_1581_);
v___x_1691_ = lean_unsigned_to_nat(3u);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 4, v_l_1574_);
lean_ctor_set(v___x_1655_, 2, v_v_1690_);
lean_ctor_set(v___x_1655_, 1, v_k_1689_);
lean_ctor_set(v___x_1655_, 0, v___x_1576_);
v___x_1693_ = v___x_1655_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_k_1689_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_v_1690_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v_l_1574_);
lean_ctor_set(v_reuseFailAlloc_1697_, 4, v_l_1574_);
v___x_1693_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_r_1575_);
lean_ctor_set(v___x_1579_, 3, v___x_1693_);
lean_ctor_set(v___x_1579_, 2, v_v_1573_);
lean_ctor_set(v___x_1579_, 1, v_k_1572_);
lean_ctor_set(v___x_1579_, 0, v___x_1691_);
v___x_1695_ = v___x_1579_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v_r_1575_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_k_1698_; lean_object* v_v_1699_; lean_object* v___x_1701_; 
v_k_1698_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_k_1698_);
v_v_1699_ = lean_ctor_get(v___x_1581_, 1);
lean_inc(v_v_1699_);
lean_dec_ref(v___x_1581_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 3, v_r_1575_);
v___x_1701_ = v___x_1655_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_size_1571_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_r_1575_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_r_1575_);
v___x_1701_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_unsigned_to_nat(2u);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v___x_1701_);
lean_ctor_set(v___x_1579_, 3, v_r_1575_);
lean_ctor_set(v___x_1579_, 2, v_v_1699_);
lean_ctor_set(v___x_1579_, 1, v_k_1698_);
lean_ctor_set(v___x_1579_, 0, v___x_1702_);
v___x_1704_ = v___x_1579_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_k_1698_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_v_1699_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v_r_1575_);
lean_ctor_set(v_reuseFailAlloc_1705_, 4, v___x_1701_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
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
lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1871_; 
lean_inc(v_r_1575_);
lean_inc(v_v_1573_);
lean_inc(v_k_1572_);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; lean_object* v_unused_1873_; lean_object* v_unused_1874_; lean_object* v_unused_1875_; lean_object* v_unused_1876_; 
v_unused_1872_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1872_);
v_unused_1873_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_r_1387_, 2);
lean_dec(v_unused_1874_);
v_unused_1875_ = lean_ctor_get(v_r_1387_, 1);
lean_dec(v_unused_1875_);
v_unused_1876_ = lean_ctor_get(v_r_1387_, 0);
lean_dec(v_unused_1876_);
v___x_1720_ = v_r_1387_;
v_isShared_1721_ = v_isSharedCheck_1871_;
goto v_resetjp_1719_;
}
else
{
lean_dec(v_r_1387_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1871_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v_tree_1723_; 
v___x_1722_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1572_, v_v_1573_, v_l_1574_, v_r_1575_);
v_tree_1723_ = lean_ctor_get(v___x_1722_, 2);
lean_inc(v_tree_1723_);
if (lean_obj_tag(v_tree_1723_) == 0)
{
lean_object* v_k_1724_; lean_object* v_v_1725_; lean_object* v_size_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_k_1724_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_k_1724_);
v_v_1725_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_v_1725_);
lean_dec_ref(v___x_1722_);
v_size_1726_ = lean_ctor_get(v_tree_1723_, 0);
v___x_1727_ = lean_unsigned_to_nat(3u);
v___x_1728_ = lean_nat_mul(v___x_1727_, v_size_1726_);
v___x_1729_ = lean_nat_dec_lt(v___x_1728_, v_size_1566_);
lean_dec(v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_dec(v_r_1570_);
v___x_1730_ = lean_nat_add(v___x_1576_, v_size_1566_);
v___x_1731_ = lean_nat_add(v___x_1730_, v_size_1726_);
lean_dec(v___x_1730_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v_tree_1723_);
lean_ctor_set(v___x_1720_, 3, v_l_1386_);
lean_ctor_set(v___x_1720_, 2, v_v_1725_);
lean_ctor_set(v___x_1720_, 1, v_k_1724_);
lean_ctor_set(v___x_1720_, 0, v___x_1731_);
v___x_1733_ = v___x_1720_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_k_1724_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_v_1725_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v_tree_1723_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
else
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1800_; 
lean_inc(v_l_1569_);
lean_inc(v_v_1568_);
lean_inc(v_k_1567_);
lean_inc(v_size_1566_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; 
v_unused_1801_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_l_1386_, 2);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_l_1386_, 1);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1805_);
v___x_1736_ = v_l_1386_;
v_isShared_1737_ = v_isSharedCheck_1800_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v_l_1386_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1800_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_size_1738_; lean_object* v_size_1739_; lean_object* v_k_1740_; lean_object* v_v_1741_; lean_object* v_l_1742_; lean_object* v_r_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v_size_1738_ = lean_ctor_get(v_l_1569_, 0);
v_size_1739_ = lean_ctor_get(v_r_1570_, 0);
v_k_1740_ = lean_ctor_get(v_r_1570_, 1);
v_v_1741_ = lean_ctor_get(v_r_1570_, 2);
v_l_1742_ = lean_ctor_get(v_r_1570_, 3);
v_r_1743_ = lean_ctor_get(v_r_1570_, 4);
v___x_1744_ = lean_unsigned_to_nat(2u);
v___x_1745_ = lean_nat_mul(v___x_1744_, v_size_1738_);
v___x_1746_ = lean_nat_dec_lt(v_size_1739_, v___x_1745_);
lean_dec(v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1784_; 
lean_inc(v_r_1743_);
lean_inc(v_l_1742_);
lean_inc(v_v_1741_);
lean_inc(v_k_1740_);
lean_del_object(v___x_1736_);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_r_1570_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; lean_object* v_unused_1786_; lean_object* v_unused_1787_; lean_object* v_unused_1788_; lean_object* v_unused_1789_; 
v_unused_1785_ = lean_ctor_get(v_r_1570_, 4);
lean_dec(v_unused_1785_);
v_unused_1786_ = lean_ctor_get(v_r_1570_, 3);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v_r_1570_, 2);
lean_dec(v_unused_1787_);
v_unused_1788_ = lean_ctor_get(v_r_1570_, 1);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v_r_1570_, 0);
lean_dec(v_unused_1789_);
v___x_1748_ = v_r_1570_;
v_isShared_1749_ = v_isSharedCheck_1784_;
goto v_resetjp_1747_;
}
else
{
lean_dec(v_r_1570_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1784_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___x_1772_; lean_object* v___y_1774_; 
v___x_1750_ = lean_nat_add(v___x_1576_, v_size_1566_);
lean_dec(v_size_1566_);
v___x_1751_ = lean_nat_add(v___x_1750_, v_size_1726_);
lean_dec(v___x_1750_);
v___x_1772_ = lean_nat_add(v___x_1576_, v_size_1738_);
if (lean_obj_tag(v_l_1742_) == 0)
{
lean_object* v_size_1782_; 
v_size_1782_ = lean_ctor_get(v_l_1742_, 0);
lean_inc(v_size_1782_);
v___y_1774_ = v_size_1782_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_unsigned_to_nat(0u);
v___y_1774_ = v___x_1783_;
goto v___jp_1773_;
}
v___jp_1752_:
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1756_ = lean_nat_add(v___y_1753_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec(v___y_1753_);
lean_inc_ref(v_tree_1723_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 4, v_tree_1723_);
lean_ctor_set(v___x_1748_, 3, v_r_1743_);
lean_ctor_set(v___x_1748_, 2, v_v_1725_);
lean_ctor_set(v___x_1748_, 1, v_k_1724_);
lean_ctor_set(v___x_1748_, 0, v___x_1756_);
v___x_1758_ = v___x_1748_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_k_1724_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_v_1725_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_r_1743_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_tree_1723_);
v___x_1758_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_isSharedCheck_1765_ = !lean_is_exclusive(v_tree_1723_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; lean_object* v_unused_1767_; lean_object* v_unused_1768_; lean_object* v_unused_1769_; lean_object* v_unused_1770_; 
v_unused_1766_ = lean_ctor_get(v_tree_1723_, 4);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v_tree_1723_, 3);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_tree_1723_, 2);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_tree_1723_, 1);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_tree_1723_, 0);
lean_dec(v_unused_1770_);
v___x_1760_ = v_tree_1723_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v_tree_1723_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 4, v___x_1758_);
lean_ctor_set(v___x_1760_, 3, v___y_1754_);
lean_ctor_set(v___x_1760_, 2, v_v_1741_);
lean_ctor_set(v___x_1760_, 1, v_k_1740_);
lean_ctor_set(v___x_1760_, 0, v___x_1751_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_k_1740_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_v_1741_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v___y_1754_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v___x_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
v___jp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_nat_add(v___x_1772_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec(v___x_1772_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v_l_1742_);
lean_ctor_set(v___x_1720_, 3, v_l_1569_);
lean_ctor_set(v___x_1720_, 2, v_v_1568_);
lean_ctor_set(v___x_1720_, 1, v_k_1567_);
lean_ctor_set(v___x_1720_, 0, v___x_1775_);
v___x_1777_ = v___x_1720_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_k_1567_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_v_1568_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_l_1569_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v_l_1742_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_nat_add(v___x_1576_, v_size_1726_);
if (lean_obj_tag(v_r_1743_) == 0)
{
lean_object* v_size_1779_; 
v_size_1779_ = lean_ctor_get(v_r_1743_, 0);
lean_inc(v_size_1779_);
v___y_1753_ = v___x_1778_;
v___y_1754_ = v___x_1777_;
v___y_1755_ = v_size_1779_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_unsigned_to_nat(0u);
v___y_1753_ = v___x_1778_;
v___y_1754_ = v___x_1777_;
v___y_1755_ = v___x_1780_;
goto v___jp_1752_;
}
}
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1790_ = lean_nat_add(v___x_1576_, v_size_1566_);
lean_dec(v_size_1566_);
v___x_1791_ = lean_nat_add(v___x_1790_, v_size_1726_);
lean_dec(v___x_1790_);
v___x_1792_ = lean_nat_add(v___x_1576_, v_size_1726_);
v___x_1793_ = lean_nat_add(v___x_1792_, v_size_1739_);
lean_dec(v___x_1792_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v_tree_1723_);
lean_ctor_set(v___x_1720_, 3, v_r_1570_);
lean_ctor_set(v___x_1720_, 2, v_v_1725_);
lean_ctor_set(v___x_1720_, 1, v_k_1724_);
lean_ctor_set(v___x_1720_, 0, v___x_1793_);
v___x_1795_ = v___x_1720_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_k_1724_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_v_1725_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_r_1570_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_tree_1723_);
v___x_1795_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 4, v___x_1795_);
lean_ctor_set(v___x_1736_, 0, v___x_1791_);
v___x_1797_ = v___x_1736_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_k_1567_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_v_1568_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_l_1569_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1569_) == 0)
{
lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1829_; 
lean_inc_ref(v_l_1569_);
lean_inc(v_v_1568_);
lean_inc(v_k_1567_);
lean_inc(v_size_1566_);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; lean_object* v_unused_1831_; lean_object* v_unused_1832_; lean_object* v_unused_1833_; lean_object* v_unused_1834_; 
v_unused_1830_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1830_);
v_unused_1831_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_l_1386_, 2);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_l_1386_, 1);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1834_);
v___x_1807_ = v_l_1386_;
v_isShared_1808_ = v_isSharedCheck_1829_;
goto v_resetjp_1806_;
}
else
{
lean_dec(v_l_1386_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1829_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
if (lean_obj_tag(v_r_1570_) == 0)
{
lean_object* v_k_1809_; lean_object* v_v_1810_; lean_object* v_size_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v_k_1809_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_k_1809_);
v_v_1810_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_v_1810_);
lean_dec_ref(v___x_1722_);
v_size_1811_ = lean_ctor_get(v_r_1570_, 0);
v___x_1812_ = lean_nat_add(v___x_1576_, v_size_1566_);
lean_dec(v_size_1566_);
v___x_1813_ = lean_nat_add(v___x_1576_, v_size_1811_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v_tree_1723_);
lean_ctor_set(v___x_1720_, 3, v_r_1570_);
lean_ctor_set(v___x_1720_, 2, v_v_1810_);
lean_ctor_set(v___x_1720_, 1, v_k_1809_);
lean_ctor_set(v___x_1720_, 0, v___x_1813_);
v___x_1815_ = v___x_1720_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_k_1809_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_v_1810_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_r_1570_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v_tree_1723_);
v___x_1815_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1817_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 4, v___x_1815_);
lean_ctor_set(v___x_1807_, 0, v___x_1812_);
v___x_1817_ = v___x_1807_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_k_1567_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_v_1568_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_l_1569_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_k_1820_; lean_object* v_v_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
lean_dec(v_size_1566_);
v_k_1820_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_k_1820_);
v_v_1821_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_v_1821_);
lean_dec_ref(v___x_1722_);
v___x_1822_ = lean_unsigned_to_nat(3u);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v_r_1570_);
lean_ctor_set(v___x_1720_, 3, v_r_1570_);
lean_ctor_set(v___x_1720_, 2, v_v_1821_);
lean_ctor_set(v___x_1720_, 1, v_k_1820_);
lean_ctor_set(v___x_1720_, 0, v___x_1576_);
v___x_1824_ = v___x_1720_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_k_1820_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_v_1821_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_r_1570_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v_r_1570_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 4, v___x_1824_);
lean_ctor_set(v___x_1807_, 0, v___x_1822_);
v___x_1826_ = v___x_1807_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_k_1567_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_v_1568_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_l_1569_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1570_) == 0)
{
lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1859_; 
lean_inc(v_l_1569_);
lean_inc(v_v_1568_);
lean_inc(v_k_1567_);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; lean_object* v_unused_1864_; 
v_unused_1860_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_l_1386_, 2);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_l_1386_, 1);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1864_);
v___x_1836_ = v_l_1386_;
v_isShared_1837_ = v_isSharedCheck_1859_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v_l_1386_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1859_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_k_1838_; lean_object* v_v_1839_; lean_object* v_k_1840_; lean_object* v_v_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1855_; 
v_k_1838_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_k_1838_);
v_v_1839_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_v_1839_);
lean_dec_ref(v___x_1722_);
v_k_1840_ = lean_ctor_get(v_r_1570_, 1);
v_v_1841_ = lean_ctor_get(v_r_1570_, 2);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_r_1570_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; 
v_unused_1856_ = lean_ctor_get(v_r_1570_, 4);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_r_1570_, 3);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_r_1570_, 0);
lean_dec(v_unused_1858_);
v___x_1843_ = v_r_1570_;
v_isShared_1844_ = v_isSharedCheck_1855_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_v_1841_);
lean_inc(v_k_1840_);
lean_dec(v_r_1570_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1855_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1845_ = lean_unsigned_to_nat(3u);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 4, v_l_1569_);
lean_ctor_set(v___x_1843_, 3, v_l_1569_);
lean_ctor_set(v___x_1843_, 2, v_v_1568_);
lean_ctor_set(v___x_1843_, 1, v_k_1567_);
lean_ctor_set(v___x_1843_, 0, v___x_1576_);
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_k_1567_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_v_1568_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_l_1569_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v_l_1569_);
v___x_1847_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v_l_1569_);
lean_ctor_set(v___x_1720_, 3, v_l_1569_);
lean_ctor_set(v___x_1720_, 2, v_v_1839_);
lean_ctor_set(v___x_1720_, 1, v_k_1838_);
lean_ctor_set(v___x_1720_, 0, v___x_1576_);
v___x_1849_ = v___x_1720_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_k_1838_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_v_1839_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_l_1569_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v_l_1569_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 4, v___x_1849_);
lean_ctor_set(v___x_1836_, 3, v___x_1847_);
lean_ctor_set(v___x_1836_, 2, v_v_1841_);
lean_ctor_set(v___x_1836_, 1, v_k_1840_);
lean_ctor_set(v___x_1836_, 0, v___x_1845_);
v___x_1851_ = v___x_1836_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_k_1840_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_v_1841_);
lean_ctor_set(v_reuseFailAlloc_1852_, 3, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1852_, 4, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
}
else
{
lean_object* v_k_1865_; lean_object* v_v_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v_k_1865_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_k_1865_);
v_v_1866_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_v_1866_);
lean_dec_ref(v___x_1722_);
v___x_1867_ = lean_unsigned_to_nat(2u);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v_r_1570_);
lean_ctor_set(v___x_1720_, 3, v_l_1386_);
lean_ctor_set(v___x_1720_, 2, v_v_1866_);
lean_ctor_set(v___x_1720_, 1, v_k_1865_);
lean_ctor_set(v___x_1720_, 0, v___x_1867_);
v___x_1869_ = v___x_1720_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_k_1865_);
lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_v_1866_);
lean_ctor_set(v_reuseFailAlloc_1870_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1870_, 4, v_r_1570_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
}
}
else
{
return v_l_1386_;
}
}
else
{
return v_r_1387_;
}
}
default: 
{
lean_object* v_impl_1877_; lean_object* v___x_1878_; 
v_impl_1877_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1382_, v_r_1387_);
v___x_1878_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1877_) == 0)
{
if (lean_obj_tag(v_l_1386_) == 0)
{
lean_object* v_size_1879_; lean_object* v_size_1880_; lean_object* v_k_1881_; lean_object* v_v_1882_; lean_object* v_l_1883_; lean_object* v_r_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_size_1879_ = lean_ctor_get(v_impl_1877_, 0);
lean_inc(v_size_1879_);
v_size_1880_ = lean_ctor_get(v_l_1386_, 0);
v_k_1881_ = lean_ctor_get(v_l_1386_, 1);
v_v_1882_ = lean_ctor_get(v_l_1386_, 2);
v_l_1883_ = lean_ctor_get(v_l_1386_, 3);
v_r_1884_ = lean_ctor_get(v_l_1386_, 4);
lean_inc(v_r_1884_);
v___x_1885_ = lean_unsigned_to_nat(3u);
v___x_1886_ = lean_nat_mul(v___x_1885_, v_size_1879_);
v___x_1887_ = lean_nat_dec_lt(v___x_1886_, v_size_1880_);
lean_dec(v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_dec(v_r_1884_);
v___x_1888_ = lean_nat_add(v___x_1878_, v_size_1880_);
v___x_1889_ = lean_nat_add(v___x_1888_, v_size_1879_);
lean_dec(v_size_1879_);
lean_dec(v___x_1888_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_impl_1877_);
lean_ctor_set(v___x_1389_, 0, v___x_1889_);
v___x_1891_ = v___x_1389_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_impl_1877_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
else
{
lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1958_; 
lean_inc(v_l_1883_);
lean_inc(v_v_1882_);
lean_inc(v_k_1881_);
lean_inc(v_size_1880_);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; lean_object* v_unused_1960_; lean_object* v_unused_1961_; lean_object* v_unused_1962_; lean_object* v_unused_1963_; 
v_unused_1959_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1959_);
v_unused_1960_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1960_);
v_unused_1961_ = lean_ctor_get(v_l_1386_, 2);
lean_dec(v_unused_1961_);
v_unused_1962_ = lean_ctor_get(v_l_1386_, 1);
lean_dec(v_unused_1962_);
v_unused_1963_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1963_);
v___x_1894_ = v_l_1386_;
v_isShared_1895_ = v_isSharedCheck_1958_;
goto v_resetjp_1893_;
}
else
{
lean_dec(v_l_1386_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1958_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v_size_1896_; lean_object* v_size_1897_; lean_object* v_k_1898_; lean_object* v_v_1899_; lean_object* v_l_1900_; lean_object* v_r_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v_size_1896_ = lean_ctor_get(v_l_1883_, 0);
v_size_1897_ = lean_ctor_get(v_r_1884_, 0);
v_k_1898_ = lean_ctor_get(v_r_1884_, 1);
v_v_1899_ = lean_ctor_get(v_r_1884_, 2);
v_l_1900_ = lean_ctor_get(v_r_1884_, 3);
v_r_1901_ = lean_ctor_get(v_r_1884_, 4);
v___x_1902_ = lean_unsigned_to_nat(2u);
v___x_1903_ = lean_nat_mul(v___x_1902_, v_size_1896_);
v___x_1904_ = lean_nat_dec_lt(v_size_1897_, v___x_1903_);
lean_dec(v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1933_; 
lean_inc(v_r_1901_);
lean_inc(v_l_1900_);
lean_inc(v_v_1899_);
lean_inc(v_k_1898_);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_r_1884_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; lean_object* v_unused_1935_; lean_object* v_unused_1936_; lean_object* v_unused_1937_; lean_object* v_unused_1938_; 
v_unused_1934_ = lean_ctor_get(v_r_1884_, 4);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_r_1884_, 3);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_r_1884_, 2);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_r_1884_, 1);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_r_1884_, 0);
lean_dec(v_unused_1938_);
v___x_1906_ = v_r_1884_;
v_isShared_1907_ = v_isSharedCheck_1933_;
goto v_resetjp_1905_;
}
else
{
lean_dec(v_r_1884_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1933_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___x_1921_; lean_object* v___y_1923_; 
v___x_1908_ = lean_nat_add(v___x_1878_, v_size_1880_);
lean_dec(v_size_1880_);
v___x_1909_ = lean_nat_add(v___x_1908_, v_size_1879_);
lean_dec(v___x_1908_);
v___x_1921_ = lean_nat_add(v___x_1878_, v_size_1896_);
if (lean_obj_tag(v_l_1900_) == 0)
{
lean_object* v_size_1931_; 
v_size_1931_ = lean_ctor_get(v_l_1900_, 0);
lean_inc(v_size_1931_);
v___y_1923_ = v_size_1931_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_unsigned_to_nat(0u);
v___y_1923_ = v___x_1932_;
goto v___jp_1922_;
}
v___jp_1910_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_nat_add(v___y_1911_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec(v___y_1911_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 4, v_impl_1877_);
lean_ctor_set(v___x_1906_, 3, v_r_1901_);
lean_ctor_set(v___x_1906_, 2, v_v_1385_);
lean_ctor_set(v___x_1906_, 1, v_k_1384_);
lean_ctor_set(v___x_1906_, 0, v___x_1914_);
v___x_1916_ = v___x_1906_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_r_1901_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_impl_1877_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 4, v___x_1916_);
lean_ctor_set(v___x_1894_, 3, v___y_1912_);
lean_ctor_set(v___x_1894_, 2, v_v_1899_);
lean_ctor_set(v___x_1894_, 1, v_k_1898_);
lean_ctor_set(v___x_1894_, 0, v___x_1909_);
v___x_1918_ = v___x_1894_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_k_1898_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_v_1899_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v___y_1912_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
v___jp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = lean_nat_add(v___x_1921_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec(v___x_1921_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_l_1900_);
lean_ctor_set(v___x_1389_, 3, v_l_1883_);
lean_ctor_set(v___x_1389_, 2, v_v_1882_);
lean_ctor_set(v___x_1389_, 1, v_k_1881_);
lean_ctor_set(v___x_1389_, 0, v___x_1924_);
v___x_1926_ = v___x_1389_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1881_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1882_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_l_1883_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_l_1900_);
v___x_1926_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_nat_add(v___x_1878_, v_size_1879_);
lean_dec(v_size_1879_);
if (lean_obj_tag(v_r_1901_) == 0)
{
lean_object* v_size_1928_; 
v_size_1928_ = lean_ctor_get(v_r_1901_, 0);
lean_inc(v_size_1928_);
v___y_1911_ = v___x_1927_;
v___y_1912_ = v___x_1926_;
v___y_1913_ = v_size_1928_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_unsigned_to_nat(0u);
v___y_1911_ = v___x_1927_;
v___y_1912_ = v___x_1926_;
v___y_1913_ = v___x_1929_;
goto v___jp_1910_;
}
}
}
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
lean_del_object(v___x_1389_);
v___x_1939_ = lean_nat_add(v___x_1878_, v_size_1880_);
lean_dec(v_size_1880_);
v___x_1940_ = lean_nat_add(v___x_1939_, v_size_1879_);
lean_dec(v___x_1939_);
v___x_1941_ = lean_nat_add(v___x_1878_, v_size_1879_);
lean_dec(v_size_1879_);
v___x_1942_ = lean_nat_add(v___x_1941_, v_size_1897_);
lean_dec(v___x_1941_);
lean_inc_ref(v_impl_1877_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 4, v_impl_1877_);
lean_ctor_set(v___x_1894_, 3, v_r_1884_);
lean_ctor_set(v___x_1894_, 2, v_v_1385_);
lean_ctor_set(v___x_1894_, 1, v_k_1384_);
lean_ctor_set(v___x_1894_, 0, v___x_1942_);
v___x_1944_ = v___x_1894_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_r_1884_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v_impl_1877_);
v___x_1944_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_isSharedCheck_1951_ = !lean_is_exclusive(v_impl_1877_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; lean_object* v_unused_1953_; lean_object* v_unused_1954_; lean_object* v_unused_1955_; lean_object* v_unused_1956_; 
v_unused_1952_ = lean_ctor_get(v_impl_1877_, 4);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_impl_1877_, 3);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_impl_1877_, 2);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_impl_1877_, 1);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_impl_1877_, 0);
lean_dec(v_unused_1956_);
v___x_1946_ = v_impl_1877_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_dec(v_impl_1877_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_1944_);
lean_ctor_set(v___x_1946_, 3, v_l_1883_);
lean_ctor_set(v___x_1946_, 2, v_v_1882_);
lean_ctor_set(v___x_1946_, 1, v_k_1881_);
lean_ctor_set(v___x_1946_, 0, v___x_1940_);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_k_1881_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_v_1882_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_l_1883_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v___x_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v_size_1964_ = lean_ctor_get(v_impl_1877_, 0);
lean_inc(v_size_1964_);
v___x_1965_ = lean_nat_add(v___x_1878_, v_size_1964_);
lean_dec(v_size_1964_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_impl_1877_);
lean_ctor_set(v___x_1389_, 0, v___x_1965_);
v___x_1967_ = v___x_1389_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v_impl_1877_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
if (lean_obj_tag(v_l_1386_) == 0)
{
lean_object* v_l_1969_; 
v_l_1969_ = lean_ctor_get(v_l_1386_, 3);
if (lean_obj_tag(v_l_1969_) == 0)
{
lean_object* v_r_1970_; 
lean_inc_ref(v_l_1969_);
v_r_1970_ = lean_ctor_get(v_l_1386_, 4);
lean_inc(v_r_1970_);
if (lean_obj_tag(v_r_1970_) == 0)
{
lean_object* v_size_1971_; lean_object* v_k_1972_; lean_object* v_v_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1986_; 
v_size_1971_ = lean_ctor_get(v_l_1386_, 0);
v_k_1972_ = lean_ctor_get(v_l_1386_, 1);
v_v_1973_ = lean_ctor_get(v_l_1386_, 2);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1988_);
v___x_1975_ = v_l_1386_;
v_isShared_1976_ = v_isSharedCheck_1986_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_v_1973_);
lean_inc(v_k_1972_);
lean_inc(v_size_1971_);
lean_dec(v_l_1386_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1986_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_size_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v_size_1977_ = lean_ctor_get(v_r_1970_, 0);
v___x_1978_ = lean_nat_add(v___x_1878_, v_size_1971_);
lean_dec(v_size_1971_);
v___x_1979_ = lean_nat_add(v___x_1878_, v_size_1977_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v_impl_1877_);
lean_ctor_set(v___x_1975_, 3, v_r_1970_);
lean_ctor_set(v___x_1975_, 2, v_v_1385_);
lean_ctor_set(v___x_1975_, 1, v_k_1384_);
lean_ctor_set(v___x_1975_, 0, v___x_1979_);
v___x_1981_ = v___x_1975_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_r_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v_impl_1877_);
v___x_1981_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_1981_);
lean_ctor_set(v___x_1389_, 3, v_l_1969_);
lean_ctor_set(v___x_1389_, 2, v_v_1973_);
lean_ctor_set(v___x_1389_, 1, v_k_1972_);
lean_ctor_set(v___x_1389_, 0, v___x_1978_);
v___x_1983_ = v___x_1389_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_k_1972_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_v_1973_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v_l_1969_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_k_1989_; lean_object* v_v_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2001_; 
v_k_1989_ = lean_ctor_get(v_l_1386_, 1);
v_v_1990_ = lean_ctor_get(v_l_1386_, 2);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; lean_object* v_unused_2003_; lean_object* v_unused_2004_; 
v_unused_2002_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_2004_);
v___x_1992_ = v_l_1386_;
v_isShared_1993_ = v_isSharedCheck_2001_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_v_1990_);
lean_inc(v_k_1989_);
lean_dec(v_l_1386_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2001_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_unsigned_to_nat(3u);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 3, v_r_1970_);
lean_ctor_set(v___x_1992_, 2, v_v_1385_);
lean_ctor_set(v___x_1992_, 1, v_k_1384_);
lean_ctor_set(v___x_1992_, 0, v___x_1878_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_r_1970_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_r_1970_);
v___x_1996_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1998_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_1996_);
lean_ctor_set(v___x_1389_, 3, v_l_1969_);
lean_ctor_set(v___x_1389_, 2, v_v_1990_);
lean_ctor_set(v___x_1389_, 1, v_k_1989_);
lean_ctor_set(v___x_1389_, 0, v___x_1994_);
v___x_1998_ = v___x_1389_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_k_1989_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_v_1990_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_l_1969_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
else
{
lean_object* v_r_2005_; 
v_r_2005_ = lean_ctor_get(v_l_1386_, 4);
lean_inc(v_r_2005_);
if (lean_obj_tag(v_r_2005_) == 0)
{
lean_object* v_k_2006_; lean_object* v_v_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2030_; 
lean_inc(v_l_1969_);
v_k_2006_ = lean_ctor_get(v_l_1386_, 1);
v_v_2007_ = lean_ctor_get(v_l_1386_, 2);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; 
v_unused_2031_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_2033_);
v___x_2009_ = v_l_1386_;
v_isShared_2010_ = v_isSharedCheck_2030_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_v_2007_);
lean_inc(v_k_2006_);
lean_dec(v_l_1386_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2030_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_k_2011_; lean_object* v_v_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2026_; 
v_k_2011_ = lean_ctor_get(v_r_2005_, 1);
v_v_2012_ = lean_ctor_get(v_r_2005_, 2);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_r_2005_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; 
v_unused_2027_ = lean_ctor_get(v_r_2005_, 4);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_r_2005_, 3);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_r_2005_, 0);
lean_dec(v_unused_2029_);
v___x_2014_ = v_r_2005_;
v_isShared_2015_ = v_isSharedCheck_2026_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_v_2012_);
lean_inc(v_k_2011_);
lean_dec(v_r_2005_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2026_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_unsigned_to_nat(3u);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 4, v_l_1969_);
lean_ctor_set(v___x_2014_, 3, v_l_1969_);
lean_ctor_set(v___x_2014_, 2, v_v_2007_);
lean_ctor_set(v___x_2014_, 1, v_k_2006_);
lean_ctor_set(v___x_2014_, 0, v___x_1878_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_k_2006_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_v_2007_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_l_1969_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_l_1969_);
v___x_2018_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v_l_1969_);
lean_ctor_set(v___x_2009_, 2, v_v_1385_);
lean_ctor_set(v___x_2009_, 1, v_k_1384_);
lean_ctor_set(v___x_2009_, 0, v___x_1878_);
v___x_2020_ = v___x_2009_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v_l_1969_);
lean_ctor_set(v_reuseFailAlloc_2024_, 4, v_l_1969_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_2020_);
lean_ctor_set(v___x_1389_, 3, v___x_2018_);
lean_ctor_set(v___x_1389_, 2, v_v_2012_);
lean_ctor_set(v___x_1389_, 1, v_k_2011_);
lean_ctor_set(v___x_1389_, 0, v___x_2016_);
v___x_2022_ = v___x_1389_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_k_2011_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_v_2012_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = lean_unsigned_to_nat(2u);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_r_2005_);
lean_ctor_set(v___x_1389_, 0, v___x_2034_);
v___x_2036_ = v___x_1389_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_2037_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_2037_, 4, v_r_2005_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v___x_2039_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_l_1386_);
lean_ctor_set(v___x_1389_, 0, v___x_1878_);
v___x_2039_ = v___x_1389_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_2040_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_2040_, 4, v_l_1386_);
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
}
}
}
else
{
return v_t_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2043_, lean_object* v_t_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2043_, v_t_2044_);
lean_dec(v_k_2043_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2046_, lean_object* v_v_2047_, lean_object* v_i_2048_){
_start:
{
lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = lean_array_get_size(v_xs_2046_);
v___x_2050_ = lean_nat_dec_lt(v_i_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
lean_dec(v_i_2048_);
v___x_2051_ = lean_box(0);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = lean_array_fget_borrowed(v_xs_2046_, v_i_2048_);
v___x_2053_ = l_Lean_instBEqFVarId_beq(v___x_2052_, v_v_2047_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_unsigned_to_nat(1u);
v___x_2055_ = lean_nat_add(v_i_2048_, v___x_2054_);
lean_dec(v_i_2048_);
v_i_2048_ = v___x_2055_;
goto _start;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_i_2048_);
return v___x_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2058_, lean_object* v_v_2059_, lean_object* v_i_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2058_, v_v_2059_, v_i_2060_);
lean_dec(v_v_2059_);
lean_dec_ref(v_xs_2058_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2062_, lean_object* v_v_2063_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2062_, v_v_2063_, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2066_, lean_object* v_v_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2066_, v_v_2067_);
lean_dec(v_v_2067_);
lean_dec_ref(v_xs_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2069_, size_t v_x_2070_, lean_object* v_x_2071_){
_start:
{
if (lean_obj_tag(v_x_2069_) == 0)
{
lean_object* v_es_2072_; lean_object* v___x_2073_; size_t v___x_2074_; size_t v___x_2075_; size_t v___x_2076_; lean_object* v_j_2077_; lean_object* v_entry_2078_; 
v_es_2072_ = lean_ctor_get(v_x_2069_, 0);
v___x_2073_ = lean_box(2);
v___x_2074_ = ((size_t)5ULL);
v___x_2075_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_2076_ = lean_usize_land(v_x_2070_, v___x_2075_);
v_j_2077_ = lean_usize_to_nat(v___x_2076_);
v_entry_2078_ = lean_array_get(v___x_2073_, v_es_2072_, v_j_2077_);
switch(lean_obj_tag(v_entry_2078_))
{
case 0:
{
lean_object* v_key_2079_; uint8_t v___x_2080_; 
v_key_2079_ = lean_ctor_get(v_entry_2078_, 0);
lean_inc(v_key_2079_);
lean_dec_ref(v_entry_2078_);
v___x_2080_ = l_Lean_instBEqFVarId_beq(v_x_2071_, v_key_2079_);
lean_dec(v_key_2079_);
if (v___x_2080_ == 0)
{
lean_dec(v_j_2077_);
return v_x_2069_;
}
else
{
lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2088_; 
lean_inc_ref(v_es_2072_);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_x_2069_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; 
v_unused_2089_ = lean_ctor_get(v_x_2069_, 0);
lean_dec(v_unused_2089_);
v___x_2082_ = v_x_2069_;
v_isShared_2083_ = v_isSharedCheck_2088_;
goto v_resetjp_2081_;
}
else
{
lean_dec(v_x_2069_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2088_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_array_set(v_es_2072_, v_j_2077_, v___x_2073_);
lean_dec(v_j_2077_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2084_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
case 1:
{
lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2123_; 
lean_inc_ref(v_es_2072_);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_x_2069_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; 
v_unused_2124_ = lean_ctor_get(v_x_2069_, 0);
lean_dec(v_unused_2124_);
v___x_2091_ = v_x_2069_;
v_isShared_2092_ = v_isSharedCheck_2123_;
goto v_resetjp_2090_;
}
else
{
lean_dec(v_x_2069_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2123_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_node_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2122_; 
v_node_2093_ = lean_ctor_get(v_entry_2078_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_entry_2078_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2095_ = v_entry_2078_;
v_isShared_2096_ = v_isSharedCheck_2122_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_node_2093_);
lean_dec(v_entry_2078_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2122_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_entries_2097_; size_t v___x_2098_; lean_object* v_newNode_2099_; lean_object* v___x_2100_; 
v_entries_2097_ = lean_array_set(v_es_2072_, v_j_2077_, v___x_2073_);
v___x_2098_ = lean_usize_shift_right(v_x_2070_, v___x_2074_);
v_newNode_2099_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2093_, v___x_2098_, v_x_2071_);
lean_inc_ref(v_newNode_2099_);
v___x_2100_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v___x_2102_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v_newNode_2099_);
v___x_2102_ = v___x_2095_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_newNode_2099_);
v___x_2102_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_array_set(v_entries_2097_, v_j_2077_, v___x_2102_);
lean_dec(v_j_2077_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2103_);
v___x_2105_ = v___x_2091_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
else
{
lean_object* v_val_2108_; lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref(v_newNode_2099_);
lean_del_object(v___x_2095_);
v_val_2108_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_val_2108_);
lean_dec_ref(v___x_2100_);
v_fst_2109_ = lean_ctor_get(v_val_2108_, 0);
v_snd_2110_ = lean_ctor_get(v_val_2108_, 1);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_val_2108_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2112_ = v_val_2108_;
v_isShared_2113_ = v_isSharedCheck_2121_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_inc(v_fst_2109_);
lean_dec(v_val_2108_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2121_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_fst_2109_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_snd_2110_);
v___x_2115_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2116_ = lean_array_set(v_entries_2097_, v_j_2077_, v___x_2115_);
lean_dec(v_j_2077_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2116_);
v___x_2118_ = v___x_2091_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2077_);
return v_x_2069_;
}
}
}
else
{
lean_object* v_ks_2125_; lean_object* v_vs_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2140_; 
v_ks_2125_ = lean_ctor_get(v_x_2069_, 0);
v_vs_2126_ = lean_ctor_get(v_x_2069_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_x_2069_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2128_ = v_x_2069_;
v_isShared_2129_ = v_isSharedCheck_2140_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_vs_2126_);
lean_inc(v_ks_2125_);
lean_dec(v_x_2069_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2140_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2125_, v_x_2071_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2132_; 
if (v_isShared_2129_ == 0)
{
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_ks_2125_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_vs_2126_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
else
{
lean_object* v_val_2134_; lean_object* v_keys_x27_2135_; lean_object* v_vals_x27_2136_; lean_object* v___x_2138_; 
v_val_2134_ = lean_ctor_get(v___x_2130_, 0);
lean_inc_n(v_val_2134_, 2);
lean_dec_ref(v___x_2130_);
v_keys_x27_2135_ = l_Array_eraseIdx___redArg(v_ks_2125_, v_val_2134_);
v_vals_x27_2136_ = l_Array_eraseIdx___redArg(v_vs_2126_, v_val_2134_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_vals_x27_2136_);
lean_ctor_set(v___x_2128_, 0, v_keys_x27_2135_);
v___x_2138_ = v___x_2128_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_keys_x27_2135_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_vals_x27_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2141_, lean_object* v_x_2142_, lean_object* v_x_2143_){
_start:
{
size_t v_x_2695__boxed_2144_; lean_object* v_res_2145_; 
v_x_2695__boxed_2144_ = lean_unbox_usize(v_x_2142_);
lean_dec(v_x_2142_);
v_res_2145_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2141_, v_x_2695__boxed_2144_, v_x_2143_);
lean_dec(v_x_2143_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2146_, lean_object* v_x_2147_){
_start:
{
uint64_t v___x_2148_; size_t v_h_2149_; lean_object* v___x_2150_; 
v___x_2148_ = l_Lean_instHashableFVarId_hash(v_x_2147_);
v_h_2149_ = lean_uint64_to_usize(v___x_2148_);
v___x_2150_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2146_, v_h_2149_, v_x_2147_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2151_, v_x_2152_);
lean_dec(v_x_2152_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* v_lctx_2154_, lean_object* v_fvarId_2155_){
_start:
{
lean_object* v_fvarIdToDecl_2156_; lean_object* v_decls_2157_; lean_object* v_auxDeclToFullName_2158_; lean_object* v___x_2159_; 
v_fvarIdToDecl_2156_ = lean_ctor_get(v_lctx_2154_, 0);
v_decls_2157_ = lean_ctor_get(v_lctx_2154_, 1);
v_auxDeclToFullName_2158_ = lean_ctor_get(v_lctx_2154_, 2);
lean_inc_ref(v_fvarIdToDecl_2156_);
v___x_2159_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2156_, v_fvarId_2155_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_dec(v_fvarId_2155_);
return v_lctx_2154_;
}
else
{
lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2179_; 
lean_inc(v_auxDeclToFullName_2158_);
lean_inc_ref(v_decls_2157_);
lean_inc_ref(v_fvarIdToDecl_2156_);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_lctx_2154_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; lean_object* v_unused_2181_; lean_object* v_unused_2182_; 
v_unused_2180_ = lean_ctor_get(v_lctx_2154_, 2);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v_lctx_2154_, 1);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_lctx_2154_, 0);
lean_dec(v_unused_2182_);
v___x_2161_ = v_lctx_2154_;
v_isShared_2162_ = v_isSharedCheck_2179_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v_lctx_2154_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2179_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_val_2163_; lean_object* v___x_2164_; lean_object* v___y_2166_; lean_object* v_index_2178_; 
v_val_2163_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_val_2163_);
lean_dec_ref(v___x_2159_);
v___x_2164_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2156_, v_fvarId_2155_);
v_index_2178_ = lean_ctor_get(v_val_2163_, 0);
lean_inc(v_index_2178_);
v___y_2166_ = v_index_2178_;
goto v___jp_2165_;
v___jp_2165_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = l_Lean_PersistentArray_set___redArg(v_decls_2157_, v___y_2166_, v___x_2167_);
lean_dec(v___y_2166_);
v___x_2169_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2168_);
v___x_2170_ = l_Lean_LocalDecl_isAuxDecl(v_val_2163_);
lean_dec(v_val_2163_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2172_; 
lean_dec(v_fvarId_2155_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2169_);
lean_ctor_set(v___x_2161_, 0, v___x_2164_);
v___x_2172_ = v___x_2161_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_auxDeclToFullName_2158_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2174_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2155_, v_auxDeclToFullName_2158_);
lean_dec(v_fvarId_2155_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 2, v___x_2174_);
lean_ctor_set(v___x_2161_, 1, v___x_2169_);
lean_ctor_set(v___x_2161_, 0, v___x_2164_);
v___x_2176_ = v___x_2161_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2183_, lean_object* v_x_2184_, lean_object* v_x_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2184_, v_x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2187_, v_x_2188_, v_x_2189_);
lean_dec(v_x_2189_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2191_, lean_object* v_k_2192_, lean_object* v_t_2193_, lean_object* v_h_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2192_, v_t_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2196_, lean_object* v_k_2197_, lean_object* v_t_2198_, lean_object* v_h_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2196_, v_k_2197_, v_t_2198_, v_h_2199_);
lean_dec(v_k_2197_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2201_, lean_object* v_x_2202_, size_t v_x_2203_, lean_object* v_x_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2202_, v_x_2203_, v_x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
size_t v_x_2919__boxed_2210_; lean_object* v_res_2211_; 
v_x_2919__boxed_2210_ = lean_unbox_usize(v_x_2208_);
lean_dec(v_x_2208_);
v_res_2211_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2206_, v_x_2207_, v_x_2919__boxed_2210_, v_x_2209_);
lean_dec(v_x_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2212_){
_start:
{
lean_object* v_decls_2213_; lean_object* v_fvarIdToDecl_2214_; lean_object* v_auxDeclToFullName_2215_; lean_object* v_size_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v_decls_2213_ = lean_ctor_get(v_lctx_2212_, 1);
v_fvarIdToDecl_2214_ = lean_ctor_get(v_lctx_2212_, 0);
v_auxDeclToFullName_2215_ = lean_ctor_get(v_lctx_2212_, 2);
v_size_2216_ = lean_ctor_get(v_decls_2213_, 2);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_nat_dec_eq(v_size_2216_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_unsigned_to_nat(1u);
v___x_2221_ = lean_nat_sub(v_size_2216_, v___x_2220_);
v___x_2222_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2219_, v_decls_2213_, v___x_2221_);
lean_dec(v___x_2221_);
if (lean_obj_tag(v___x_2222_) == 0)
{
return v_lctx_2212_;
}
else
{
lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2241_; 
lean_inc(v_auxDeclToFullName_2215_);
lean_inc_ref(v_fvarIdToDecl_2214_);
lean_inc_ref(v_decls_2213_);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_lctx_2212_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; lean_object* v_unused_2243_; lean_object* v_unused_2244_; 
v_unused_2242_ = lean_ctor_get(v_lctx_2212_, 2);
lean_dec(v_unused_2242_);
v_unused_2243_ = lean_ctor_get(v_lctx_2212_, 1);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v_lctx_2212_, 0);
lean_dec(v_unused_2244_);
v___x_2224_ = v_lctx_2212_;
v_isShared_2225_ = v_isSharedCheck_2241_;
goto v_resetjp_2223_;
}
else
{
lean_dec(v_lctx_2212_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2241_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v_val_2226_; lean_object* v___y_2228_; lean_object* v_fvarId_2240_; 
v_val_2226_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_val_2226_);
lean_dec_ref(v___x_2222_);
v_fvarId_2240_ = lean_ctor_get(v_val_2226_, 1);
lean_inc(v_fvarId_2240_);
v___y_2228_ = v_fvarId_2240_;
goto v___jp_2227_;
v___jp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2229_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2214_, v___y_2228_);
v___x_2230_ = l_Lean_PersistentArray_pop___redArg(v_decls_2213_);
v___x_2231_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2230_);
v___x_2232_ = l_Lean_LocalDecl_isAuxDecl(v_val_2226_);
lean_dec(v_val_2226_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2234_; 
lean_dec(v___y_2228_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 1, v___x_2231_);
lean_ctor_set(v___x_2224_, 0, v___x_2229_);
v___x_2234_ = v___x_2224_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_auxDeclToFullName_2215_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2228_, v_auxDeclToFullName_2215_);
lean_dec(v___y_2228_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 2, v___x_2236_);
lean_ctor_set(v___x_2224_, 1, v___x_2231_);
lean_ctor_set(v___x_2224_, 0, v___x_2229_);
v___x_2238_ = v___x_2224_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
}
else
{
return v_lctx_2212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2245_, lean_object* v_as_2246_, lean_object* v_i_2247_){
_start:
{
lean_object* v_zero_2248_; uint8_t v_isZero_2249_; 
v_zero_2248_ = lean_unsigned_to_nat(0u);
v_isZero_2249_ = lean_nat_dec_eq(v_i_2247_, v_zero_2248_);
if (v_isZero_2249_ == 1)
{
lean_object* v___x_2250_; 
lean_dec(v_i_2247_);
v___x_2250_ = lean_box(0);
return v___x_2250_;
}
else
{
lean_object* v_one_2251_; lean_object* v_n_2252_; lean_object* v___y_2254_; lean_object* v___x_2256_; lean_object* v___y_2258_; 
v_one_2251_ = lean_unsigned_to_nat(1u);
v_n_2252_ = lean_nat_sub(v_i_2247_, v_one_2251_);
lean_dec(v_i_2247_);
v___x_2256_ = lean_array_fget_borrowed(v_as_2246_, v_n_2252_);
if (lean_obj_tag(v___x_2256_) == 0)
{
v___y_2254_ = v___x_2256_;
goto v___jp_2253_;
}
else
{
lean_object* v_val_2261_; lean_object* v_userName_2262_; 
v_val_2261_ = lean_ctor_get(v___x_2256_, 0);
v_userName_2262_ = lean_ctor_get(v_val_2261_, 2);
v___y_2258_ = v_userName_2262_;
goto v___jp_2257_;
}
v___jp_2253_:
{
if (lean_obj_tag(v___y_2254_) == 0)
{
v_i_2247_ = v_n_2252_;
goto _start;
}
else
{
lean_dec(v_n_2252_);
lean_inc_ref(v___y_2254_);
return v___y_2254_;
}
}
v___jp_2257_:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_name_eq(v___y_2258_, v_userName_2245_);
if (v___x_2259_ == 0)
{
v_i_2247_ = v_n_2252_;
goto _start;
}
else
{
v___y_2254_ = v___x_2256_;
goto v___jp_2253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2263_, lean_object* v_as_2264_, lean_object* v_i_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2263_, v_as_2264_, v_i_2265_);
lean_dec_ref(v_as_2264_);
lean_dec(v_userName_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2267_, lean_object* v_as_2268_, lean_object* v_i_2269_){
_start:
{
lean_object* v_zero_2270_; uint8_t v_isZero_2271_; 
v_zero_2270_ = lean_unsigned_to_nat(0u);
v_isZero_2271_ = lean_nat_dec_eq(v_i_2269_, v_zero_2270_);
if (v_isZero_2271_ == 1)
{
lean_object* v___x_2272_; 
lean_dec(v_i_2269_);
v___x_2272_ = lean_box(0);
return v___x_2272_;
}
else
{
lean_object* v_one_2273_; lean_object* v_n_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_one_2273_ = lean_unsigned_to_nat(1u);
v_n_2274_ = lean_nat_sub(v_i_2269_, v_one_2273_);
lean_dec(v_i_2269_);
v___x_2275_ = lean_array_fget_borrowed(v_as_2268_, v_n_2274_);
v___x_2276_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2267_, v___x_2275_);
if (lean_obj_tag(v___x_2276_) == 0)
{
v_i_2269_ = v_n_2274_;
goto _start;
}
else
{
lean_dec(v_n_2274_);
return v___x_2276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2278_, lean_object* v_x_2279_){
_start:
{
if (lean_obj_tag(v_x_2279_) == 0)
{
lean_object* v_cs_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_cs_2280_ = lean_ctor_get(v_x_2279_, 0);
v___x_2281_ = lean_array_get_size(v_cs_2280_);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2278_, v_cs_2280_, v___x_2281_);
return v___x_2282_;
}
else
{
lean_object* v_vs_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_vs_2283_ = lean_ctor_get(v_x_2279_, 0);
v___x_2284_ = lean_array_get_size(v_vs_2283_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2278_, v_vs_2283_, v___x_2284_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2286_, lean_object* v_x_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2286_, v_x_2287_);
lean_dec_ref(v_x_2287_);
lean_dec(v_userName_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2289_, lean_object* v_as_2290_, lean_object* v_i_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2289_, v_as_2290_, v_i_2291_);
lean_dec_ref(v_as_2290_);
lean_dec(v_userName_2289_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2293_, lean_object* v_t_2294_){
_start:
{
lean_object* v_root_2295_; lean_object* v_tail_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_root_2295_ = lean_ctor_get(v_t_2294_, 0);
v_tail_2296_ = lean_ctor_get(v_t_2294_, 1);
v___x_2297_ = lean_array_get_size(v_tail_2296_);
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2293_, v_tail_2296_, v___x_2297_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2293_, v_root_2295_);
return v___x_2299_;
}
else
{
return v___x_2298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2300_, lean_object* v_t_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2300_, v_t_2301_);
lean_dec_ref(v_t_2301_);
lean_dec(v_userName_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2303_, lean_object* v_userName_2304_){
_start:
{
lean_object* v_decls_2305_; lean_object* v___x_2306_; 
v_decls_2305_ = lean_ctor_get(v_lctx_2303_, 1);
v___x_2306_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2304_, v_decls_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2307_, lean_object* v_userName_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2307_, v_userName_2308_);
lean_dec(v_userName_2308_);
lean_dec_ref(v_lctx_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2310_, lean_object* v_as_2311_, lean_object* v_i_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2310_, v_as_2311_, v_i_2312_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2315_, lean_object* v_as_2316_, lean_object* v_i_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2315_, v_as_2316_, v_i_2317_, v_a_2318_);
lean_dec_ref(v_as_2316_);
lean_dec(v_userName_2315_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2320_, lean_object* v_as_2321_, lean_object* v_i_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2320_, v_as_2321_, v_i_2322_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2325_, lean_object* v_as_2326_, lean_object* v_i_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2325_, v_as_2326_, v_i_2327_, v_a_2328_);
lean_dec_ref(v_as_2326_);
lean_dec(v_userName_2325_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2333_, lean_object* v_userName_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2333_, v_userName_2334_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2336_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2337_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2338_ = lean_unsigned_to_nat(403u);
v___x_2339_ = lean_unsigned_to_nat(17u);
v___x_2340_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2341_ = 1;
v___x_2342_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2334_, v___x_2341_);
v___x_2343_ = lean_string_append(v___x_2340_, v___x_2342_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2345_ = lean_string_append(v___x_2343_, v___x_2344_);
v___x_2346_ = l_mkPanicMessageWithDecl(v___x_2336_, v___x_2337_, v___x_2338_, v___x_2339_, v___x_2345_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2346_);
return v___x_2347_;
}
else
{
lean_object* v_val_2348_; 
lean_dec(v_userName_2334_);
v_val_2348_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_val_2348_);
lean_dec_ref(v___x_2335_);
return v_val_2348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2349_, lean_object* v_userName_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2349_, v_userName_2350_);
lean_dec_ref(v_lctx_2349_);
return v_res_2351_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2352_, lean_object* v_userName_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2352_, v_userName_2353_);
if (lean_obj_tag(v___x_2354_) == 0)
{
uint8_t v___x_2355_; 
v___x_2355_ = 0;
return v___x_2355_;
}
else
{
uint8_t v___x_2356_; 
lean_dec_ref(v___x_2354_);
v___x_2356_ = 1;
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2357_, lean_object* v_userName_2358_){
_start:
{
uint8_t v_res_2359_; lean_object* v_r_2360_; 
v_res_2359_ = l_Lean_LocalContext_usesUserName(v_lctx_2357_, v_userName_2358_);
lean_dec(v_userName_2358_);
lean_dec_ref(v_lctx_2357_);
v_r_2360_ = lean_box(v_res_2359_);
return v_r_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2361_, lean_object* v_suggestion_2362_, lean_object* v_i_2363_){
_start:
{
lean_object* v_curr_2364_; uint8_t v___x_2365_; 
lean_inc(v_i_2363_);
lean_inc(v_suggestion_2362_);
v_curr_2364_ = lean_name_append_index_after(v_suggestion_2362_, v_i_2363_);
v___x_2365_ = l_Lean_LocalContext_usesUserName(v_lctx_2361_, v_curr_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_dec(v_suggestion_2362_);
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_nat_add(v_i_2363_, v___x_2366_);
lean_dec(v_i_2363_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_curr_2364_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
return v___x_2368_;
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_dec(v_curr_2364_);
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_i_2363_, v___x_2369_);
lean_dec(v_i_2363_);
v_i_2363_ = v___x_2370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2372_, lean_object* v_suggestion_2373_, lean_object* v_i_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2372_, v_suggestion_2373_, v_i_2374_);
lean_dec_ref(v_lctx_2372_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2376_, lean_object* v_suggestion_2377_){
_start:
{
lean_object* v_suggestion_2378_; uint8_t v___x_2379_; 
v_suggestion_2378_ = lean_erase_macro_scopes(v_suggestion_2377_);
v___x_2379_ = l_Lean_LocalContext_usesUserName(v_lctx_2376_, v_suggestion_2378_);
if (v___x_2379_ == 0)
{
return v_suggestion_2378_;
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_fst_2382_; 
v___x_2380_ = lean_unsigned_to_nat(1u);
v___x_2381_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2376_, v_suggestion_2378_, v___x_2380_);
v_fst_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_fst_2382_);
lean_dec_ref(v___x_2381_);
return v_fst_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2383_, lean_object* v_suggestion_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_LocalContext_getUnusedName(v_lctx_2383_, v_suggestion_2384_);
lean_dec_ref(v_lctx_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2386_){
_start:
{
lean_object* v_decls_2387_; lean_object* v_size_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_decls_2387_ = lean_ctor_get(v_lctx_2386_, 1);
v_size_2388_ = lean_ctor_get(v_decls_2387_, 2);
v___x_2389_ = lean_box(0);
v___x_2390_ = lean_unsigned_to_nat(1u);
v___x_2391_ = lean_nat_sub(v_size_2388_, v___x_2390_);
v___x_2392_ = lean_nat_dec_lt(v___x_2391_, v_size_2388_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec(v___x_2391_);
v___x_2393_ = l_outOfBounds___redArg(v___x_2389_);
return v___x_2393_;
}
else
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2389_, v_decls_2387_, v___x_2391_);
lean_dec(v___x_2391_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_LocalContext_lastDecl(v_lctx_2395_);
lean_dec_ref(v_lctx_2395_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2397_, lean_object* v_fvarId_2398_, lean_object* v_userName_2399_){
_start:
{
lean_object* v_fvarIdToDecl_2400_; lean_object* v_decls_2401_; lean_object* v_auxDeclToFullName_2402_; lean_object* v_decl_2403_; lean_object* v_decl_2404_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2412_; lean_object* v_fvarId_2415_; 
v_fvarIdToDecl_2400_ = lean_ctor_get(v_lctx_2397_, 0);
lean_inc_ref(v_fvarIdToDecl_2400_);
v_decls_2401_ = lean_ctor_get(v_lctx_2397_, 1);
lean_inc_ref(v_decls_2401_);
v_auxDeclToFullName_2402_ = lean_ctor_get(v_lctx_2397_, 2);
lean_inc(v_auxDeclToFullName_2402_);
v_decl_2403_ = l_Lean_LocalContext_get_x21(v_lctx_2397_, v_fvarId_2398_);
v_decl_2404_ = l_Lean_LocalDecl_setUserName(v_decl_2403_, v_userName_2399_);
v_fvarId_2415_ = lean_ctor_get(v_decl_2404_, 1);
lean_inc(v_fvarId_2415_);
v___y_2412_ = v_fvarId_2415_;
goto v___jp_2411_;
v___jp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_decl_2404_);
v___x_2409_ = l_Lean_PersistentArray_set___redArg(v_decls_2401_, v___y_2407_, v___x_2408_);
lean_dec(v___y_2407_);
v___x_2410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2410_, 0, v___y_2406_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
lean_ctor_set(v___x_2410_, 2, v_auxDeclToFullName_2402_);
return v___x_2410_;
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v_index_2414_; 
lean_inc_ref(v_decl_2404_);
v___x_2413_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2400_, v___y_2412_, v_decl_2404_);
v_index_2414_ = lean_ctor_get(v_decl_2404_, 0);
lean_inc(v_index_2414_);
v___y_2406_ = v___x_2413_;
v___y_2407_ = v_index_2414_;
goto v___jp_2405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2416_, lean_object* v_fromName_2417_, lean_object* v_toName_2418_){
_start:
{
lean_object* v_fvarIdToDecl_2419_; lean_object* v_decls_2420_; lean_object* v_auxDeclToFullName_2421_; lean_object* v___x_2422_; 
v_fvarIdToDecl_2419_ = lean_ctor_get(v_lctx_2416_, 0);
v_decls_2420_ = lean_ctor_get(v_lctx_2416_, 1);
v_auxDeclToFullName_2421_ = lean_ctor_get(v_lctx_2416_, 2);
v___x_2422_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2416_, v_fromName_2417_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_dec(v_toName_2418_);
return v_lctx_2416_;
}
else
{
lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2447_; 
lean_inc(v_auxDeclToFullName_2421_);
lean_inc_ref(v_decls_2420_);
lean_inc_ref(v_fvarIdToDecl_2419_);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_lctx_2416_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; lean_object* v_unused_2449_; lean_object* v_unused_2450_; 
v_unused_2448_ = lean_ctor_get(v_lctx_2416_, 2);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v_lctx_2416_, 1);
lean_dec(v_unused_2449_);
v_unused_2450_ = lean_ctor_get(v_lctx_2416_, 0);
lean_dec(v_unused_2450_);
v___x_2424_ = v_lctx_2416_;
v_isShared_2425_ = v_isSharedCheck_2447_;
goto v_resetjp_2423_;
}
else
{
lean_dec(v_lctx_2416_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2447_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v_val_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2446_; 
v_val_2426_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2428_ = v___x_2422_;
v_isShared_2429_ = v_isSharedCheck_2446_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_val_2426_);
lean_dec(v___x_2422_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2446_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v_decl_2430_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2442_; lean_object* v_fvarId_2445_; 
v_decl_2430_ = l_Lean_LocalDecl_setUserName(v_val_2426_, v_toName_2418_);
v_fvarId_2445_ = lean_ctor_get(v_decl_2430_, 1);
lean_inc(v_fvarId_2445_);
v___y_2442_ = v_fvarId_2445_;
goto v___jp_2441_;
v___jp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v_decl_2430_);
v___x_2435_ = v___x_2428_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_decl_2430_);
v___x_2435_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = l_Lean_PersistentArray_set___redArg(v_decls_2420_, v___y_2433_, v___x_2435_);
lean_dec(v___y_2433_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2436_);
lean_ctor_set(v___x_2424_, 0, v___y_2432_);
v___x_2438_ = v___x_2424_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___y_2432_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v_auxDeclToFullName_2421_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
v___jp_2441_:
{
lean_object* v___x_2443_; lean_object* v_index_2444_; 
lean_inc_ref(v_decl_2430_);
v___x_2443_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2419_, v___y_2442_, v_decl_2430_);
v_index_2444_ = lean_ctor_get(v_decl_2430_, 0);
lean_inc(v_index_2444_);
v___y_2432_ = v___x_2443_;
v___y_2433_ = v_index_2444_;
goto v___jp_2431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2451_, lean_object* v_fromName_2452_, lean_object* v_toName_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_LocalContext_renameUserName(v_lctx_2451_, v_fromName_2452_, v_toName_2453_);
lean_dec(v_fromName_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2457_, lean_object* v_fvarId_2458_, lean_object* v_f_2459_){
_start:
{
lean_object* v_fvarIdToDecl_2460_; lean_object* v_decls_2461_; lean_object* v_auxDeclToFullName_2462_; lean_object* v___x_2463_; 
v_fvarIdToDecl_2460_ = lean_ctor_get(v_lctx_2457_, 0);
v_decls_2461_ = lean_ctor_get(v_lctx_2457_, 1);
v_auxDeclToFullName_2462_ = lean_ctor_get(v_lctx_2457_, 2);
lean_inc_ref(v_lctx_2457_);
v___x_2463_ = lean_local_ctx_find(v_lctx_2457_, v_fvarId_2458_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_dec_ref(v_f_2459_);
return v_lctx_2457_;
}
else
{
lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2490_; 
lean_inc(v_auxDeclToFullName_2462_);
lean_inc_ref(v_decls_2461_);
lean_inc_ref(v_fvarIdToDecl_2460_);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_lctx_2457_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; 
v_unused_2491_ = lean_ctor_get(v_lctx_2457_, 2);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_lctx_2457_, 1);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_lctx_2457_, 0);
lean_dec(v_unused_2493_);
v___x_2465_ = v_lctx_2457_;
v_isShared_2466_ = v_isSharedCheck_2490_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v_lctx_2457_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2490_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v_val_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2489_; 
v_val_2467_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2469_ = v___x_2463_;
v_isShared_2470_ = v_isSharedCheck_2489_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_val_2467_);
lean_dec(v___x_2463_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2489_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_decl_2473_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2485_; lean_object* v_fvarId_2488_; 
v___x_2471_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2472_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2473_ = lean_apply_1(v_f_2459_, v_val_2467_);
v_fvarId_2488_ = lean_ctor_get(v_decl_2473_, 1);
lean_inc(v_fvarId_2488_);
v___y_2485_ = v_fvarId_2488_;
goto v___jp_2484_;
v___jp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v_decl_2473_);
v___x_2478_ = v___x_2469_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_decl_2473_);
v___x_2478_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = l_Lean_PersistentArray_set___redArg(v_decls_2461_, v___y_2476_, v___x_2478_);
lean_dec(v___y_2476_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v___x_2479_);
lean_ctor_set(v___x_2465_, 0, v___y_2475_);
v___x_2481_ = v___x_2465_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___y_2475_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___x_2479_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_auxDeclToFullName_2462_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
v___jp_2484_:
{
lean_object* v___x_2486_; lean_object* v_index_2487_; 
lean_inc_ref(v_decl_2473_);
v___x_2486_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2471_, v___x_2472_, v_fvarIdToDecl_2460_, v___y_2485_, v_decl_2473_);
v_index_2487_ = lean_ctor_get(v_decl_2473_, 0);
lean_inc(v_index_2487_);
v___y_2475_ = v___x_2486_;
v___y_2476_ = v_index_2487_;
goto v___jp_2474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2494_, lean_object* v_as_2495_, size_t v_i_2496_, size_t v_stop_2497_, lean_object* v_b_2498_){
_start:
{
lean_object* v___y_2500_; uint8_t v___x_2504_; 
v___x_2504_ = lean_usize_dec_eq(v_i_2496_, v_stop_2497_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_array_uget(v_as_2495_, v_i_2496_);
if (lean_obj_tag(v___x_2505_) == 0)
{
v___y_2500_ = v_b_2498_;
goto v___jp_2499_;
}
else
{
lean_object* v_val_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2533_; 
v_val_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2533_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_val_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2533_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v_fvarIdToDecl_2510_; lean_object* v_decls_2511_; lean_object* v_auxDeclToFullName_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2532_; 
v_fvarIdToDecl_2510_ = lean_ctor_get(v_b_2498_, 0);
v_decls_2511_ = lean_ctor_get(v_b_2498_, 1);
v_auxDeclToFullName_2512_ = lean_ctor_get(v_b_2498_, 2);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_b_2498_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2514_ = v_b_2498_;
v_isShared_2515_ = v_isSharedCheck_2532_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_auxDeclToFullName_2512_);
lean_inc(v_decls_2511_);
lean_inc(v_fvarIdToDecl_2510_);
lean_dec(v_b_2498_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2532_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v_decl_2516_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2528_; lean_object* v_fvarId_2531_; 
lean_inc_ref(v_f_2494_);
v_decl_2516_ = lean_apply_1(v_f_2494_, v_val_2506_);
v_fvarId_2531_ = lean_ctor_get(v_decl_2516_, 1);
lean_inc(v_fvarId_2531_);
v___y_2528_ = v_fvarId_2531_;
goto v___jp_2527_;
v___jp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v_decl_2516_);
v___x_2521_ = v___x_2508_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_decl_2516_);
v___x_2521_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = l_Lean_PersistentArray_set___redArg(v_decls_2511_, v___y_2519_, v___x_2521_);
lean_dec(v___y_2519_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 1, v___x_2522_);
lean_ctor_set(v___x_2514_, 0, v___y_2518_);
v___x_2524_ = v___x_2514_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___y_2518_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_auxDeclToFullName_2512_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
v___y_2500_ = v___x_2524_;
goto v___jp_2499_;
}
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v_index_2530_; 
lean_inc_ref(v_decl_2516_);
v___x_2529_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2510_, v___y_2528_, v_decl_2516_);
v_index_2530_ = lean_ctor_get(v_decl_2516_, 0);
lean_inc(v_index_2530_);
v___y_2518_ = v___x_2529_;
v___y_2519_ = v_index_2530_;
goto v___jp_2517_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2494_);
return v_b_2498_;
}
v___jp_2499_:
{
size_t v___x_2501_; size_t v___x_2502_; 
v___x_2501_ = ((size_t)1ULL);
v___x_2502_ = lean_usize_add(v_i_2496_, v___x_2501_);
v_i_2496_ = v___x_2502_;
v_b_2498_ = v___y_2500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2534_, lean_object* v_as_2535_, lean_object* v_i_2536_, lean_object* v_stop_2537_, lean_object* v_b_2538_){
_start:
{
size_t v_i_boxed_2539_; size_t v_stop_boxed_2540_; lean_object* v_res_2541_; 
v_i_boxed_2539_ = lean_unbox_usize(v_i_2536_);
lean_dec(v_i_2536_);
v_stop_boxed_2540_ = lean_unbox_usize(v_stop_2537_);
lean_dec(v_stop_2537_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2534_, v_as_2535_, v_i_boxed_2539_, v_stop_boxed_2540_, v_b_2538_);
lean_dec_ref(v_as_2535_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2542_, lean_object* v_x_2543_, lean_object* v_x_2544_){
_start:
{
if (lean_obj_tag(v_x_2543_) == 0)
{
lean_object* v_cs_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_cs_2545_ = lean_ctor_get(v_x_2543_, 0);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_array_get_size(v_cs_2545_);
v___x_2548_ = lean_nat_dec_lt(v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_dec_ref(v_f_2542_);
return v_x_2544_;
}
else
{
uint8_t v___x_2549_; 
v___x_2549_ = lean_nat_dec_le(v___x_2547_, v___x_2547_);
if (v___x_2549_ == 0)
{
if (v___x_2548_ == 0)
{
lean_dec_ref(v_f_2542_);
return v_x_2544_;
}
else
{
size_t v___x_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = lean_usize_of_nat(v___x_2547_);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2542_, v_cs_2545_, v___x_2550_, v___x_2551_, v_x_2544_);
return v___x_2552_;
}
}
else
{
size_t v___x_2553_; size_t v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = ((size_t)0ULL);
v___x_2554_ = lean_usize_of_nat(v___x_2547_);
v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2542_, v_cs_2545_, v___x_2553_, v___x_2554_, v_x_2544_);
return v___x_2555_;
}
}
}
else
{
lean_object* v_vs_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v_vs_2556_ = lean_ctor_get(v_x_2543_, 0);
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = lean_array_get_size(v_vs_2556_);
v___x_2559_ = lean_nat_dec_lt(v___x_2557_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_dec_ref(v_f_2542_);
return v_x_2544_;
}
else
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_nat_dec_le(v___x_2558_, v___x_2558_);
if (v___x_2560_ == 0)
{
if (v___x_2559_ == 0)
{
lean_dec_ref(v_f_2542_);
return v_x_2544_;
}
else
{
size_t v___x_2561_; size_t v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = ((size_t)0ULL);
v___x_2562_ = lean_usize_of_nat(v___x_2558_);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2542_, v_vs_2556_, v___x_2561_, v___x_2562_, v_x_2544_);
return v___x_2563_;
}
}
else
{
size_t v___x_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = ((size_t)0ULL);
v___x_2565_ = lean_usize_of_nat(v___x_2558_);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2542_, v_vs_2556_, v___x_2564_, v___x_2565_, v_x_2544_);
return v___x_2566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2567_, lean_object* v_as_2568_, size_t v_i_2569_, size_t v_stop_2570_, lean_object* v_b_2571_){
_start:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_usize_dec_eq(v_i_2569_, v_stop_2570_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; size_t v___x_2575_; size_t v___x_2576_; 
v___x_2573_ = lean_array_uget_borrowed(v_as_2568_, v_i_2569_);
lean_inc_ref(v_f_2567_);
v___x_2574_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2567_, v___x_2573_, v_b_2571_);
v___x_2575_ = ((size_t)1ULL);
v___x_2576_ = lean_usize_add(v_i_2569_, v___x_2575_);
v_i_2569_ = v___x_2576_;
v_b_2571_ = v___x_2574_;
goto _start;
}
else
{
lean_dec_ref(v_f_2567_);
return v_b_2571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2578_, lean_object* v_as_2579_, lean_object* v_i_2580_, lean_object* v_stop_2581_, lean_object* v_b_2582_){
_start:
{
size_t v_i_boxed_2583_; size_t v_stop_boxed_2584_; lean_object* v_res_2585_; 
v_i_boxed_2583_ = lean_unbox_usize(v_i_2580_);
lean_dec(v_i_2580_);
v_stop_boxed_2584_ = lean_unbox_usize(v_stop_2581_);
lean_dec(v_stop_2581_);
v_res_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2578_, v_as_2579_, v_i_boxed_2583_, v_stop_boxed_2584_, v_b_2582_);
lean_dec_ref(v_as_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2586_, lean_object* v_x_2587_, lean_object* v_x_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2586_, v_x_2587_, v_x_2588_);
lean_dec_ref(v_x_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2590_, lean_object* v_x_2591_, size_t v_x_2592_, size_t v_x_2593_, lean_object* v_x_2594_){
_start:
{
if (lean_obj_tag(v_x_2591_) == 0)
{
lean_object* v_cs_2595_; lean_object* v___x_2596_; size_t v___x_2597_; lean_object* v_j_2598_; lean_object* v___x_2599_; size_t v___x_2600_; size_t v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v_cs_2595_ = lean_ctor_get(v_x_2591_, 0);
v___x_2596_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2597_ = lean_usize_shift_right(v_x_2592_, v_x_2593_);
v_j_2598_ = lean_usize_to_nat(v___x_2597_);
v___x_2599_ = lean_array_get_borrowed(v___x_2596_, v_cs_2595_, v_j_2598_);
v___x_2600_ = ((size_t)1ULL);
v___x_2601_ = lean_usize_shift_left(v___x_2600_, v_x_2593_);
v___x_2602_ = lean_usize_sub(v___x_2601_, v___x_2600_);
v___x_2603_ = lean_usize_land(v_x_2592_, v___x_2602_);
v___x_2604_ = ((size_t)5ULL);
v___x_2605_ = lean_usize_sub(v_x_2593_, v___x_2604_);
lean_inc_ref(v_f_2590_);
v___x_2606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2590_, v___x_2599_, v___x_2603_, v___x_2605_, v_x_2594_);
v___x_2607_ = lean_unsigned_to_nat(1u);
v___x_2608_ = lean_nat_add(v_j_2598_, v___x_2607_);
lean_dec(v_j_2598_);
v___x_2609_ = lean_array_get_size(v_cs_2595_);
v___x_2610_ = lean_nat_dec_lt(v___x_2608_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_dec(v___x_2608_);
lean_dec_ref(v_f_2590_);
return v___x_2606_;
}
else
{
uint8_t v___x_2611_; 
v___x_2611_ = lean_nat_dec_le(v___x_2609_, v___x_2609_);
if (v___x_2611_ == 0)
{
if (v___x_2610_ == 0)
{
lean_dec(v___x_2608_);
lean_dec_ref(v_f_2590_);
return v___x_2606_;
}
else
{
size_t v___x_2612_; size_t v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_usize_of_nat(v___x_2608_);
lean_dec(v___x_2608_);
v___x_2613_ = lean_usize_of_nat(v___x_2609_);
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2590_, v_cs_2595_, v___x_2612_, v___x_2613_, v___x_2606_);
return v___x_2614_;
}
}
else
{
size_t v___x_2615_; size_t v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_usize_of_nat(v___x_2608_);
lean_dec(v___x_2608_);
v___x_2616_ = lean_usize_of_nat(v___x_2609_);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2590_, v_cs_2595_, v___x_2615_, v___x_2616_, v___x_2606_);
return v___x_2617_;
}
}
}
else
{
lean_object* v_vs_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_vs_2618_ = lean_ctor_get(v_x_2591_, 0);
v___x_2619_ = lean_usize_to_nat(v_x_2592_);
v___x_2620_ = lean_array_get_size(v_vs_2618_);
v___x_2621_ = lean_nat_dec_lt(v___x_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_dec(v___x_2619_);
lean_dec_ref(v_f_2590_);
return v_x_2594_;
}
else
{
uint8_t v___x_2622_; 
v___x_2622_ = lean_nat_dec_le(v___x_2620_, v___x_2620_);
if (v___x_2622_ == 0)
{
if (v___x_2621_ == 0)
{
lean_dec(v___x_2619_);
lean_dec_ref(v_f_2590_);
return v_x_2594_;
}
else
{
size_t v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_usize_of_nat(v___x_2619_);
lean_dec(v___x_2619_);
v___x_2624_ = lean_usize_of_nat(v___x_2620_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2590_, v_vs_2618_, v___x_2623_, v___x_2624_, v_x_2594_);
return v___x_2625_;
}
}
else
{
size_t v___x_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_usize_of_nat(v___x_2619_);
lean_dec(v___x_2619_);
v___x_2627_ = lean_usize_of_nat(v___x_2620_);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2590_, v_vs_2618_, v___x_2626_, v___x_2627_, v_x_2594_);
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_, lean_object* v_x_2633_){
_start:
{
size_t v_x_1859__boxed_2634_; size_t v_x_1860__boxed_2635_; lean_object* v_res_2636_; 
v_x_1859__boxed_2634_ = lean_unbox_usize(v_x_2631_);
lean_dec(v_x_2631_);
v_x_1860__boxed_2635_ = lean_unbox_usize(v_x_2632_);
lean_dec(v_x_2632_);
v_res_2636_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2629_, v_x_2630_, v_x_1859__boxed_2634_, v_x_1860__boxed_2635_, v_x_2633_);
lean_dec_ref(v_x_2630_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2637_, lean_object* v_t_2638_, lean_object* v_init_2639_, lean_object* v_start_2640_){
_start:
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = lean_nat_dec_eq(v_start_2640_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v_root_2643_; lean_object* v_tail_2644_; size_t v_shift_2645_; lean_object* v_tailOff_2646_; uint8_t v___x_2647_; 
v_root_2643_ = lean_ctor_get(v_t_2638_, 0);
v_tail_2644_ = lean_ctor_get(v_t_2638_, 1);
v_shift_2645_ = lean_ctor_get_usize(v_t_2638_, 4);
v_tailOff_2646_ = lean_ctor_get(v_t_2638_, 3);
v___x_2647_ = lean_nat_dec_le(v_tailOff_2646_, v_start_2640_);
if (v___x_2647_ == 0)
{
size_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2648_ = lean_usize_of_nat(v_start_2640_);
lean_inc_ref(v_f_2637_);
v___x_2649_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2637_, v_root_2643_, v___x_2648_, v_shift_2645_, v_init_2639_);
v___x_2650_ = lean_array_get_size(v_tail_2644_);
v___x_2651_ = lean_nat_dec_lt(v___x_2641_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_dec_ref(v_f_2637_);
return v___x_2649_;
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_nat_dec_le(v___x_2650_, v___x_2650_);
if (v___x_2652_ == 0)
{
if (v___x_2651_ == 0)
{
lean_dec_ref(v_f_2637_);
return v___x_2649_;
}
else
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_of_nat(v___x_2650_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2637_, v_tail_2644_, v___x_2653_, v___x_2654_, v___x_2649_);
return v___x_2655_;
}
}
else
{
size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2650_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2637_, v_tail_2644_, v___x_2656_, v___x_2657_, v___x_2649_);
return v___x_2658_;
}
}
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2659_ = lean_nat_sub(v_start_2640_, v_tailOff_2646_);
v___x_2660_ = lean_array_get_size(v_tail_2644_);
v___x_2661_ = lean_nat_dec_lt(v___x_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_dec(v___x_2659_);
lean_dec_ref(v_f_2637_);
return v_init_2639_;
}
else
{
uint8_t v___x_2662_; 
v___x_2662_ = lean_nat_dec_le(v___x_2660_, v___x_2660_);
if (v___x_2662_ == 0)
{
if (v___x_2661_ == 0)
{
lean_dec(v___x_2659_);
lean_dec_ref(v_f_2637_);
return v_init_2639_;
}
else
{
size_t v___x_2663_; size_t v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = lean_usize_of_nat(v___x_2659_);
lean_dec(v___x_2659_);
v___x_2664_ = lean_usize_of_nat(v___x_2660_);
v___x_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2637_, v_tail_2644_, v___x_2663_, v___x_2664_, v_init_2639_);
return v___x_2665_;
}
}
else
{
size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = lean_usize_of_nat(v___x_2659_);
lean_dec(v___x_2659_);
v___x_2667_ = lean_usize_of_nat(v___x_2660_);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2637_, v_tail_2644_, v___x_2666_, v___x_2667_, v_init_2639_);
return v___x_2668_;
}
}
}
}
else
{
lean_object* v_root_2669_; lean_object* v_tail_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v_root_2669_ = lean_ctor_get(v_t_2638_, 0);
v_tail_2670_ = lean_ctor_get(v_t_2638_, 1);
lean_inc_ref(v_f_2637_);
v___x_2671_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2637_, v_root_2669_, v_init_2639_);
v___x_2672_ = lean_array_get_size(v_tail_2670_);
v___x_2673_ = lean_nat_dec_lt(v___x_2641_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_dec_ref(v_f_2637_);
return v___x_2671_;
}
else
{
uint8_t v___x_2674_; 
v___x_2674_ = lean_nat_dec_le(v___x_2672_, v___x_2672_);
if (v___x_2674_ == 0)
{
if (v___x_2673_ == 0)
{
lean_dec_ref(v_f_2637_);
return v___x_2671_;
}
else
{
size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = ((size_t)0ULL);
v___x_2676_ = lean_usize_of_nat(v___x_2672_);
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2637_, v_tail_2670_, v___x_2675_, v___x_2676_, v___x_2671_);
return v___x_2677_;
}
}
else
{
size_t v___x_2678_; size_t v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = ((size_t)0ULL);
v___x_2679_ = lean_usize_of_nat(v___x_2672_);
v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2637_, v_tail_2670_, v___x_2678_, v___x_2679_, v___x_2671_);
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2681_, lean_object* v_t_2682_, lean_object* v_init_2683_, lean_object* v_start_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2681_, v_t_2682_, v_init_2683_, v_start_2684_);
lean_dec(v_start_2684_);
lean_dec_ref(v_t_2682_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2686_, lean_object* v_f_2687_){
_start:
{
lean_object* v_decls_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_decls_2688_ = lean_ctor_get(v_lctx_2686_, 1);
lean_inc_ref(v_decls_2688_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2687_, v_decls_2688_, v_lctx_2686_, v___x_2689_);
lean_dec_ref(v_decls_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2691_, lean_object* v_fvarId_2692_, uint8_t v_kind_2693_){
_start:
{
lean_object* v_fvarIdToDecl_2694_; lean_object* v_decls_2695_; lean_object* v_auxDeclToFullName_2696_; lean_object* v___x_2697_; 
v_fvarIdToDecl_2694_ = lean_ctor_get(v_lctx_2691_, 0);
v_decls_2695_ = lean_ctor_get(v_lctx_2691_, 1);
v_auxDeclToFullName_2696_ = lean_ctor_get(v_lctx_2691_, 2);
lean_inc_ref(v_lctx_2691_);
v___x_2697_ = lean_local_ctx_find(v_lctx_2691_, v_fvarId_2692_);
if (lean_obj_tag(v___x_2697_) == 0)
{
return v_lctx_2691_;
}
else
{
lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2722_; 
lean_inc(v_auxDeclToFullName_2696_);
lean_inc_ref(v_decls_2695_);
lean_inc_ref(v_fvarIdToDecl_2694_);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_lctx_2691_);
if (v_isSharedCheck_2722_ == 0)
{
lean_object* v_unused_2723_; lean_object* v_unused_2724_; lean_object* v_unused_2725_; 
v_unused_2723_ = lean_ctor_get(v_lctx_2691_, 2);
lean_dec(v_unused_2723_);
v_unused_2724_ = lean_ctor_get(v_lctx_2691_, 1);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_lctx_2691_, 0);
lean_dec(v_unused_2725_);
v___x_2699_ = v_lctx_2691_;
v_isShared_2700_ = v_isSharedCheck_2722_;
goto v_resetjp_2698_;
}
else
{
lean_dec(v_lctx_2691_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2722_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_val_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2721_; 
v_val_2701_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2703_ = v___x_2697_;
v_isShared_2704_ = v_isSharedCheck_2721_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_val_2701_);
lean_dec(v___x_2697_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2721_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v_decl_2705_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2717_; lean_object* v_fvarId_2720_; 
v_decl_2705_ = l_Lean_LocalDecl_setKind(v_val_2701_, v_kind_2693_);
v_fvarId_2720_ = lean_ctor_get(v_decl_2705_, 1);
lean_inc(v_fvarId_2720_);
v___y_2717_ = v_fvarId_2720_;
goto v___jp_2716_;
v___jp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v_decl_2705_);
v___x_2710_ = v___x_2703_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_decl_2705_);
v___x_2710_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2711_ = l_Lean_PersistentArray_set___redArg(v_decls_2695_, v___y_2708_, v___x_2710_);
lean_dec(v___y_2708_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2711_);
lean_ctor_set(v___x_2699_, 0, v___y_2707_);
v___x_2713_ = v___x_2699_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___y_2707_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v_auxDeclToFullName_2696_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v_index_2719_; 
lean_inc_ref(v_decl_2705_);
v___x_2718_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2694_, v___y_2717_, v_decl_2705_);
v_index_2719_ = lean_ctor_get(v_decl_2705_, 0);
lean_inc(v_index_2719_);
v___y_2707_ = v___x_2718_;
v___y_2708_ = v_index_2719_;
goto v___jp_2706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2726_, lean_object* v_fvarId_2727_, lean_object* v_kind_2728_){
_start:
{
uint8_t v_kind_boxed_2729_; lean_object* v_res_2730_; 
v_kind_boxed_2729_ = lean_unbox(v_kind_2728_);
v_res_2730_ = l_Lean_LocalContext_setKind(v_lctx_2726_, v_fvarId_2727_, v_kind_boxed_2729_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2731_, lean_object* v_fvarId_2732_, uint8_t v_bi_2733_){
_start:
{
lean_object* v_fvarIdToDecl_2734_; lean_object* v_decls_2735_; lean_object* v_auxDeclToFullName_2736_; lean_object* v___x_2737_; 
v_fvarIdToDecl_2734_ = lean_ctor_get(v_lctx_2731_, 0);
v_decls_2735_ = lean_ctor_get(v_lctx_2731_, 1);
v_auxDeclToFullName_2736_ = lean_ctor_get(v_lctx_2731_, 2);
lean_inc_ref(v_lctx_2731_);
v___x_2737_ = lean_local_ctx_find(v_lctx_2731_, v_fvarId_2732_);
if (lean_obj_tag(v___x_2737_) == 0)
{
return v_lctx_2731_;
}
else
{
lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2762_; 
lean_inc(v_auxDeclToFullName_2736_);
lean_inc_ref(v_decls_2735_);
lean_inc_ref(v_fvarIdToDecl_2734_);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_lctx_2731_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; lean_object* v_unused_2764_; lean_object* v_unused_2765_; 
v_unused_2763_ = lean_ctor_get(v_lctx_2731_, 2);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_lctx_2731_, 1);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v_lctx_2731_, 0);
lean_dec(v_unused_2765_);
v___x_2739_ = v_lctx_2731_;
v_isShared_2740_ = v_isSharedCheck_2762_;
goto v_resetjp_2738_;
}
else
{
lean_dec(v_lctx_2731_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2762_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v_val_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2761_; 
v_val_2741_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2743_ = v___x_2737_;
v_isShared_2744_ = v_isSharedCheck_2761_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_val_2741_);
lean_dec(v___x_2737_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2761_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_decl_2745_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2757_; lean_object* v_fvarId_2760_; 
v_decl_2745_ = l_Lean_LocalDecl_setBinderInfo(v_val_2741_, v_bi_2733_);
v_fvarId_2760_ = lean_ctor_get(v_decl_2745_, 1);
lean_inc(v_fvarId_2760_);
v___y_2757_ = v_fvarId_2760_;
goto v___jp_2756_;
v___jp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v_decl_2745_);
v___x_2750_ = v___x_2743_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_decl_2745_);
v___x_2750_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = l_Lean_PersistentArray_set___redArg(v_decls_2735_, v___y_2748_, v___x_2750_);
lean_dec(v___y_2748_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 1, v___x_2751_);
lean_ctor_set(v___x_2739_, 0, v___y_2747_);
v___x_2753_ = v___x_2739_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___y_2747_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_auxDeclToFullName_2736_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
v___jp_2756_:
{
lean_object* v___x_2758_; lean_object* v_index_2759_; 
lean_inc_ref(v_decl_2745_);
v___x_2758_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2734_, v___y_2757_, v_decl_2745_);
v_index_2759_ = lean_ctor_get(v_decl_2745_, 0);
lean_inc(v_index_2759_);
v___y_2747_ = v___x_2758_;
v___y_2748_ = v_index_2759_;
goto v___jp_2746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2766_, lean_object* v_fvarId_2767_, lean_object* v_bi_2768_){
_start:
{
uint8_t v_bi_boxed_2769_; lean_object* v_res_2770_; 
v_bi_boxed_2769_ = lean_unbox(v_bi_2768_);
v_res_2770_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2766_, v_fvarId_2767_, v_bi_boxed_2769_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2771_){
_start:
{
lean_object* v_decls_2772_; lean_object* v_size_2773_; 
v_decls_2772_ = lean_ctor_get(v_lctx_2771_, 1);
lean_inc_ref(v_decls_2772_);
lean_dec_ref(v_lctx_2771_);
v_size_2773_ = lean_ctor_get(v_decls_2772_, 2);
lean_inc(v_size_2773_);
lean_dec_ref(v_decls_2772_);
return v_size_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2774_, lean_object* v_i_2775_){
_start:
{
lean_object* v_decls_2776_; lean_object* v_size_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v_decls_2776_ = lean_ctor_get(v_lctx_2774_, 1);
v_size_2777_ = lean_ctor_get(v_decls_2776_, 2);
v___x_2778_ = lean_box(0);
v___x_2779_ = lean_nat_dec_lt(v_i_2775_, v_size_2777_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
v___x_2780_ = l_outOfBounds___redArg(v___x_2778_);
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2778_, v_decls_2776_, v_i_2775_);
return v___x_2781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2782_, lean_object* v_i_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2782_, v_i_2783_);
lean_dec(v_i_2783_);
lean_dec_ref(v_lctx_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2785_, lean_object* v_f_2786_, lean_object* v_b_2787_, lean_object* v_decl_2788_){
_start:
{
if (lean_obj_tag(v_decl_2788_) == 0)
{
lean_object* v___x_2789_; 
lean_dec(v_f_2786_);
v___x_2789_ = lean_apply_2(v_toPure_2785_, lean_box(0), v_b_2787_);
return v___x_2789_;
}
else
{
lean_object* v_val_2790_; lean_object* v___x_2791_; 
lean_dec(v_toPure_2785_);
v_val_2790_ = lean_ctor_get(v_decl_2788_, 0);
lean_inc(v_val_2790_);
lean_dec_ref(v_decl_2788_);
v___x_2791_ = lean_apply_2(v_f_2786_, v_b_2787_, v_val_2790_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2792_, lean_object* v_lctx_2793_, lean_object* v_f_2794_, lean_object* v_init_2795_, lean_object* v_start_2796_){
_start:
{
lean_object* v_toApplicative_2797_; lean_object* v_decls_2798_; lean_object* v_toPure_2799_; lean_object* v___f_2800_; lean_object* v___x_2801_; 
v_toApplicative_2797_ = lean_ctor_get(v_inst_2792_, 0);
v_decls_2798_ = lean_ctor_get(v_lctx_2793_, 1);
lean_inc_ref(v_decls_2798_);
lean_dec_ref(v_lctx_2793_);
v_toPure_2799_ = lean_ctor_get(v_toApplicative_2797_, 1);
lean_inc(v_toPure_2799_);
v___f_2800_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2800_, 0, v_toPure_2799_);
lean_closure_set(v___f_2800_, 1, v_f_2794_);
v___x_2801_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2792_, v_decls_2798_, v___f_2800_, v_init_2795_, v_start_2796_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2802_, lean_object* v_lctx_2803_, lean_object* v_f_2804_, lean_object* v_init_2805_, lean_object* v_start_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2802_, v_lctx_2803_, v_f_2804_, v_init_2805_, v_start_2806_);
lean_dec(v_start_2806_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2808_, lean_object* v_00_u03b2_2809_, lean_object* v_inst_2810_, lean_object* v_lctx_2811_, lean_object* v_f_2812_, lean_object* v_init_2813_, lean_object* v_start_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2810_, v_lctx_2811_, v_f_2812_, v_init_2813_, v_start_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2816_, lean_object* v_00_u03b2_2817_, lean_object* v_inst_2818_, lean_object* v_lctx_2819_, lean_object* v_f_2820_, lean_object* v_init_2821_, lean_object* v_start_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_LocalContext_foldlM(v_m_2816_, v_00_u03b2_2817_, v_inst_2818_, v_lctx_2819_, v_f_2820_, v_init_2821_, v_start_2822_);
lean_dec(v_start_2822_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2824_, lean_object* v_f_2825_, lean_object* v_decl_2826_, lean_object* v_b_2827_){
_start:
{
if (lean_obj_tag(v_decl_2826_) == 0)
{
lean_object* v___x_2828_; 
lean_dec(v_f_2825_);
v___x_2828_ = lean_apply_2(v_toPure_2824_, lean_box(0), v_b_2827_);
return v___x_2828_;
}
else
{
lean_object* v_val_2829_; lean_object* v___x_2830_; 
lean_dec(v_toPure_2824_);
v_val_2829_ = lean_ctor_get(v_decl_2826_, 0);
lean_inc(v_val_2829_);
lean_dec_ref(v_decl_2826_);
v___x_2830_ = lean_apply_2(v_f_2825_, v_val_2829_, v_b_2827_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2831_, lean_object* v_lctx_2832_, lean_object* v_f_2833_, lean_object* v_init_2834_){
_start:
{
lean_object* v_toApplicative_2835_; lean_object* v_decls_2836_; lean_object* v_toPure_2837_; lean_object* v___f_2838_; lean_object* v___x_2839_; 
v_toApplicative_2835_ = lean_ctor_get(v_inst_2831_, 0);
v_decls_2836_ = lean_ctor_get(v_lctx_2832_, 1);
lean_inc_ref(v_decls_2836_);
lean_dec_ref(v_lctx_2832_);
v_toPure_2837_ = lean_ctor_get(v_toApplicative_2835_, 1);
lean_inc(v_toPure_2837_);
v___f_2838_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2838_, 0, v_toPure_2837_);
lean_closure_set(v___f_2838_, 1, v_f_2833_);
v___x_2839_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2831_, v_decls_2836_, v___f_2838_, v_init_2834_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2840_, lean_object* v_00_u03b2_2841_, lean_object* v_inst_2842_, lean_object* v_lctx_2843_, lean_object* v_f_2844_, lean_object* v_init_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2842_, v_lctx_2843_, v_f_2844_, v_init_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2847_, lean_object* v_f_2848_, lean_object* v_decl_2849_){
_start:
{
if (lean_obj_tag(v_decl_2849_) == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_dec(v_f_2848_);
v___x_2850_ = lean_box(0);
v___x_2851_ = lean_apply_2(v_toPure_2847_, lean_box(0), v___x_2850_);
return v___x_2851_;
}
else
{
lean_object* v_val_2852_; lean_object* v___x_2853_; 
lean_dec(v_toPure_2847_);
v_val_2852_ = lean_ctor_get(v_decl_2849_, 0);
lean_inc(v_val_2852_);
lean_dec_ref(v_decl_2849_);
v___x_2853_ = lean_apply_1(v_f_2848_, v_val_2852_);
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2854_, lean_object* v_lctx_2855_, lean_object* v_f_2856_, lean_object* v_start_2857_){
_start:
{
lean_object* v_toApplicative_2858_; lean_object* v_decls_2859_; lean_object* v_toPure_2860_; lean_object* v___f_2861_; lean_object* v___x_2862_; 
v_toApplicative_2858_ = lean_ctor_get(v_inst_2854_, 0);
v_decls_2859_ = lean_ctor_get(v_lctx_2855_, 1);
lean_inc_ref(v_decls_2859_);
lean_dec_ref(v_lctx_2855_);
v_toPure_2860_ = lean_ctor_get(v_toApplicative_2858_, 1);
lean_inc(v_toPure_2860_);
v___f_2861_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2861_, 0, v_toPure_2860_);
lean_closure_set(v___f_2861_, 1, v_f_2856_);
v___x_2862_ = l_Lean_PersistentArray_forM___redArg(v_inst_2854_, v_decls_2859_, v___f_2861_, v_start_2857_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2863_, lean_object* v_lctx_2864_, lean_object* v_f_2865_, lean_object* v_start_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_LocalContext_forM___redArg(v_inst_2863_, v_lctx_2864_, v_f_2865_, v_start_2866_);
lean_dec(v_start_2866_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2868_, lean_object* v_inst_2869_, lean_object* v_lctx_2870_, lean_object* v_f_2871_, lean_object* v_start_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_LocalContext_forM___redArg(v_inst_2869_, v_lctx_2870_, v_f_2871_, v_start_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2874_, lean_object* v_inst_2875_, lean_object* v_lctx_2876_, lean_object* v_f_2877_, lean_object* v_start_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_LocalContext_forM(v_m_2874_, v_inst_2875_, v_lctx_2876_, v_f_2877_, v_start_2878_);
lean_dec(v_start_2878_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2880_, lean_object* v_f_2881_, lean_object* v_decl_2882_){
_start:
{
if (lean_obj_tag(v_decl_2882_) == 0)
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec(v_f_2881_);
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_apply_2(v_toPure_2880_, lean_box(0), v___x_2883_);
return v___x_2884_;
}
else
{
lean_object* v_val_2885_; lean_object* v___x_2886_; 
lean_dec(v_toPure_2880_);
v_val_2885_ = lean_ctor_get(v_decl_2882_, 0);
lean_inc(v_val_2885_);
lean_dec_ref(v_decl_2882_);
v___x_2886_ = lean_apply_1(v_f_2881_, v_val_2885_);
return v___x_2886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2887_, lean_object* v_lctx_2888_, lean_object* v_f_2889_){
_start:
{
lean_object* v_toApplicative_2890_; lean_object* v_decls_2891_; lean_object* v_toPure_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; 
v_toApplicative_2890_ = lean_ctor_get(v_inst_2887_, 0);
v_decls_2891_ = lean_ctor_get(v_lctx_2888_, 1);
lean_inc_ref(v_decls_2891_);
lean_dec_ref(v_lctx_2888_);
v_toPure_2892_ = lean_ctor_get(v_toApplicative_2890_, 1);
lean_inc(v_toPure_2892_);
v___f_2893_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2893_, 0, v_toPure_2892_);
lean_closure_set(v___f_2893_, 1, v_f_2889_);
v___x_2894_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2887_, v_decls_2891_, v___f_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2895_, lean_object* v_00_u03b2_2896_, lean_object* v_inst_2897_, lean_object* v_lctx_2898_, lean_object* v_f_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2897_, v_lctx_2898_, v_f_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2901_, lean_object* v_lctx_2902_, lean_object* v_f_2903_){
_start:
{
lean_object* v_toApplicative_2904_; lean_object* v_decls_2905_; lean_object* v_toPure_2906_; lean_object* v___f_2907_; lean_object* v___x_2908_; 
v_toApplicative_2904_ = lean_ctor_get(v_inst_2901_, 0);
v_decls_2905_ = lean_ctor_get(v_lctx_2902_, 1);
lean_inc_ref(v_decls_2905_);
lean_dec_ref(v_lctx_2902_);
v_toPure_2906_ = lean_ctor_get(v_toApplicative_2904_, 1);
lean_inc(v_toPure_2906_);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2907_, 0, v_toPure_2906_);
lean_closure_set(v___f_2907_, 1, v_f_2903_);
v___x_2908_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2901_, v_decls_2905_, v___f_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2909_, lean_object* v_00_u03b2_2910_, lean_object* v_inst_2911_, lean_object* v_lctx_2912_, lean_object* v_f_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2911_, v_lctx_2912_, v_f_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2915_, lean_object* v_f_2916_, lean_object* v_d_x3f_2917_, lean_object* v_b_2918_){
_start:
{
if (lean_obj_tag(v_d_x3f_2917_) == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec(v_f_2916_);
v___x_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2919_, 0, v_b_2918_);
v___x_2920_ = lean_apply_2(v_toPure_2915_, lean_box(0), v___x_2919_);
return v___x_2920_;
}
else
{
lean_object* v_val_2921_; lean_object* v___x_2922_; 
lean_dec(v_toPure_2915_);
v_val_2921_ = lean_ctor_get(v_d_x3f_2917_, 0);
lean_inc(v_val_2921_);
lean_dec_ref(v_d_x3f_2917_);
v___x_2922_ = lean_apply_2(v_f_2916_, v_val_2921_, v_b_2918_);
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2923_, lean_object* v_inst_2924_, lean_object* v_00_u03b2_2925_, lean_object* v_lctx_2926_, lean_object* v_init_2927_, lean_object* v_f_2928_){
_start:
{
lean_object* v_decls_2929_; lean_object* v___f_2930_; lean_object* v___x_2931_; 
v_decls_2929_ = lean_ctor_get(v_lctx_2926_, 1);
lean_inc_ref(v_decls_2929_);
lean_dec_ref(v_lctx_2926_);
v___f_2930_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2930_, 0, v_toPure_2923_);
lean_closure_set(v___f_2930_, 1, v_f_2928_);
v___x_2931_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2924_, v_decls_2929_, v_init_2927_, v___f_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2932_){
_start:
{
lean_object* v_toApplicative_2933_; lean_object* v_toPure_2934_; lean_object* v___f_2935_; 
v_toApplicative_2933_ = lean_ctor_get(v_inst_2932_, 0);
v_toPure_2934_ = lean_ctor_get(v_toApplicative_2933_, 1);
lean_inc(v_toPure_2934_);
v___f_2935_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1), 6, 2);
lean_closure_set(v___f_2935_, 0, v_toPure_2934_);
lean_closure_set(v___f_2935_, 1, v_inst_2932_);
return v___f_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2936_, lean_object* v_inst_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2939_, lean_object* v_x1_2940_, lean_object* v_x2_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_apply_2(v_f_2939_, v_x1_2940_, v_x2_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2962_, lean_object* v_f_2963_, lean_object* v_init_2964_, lean_object* v_start_2965_){
_start:
{
lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___f_2966_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2966_, 0, v_f_2963_);
v___x_2967_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2968_ = l_Lean_LocalContext_foldlM___redArg(v___x_2967_, v_lctx_2962_, v___f_2966_, v_init_2964_, v_start_2965_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2969_, lean_object* v_f_2970_, lean_object* v_init_2971_, lean_object* v_start_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2969_, v_f_2970_, v_init_2971_, v_start_2972_);
lean_dec(v_start_2972_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2974_, lean_object* v_lctx_2975_, lean_object* v_f_2976_, lean_object* v_init_2977_, lean_object* v_start_2978_){
_start:
{
lean_object* v___f_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2979_, 0, v_f_2976_);
v___x_2980_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2981_ = l_Lean_LocalContext_foldlM___redArg(v___x_2980_, v_lctx_2975_, v___f_2979_, v_init_2977_, v_start_2978_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_2982_, lean_object* v_lctx_2983_, lean_object* v_f_2984_, lean_object* v_init_2985_, lean_object* v_start_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_LocalContext_foldl(v_00_u03b2_2982_, v_lctx_2983_, v_f_2984_, v_init_2985_, v_start_2986_);
lean_dec(v_start_2986_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_2988_, lean_object* v_x1_2989_, lean_object* v_x2_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_apply_2(v_f_2988_, v_x1_2989_, v_x2_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_2992_, lean_object* v_f_2993_, lean_object* v_init_2994_){
_start:
{
lean_object* v___f_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___f_2995_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2995_, 0, v_f_2993_);
v___x_2996_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2997_ = l_Lean_LocalContext_foldrM___redArg(v___x_2996_, v_lctx_2992_, v___f_2995_, v_init_2994_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_2998_, lean_object* v_lctx_2999_, lean_object* v_f_3000_, lean_object* v_init_3001_){
_start:
{
lean_object* v___f_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___f_3002_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3002_, 0, v_f_3000_);
v___x_3003_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3004_ = l_Lean_LocalContext_foldrM___redArg(v___x_3003_, v_lctx_2999_, v___f_3002_, v_init_3001_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_3005_, size_t v_i_3006_, size_t v_stop_3007_, lean_object* v_b_3008_){
_start:
{
lean_object* v___y_3010_; uint8_t v___x_3014_; 
v___x_3014_ = lean_usize_dec_eq(v_i_3006_, v_stop_3007_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_array_uget_borrowed(v_as_3005_, v_i_3006_);
if (lean_obj_tag(v___x_3015_) == 0)
{
v___y_3010_ = v_b_3008_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_unsigned_to_nat(1u);
v___x_3017_ = lean_nat_add(v_b_3008_, v___x_3016_);
lean_dec(v_b_3008_);
v___y_3010_ = v___x_3017_;
goto v___jp_3009_;
}
}
else
{
return v_b_3008_;
}
v___jp_3009_:
{
size_t v___x_3011_; size_t v___x_3012_; 
v___x_3011_ = ((size_t)1ULL);
v___x_3012_ = lean_usize_add(v_i_3006_, v___x_3011_);
v_i_3006_ = v___x_3012_;
v_b_3008_ = v___y_3010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3018_, lean_object* v_i_3019_, lean_object* v_stop_3020_, lean_object* v_b_3021_){
_start:
{
size_t v_i_boxed_3022_; size_t v_stop_boxed_3023_; lean_object* v_res_3024_; 
v_i_boxed_3022_ = lean_unbox_usize(v_i_3019_);
lean_dec(v_i_3019_);
v_stop_boxed_3023_ = lean_unbox_usize(v_stop_3020_);
lean_dec(v_stop_3020_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3018_, v_i_boxed_3022_, v_stop_boxed_3023_, v_b_3021_);
lean_dec_ref(v_as_3018_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3025_, lean_object* v_x_3026_){
_start:
{
if (lean_obj_tag(v_x_3025_) == 0)
{
lean_object* v_cs_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; 
v_cs_3027_ = lean_ctor_get(v_x_3025_, 0);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = lean_array_get_size(v_cs_3027_);
v___x_3030_ = lean_nat_dec_lt(v___x_3028_, v___x_3029_);
if (v___x_3030_ == 0)
{
return v_x_3026_;
}
else
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_nat_dec_le(v___x_3029_, v___x_3029_);
if (v___x_3031_ == 0)
{
if (v___x_3030_ == 0)
{
return v_x_3026_;
}
else
{
size_t v___x_3032_; size_t v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = ((size_t)0ULL);
v___x_3033_ = lean_usize_of_nat(v___x_3029_);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3027_, v___x_3032_, v___x_3033_, v_x_3026_);
return v___x_3034_;
}
}
else
{
size_t v___x_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = lean_usize_of_nat(v___x_3029_);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3027_, v___x_3035_, v___x_3036_, v_x_3026_);
return v___x_3037_;
}
}
}
else
{
lean_object* v_vs_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v_vs_3038_ = lean_ctor_get(v_x_3025_, 0);
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = lean_array_get_size(v_vs_3038_);
v___x_3041_ = lean_nat_dec_lt(v___x_3039_, v___x_3040_);
if (v___x_3041_ == 0)
{
return v_x_3026_;
}
else
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_nat_dec_le(v___x_3040_, v___x_3040_);
if (v___x_3042_ == 0)
{
if (v___x_3041_ == 0)
{
return v_x_3026_;
}
else
{
size_t v___x_3043_; size_t v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = ((size_t)0ULL);
v___x_3044_ = lean_usize_of_nat(v___x_3040_);
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3038_, v___x_3043_, v___x_3044_, v_x_3026_);
return v___x_3045_;
}
}
else
{
size_t v___x_3046_; size_t v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = lean_usize_of_nat(v___x_3040_);
v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3038_, v___x_3046_, v___x_3047_, v_x_3026_);
return v___x_3048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3049_, size_t v_i_3050_, size_t v_stop_3051_, lean_object* v_b_3052_){
_start:
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_usize_dec_eq(v_i_3050_, v_stop_3051_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; size_t v___x_3056_; size_t v___x_3057_; 
v___x_3054_ = lean_array_uget_borrowed(v_as_3049_, v_i_3050_);
v___x_3055_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3054_, v_b_3052_);
v___x_3056_ = ((size_t)1ULL);
v___x_3057_ = lean_usize_add(v_i_3050_, v___x_3056_);
v_i_3050_ = v___x_3057_;
v_b_3052_ = v___x_3055_;
goto _start;
}
else
{
return v_b_3052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3059_, lean_object* v_i_3060_, lean_object* v_stop_3061_, lean_object* v_b_3062_){
_start:
{
size_t v_i_boxed_3063_; size_t v_stop_boxed_3064_; lean_object* v_res_3065_; 
v_i_boxed_3063_ = lean_unbox_usize(v_i_3060_);
lean_dec(v_i_3060_);
v_stop_boxed_3064_ = lean_unbox_usize(v_stop_3061_);
lean_dec(v_stop_3061_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3059_, v_i_boxed_3063_, v_stop_boxed_3064_, v_b_3062_);
lean_dec_ref(v_as_3059_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3066_, lean_object* v_x_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3066_, v_x_3067_);
lean_dec_ref(v_x_3066_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3069_, size_t v_x_3070_, size_t v_x_3071_, lean_object* v_x_3072_){
_start:
{
if (lean_obj_tag(v_x_3069_) == 0)
{
lean_object* v_cs_3073_; lean_object* v___x_3074_; size_t v___x_3075_; lean_object* v_j_3076_; lean_object* v___x_3077_; size_t v___x_3078_; size_t v___x_3079_; size_t v___x_3080_; size_t v___x_3081_; size_t v___x_3082_; size_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; 
v_cs_3073_ = lean_ctor_get(v_x_3069_, 0);
v___x_3074_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3075_ = lean_usize_shift_right(v_x_3070_, v_x_3071_);
v_j_3076_ = lean_usize_to_nat(v___x_3075_);
v___x_3077_ = lean_array_get_borrowed(v___x_3074_, v_cs_3073_, v_j_3076_);
v___x_3078_ = ((size_t)1ULL);
v___x_3079_ = lean_usize_shift_left(v___x_3078_, v_x_3071_);
v___x_3080_ = lean_usize_sub(v___x_3079_, v___x_3078_);
v___x_3081_ = lean_usize_land(v_x_3070_, v___x_3080_);
v___x_3082_ = ((size_t)5ULL);
v___x_3083_ = lean_usize_sub(v_x_3071_, v___x_3082_);
v___x_3084_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3077_, v___x_3081_, v___x_3083_, v_x_3072_);
v___x_3085_ = lean_unsigned_to_nat(1u);
v___x_3086_ = lean_nat_add(v_j_3076_, v___x_3085_);
lean_dec(v_j_3076_);
v___x_3087_ = lean_array_get_size(v_cs_3073_);
v___x_3088_ = lean_nat_dec_lt(v___x_3086_, v___x_3087_);
if (v___x_3088_ == 0)
{
lean_dec(v___x_3086_);
return v___x_3084_;
}
else
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_nat_dec_le(v___x_3087_, v___x_3087_);
if (v___x_3089_ == 0)
{
if (v___x_3088_ == 0)
{
lean_dec(v___x_3086_);
return v___x_3084_;
}
else
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_usize_of_nat(v___x_3086_);
lean_dec(v___x_3086_);
v___x_3091_ = lean_usize_of_nat(v___x_3087_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3073_, v___x_3090_, v___x_3091_, v___x_3084_);
return v___x_3092_;
}
}
else
{
size_t v___x_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_usize_of_nat(v___x_3086_);
lean_dec(v___x_3086_);
v___x_3094_ = lean_usize_of_nat(v___x_3087_);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3073_, v___x_3093_, v___x_3094_, v___x_3084_);
return v___x_3095_;
}
}
}
else
{
lean_object* v_vs_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_vs_3096_ = lean_ctor_get(v_x_3069_, 0);
v___x_3097_ = lean_usize_to_nat(v_x_3070_);
v___x_3098_ = lean_array_get_size(v_vs_3096_);
v___x_3099_ = lean_nat_dec_lt(v___x_3097_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_dec(v___x_3097_);
return v_x_3072_;
}
else
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_nat_dec_le(v___x_3098_, v___x_3098_);
if (v___x_3100_ == 0)
{
if (v___x_3099_ == 0)
{
lean_dec(v___x_3097_);
return v_x_3072_;
}
else
{
size_t v___x_3101_; size_t v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_usize_of_nat(v___x_3097_);
lean_dec(v___x_3097_);
v___x_3102_ = lean_usize_of_nat(v___x_3098_);
v___x_3103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3096_, v___x_3101_, v___x_3102_, v_x_3072_);
return v___x_3103_;
}
}
else
{
size_t v___x_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = lean_usize_of_nat(v___x_3097_);
lean_dec(v___x_3097_);
v___x_3105_ = lean_usize_of_nat(v___x_3098_);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3096_, v___x_3104_, v___x_3105_, v_x_3072_);
return v___x_3106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3107_, lean_object* v_x_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_){
_start:
{
size_t v_x_1557__boxed_3111_; size_t v_x_1558__boxed_3112_; lean_object* v_res_3113_; 
v_x_1557__boxed_3111_ = lean_unbox_usize(v_x_3108_);
lean_dec(v_x_3108_);
v_x_1558__boxed_3112_ = lean_unbox_usize(v_x_3109_);
lean_dec(v_x_3109_);
v_res_3113_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3107_, v_x_1557__boxed_3111_, v_x_1558__boxed_3112_, v_x_3110_);
lean_dec_ref(v_x_3107_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3114_, lean_object* v_init_3115_, lean_object* v_start_3116_){
_start:
{
lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = lean_nat_dec_eq(v_start_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v_root_3119_; lean_object* v_tail_3120_; size_t v_shift_3121_; lean_object* v_tailOff_3122_; uint8_t v___x_3123_; 
v_root_3119_ = lean_ctor_get(v_t_3114_, 0);
v_tail_3120_ = lean_ctor_get(v_t_3114_, 1);
v_shift_3121_ = lean_ctor_get_usize(v_t_3114_, 4);
v_tailOff_3122_ = lean_ctor_get(v_t_3114_, 3);
v___x_3123_ = lean_nat_dec_le(v_tailOff_3122_, v_start_3116_);
if (v___x_3123_ == 0)
{
size_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v___x_3124_ = lean_usize_of_nat(v_start_3116_);
v___x_3125_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3119_, v___x_3124_, v_shift_3121_, v_init_3115_);
v___x_3126_ = lean_array_get_size(v_tail_3120_);
v___x_3127_ = lean_nat_dec_lt(v___x_3117_, v___x_3126_);
if (v___x_3127_ == 0)
{
return v___x_3125_;
}
else
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_nat_dec_le(v___x_3126_, v___x_3126_);
if (v___x_3128_ == 0)
{
if (v___x_3127_ == 0)
{
return v___x_3125_;
}
else
{
size_t v___x_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = ((size_t)0ULL);
v___x_3130_ = lean_usize_of_nat(v___x_3126_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3120_, v___x_3129_, v___x_3130_, v___x_3125_);
return v___x_3131_;
}
}
else
{
size_t v___x_3132_; size_t v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = ((size_t)0ULL);
v___x_3133_ = lean_usize_of_nat(v___x_3126_);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3120_, v___x_3132_, v___x_3133_, v___x_3125_);
return v___x_3134_;
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3135_ = lean_nat_sub(v_start_3116_, v_tailOff_3122_);
v___x_3136_ = lean_array_get_size(v_tail_3120_);
v___x_3137_ = lean_nat_dec_lt(v___x_3135_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_dec(v___x_3135_);
return v_init_3115_;
}
else
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_nat_dec_le(v___x_3136_, v___x_3136_);
if (v___x_3138_ == 0)
{
if (v___x_3137_ == 0)
{
lean_dec(v___x_3135_);
return v_init_3115_;
}
else
{
size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = lean_usize_of_nat(v___x_3135_);
lean_dec(v___x_3135_);
v___x_3140_ = lean_usize_of_nat(v___x_3136_);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3120_, v___x_3139_, v___x_3140_, v_init_3115_);
return v___x_3141_;
}
}
else
{
size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = lean_usize_of_nat(v___x_3135_);
lean_dec(v___x_3135_);
v___x_3143_ = lean_usize_of_nat(v___x_3136_);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3120_, v___x_3142_, v___x_3143_, v_init_3115_);
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_root_3145_; lean_object* v_tail_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_root_3145_ = lean_ctor_get(v_t_3114_, 0);
v_tail_3146_ = lean_ctor_get(v_t_3114_, 1);
v___x_3147_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3145_, v_init_3115_);
v___x_3148_ = lean_array_get_size(v_tail_3146_);
v___x_3149_ = lean_nat_dec_lt(v___x_3117_, v___x_3148_);
if (v___x_3149_ == 0)
{
return v___x_3147_;
}
else
{
uint8_t v___x_3150_; 
v___x_3150_ = lean_nat_dec_le(v___x_3148_, v___x_3148_);
if (v___x_3150_ == 0)
{
if (v___x_3149_ == 0)
{
return v___x_3147_;
}
else
{
size_t v___x_3151_; size_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = ((size_t)0ULL);
v___x_3152_ = lean_usize_of_nat(v___x_3148_);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3146_, v___x_3151_, v___x_3152_, v___x_3147_);
return v___x_3153_;
}
}
else
{
size_t v___x_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((size_t)0ULL);
v___x_3155_ = lean_usize_of_nat(v___x_3148_);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3146_, v___x_3154_, v___x_3155_, v___x_3147_);
return v___x_3156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3157_, lean_object* v_init_3158_, lean_object* v_start_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3157_, v_init_3158_, v_start_3159_);
lean_dec(v_start_3159_);
lean_dec_ref(v_t_3157_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3161_, lean_object* v_init_3162_, lean_object* v_start_3163_){
_start:
{
lean_object* v_decls_3164_; lean_object* v___x_3165_; 
v_decls_3164_ = lean_ctor_get(v_lctx_3161_, 1);
v___x_3165_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3164_, v_init_3162_, v_start_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3166_, lean_object* v_init_3167_, lean_object* v_start_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3166_, v_init_3167_, v_start_3168_);
lean_dec(v_start_3168_);
lean_dec_ref(v_lctx_3166_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3170_){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3170_, v___x_3171_, v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_LocalContext_size(v_lctx_3173_);
lean_dec_ref(v_lctx_3173_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3175_, lean_object* v_x_3176_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_apply_1(v_f_3175_, v_x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3178_, lean_object* v_f_3179_){
_start:
{
lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___f_3180_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3180_, 0, v_f_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3182_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3181_, v_lctx_3178_, v___f_3180_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3183_, lean_object* v_lctx_3184_, lean_object* v_f_3185_){
_start:
{
lean_object* v___f_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___f_3186_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3186_, 0, v_f_3185_);
v___x_3187_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3188_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3187_, v_lctx_3184_, v___f_3186_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3189_, lean_object* v_f_3190_){
_start:
{
lean_object* v___f_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___f_3191_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3191_, 0, v_f_3190_);
v___x_3192_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3193_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3192_, v_lctx_3189_, v___f_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3194_, lean_object* v_lctx_3195_, lean_object* v_f_3196_){
_start:
{
lean_object* v___f_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___f_3197_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3197_, 0, v_f_3196_);
v___x_3198_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3199_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3198_, v_lctx_3195_, v___f_3197_);
return v___x_3199_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3200_, lean_object* v_as_3201_, size_t v_i_3202_, size_t v_stop_3203_){
_start:
{
uint8_t v___x_3204_; 
v___x_3204_ = lean_usize_dec_eq(v_i_3202_, v_stop_3203_);
if (v___x_3204_ == 0)
{
uint8_t v___x_3205_; uint8_t v___y_3207_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_fvarId_3213_; uint8_t v___x_3214_; 
v___x_3205_ = 1;
v___x_3211_ = lean_array_uget_borrowed(v_as_3201_, v_i_3202_);
v___x_3212_ = l_Lean_Expr_fvarId_x21(v___x_3211_);
v_fvarId_3213_ = lean_ctor_get(v_val_3200_, 1);
v___x_3214_ = l_Lean_instBEqFVarId_beq(v___x_3212_, v_fvarId_3213_);
lean_dec(v___x_3212_);
v___y_3207_ = v___x_3214_;
goto v___jp_3206_;
v___jp_3206_:
{
if (v___y_3207_ == 0)
{
size_t v___x_3208_; size_t v___x_3209_; 
v___x_3208_ = ((size_t)1ULL);
v___x_3209_ = lean_usize_add(v_i_3202_, v___x_3208_);
v_i_3202_ = v___x_3209_;
goto _start;
}
else
{
return v___x_3205_;
}
}
}
else
{
uint8_t v___x_3215_; 
v___x_3215_ = 0;
return v___x_3215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3216_, lean_object* v_as_3217_, lean_object* v_i_3218_, lean_object* v_stop_3219_){
_start:
{
size_t v_i_boxed_3220_; size_t v_stop_boxed_3221_; uint8_t v_res_3222_; lean_object* v_r_3223_; 
v_i_boxed_3220_ = lean_unbox_usize(v_i_3218_);
lean_dec(v_i_3218_);
v_stop_boxed_3221_ = lean_unbox_usize(v_stop_3219_);
lean_dec(v_stop_3219_);
v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3216_, v_as_3217_, v_i_boxed_3220_, v_stop_boxed_3221_);
lean_dec_ref(v_as_3217_);
lean_dec_ref(v_val_3216_);
v_r_3223_ = lean_box(v_res_3222_);
return v_r_3223_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3224_, lean_object* v_a_u2082_3225_, lean_object* v_exceptFVars_3226_, lean_object* v_i_3227_, lean_object* v_j_3228_){
_start:
{
lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v_size_3244_; uint8_t v___x_3245_; 
v_size_3244_ = lean_ctor_get(v_a_u2081_3224_, 2);
v___x_3245_ = lean_nat_dec_lt(v_i_3227_, v_size_3244_);
if (v___x_3245_ == 0)
{
uint8_t v___x_3246_; 
lean_dec(v_j_3228_);
lean_dec(v_i_3227_);
v___x_3246_ = 1;
return v___x_3246_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = lean_box(0);
v___x_3248_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3247_, v_a_u2081_3224_, v_i_3227_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_unsigned_to_nat(1u);
v___x_3250_ = lean_nat_add(v_i_3227_, v___x_3249_);
lean_dec(v_i_3227_);
v_i_3227_ = v___x_3250_;
goto _start;
}
else
{
lean_object* v_val_3252_; uint8_t v___y_3254_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v_val_3252_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_val_3252_);
lean_dec_ref(v___x_3248_);
v___x_3263_ = lean_unsigned_to_nat(0u);
v___x_3264_ = lean_array_get_size(v_exceptFVars_3226_);
v___x_3265_ = lean_nat_dec_lt(v___x_3263_, v___x_3264_);
if (v___x_3265_ == 0)
{
v___y_3254_ = v___x_3265_;
goto v___jp_3253_;
}
else
{
if (v___x_3265_ == 0)
{
v___y_3254_ = v___x_3265_;
goto v___jp_3253_;
}
else
{
size_t v___x_3266_; size_t v___x_3267_; uint8_t v___x_3268_; 
v___x_3266_ = ((size_t)0ULL);
v___x_3267_ = lean_usize_of_nat(v___x_3264_);
v___x_3268_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3252_, v_exceptFVars_3226_, v___x_3266_, v___x_3267_);
if (v___x_3268_ == 0)
{
v___y_3254_ = v___x_3268_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec(v_val_3252_);
v___x_3269_ = lean_unsigned_to_nat(1u);
v___x_3270_ = lean_nat_add(v_i_3227_, v___x_3269_);
lean_dec(v_i_3227_);
v_i_3227_ = v___x_3270_;
goto _start;
}
}
}
v___jp_3253_:
{
lean_object* v_size_3255_; uint8_t v___x_3256_; 
v_size_3255_ = lean_ctor_get(v_a_u2082_3225_, 2);
v___x_3256_ = lean_nat_dec_lt(v_j_3228_, v_size_3255_);
if (v___x_3256_ == 0)
{
lean_dec(v_val_3252_);
lean_dec(v_j_3228_);
lean_dec(v_i_3227_);
return v___y_3254_;
}
else
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3247_, v_a_u2082_3225_, v_j_3228_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec(v_val_3252_);
v___x_3258_ = lean_unsigned_to_nat(1u);
v___x_3259_ = lean_nat_add(v_j_3228_, v___x_3258_);
lean_dec(v_j_3228_);
v_j_3228_ = v___x_3259_;
goto _start;
}
else
{
lean_object* v_val_3261_; lean_object* v_fvarId_3262_; 
v_val_3261_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_val_3261_);
lean_dec_ref(v___x_3257_);
v_fvarId_3262_ = lean_ctor_get(v_val_3252_, 1);
lean_inc(v_fvarId_3262_);
lean_dec(v_val_3252_);
v___y_3241_ = v_val_3261_;
v___y_3242_ = v_fvarId_3262_;
goto v___jp_3240_;
}
}
}
}
}
v___jp_3229_:
{
uint8_t v___x_3232_; 
v___x_3232_ = l_Lean_instBEqFVarId_beq(v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3234_ = lean_nat_add(v_j_3228_, v___x_3233_);
lean_dec(v_j_3228_);
v_j_3228_ = v___x_3234_;
goto _start;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_unsigned_to_nat(1u);
v___x_3237_ = lean_nat_add(v_i_3227_, v___x_3236_);
lean_dec(v_i_3227_);
v___x_3238_ = lean_nat_add(v_j_3228_, v___x_3236_);
lean_dec(v_j_3228_);
v_i_3227_ = v___x_3237_;
v_j_3228_ = v___x_3238_;
goto _start;
}
}
v___jp_3240_:
{
lean_object* v_fvarId_3243_; 
v_fvarId_3243_ = lean_ctor_get(v___y_3241_, 1);
lean_inc(v_fvarId_3243_);
lean_dec_ref(v___y_3241_);
v___y_3230_ = v___y_3242_;
v___y_3231_ = v_fvarId_3243_;
goto v___jp_3229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3272_, lean_object* v_a_u2082_3273_, lean_object* v_exceptFVars_3274_, lean_object* v_i_3275_, lean_object* v_j_3276_){
_start:
{
uint8_t v_res_3277_; lean_object* v_r_3278_; 
v_res_3277_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3272_, v_a_u2082_3273_, v_exceptFVars_3274_, v_i_3275_, v_j_3276_);
lean_dec_ref(v_exceptFVars_3274_);
lean_dec_ref(v_a_u2082_3273_);
lean_dec_ref(v_a_u2081_3272_);
v_r_3278_ = lean_box(v_res_3277_);
return v_r_3278_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3279_, lean_object* v_lctx_u2082_3280_, lean_object* v_exceptFVars_3281_){
_start:
{
lean_object* v_decls_3282_; lean_object* v_decls_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_decls_3282_ = lean_ctor_get(v_lctx_u2081_3279_, 1);
v_decls_3283_ = lean_ctor_get(v_lctx_u2082_3280_, 1);
v___x_3284_ = lean_unsigned_to_nat(0u);
v___x_3285_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3282_, v_decls_3283_, v_exceptFVars_3281_, v___x_3284_, v___x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3286_, lean_object* v_lctx_u2082_3287_, lean_object* v_exceptFVars_3288_){
_start:
{
uint8_t v_res_3289_; lean_object* v_r_3290_; 
v_res_3289_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3286_, v_lctx_u2082_3287_, v_exceptFVars_3288_);
lean_dec_ref(v_exceptFVars_3288_);
lean_dec_ref(v_lctx_u2082_3287_);
lean_dec_ref(v_lctx_u2081_3286_);
v_r_3290_ = lean_box(v_res_3289_);
return v_r_3290_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3292_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3293_ = lean_unsigned_to_nat(14u);
v___x_3294_ = lean_unsigned_to_nat(573u);
v___x_3295_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3296_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3297_ = l_mkPanicMessageWithDecl(v___x_3296_, v___x_3295_, v___x_3294_, v___x_3293_, v___x_3292_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3298_, lean_object* v_lctx_3299_, lean_object* v___x_3300_, uint8_t v_isLambda_3301_, uint8_t v_usedLetOnly_3302_, uint8_t v_generalizeNondepLet_3303_, lean_object* v_i_3304_, lean_object* v_x_3305_, lean_object* v_b_3306_){
_start:
{
lean_object* v_n_3308_; lean_object* v_ty_3309_; uint8_t v_bi_3310_; lean_object* v_x_3314_; lean_object* v___x_3315_; 
v_x_3314_ = lean_array_fget_borrowed(v_xs_3298_, v_i_3304_);
v___x_3315_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3299_, v_x_3314_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_dec_ref(v_b_3306_);
v___x_3316_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3317_ = l_panic___redArg(v___x_3300_, v___x_3316_);
return v___x_3317_;
}
else
{
lean_object* v_val_3318_; 
v_val_3318_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_val_3318_);
lean_dec_ref(v___x_3315_);
if (lean_obj_tag(v_val_3318_) == 0)
{
lean_object* v_userName_3319_; lean_object* v_type_3320_; uint8_t v_bi_3321_; 
v_userName_3319_ = lean_ctor_get(v_val_3318_, 2);
lean_inc(v_userName_3319_);
v_type_3320_ = lean_ctor_get(v_val_3318_, 3);
lean_inc_ref(v_type_3320_);
v_bi_3321_ = lean_ctor_get_uint8(v_val_3318_, sizeof(void*)*4);
lean_dec_ref(v_val_3318_);
v_n_3308_ = v_userName_3319_;
v_ty_3309_ = v_type_3320_;
v_bi_3310_ = v_bi_3321_;
goto v___jp_3307_;
}
else
{
lean_object* v_userName_3322_; lean_object* v_type_3323_; lean_object* v_value_3324_; uint8_t v_nondep_3325_; uint8_t v___y_3331_; 
v_userName_3322_ = lean_ctor_get(v_val_3318_, 2);
lean_inc(v_userName_3322_);
v_type_3323_ = lean_ctor_get(v_val_3318_, 3);
lean_inc_ref(v_type_3323_);
v_value_3324_ = lean_ctor_get(v_val_3318_, 4);
lean_inc_ref(v_value_3324_);
v_nondep_3325_ = lean_ctor_get_uint8(v_val_3318_, sizeof(void*)*5);
lean_dec_ref(v_val_3318_);
if (v_nondep_3325_ == 0)
{
v___y_3331_ = v_nondep_3325_;
goto v___jp_3330_;
}
else
{
if (v_generalizeNondepLet_3303_ == 0)
{
v___y_3331_ = v_generalizeNondepLet_3303_;
goto v___jp_3330_;
}
else
{
uint8_t v___x_3336_; 
lean_dec_ref(v_value_3324_);
v___x_3336_ = 0;
v_n_3308_ = v_userName_3322_;
v_ty_3309_ = v_type_3323_;
v_bi_3310_ = v___x_3336_;
goto v___jp_3307_;
}
}
v___jp_3326_:
{
lean_object* v_ty_3327_; lean_object* v_val_3328_; lean_object* v___x_3329_; 
v_ty_3327_ = lean_expr_abstract_range(v_type_3323_, v_i_3304_, v_xs_3298_);
lean_dec_ref(v_type_3323_);
v_val_3328_ = lean_expr_abstract_range(v_value_3324_, v_i_3304_, v_xs_3298_);
lean_dec_ref(v_value_3324_);
v___x_3329_ = l_Lean_Expr_letE___override(v_userName_3322_, v_ty_3327_, v_val_3328_, v_b_3306_, v_nondep_3325_);
return v___x_3329_;
}
v___jp_3330_:
{
if (v_usedLetOnly_3302_ == 0)
{
goto v___jp_3326_;
}
else
{
if (v___y_3331_ == 0)
{
lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_expr_has_loose_bvar(v_b_3306_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref(v_value_3324_);
lean_dec_ref(v_type_3323_);
lean_dec(v_userName_3322_);
v___x_3334_ = lean_unsigned_to_nat(1u);
v___x_3335_ = lean_expr_lower_loose_bvars(v_b_3306_, v___x_3334_, v___x_3334_);
lean_dec_ref(v_b_3306_);
return v___x_3335_;
}
else
{
goto v___jp_3326_;
}
}
else
{
goto v___jp_3326_;
}
}
}
}
}
v___jp_3307_:
{
lean_object* v_ty_3311_; 
v_ty_3311_ = lean_expr_abstract_range(v_ty_3309_, v_i_3304_, v_xs_3298_);
lean_dec_ref(v_ty_3309_);
if (v_isLambda_3301_ == 0)
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_mkForall(v_n_3308_, v_bi_3310_, v_ty_3311_, v_b_3306_);
return v___x_3312_;
}
else
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_mkLambda(v_n_3308_, v_bi_3310_, v_ty_3311_, v_b_3306_);
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3337_, lean_object* v_lctx_3338_, lean_object* v___x_3339_, lean_object* v_isLambda_3340_, lean_object* v_usedLetOnly_3341_, lean_object* v_generalizeNondepLet_3342_, lean_object* v_i_3343_, lean_object* v_x_3344_, lean_object* v_b_3345_){
_start:
{
uint8_t v_isLambda_boxed_3346_; uint8_t v_usedLetOnly_boxed_3347_; uint8_t v_generalizeNondepLet_boxed_3348_; lean_object* v_res_3349_; 
v_isLambda_boxed_3346_ = lean_unbox(v_isLambda_3340_);
v_usedLetOnly_boxed_3347_ = lean_unbox(v_usedLetOnly_3341_);
v_generalizeNondepLet_boxed_3348_ = lean_unbox(v_generalizeNondepLet_3342_);
v_res_3349_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3337_, v_lctx_3338_, v___x_3339_, v_isLambda_boxed_3346_, v_usedLetOnly_boxed_3347_, v_generalizeNondepLet_boxed_3348_, v_i_3343_, v_x_3344_, v_b_3345_);
lean_dec(v_i_3343_);
lean_dec_ref(v___x_3339_);
lean_dec_ref(v_xs_3337_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3350_, lean_object* v_lctx_3351_, lean_object* v_xs_3352_, lean_object* v_b_3353_, uint8_t v_usedLetOnly_3354_, uint8_t v_generalizeNondepLet_3355_){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___f_3360_; lean_object* v_b_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3356_ = l_Lean_instInhabitedExpr;
v___x_3357_ = lean_box(v_isLambda_3350_);
v___x_3358_ = lean_box(v_usedLetOnly_3354_);
v___x_3359_ = lean_box(v_generalizeNondepLet_3355_);
lean_inc_ref(v_xs_3352_);
v___f_3360_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3360_, 0, v_xs_3352_);
lean_closure_set(v___f_3360_, 1, v_lctx_3351_);
lean_closure_set(v___f_3360_, 2, v___x_3356_);
lean_closure_set(v___f_3360_, 3, v___x_3357_);
lean_closure_set(v___f_3360_, 4, v___x_3358_);
lean_closure_set(v___f_3360_, 5, v___x_3359_);
v_b_3361_ = lean_expr_abstract(v_b_3353_, v_xs_3352_);
v___x_3362_ = lean_array_get_size(v_xs_3352_);
lean_dec_ref(v_xs_3352_);
v___x_3363_ = l_Nat_foldRev___redArg(v___x_3362_, v___f_3360_, v_b_3361_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3364_, lean_object* v_lctx_3365_, lean_object* v_xs_3366_, lean_object* v_b_3367_, lean_object* v_usedLetOnly_3368_, lean_object* v_generalizeNondepLet_3369_){
_start:
{
uint8_t v_isLambda_boxed_3370_; uint8_t v_usedLetOnly_boxed_3371_; uint8_t v_generalizeNondepLet_boxed_3372_; lean_object* v_res_3373_; 
v_isLambda_boxed_3370_ = lean_unbox(v_isLambda_3364_);
v_usedLetOnly_boxed_3371_ = lean_unbox(v_usedLetOnly_3368_);
v_generalizeNondepLet_boxed_3372_ = lean_unbox(v_generalizeNondepLet_3369_);
v_res_3373_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3370_, v_lctx_3365_, v_xs_3366_, v_b_3367_, v_usedLetOnly_boxed_3371_, v_generalizeNondepLet_boxed_3372_);
lean_dec_ref(v_b_3367_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3374_, lean_object* v_lctx_3375_, uint8_t v_usedLetOnly_3376_, uint8_t v_generalizeNondepLet_3377_, lean_object* v_x_3378_, lean_object* v_x_3379_){
_start:
{
lean_object* v_zero_3380_; uint8_t v_isZero_3381_; 
v_zero_3380_ = lean_unsigned_to_nat(0u);
v_isZero_3381_ = lean_nat_dec_eq(v_x_3378_, v_zero_3380_);
if (v_isZero_3381_ == 1)
{
lean_dec(v_x_3378_);
lean_dec_ref(v_lctx_3375_);
return v_x_3379_;
}
else
{
lean_object* v_one_3382_; lean_object* v_n_3383_; lean_object* v_n_3385_; lean_object* v_ty_3386_; uint8_t v_bi_3387_; lean_object* v_x_3391_; lean_object* v___x_3392_; 
v_one_3382_ = lean_unsigned_to_nat(1u);
v_n_3383_ = lean_nat_sub(v_x_3378_, v_one_3382_);
lean_dec(v_x_3378_);
v_x_3391_ = lean_array_fget_borrowed(v_xs_3374_, v_n_3383_);
lean_inc_ref(v_lctx_3375_);
v___x_3392_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3375_, v_x_3391_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_dec_ref(v_x_3379_);
v___x_3393_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3394_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3393_);
v_x_3378_ = v_n_3383_;
v_x_3379_ = v___x_3394_;
goto _start;
}
else
{
lean_object* v_val_3396_; 
v_val_3396_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_val_3396_);
lean_dec_ref(v___x_3392_);
if (lean_obj_tag(v_val_3396_) == 0)
{
lean_object* v_userName_3397_; lean_object* v_type_3398_; uint8_t v_bi_3399_; 
v_userName_3397_ = lean_ctor_get(v_val_3396_, 2);
lean_inc(v_userName_3397_);
v_type_3398_ = lean_ctor_get(v_val_3396_, 3);
lean_inc_ref(v_type_3398_);
v_bi_3399_ = lean_ctor_get_uint8(v_val_3396_, sizeof(void*)*4);
lean_dec_ref(v_val_3396_);
v_n_3385_ = v_userName_3397_;
v_ty_3386_ = v_type_3398_;
v_bi_3387_ = v_bi_3399_;
goto v___jp_3384_;
}
else
{
lean_object* v_userName_3400_; lean_object* v_type_3401_; lean_object* v_value_3402_; uint8_t v_nondep_3403_; uint8_t v___y_3410_; 
v_userName_3400_ = lean_ctor_get(v_val_3396_, 2);
lean_inc(v_userName_3400_);
v_type_3401_ = lean_ctor_get(v_val_3396_, 3);
lean_inc_ref(v_type_3401_);
v_value_3402_ = lean_ctor_get(v_val_3396_, 4);
lean_inc_ref(v_value_3402_);
v_nondep_3403_ = lean_ctor_get_uint8(v_val_3396_, sizeof(void*)*5);
lean_dec_ref(v_val_3396_);
if (v_nondep_3403_ == 0)
{
v___y_3410_ = v_nondep_3403_;
goto v___jp_3409_;
}
else
{
if (v_generalizeNondepLet_3377_ == 0)
{
v___y_3410_ = v_generalizeNondepLet_3377_;
goto v___jp_3409_;
}
else
{
uint8_t v___x_3414_; 
lean_dec_ref(v_value_3402_);
v___x_3414_ = 0;
v_n_3385_ = v_userName_3400_;
v_ty_3386_ = v_type_3401_;
v_bi_3387_ = v___x_3414_;
goto v___jp_3384_;
}
}
v___jp_3404_:
{
lean_object* v_ty_3405_; lean_object* v_val_3406_; lean_object* v___x_3407_; 
v_ty_3405_ = lean_expr_abstract_range(v_type_3401_, v_n_3383_, v_xs_3374_);
lean_dec_ref(v_type_3401_);
v_val_3406_ = lean_expr_abstract_range(v_value_3402_, v_n_3383_, v_xs_3374_);
lean_dec_ref(v_value_3402_);
v___x_3407_ = l_Lean_Expr_letE___override(v_userName_3400_, v_ty_3405_, v_val_3406_, v_x_3379_, v_nondep_3403_);
v_x_3378_ = v_n_3383_;
v_x_3379_ = v___x_3407_;
goto _start;
}
v___jp_3409_:
{
if (v_usedLetOnly_3376_ == 0)
{
goto v___jp_3404_;
}
else
{
if (v___y_3410_ == 0)
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_expr_has_loose_bvar(v_x_3379_, v_zero_3380_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
lean_dec_ref(v_value_3402_);
lean_dec_ref(v_type_3401_);
lean_dec(v_userName_3400_);
v___x_3412_ = lean_expr_lower_loose_bvars(v_x_3379_, v_one_3382_, v_one_3382_);
lean_dec_ref(v_x_3379_);
v_x_3378_ = v_n_3383_;
v_x_3379_ = v___x_3412_;
goto _start;
}
else
{
goto v___jp_3404_;
}
}
else
{
goto v___jp_3404_;
}
}
}
}
}
v___jp_3384_:
{
lean_object* v_ty_3388_; lean_object* v___x_3389_; 
v_ty_3388_ = lean_expr_abstract_range(v_ty_3386_, v_n_3383_, v_xs_3374_);
lean_dec_ref(v_ty_3386_);
v___x_3389_ = l_Lean_mkLambda(v_n_3385_, v_bi_3387_, v_ty_3388_, v_x_3379_);
v_x_3378_ = v_n_3383_;
v_x_3379_ = v___x_3389_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3415_, lean_object* v_lctx_3416_, lean_object* v_usedLetOnly_3417_, lean_object* v_generalizeNondepLet_3418_, lean_object* v_x_3419_, lean_object* v_x_3420_){
_start:
{
uint8_t v_usedLetOnly_boxed_3421_; uint8_t v_generalizeNondepLet_boxed_3422_; lean_object* v_res_3423_; 
v_usedLetOnly_boxed_3421_ = lean_unbox(v_usedLetOnly_3417_);
v_generalizeNondepLet_boxed_3422_ = lean_unbox(v_generalizeNondepLet_3418_);
v_res_3423_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3415_, v_lctx_3416_, v_usedLetOnly_boxed_3421_, v_generalizeNondepLet_boxed_3422_, v_x_3419_, v_x_3420_);
lean_dec_ref(v_xs_3415_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3424_, lean_object* v_lctx_3425_, uint8_t v_usedLetOnly_3426_, uint8_t v_generalizeNondepLet_3427_, lean_object* v_x_3428_, lean_object* v_x_3429_){
_start:
{
lean_object* v_zero_3430_; uint8_t v_isZero_3431_; 
v_zero_3430_ = lean_unsigned_to_nat(0u);
v_isZero_3431_ = lean_nat_dec_eq(v_x_3428_, v_zero_3430_);
if (v_isZero_3431_ == 1)
{
lean_dec_ref(v_lctx_3425_);
return v_x_3429_;
}
else
{
lean_object* v_one_3432_; lean_object* v_n_3433_; lean_object* v_n_3435_; lean_object* v_ty_3436_; uint8_t v_bi_3437_; lean_object* v_x_3441_; lean_object* v___x_3442_; 
v_one_3432_ = lean_unsigned_to_nat(1u);
v_n_3433_ = lean_nat_sub(v_x_3428_, v_one_3432_);
v_x_3441_ = lean_array_fget_borrowed(v_xs_3424_, v_n_3433_);
lean_inc_ref(v_lctx_3425_);
v___x_3442_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3425_, v_x_3441_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec_ref(v_x_3429_);
v___x_3443_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3444_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3443_);
v___x_3445_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3424_, v_lctx_3425_, v_usedLetOnly_3426_, v_generalizeNondepLet_3427_, v_n_3433_, v___x_3444_);
return v___x_3445_;
}
else
{
lean_object* v_val_3446_; 
v_val_3446_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_val_3446_);
lean_dec_ref(v___x_3442_);
if (lean_obj_tag(v_val_3446_) == 0)
{
lean_object* v_userName_3447_; lean_object* v_type_3448_; uint8_t v_bi_3449_; 
v_userName_3447_ = lean_ctor_get(v_val_3446_, 2);
lean_inc(v_userName_3447_);
v_type_3448_ = lean_ctor_get(v_val_3446_, 3);
lean_inc_ref(v_type_3448_);
v_bi_3449_ = lean_ctor_get_uint8(v_val_3446_, sizeof(void*)*4);
lean_dec_ref(v_val_3446_);
v_n_3435_ = v_userName_3447_;
v_ty_3436_ = v_type_3448_;
v_bi_3437_ = v_bi_3449_;
goto v___jp_3434_;
}
else
{
lean_object* v_userName_3450_; lean_object* v_type_3451_; lean_object* v_value_3452_; uint8_t v_nondep_3453_; uint8_t v___y_3460_; 
v_userName_3450_ = lean_ctor_get(v_val_3446_, 2);
lean_inc(v_userName_3450_);
v_type_3451_ = lean_ctor_get(v_val_3446_, 3);
lean_inc_ref(v_type_3451_);
v_value_3452_ = lean_ctor_get(v_val_3446_, 4);
lean_inc_ref(v_value_3452_);
v_nondep_3453_ = lean_ctor_get_uint8(v_val_3446_, sizeof(void*)*5);
lean_dec_ref(v_val_3446_);
if (v_nondep_3453_ == 0)
{
v___y_3460_ = v_nondep_3453_;
goto v___jp_3459_;
}
else
{
if (v_generalizeNondepLet_3427_ == 0)
{
v___y_3460_ = v_generalizeNondepLet_3427_;
goto v___jp_3459_;
}
else
{
uint8_t v___x_3464_; 
lean_dec_ref(v_value_3452_);
v___x_3464_ = 0;
v_n_3435_ = v_userName_3450_;
v_ty_3436_ = v_type_3451_;
v_bi_3437_ = v___x_3464_;
goto v___jp_3434_;
}
}
v___jp_3454_:
{
lean_object* v_ty_3455_; lean_object* v_val_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_ty_3455_ = lean_expr_abstract_range(v_type_3451_, v_n_3433_, v_xs_3424_);
lean_dec_ref(v_type_3451_);
v_val_3456_ = lean_expr_abstract_range(v_value_3452_, v_n_3433_, v_xs_3424_);
lean_dec_ref(v_value_3452_);
v___x_3457_ = l_Lean_Expr_letE___override(v_userName_3450_, v_ty_3455_, v_val_3456_, v_x_3429_, v_nondep_3453_);
v___x_3458_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3424_, v_lctx_3425_, v_usedLetOnly_3426_, v_generalizeNondepLet_3427_, v_n_3433_, v___x_3457_);
return v___x_3458_;
}
v___jp_3459_:
{
if (v_usedLetOnly_3426_ == 0)
{
goto v___jp_3454_;
}
else
{
if (v___y_3460_ == 0)
{
uint8_t v___x_3461_; 
v___x_3461_ = lean_expr_has_loose_bvar(v_x_3429_, v_zero_3430_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
lean_dec_ref(v_value_3452_);
lean_dec_ref(v_type_3451_);
lean_dec(v_userName_3450_);
v___x_3462_ = lean_expr_lower_loose_bvars(v_x_3429_, v_one_3432_, v_one_3432_);
lean_dec_ref(v_x_3429_);
v___x_3463_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3424_, v_lctx_3425_, v_usedLetOnly_3426_, v_generalizeNondepLet_3427_, v_n_3433_, v___x_3462_);
return v___x_3463_;
}
else
{
goto v___jp_3454_;
}
}
else
{
goto v___jp_3454_;
}
}
}
}
}
v___jp_3434_:
{
lean_object* v_ty_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_ty_3438_ = lean_expr_abstract_range(v_ty_3436_, v_n_3433_, v_xs_3424_);
lean_dec_ref(v_ty_3436_);
v___x_3439_ = l_Lean_mkLambda(v_n_3435_, v_bi_3437_, v_ty_3438_, v_x_3429_);
v___x_3440_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3424_, v_lctx_3425_, v_usedLetOnly_3426_, v_generalizeNondepLet_3427_, v_n_3433_, v___x_3439_);
return v___x_3440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3465_, lean_object* v_lctx_3466_, lean_object* v_usedLetOnly_3467_, lean_object* v_generalizeNondepLet_3468_, lean_object* v_x_3469_, lean_object* v_x_3470_){
_start:
{
uint8_t v_usedLetOnly_boxed_3471_; uint8_t v_generalizeNondepLet_boxed_3472_; lean_object* v_res_3473_; 
v_usedLetOnly_boxed_3471_ = lean_unbox(v_usedLetOnly_3467_);
v_generalizeNondepLet_boxed_3472_ = lean_unbox(v_generalizeNondepLet_3468_);
v_res_3473_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3465_, v_lctx_3466_, v_usedLetOnly_boxed_3471_, v_generalizeNondepLet_boxed_3472_, v_x_3469_, v_x_3470_);
lean_dec(v_x_3469_);
lean_dec_ref(v_xs_3465_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3474_, lean_object* v_xs_3475_, lean_object* v_b_3476_, uint8_t v_usedLetOnly_3477_, uint8_t v_generalizeNondepLet_3478_){
_start:
{
lean_object* v_b_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_b_3479_ = lean_expr_abstract(v_b_3476_, v_xs_3475_);
v___x_3480_ = lean_array_get_size(v_xs_3475_);
v___x_3481_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3475_, v_lctx_3474_, v_usedLetOnly_3477_, v_generalizeNondepLet_3478_, v___x_3480_, v_b_3479_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3482_, lean_object* v_xs_3483_, lean_object* v_b_3484_, lean_object* v_usedLetOnly_3485_, lean_object* v_generalizeNondepLet_3486_){
_start:
{
uint8_t v_usedLetOnly_boxed_3487_; uint8_t v_generalizeNondepLet_boxed_3488_; lean_object* v_res_3489_; 
v_usedLetOnly_boxed_3487_ = lean_unbox(v_usedLetOnly_3485_);
v_generalizeNondepLet_boxed_3488_ = lean_unbox(v_generalizeNondepLet_3486_);
v_res_3489_ = l_Lean_LocalContext_mkLambda(v_lctx_3482_, v_xs_3483_, v_b_3484_, v_usedLetOnly_boxed_3487_, v_generalizeNondepLet_boxed_3488_);
lean_dec_ref(v_b_3484_);
lean_dec_ref(v_xs_3483_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3490_, lean_object* v_lctx_3491_, uint8_t v_usedLetOnly_3492_, uint8_t v_generalizeNondepLet_3493_, lean_object* v_x_3494_, lean_object* v_x_3495_){
_start:
{
lean_object* v_zero_3496_; uint8_t v_isZero_3497_; 
v_zero_3496_ = lean_unsigned_to_nat(0u);
v_isZero_3497_ = lean_nat_dec_eq(v_x_3494_, v_zero_3496_);
if (v_isZero_3497_ == 1)
{
lean_dec(v_x_3494_);
lean_dec_ref(v_lctx_3491_);
return v_x_3495_;
}
else
{
lean_object* v_one_3498_; lean_object* v_n_3499_; lean_object* v_n_3501_; lean_object* v_ty_3502_; uint8_t v_bi_3503_; lean_object* v_x_3507_; lean_object* v___x_3508_; 
v_one_3498_ = lean_unsigned_to_nat(1u);
v_n_3499_ = lean_nat_sub(v_x_3494_, v_one_3498_);
lean_dec(v_x_3494_);
v_x_3507_ = lean_array_fget_borrowed(v_xs_3490_, v_n_3499_);
lean_inc_ref(v_lctx_3491_);
v___x_3508_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3491_, v_x_3507_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec_ref(v_x_3495_);
v___x_3509_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3510_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3509_);
v_x_3494_ = v_n_3499_;
v_x_3495_ = v___x_3510_;
goto _start;
}
else
{
lean_object* v_val_3512_; 
v_val_3512_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_val_3512_);
lean_dec_ref(v___x_3508_);
if (lean_obj_tag(v_val_3512_) == 0)
{
lean_object* v_userName_3513_; lean_object* v_type_3514_; uint8_t v_bi_3515_; 
v_userName_3513_ = lean_ctor_get(v_val_3512_, 2);
lean_inc(v_userName_3513_);
v_type_3514_ = lean_ctor_get(v_val_3512_, 3);
lean_inc_ref(v_type_3514_);
v_bi_3515_ = lean_ctor_get_uint8(v_val_3512_, sizeof(void*)*4);
lean_dec_ref(v_val_3512_);
v_n_3501_ = v_userName_3513_;
v_ty_3502_ = v_type_3514_;
v_bi_3503_ = v_bi_3515_;
goto v___jp_3500_;
}
else
{
lean_object* v_userName_3516_; lean_object* v_type_3517_; lean_object* v_value_3518_; uint8_t v_nondep_3519_; uint8_t v___y_3526_; 
v_userName_3516_ = lean_ctor_get(v_val_3512_, 2);
lean_inc(v_userName_3516_);
v_type_3517_ = lean_ctor_get(v_val_3512_, 3);
lean_inc_ref(v_type_3517_);
v_value_3518_ = lean_ctor_get(v_val_3512_, 4);
lean_inc_ref(v_value_3518_);
v_nondep_3519_ = lean_ctor_get_uint8(v_val_3512_, sizeof(void*)*5);
lean_dec_ref(v_val_3512_);
if (v_nondep_3519_ == 0)
{
v___y_3526_ = v_nondep_3519_;
goto v___jp_3525_;
}
else
{
if (v_generalizeNondepLet_3493_ == 0)
{
v___y_3526_ = v_generalizeNondepLet_3493_;
goto v___jp_3525_;
}
else
{
uint8_t v___x_3530_; 
lean_dec_ref(v_value_3518_);
v___x_3530_ = 0;
v_n_3501_ = v_userName_3516_;
v_ty_3502_ = v_type_3517_;
v_bi_3503_ = v___x_3530_;
goto v___jp_3500_;
}
}
v___jp_3520_:
{
lean_object* v_ty_3521_; lean_object* v_val_3522_; lean_object* v___x_3523_; 
v_ty_3521_ = lean_expr_abstract_range(v_type_3517_, v_n_3499_, v_xs_3490_);
lean_dec_ref(v_type_3517_);
v_val_3522_ = lean_expr_abstract_range(v_value_3518_, v_n_3499_, v_xs_3490_);
lean_dec_ref(v_value_3518_);
v___x_3523_ = l_Lean_Expr_letE___override(v_userName_3516_, v_ty_3521_, v_val_3522_, v_x_3495_, v_nondep_3519_);
v_x_3494_ = v_n_3499_;
v_x_3495_ = v___x_3523_;
goto _start;
}
v___jp_3525_:
{
if (v_usedLetOnly_3492_ == 0)
{
goto v___jp_3520_;
}
else
{
if (v___y_3526_ == 0)
{
uint8_t v___x_3527_; 
v___x_3527_ = lean_expr_has_loose_bvar(v_x_3495_, v_zero_3496_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; 
lean_dec_ref(v_value_3518_);
lean_dec_ref(v_type_3517_);
lean_dec(v_userName_3516_);
v___x_3528_ = lean_expr_lower_loose_bvars(v_x_3495_, v_one_3498_, v_one_3498_);
lean_dec_ref(v_x_3495_);
v_x_3494_ = v_n_3499_;
v_x_3495_ = v___x_3528_;
goto _start;
}
else
{
goto v___jp_3520_;
}
}
else
{
goto v___jp_3520_;
}
}
}
}
}
v___jp_3500_:
{
lean_object* v_ty_3504_; lean_object* v___x_3505_; 
v_ty_3504_ = lean_expr_abstract_range(v_ty_3502_, v_n_3499_, v_xs_3490_);
lean_dec_ref(v_ty_3502_);
v___x_3505_ = l_Lean_mkForall(v_n_3501_, v_bi_3503_, v_ty_3504_, v_x_3495_);
v_x_3494_ = v_n_3499_;
v_x_3495_ = v___x_3505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3531_, lean_object* v_lctx_3532_, lean_object* v_usedLetOnly_3533_, lean_object* v_generalizeNondepLet_3534_, lean_object* v_x_3535_, lean_object* v_x_3536_){
_start:
{
uint8_t v_usedLetOnly_boxed_3537_; uint8_t v_generalizeNondepLet_boxed_3538_; lean_object* v_res_3539_; 
v_usedLetOnly_boxed_3537_ = lean_unbox(v_usedLetOnly_3533_);
v_generalizeNondepLet_boxed_3538_ = lean_unbox(v_generalizeNondepLet_3534_);
v_res_3539_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3531_, v_lctx_3532_, v_usedLetOnly_boxed_3537_, v_generalizeNondepLet_boxed_3538_, v_x_3535_, v_x_3536_);
lean_dec_ref(v_xs_3531_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3540_, lean_object* v_lctx_3541_, uint8_t v_usedLetOnly_3542_, uint8_t v_generalizeNondepLet_3543_, lean_object* v_x_3544_, lean_object* v_x_3545_){
_start:
{
lean_object* v_zero_3546_; uint8_t v_isZero_3547_; 
v_zero_3546_ = lean_unsigned_to_nat(0u);
v_isZero_3547_ = lean_nat_dec_eq(v_x_3544_, v_zero_3546_);
if (v_isZero_3547_ == 1)
{
lean_dec_ref(v_lctx_3541_);
return v_x_3545_;
}
else
{
lean_object* v_one_3548_; lean_object* v_n_3549_; lean_object* v_n_3551_; lean_object* v_ty_3552_; uint8_t v_bi_3553_; lean_object* v_x_3557_; lean_object* v___x_3558_; 
v_one_3548_ = lean_unsigned_to_nat(1u);
v_n_3549_ = lean_nat_sub(v_x_3544_, v_one_3548_);
v_x_3557_ = lean_array_fget_borrowed(v_xs_3540_, v_n_3549_);
lean_inc_ref(v_lctx_3541_);
v___x_3558_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3541_, v_x_3557_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec_ref(v_x_3545_);
v___x_3559_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3560_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3559_);
v___x_3561_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3540_, v_lctx_3541_, v_usedLetOnly_3542_, v_generalizeNondepLet_3543_, v_n_3549_, v___x_3560_);
return v___x_3561_;
}
else
{
lean_object* v_val_3562_; 
v_val_3562_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_val_3562_);
lean_dec_ref(v___x_3558_);
if (lean_obj_tag(v_val_3562_) == 0)
{
lean_object* v_userName_3563_; lean_object* v_type_3564_; uint8_t v_bi_3565_; 
v_userName_3563_ = lean_ctor_get(v_val_3562_, 2);
lean_inc(v_userName_3563_);
v_type_3564_ = lean_ctor_get(v_val_3562_, 3);
lean_inc_ref(v_type_3564_);
v_bi_3565_ = lean_ctor_get_uint8(v_val_3562_, sizeof(void*)*4);
lean_dec_ref(v_val_3562_);
v_n_3551_ = v_userName_3563_;
v_ty_3552_ = v_type_3564_;
v_bi_3553_ = v_bi_3565_;
goto v___jp_3550_;
}
else
{
lean_object* v_userName_3566_; lean_object* v_type_3567_; lean_object* v_value_3568_; uint8_t v_nondep_3569_; uint8_t v___y_3576_; 
v_userName_3566_ = lean_ctor_get(v_val_3562_, 2);
lean_inc(v_userName_3566_);
v_type_3567_ = lean_ctor_get(v_val_3562_, 3);
lean_inc_ref(v_type_3567_);
v_value_3568_ = lean_ctor_get(v_val_3562_, 4);
lean_inc_ref(v_value_3568_);
v_nondep_3569_ = lean_ctor_get_uint8(v_val_3562_, sizeof(void*)*5);
lean_dec_ref(v_val_3562_);
if (v_nondep_3569_ == 0)
{
v___y_3576_ = v_nondep_3569_;
goto v___jp_3575_;
}
else
{
if (v_generalizeNondepLet_3543_ == 0)
{
v___y_3576_ = v_generalizeNondepLet_3543_;
goto v___jp_3575_;
}
else
{
uint8_t v___x_3580_; 
lean_dec_ref(v_value_3568_);
v___x_3580_ = 0;
v_n_3551_ = v_userName_3566_;
v_ty_3552_ = v_type_3567_;
v_bi_3553_ = v___x_3580_;
goto v___jp_3550_;
}
}
v___jp_3570_:
{
lean_object* v_ty_3571_; lean_object* v_val_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_ty_3571_ = lean_expr_abstract_range(v_type_3567_, v_n_3549_, v_xs_3540_);
lean_dec_ref(v_type_3567_);
v_val_3572_ = lean_expr_abstract_range(v_value_3568_, v_n_3549_, v_xs_3540_);
lean_dec_ref(v_value_3568_);
v___x_3573_ = l_Lean_Expr_letE___override(v_userName_3566_, v_ty_3571_, v_val_3572_, v_x_3545_, v_nondep_3569_);
v___x_3574_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3540_, v_lctx_3541_, v_usedLetOnly_3542_, v_generalizeNondepLet_3543_, v_n_3549_, v___x_3573_);
return v___x_3574_;
}
v___jp_3575_:
{
if (v_usedLetOnly_3542_ == 0)
{
goto v___jp_3570_;
}
else
{
if (v___y_3576_ == 0)
{
uint8_t v___x_3577_; 
v___x_3577_ = lean_expr_has_loose_bvar(v_x_3545_, v_zero_3546_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
lean_dec_ref(v_value_3568_);
lean_dec_ref(v_type_3567_);
lean_dec(v_userName_3566_);
v___x_3578_ = lean_expr_lower_loose_bvars(v_x_3545_, v_one_3548_, v_one_3548_);
lean_dec_ref(v_x_3545_);
v___x_3579_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3540_, v_lctx_3541_, v_usedLetOnly_3542_, v_generalizeNondepLet_3543_, v_n_3549_, v___x_3578_);
return v___x_3579_;
}
else
{
goto v___jp_3570_;
}
}
else
{
goto v___jp_3570_;
}
}
}
}
}
v___jp_3550_:
{
lean_object* v_ty_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v_ty_3554_ = lean_expr_abstract_range(v_ty_3552_, v_n_3549_, v_xs_3540_);
lean_dec_ref(v_ty_3552_);
v___x_3555_ = l_Lean_mkForall(v_n_3551_, v_bi_3553_, v_ty_3554_, v_x_3545_);
v___x_3556_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3540_, v_lctx_3541_, v_usedLetOnly_3542_, v_generalizeNondepLet_3543_, v_n_3549_, v___x_3555_);
return v___x_3556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3581_, lean_object* v_lctx_3582_, lean_object* v_usedLetOnly_3583_, lean_object* v_generalizeNondepLet_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_){
_start:
{
uint8_t v_usedLetOnly_boxed_3587_; uint8_t v_generalizeNondepLet_boxed_3588_; lean_object* v_res_3589_; 
v_usedLetOnly_boxed_3587_ = lean_unbox(v_usedLetOnly_3583_);
v_generalizeNondepLet_boxed_3588_ = lean_unbox(v_generalizeNondepLet_3584_);
v_res_3589_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3581_, v_lctx_3582_, v_usedLetOnly_boxed_3587_, v_generalizeNondepLet_boxed_3588_, v_x_3585_, v_x_3586_);
lean_dec(v_x_3585_);
lean_dec_ref(v_xs_3581_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3590_, lean_object* v_xs_3591_, lean_object* v_b_3592_, uint8_t v_usedLetOnly_3593_, uint8_t v_generalizeNondepLet_3594_){
_start:
{
lean_object* v_b_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_b_3595_ = lean_expr_abstract(v_b_3592_, v_xs_3591_);
v___x_3596_ = lean_array_get_size(v_xs_3591_);
v___x_3597_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3591_, v_lctx_3590_, v_usedLetOnly_3593_, v_generalizeNondepLet_3594_, v___x_3596_, v_b_3595_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3598_, lean_object* v_xs_3599_, lean_object* v_b_3600_, lean_object* v_usedLetOnly_3601_, lean_object* v_generalizeNondepLet_3602_){
_start:
{
uint8_t v_usedLetOnly_boxed_3603_; uint8_t v_generalizeNondepLet_boxed_3604_; lean_object* v_res_3605_; 
v_usedLetOnly_boxed_3603_ = lean_unbox(v_usedLetOnly_3601_);
v_generalizeNondepLet_boxed_3604_ = lean_unbox(v_generalizeNondepLet_3602_);
v_res_3605_ = l_Lean_LocalContext_mkForall(v_lctx_3598_, v_xs_3599_, v_b_3600_, v_usedLetOnly_boxed_3603_, v_generalizeNondepLet_boxed_3604_);
lean_dec_ref(v_b_3600_);
lean_dec_ref(v_xs_3599_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3606_, lean_object* v_p_3607_, lean_object* v_d_3608_){
_start:
{
if (lean_obj_tag(v_d_3608_) == 0)
{
uint8_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_dec(v_p_3607_);
v___x_3609_ = 0;
v___x_3610_ = lean_box(v___x_3609_);
v___x_3611_ = lean_apply_2(v_toPure_3606_, lean_box(0), v___x_3610_);
return v___x_3611_;
}
else
{
lean_object* v_val_3612_; lean_object* v___x_3613_; 
lean_dec(v_toPure_3606_);
v_val_3612_ = lean_ctor_get(v_d_3608_, 0);
lean_inc(v_val_3612_);
lean_dec_ref(v_d_3608_);
v___x_3613_ = lean_apply_1(v_p_3607_, v_val_3612_);
return v___x_3613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3614_, lean_object* v_lctx_3615_, lean_object* v_p_3616_){
_start:
{
lean_object* v_toApplicative_3617_; lean_object* v_decls_3618_; lean_object* v_toPure_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; 
v_toApplicative_3617_ = lean_ctor_get(v_inst_3614_, 0);
v_decls_3618_ = lean_ctor_get(v_lctx_3615_, 1);
lean_inc_ref(v_decls_3618_);
lean_dec_ref(v_lctx_3615_);
v_toPure_3619_ = lean_ctor_get(v_toApplicative_3617_, 1);
lean_inc(v_toPure_3619_);
v___f_3620_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3620_, 0, v_toPure_3619_);
lean_closure_set(v___f_3620_, 1, v_p_3616_);
v___x_3621_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3614_, v_decls_3618_, v___f_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3622_, lean_object* v_inst_3623_, lean_object* v_lctx_3624_, lean_object* v_p_3625_){
_start:
{
lean_object* v_toApplicative_3626_; lean_object* v_decls_3627_; lean_object* v_toPure_3628_; lean_object* v___f_3629_; lean_object* v___x_3630_; 
v_toApplicative_3626_ = lean_ctor_get(v_inst_3623_, 0);
v_decls_3627_ = lean_ctor_get(v_lctx_3624_, 1);
lean_inc_ref(v_decls_3627_);
lean_dec_ref(v_lctx_3624_);
v_toPure_3628_ = lean_ctor_get(v_toApplicative_3626_, 1);
lean_inc(v_toPure_3628_);
v___f_3629_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3629_, 0, v_toPure_3628_);
lean_closure_set(v___f_3629_, 1, v_p_3625_);
v___x_3630_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3623_, v_decls_3627_, v___f_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3631_, uint8_t v_b_3632_){
_start:
{
if (v_b_3632_ == 0)
{
uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = 1;
v___x_3634_ = lean_box(v___x_3633_);
v___x_3635_ = lean_apply_2(v_toPure_3631_, lean_box(0), v___x_3634_);
return v___x_3635_;
}
else
{
uint8_t v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = 0;
v___x_3637_ = lean_box(v___x_3636_);
v___x_3638_ = lean_apply_2(v_toPure_3631_, lean_box(0), v___x_3637_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3639_, lean_object* v_b_3640_){
_start:
{
uint8_t v_b_boxed_3641_; lean_object* v_res_3642_; 
v_b_boxed_3641_ = lean_unbox(v_b_3640_);
v_res_3642_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3639_, v_b_boxed_3641_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3643_, lean_object* v_toBind_3644_, lean_object* v___f_3645_, lean_object* v_p_3646_, lean_object* v_v_3647_){
_start:
{
if (lean_obj_tag(v_v_3647_) == 0)
{
uint8_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec(v_p_3646_);
v___x_3648_ = 1;
v___x_3649_ = lean_box(v___x_3648_);
v___x_3650_ = lean_apply_2(v_toPure_3643_, lean_box(0), v___x_3649_);
v___x_3651_ = lean_apply_4(v_toBind_3644_, lean_box(0), lean_box(0), v___x_3650_, v___f_3645_);
return v___x_3651_;
}
else
{
lean_object* v_val_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_dec(v_toPure_3643_);
v_val_3652_ = lean_ctor_get(v_v_3647_, 0);
lean_inc(v_val_3652_);
lean_dec_ref(v_v_3647_);
v___x_3653_ = lean_apply_1(v_p_3646_, v_val_3652_);
v___x_3654_ = lean_apply_4(v_toBind_3644_, lean_box(0), lean_box(0), v___x_3653_, v___f_3645_);
return v___x_3654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3655_, lean_object* v_lctx_3656_, lean_object* v_p_3657_){
_start:
{
lean_object* v_toApplicative_3658_; lean_object* v_decls_3659_; lean_object* v_toBind_3660_; lean_object* v_toPure_3661_; lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v_toApplicative_3658_ = lean_ctor_get(v_inst_3655_, 0);
v_decls_3659_ = lean_ctor_get(v_lctx_3656_, 1);
lean_inc_ref(v_decls_3659_);
lean_dec_ref(v_lctx_3656_);
v_toBind_3660_ = lean_ctor_get(v_inst_3655_, 1);
lean_inc_n(v_toBind_3660_, 2);
v_toPure_3661_ = lean_ctor_get(v_toApplicative_3658_, 1);
lean_inc_n(v_toPure_3661_, 2);
v___f_3662_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3662_, 0, v_toPure_3661_);
lean_inc_ref(v___f_3662_);
v___f_3663_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3663_, 0, v_toPure_3661_);
lean_closure_set(v___f_3663_, 1, v_toBind_3660_);
lean_closure_set(v___f_3663_, 2, v___f_3662_);
lean_closure_set(v___f_3663_, 3, v_p_3657_);
v___x_3664_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3655_, v_decls_3659_, v___f_3663_);
v___x_3665_ = lean_apply_4(v_toBind_3660_, lean_box(0), lean_box(0), v___x_3664_, v___f_3662_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3666_, lean_object* v_inst_3667_, lean_object* v_lctx_3668_, lean_object* v_p_3669_){
_start:
{
lean_object* v_toApplicative_3670_; lean_object* v_decls_3671_; lean_object* v_toBind_3672_; lean_object* v_toPure_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_toApplicative_3670_ = lean_ctor_get(v_inst_3667_, 0);
v_decls_3671_ = lean_ctor_get(v_lctx_3668_, 1);
lean_inc_ref(v_decls_3671_);
lean_dec_ref(v_lctx_3668_);
v_toBind_3672_ = lean_ctor_get(v_inst_3667_, 1);
lean_inc_n(v_toBind_3672_, 2);
v_toPure_3673_ = lean_ctor_get(v_toApplicative_3670_, 1);
lean_inc_n(v_toPure_3673_, 2);
v___f_3674_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3674_, 0, v_toPure_3673_);
lean_inc_ref(v___f_3674_);
v___f_3675_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3675_, 0, v_toPure_3673_);
lean_closure_set(v___f_3675_, 1, v_toBind_3672_);
lean_closure_set(v___f_3675_, 2, v___f_3674_);
lean_closure_set(v___f_3675_, 3, v_p_3669_);
v___x_3676_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3667_, v_decls_3671_, v___f_3675_);
v___x_3677_ = lean_apply_4(v_toBind_3672_, lean_box(0), lean_box(0), v___x_3676_, v___f_3674_);
return v___x_3677_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3678_, lean_object* v_d_3679_){
_start:
{
if (lean_obj_tag(v_d_3679_) == 0)
{
uint8_t v___x_3680_; 
lean_dec_ref(v_p_3678_);
v___x_3680_ = 0;
return v___x_3680_;
}
else
{
lean_object* v_val_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v_val_3681_ = lean_ctor_get(v_d_3679_, 0);
lean_inc(v_val_3681_);
lean_dec_ref(v_d_3679_);
v___x_3682_ = lean_apply_1(v_p_3678_, v_val_3681_);
v___x_3683_ = lean_unbox(v___x_3682_);
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3684_, lean_object* v_d_3685_){
_start:
{
uint8_t v_res_3686_; lean_object* v_r_3687_; 
v_res_3686_ = l_Lean_LocalContext_any___lam__0(v_p_3684_, v_d_3685_);
v_r_3687_ = lean_box(v_res_3686_);
return v_r_3687_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3688_, lean_object* v_p_3689_){
_start:
{
lean_object* v___x_3690_; lean_object* v_decls_3691_; lean_object* v___f_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v___x_3690_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3691_ = lean_ctor_get(v_lctx_3688_, 1);
lean_inc_ref(v_decls_3691_);
lean_dec_ref(v_lctx_3688_);
v___f_3692_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3692_, 0, v_p_3689_);
v___x_3693_ = l_Lean_PersistentArray_anyM___redArg(v___x_3690_, v_decls_3691_, v___f_3692_);
v___x_3694_ = lean_unbox(v___x_3693_);
lean_dec(v___x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3695_, lean_object* v_p_3696_){
_start:
{
uint8_t v_res_3697_; lean_object* v_r_3698_; 
v_res_3697_ = l_Lean_LocalContext_any(v_lctx_3695_, v_p_3696_);
v_r_3698_ = lean_box(v_res_3697_);
return v_r_3698_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3699_, lean_object* v_v_3700_){
_start:
{
if (lean_obj_tag(v_v_3700_) == 0)
{
uint8_t v___x_3701_; 
lean_dec_ref(v_p_3699_);
v___x_3701_ = 0;
return v___x_3701_;
}
else
{
lean_object* v_val_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v_val_3702_ = lean_ctor_get(v_v_3700_, 0);
lean_inc(v_val_3702_);
lean_dec_ref(v_v_3700_);
v___x_3703_ = lean_apply_1(v_p_3699_, v_val_3702_);
v___x_3704_ = lean_unbox(v___x_3703_);
if (v___x_3704_ == 0)
{
uint8_t v___x_3705_; 
v___x_3705_ = 1;
return v___x_3705_;
}
else
{
uint8_t v___x_3706_; 
v___x_3706_ = 0;
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3707_, lean_object* v_v_3708_){
_start:
{
uint8_t v_res_3709_; lean_object* v_r_3710_; 
v_res_3709_ = l_Lean_LocalContext_all___lam__0(v_p_3707_, v_v_3708_);
v_r_3710_ = lean_box(v_res_3709_);
return v_r_3710_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3711_, lean_object* v_p_3712_){
_start:
{
lean_object* v___x_3713_; lean_object* v_decls_3714_; lean_object* v___f_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3713_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3714_ = lean_ctor_get(v_lctx_3711_, 1);
lean_inc_ref(v_decls_3714_);
lean_dec_ref(v_lctx_3711_);
v___f_3715_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3715_, 0, v_p_3712_);
v___x_3716_ = l_Lean_PersistentArray_anyM___redArg(v___x_3713_, v_decls_3714_, v___f_3715_);
v___x_3717_ = lean_unbox(v___x_3716_);
lean_dec(v___x_3716_);
if (v___x_3717_ == 0)
{
uint8_t v___x_3718_; 
v___x_3718_ = 1;
return v___x_3718_;
}
else
{
uint8_t v___x_3719_; 
v___x_3719_ = 0;
return v___x_3719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3720_, lean_object* v_p_3721_){
_start:
{
uint8_t v_res_3722_; lean_object* v_r_3723_; 
v_res_3722_ = l_Lean_LocalContext_all(v_lctx_3720_, v_p_3721_);
v_r_3723_ = lean_box(v_res_3722_);
return v_r_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3724_, lean_object* v_a_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v_zero_3728_; uint8_t v_isZero_3729_; 
v_zero_3728_ = lean_unsigned_to_nat(0u);
v_isZero_3729_ = lean_nat_dec_eq(v_i_3724_, v_zero_3728_);
if (v_isZero_3729_ == 1)
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
lean_dec(v_i_3724_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_a_3725_);
lean_ctor_set(v___x_3730_, 1, v___y_3726_);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
lean_ctor_set(v___x_3731_, 1, v___y_3727_);
return v___x_3731_;
}
else
{
lean_object* v_decls_3732_; lean_object* v_size_3733_; lean_object* v_one_3734_; lean_object* v_n_3735_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3752_; lean_object* v___y_3753_; uint8_t v___y_3754_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3764_; lean_object* v___x_3768_; uint8_t v___x_3769_; 
v_decls_3732_ = lean_ctor_get(v_a_3725_, 1);
v_size_3733_ = lean_ctor_get(v_decls_3732_, 2);
v_one_3734_ = lean_unsigned_to_nat(1u);
v_n_3735_ = lean_nat_sub(v_i_3724_, v_one_3734_);
lean_dec(v_i_3724_);
v___x_3768_ = lean_box(0);
v___x_3769_ = lean_nat_dec_lt(v_n_3735_, v_size_3733_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; 
v___x_3770_ = l_outOfBounds___redArg(v___x_3768_);
v___y_3764_ = v___x_3770_;
goto v___jp_3763_;
}
else
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3768_, v_decls_3732_, v_n_3735_);
v___y_3764_ = v___x_3771_;
goto v___jp_3763_;
}
v___jp_3736_:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_LocalContext_setUserName(v_a_3725_, v___y_3740_, v___y_3737_);
v_i_3724_ = v_n_3735_;
v_a_3725_ = v___x_3741_;
v___y_3726_ = v___y_3738_;
v___y_3727_ = v___y_3739_;
goto _start;
}
v___jp_3743_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v_fst_3748_; lean_object* v_snd_3749_; lean_object* v_fvarId_3750_; 
lean_inc(v___y_3745_);
v___x_3746_ = l_Lean_NameSet_insert(v___y_3726_, v___y_3745_);
v___x_3747_ = l_Lean_sanitizeName(v___y_3745_, v___y_3727_);
v_fst_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_fst_3748_);
v_snd_3749_ = lean_ctor_get(v___x_3747_, 1);
lean_inc(v_snd_3749_);
lean_dec_ref(v___x_3747_);
v_fvarId_3750_ = lean_ctor_get(v___y_3744_, 1);
lean_inc(v_fvarId_3750_);
lean_dec_ref(v___y_3744_);
v___y_3737_ = v_fst_3748_;
v___y_3738_ = v___x_3746_;
v___y_3739_ = v_snd_3749_;
v___y_3740_ = v_fvarId_3750_;
goto v___jp_3736_;
}
v___jp_3751_:
{
if (v___y_3754_ == 0)
{
lean_object* v___x_3755_; 
lean_dec_ref(v___y_3752_);
v___x_3755_ = l_Lean_NameSet_insert(v___y_3726_, v___y_3753_);
v_i_3724_ = v_n_3735_;
v___y_3726_ = v___x_3755_;
goto _start;
}
else
{
v___y_3744_ = v___y_3752_;
v___y_3745_ = v___y_3753_;
goto v___jp_3743_;
}
}
v___jp_3757_:
{
uint8_t v___x_3760_; 
v___x_3760_ = l_Lean_Name_hasMacroScopes(v___y_3759_);
if (v___x_3760_ == 0)
{
lean_object* v_userName_3761_; uint8_t v___x_3762_; 
v_userName_3761_ = lean_ctor_get(v___y_3758_, 2);
v___x_3762_ = l_Lean_NameSet_contains(v___y_3726_, v_userName_3761_);
v___y_3752_ = v___y_3758_;
v___y_3753_ = v___y_3759_;
v___y_3754_ = v___x_3762_;
goto v___jp_3751_;
}
else
{
v___y_3744_ = v___y_3758_;
v___y_3745_ = v___y_3759_;
goto v___jp_3743_;
}
}
v___jp_3763_:
{
if (lean_obj_tag(v___y_3764_) == 0)
{
v_i_3724_ = v_n_3735_;
goto _start;
}
else
{
lean_object* v_val_3766_; lean_object* v_userName_3767_; 
v_val_3766_ = lean_ctor_get(v___y_3764_, 0);
lean_inc(v_val_3766_);
lean_dec_ref(v___y_3764_);
v_userName_3767_ = lean_ctor_get(v_val_3766_, 2);
lean_inc(v_userName_3767_);
v___y_3758_ = v_val_3766_;
v___y_3759_ = v_userName_3767_;
goto v___jp_3757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v_options_3774_; uint8_t v___x_3775_; 
v_options_3774_ = lean_ctor_get(v_a_3773_, 0);
v___x_3775_ = l_Lean_getSanitizeNames(v_options_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3776_, 0, v_lctx_3772_);
lean_ctor_set(v___x_3776_, 1, v_a_3773_);
return v___x_3776_;
}
else
{
lean_object* v_decls_3777_; lean_object* v_size_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v_fst_3781_; lean_object* v_snd_3782_; lean_object* v_fst_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
v_decls_3777_ = lean_ctor_get(v_lctx_3772_, 1);
v_size_3778_ = lean_ctor_get(v_decls_3777_, 2);
lean_inc(v_size_3778_);
v___x_3779_ = l_Lean_NameSet_empty;
v___x_3780_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3778_, v_lctx_3772_, v___x_3779_, v_a_3773_);
v_fst_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_fst_3781_);
v_snd_3782_ = lean_ctor_get(v___x_3780_, 1);
lean_inc(v_snd_3782_);
lean_dec_ref(v___x_3780_);
v_fst_3783_ = lean_ctor_get(v_fst_3781_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_fst_3781_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; 
v_unused_3791_ = lean_ctor_get(v_fst_3781_, 1);
lean_dec(v_unused_3791_);
v___x_3785_ = v_fst_3781_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_fst_3783_);
lean_dec(v_fst_3781_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 1, v_snd_3782_);
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_fst_3783_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_snd_3782_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3792_, lean_object* v_i_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3793_, v_a_3795_, v___y_3796_, v___y_3797_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3799_, lean_object* v_i_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3799_, v_i_3800_, v_a_3801_, v_a_3802_, v___y_3803_, v___y_3804_);
lean_dec(v_n_3799_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3806_, lean_object* v_fvarId_3807_){
_start:
{
lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___x_3820_; 
lean_inc_ref(v_lctx_3806_);
v___x_3820_ = lean_local_ctx_find(v_lctx_3806_, v_fvarId_3807_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v___x_3821_; 
lean_dec_ref(v_lctx_3806_);
v___x_3821_ = lean_box(0);
return v___x_3821_;
}
else
{
lean_object* v_val_3822_; lean_object* v___y_3824_; lean_object* v_userName_3829_; 
v_val_3822_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_val_3822_);
lean_dec_ref(v___x_3820_);
v_userName_3829_ = lean_ctor_get(v_val_3822_, 2);
lean_inc(v_userName_3829_);
v___y_3824_ = v_userName_3829_;
goto v___jp_3823_;
v___jp_3823_:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3806_, v___y_3824_);
lean_dec_ref(v_lctx_3806_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v___x_3826_; 
lean_dec(v___y_3824_);
lean_dec(v_val_3822_);
v___x_3826_ = lean_box(0);
return v___x_3826_;
}
else
{
lean_object* v_val_3827_; lean_object* v_fvarId_3828_; 
v_val_3827_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_val_3827_);
lean_dec_ref(v___x_3825_);
v_fvarId_3828_ = lean_ctor_get(v_val_3822_, 1);
lean_inc(v_fvarId_3828_);
lean_dec(v_val_3822_);
v___y_3816_ = v___y_3824_;
v___y_3817_ = v_val_3827_;
v___y_3818_ = v_fvarId_3828_;
goto v___jp_3815_;
}
}
}
v___jp_3808_:
{
uint8_t v___x_3812_; 
v___x_3812_ = l_Lean_instBEqFVarId_beq(v___y_3809_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec(v___y_3809_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; 
lean_dec(v___y_3810_);
v___x_3813_ = lean_box(0);
return v___x_3813_;
}
else
{
lean_object* v___x_3814_; 
v___x_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___y_3810_);
return v___x_3814_;
}
}
v___jp_3815_:
{
lean_object* v_fvarId_3819_; 
v_fvarId_3819_ = lean_ctor_get(v___y_3817_, 1);
lean_inc(v_fvarId_3819_);
lean_dec_ref(v___y_3817_);
v___y_3809_ = v___y_3818_;
v___y_3810_ = v___y_3816_;
v___y_3811_ = v_fvarId_3819_;
goto v___jp_3808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3830_, size_t v_i_3831_, lean_object* v_bs_3832_){
_start:
{
uint8_t v___x_3833_; 
v___x_3833_ = lean_usize_dec_lt(v_i_3831_, v_sz_3830_);
if (v___x_3833_ == 0)
{
return v_bs_3832_;
}
else
{
lean_object* v_v_3834_; lean_object* v_snd_3835_; lean_object* v___x_3836_; lean_object* v_bs_x27_3837_; size_t v___x_3838_; size_t v___x_3839_; lean_object* v___x_3840_; 
v_v_3834_ = lean_array_uget_borrowed(v_bs_3832_, v_i_3831_);
v_snd_3835_ = lean_ctor_get(v_v_3834_, 1);
lean_inc(v_snd_3835_);
v___x_3836_ = lean_unsigned_to_nat(0u);
v_bs_x27_3837_ = lean_array_uset(v_bs_3832_, v_i_3831_, v___x_3836_);
v___x_3838_ = ((size_t)1ULL);
v___x_3839_ = lean_usize_add(v_i_3831_, v___x_3838_);
v___x_3840_ = lean_array_uset(v_bs_x27_3837_, v_i_3831_, v_snd_3835_);
v_i_3831_ = v___x_3839_;
v_bs_3832_ = v___x_3840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3842_, lean_object* v_i_3843_, lean_object* v_bs_3844_){
_start:
{
size_t v_sz_boxed_3845_; size_t v_i_boxed_3846_; lean_object* v_res_3847_; 
v_sz_boxed_3845_ = lean_unbox_usize(v_sz_3842_);
lean_dec(v_sz_3842_);
v_i_boxed_3846_ = lean_unbox_usize(v_i_3843_);
lean_dec(v_i_3843_);
v_res_3847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3845_, v_i_boxed_3846_, v_bs_3844_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3848_, size_t v_sz_3849_, size_t v_i_3850_, lean_object* v_bs_3851_){
_start:
{
uint8_t v___x_3852_; 
v___x_3852_ = lean_usize_dec_lt(v_i_3850_, v_sz_3849_);
if (v___x_3852_ == 0)
{
lean_dec_ref(v_lctx_3848_);
return v_bs_3851_;
}
else
{
lean_object* v_fvarIdToDecl_3853_; lean_object* v_v_3854_; lean_object* v___x_3855_; lean_object* v_bs_x27_3856_; lean_object* v___y_3858_; lean_object* v___x_3863_; 
v_fvarIdToDecl_3853_ = lean_ctor_get(v_lctx_3848_, 0);
v_v_3854_ = lean_array_uget(v_bs_3851_, v_i_3850_);
v___x_3855_ = lean_unsigned_to_nat(0u);
v_bs_x27_3856_ = lean_array_uset(v_bs_3851_, v_i_3850_, v___x_3855_);
lean_inc_ref(v_fvarIdToDecl_3853_);
v___x_3863_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3853_, v_v_3854_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3855_);
lean_ctor_set(v___x_3864_, 1, v_v_3854_);
v___y_3858_ = v___x_3864_;
goto v___jp_3857_;
}
else
{
lean_object* v_val_3865_; lean_object* v_index_3866_; lean_object* v___x_3867_; 
v_val_3865_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_val_3865_);
lean_dec_ref(v___x_3863_);
v_index_3866_ = lean_ctor_get(v_val_3865_, 0);
lean_inc(v_index_3866_);
lean_dec(v_val_3865_);
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v_index_3866_);
lean_ctor_set(v___x_3867_, 1, v_v_3854_);
v___y_3858_ = v___x_3867_;
goto v___jp_3857_;
}
v___jp_3857_:
{
size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = ((size_t)1ULL);
v___x_3860_ = lean_usize_add(v_i_3850_, v___x_3859_);
v___x_3861_ = lean_array_uset(v_bs_x27_3856_, v_i_3850_, v___y_3858_);
v_i_3850_ = v___x_3860_;
v_bs_3851_ = v___x_3861_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3868_, lean_object* v_sz_3869_, lean_object* v_i_3870_, lean_object* v_bs_3871_){
_start:
{
size_t v_sz_boxed_3872_; size_t v_i_boxed_3873_; lean_object* v_res_3874_; 
v_sz_boxed_3872_ = lean_unbox_usize(v_sz_3869_);
lean_dec(v_sz_3869_);
v_i_boxed_3873_ = lean_unbox_usize(v_i_3870_);
lean_dec(v_i_3870_);
v_res_3874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3868_, v_sz_boxed_3872_, v_i_boxed_3873_, v_bs_3871_);
return v_res_3874_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3875_, lean_object* v_i_3876_){
_start:
{
lean_object* v_fst_3877_; lean_object* v_fst_3878_; uint8_t v___x_3879_; 
v_fst_3877_ = lean_ctor_get(v_h_3875_, 0);
v_fst_3878_ = lean_ctor_get(v_i_3876_, 0);
v___x_3879_ = lean_nat_dec_lt(v_fst_3877_, v_fst_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3880_, lean_object* v_i_3881_){
_start:
{
uint8_t v_res_3882_; lean_object* v_r_3883_; 
v_res_3882_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3880_, v_i_3881_);
lean_dec_ref(v_i_3881_);
lean_dec_ref(v_h_3880_);
v_r_3883_ = lean_box(v_res_3882_);
return v_r_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_as_3885_, lean_object* v_lo_3886_, lean_object* v_hi_3887_){
_start:
{
uint8_t v___x_3888_; 
v___x_3888_ = lean_nat_dec_lt(v_lo_3886_, v_hi_3887_);
if (v___x_3888_ == 0)
{
lean_dec(v_lo_3886_);
return v_as_3885_;
}
else
{
lean_object* v___f_3889_; lean_object* v___x_3890_; lean_object* v_fst_3891_; lean_object* v_snd_3892_; uint8_t v___x_3893_; 
v___f_3889_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___closed__0));
lean_inc(v_lo_3886_);
v___x_3890_ = l_Array_qpartition___redArg(v_as_3885_, v___f_3889_, v_lo_3886_, v_hi_3887_);
v_fst_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_fst_3891_);
v_snd_3892_ = lean_ctor_get(v___x_3890_, 1);
lean_inc(v_snd_3892_);
lean_dec_ref(v___x_3890_);
v___x_3893_ = lean_nat_dec_le(v_hi_3887_, v_fst_3891_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_snd_3892_, v_lo_3886_, v_fst_3891_);
v___x_3895_ = lean_unsigned_to_nat(1u);
v___x_3896_ = lean_nat_add(v_fst_3891_, v___x_3895_);
lean_dec(v_fst_3891_);
v_as_3885_ = v___x_3894_;
v_lo_3886_ = v___x_3896_;
goto _start;
}
else
{
lean_dec(v_fst_3891_);
lean_dec(v_lo_3886_);
return v_snd_3892_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_as_3898_, lean_object* v_lo_3899_, lean_object* v_hi_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_as_3898_, v_lo_3899_, v_hi_3900_);
lean_dec(v_hi_3900_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3902_, lean_object* v_hyps_3903_){
_start:
{
lean_object* v___y_3905_; size_t v_sz_3909_; size_t v___x_3910_; lean_object* v_hyps_3911_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___x_3916_; lean_object* v___x_3917_; uint8_t v___x_3918_; 
v_sz_3909_ = lean_array_size(v_hyps_3903_);
v___x_3910_ = ((size_t)0ULL);
v_hyps_3911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3902_, v_sz_3909_, v___x_3910_, v_hyps_3903_);
v___x_3916_ = lean_array_get_size(v_hyps_3911_);
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = lean_nat_dec_eq(v___x_3916_, v___x_3917_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___y_3922_; uint8_t v___x_3924_; 
v___x_3919_ = lean_unsigned_to_nat(1u);
v___x_3920_ = lean_nat_sub(v___x_3916_, v___x_3919_);
v___x_3924_ = lean_nat_dec_le(v___x_3917_, v___x_3920_);
if (v___x_3924_ == 0)
{
lean_inc(v___x_3920_);
v___y_3922_ = v___x_3920_;
goto v___jp_3921_;
}
else
{
v___y_3922_ = v___x_3917_;
goto v___jp_3921_;
}
v___jp_3921_:
{
uint8_t v___x_3923_; 
v___x_3923_ = lean_nat_dec_le(v___y_3922_, v___x_3920_);
if (v___x_3923_ == 0)
{
lean_dec(v___x_3920_);
lean_inc(v___y_3922_);
v___y_3913_ = v___y_3922_;
v___y_3914_ = v___y_3922_;
goto v___jp_3912_;
}
else
{
v___y_3913_ = v___y_3922_;
v___y_3914_ = v___x_3920_;
goto v___jp_3912_;
}
}
}
else
{
v___y_3905_ = v_hyps_3911_;
goto v___jp_3904_;
}
v___jp_3904_:
{
size_t v_sz_3906_; size_t v___x_3907_; lean_object* v___x_3908_; 
v_sz_3906_ = lean_array_size(v___y_3905_);
v___x_3907_ = ((size_t)0ULL);
v___x_3908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3906_, v___x_3907_, v___y_3905_);
return v___x_3908_;
}
v___jp_3912_:
{
lean_object* v___x_3915_; 
v___x_3915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_hyps_3911_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
v___y_3905_ = v___x_3915_;
goto v___jp_3904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_3925_, lean_object* v_as_3926_, lean_object* v_lo_3927_, lean_object* v_hi_3928_, lean_object* v_w_3929_, lean_object* v_hlo_3930_, lean_object* v_hhi_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_as_3926_, v_lo_3927_, v_hi_3928_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_3933_, lean_object* v_as_3934_, lean_object* v_lo_3935_, lean_object* v_hi_3936_, lean_object* v_w_3937_, lean_object* v_hlo_3938_, lean_object* v_hhi_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_3933_, v_as_3934_, v_lo_3935_, v_hi_3936_, v_w_3937_, v_hlo_3938_, v_hhi_3939_);
lean_dec(v_hi_3936_);
lean_dec(v_n_3933_);
return v_res_3940_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_3941_, lean_object* v_x_3942_){
_start:
{
if (lean_obj_tag(v_x_3942_) == 0)
{
uint8_t v___x_3943_; 
v___x_3943_ = 0;
return v___x_3943_;
}
else
{
lean_object* v_key_3944_; lean_object* v_tail_3945_; uint8_t v___x_3946_; 
v_key_3944_ = lean_ctor_get(v_x_3942_, 0);
v_tail_3945_ = lean_ctor_get(v_x_3942_, 2);
v___x_3946_ = lean_name_eq(v_key_3944_, v_a_3941_);
if (v___x_3946_ == 0)
{
v_x_3942_ = v_tail_3945_;
goto _start;
}
else
{
return v___x_3946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_3948_, lean_object* v_x_3949_){
_start:
{
uint8_t v_res_3950_; lean_object* v_r_3951_; 
v_res_3950_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3948_, v_x_3949_);
lean_dec(v_x_3949_);
lean_dec(v_a_3948_);
v_r_3951_ = lean_box(v_res_3950_);
return v_r_3951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_3952_, lean_object* v_x_3953_){
_start:
{
if (lean_obj_tag(v_x_3953_) == 0)
{
return v_x_3953_;
}
else
{
lean_object* v_key_3954_; lean_object* v_value_3955_; lean_object* v_tail_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3965_; 
v_key_3954_ = lean_ctor_get(v_x_3953_, 0);
v_value_3955_ = lean_ctor_get(v_x_3953_, 1);
v_tail_3956_ = lean_ctor_get(v_x_3953_, 2);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_x_3953_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3958_ = v_x_3953_;
v_isShared_3959_ = v_isSharedCheck_3965_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_tail_3956_);
lean_inc(v_value_3955_);
lean_inc(v_key_3954_);
lean_dec(v_x_3953_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3965_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
uint8_t v___x_3960_; 
v___x_3960_ = lean_name_eq(v_key_3954_, v_a_3952_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3961_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3952_, v_tail_3956_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 2, v___x_3961_);
v___x_3963_ = v___x_3958_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_key_3954_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_value_3955_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v___x_3961_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
else
{
lean_del_object(v___x_3958_);
lean_dec(v_value_3955_);
lean_dec(v_key_3954_);
return v_tail_3956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_3966_, lean_object* v_x_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3966_, v_x_3967_);
lean_dec(v_a_3966_);
return v_res_3968_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3969_; uint64_t v___x_3970_; 
v___x_3969_ = lean_unsigned_to_nat(1723u);
v___x_3970_ = lean_uint64_of_nat(v___x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v_size_3973_; lean_object* v_buckets_3974_; lean_object* v___x_3975_; uint64_t v___y_3977_; 
v_size_3973_ = lean_ctor_get(v_m_3971_, 0);
v_buckets_3974_ = lean_ctor_get(v_m_3971_, 1);
v___x_3975_ = lean_array_get_size(v_buckets_3974_);
if (lean_obj_tag(v_a_3972_) == 0)
{
uint64_t v___x_4006_; 
v___x_4006_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_3977_ = v___x_4006_;
goto v___jp_3976_;
}
else
{
uint64_t v_hash_4007_; 
v_hash_4007_ = lean_ctor_get_uint64(v_a_3972_, sizeof(void*)*2);
v___y_3977_ = v_hash_4007_;
goto v___jp_3976_;
}
v___jp_3976_:
{
uint64_t v___x_3978_; uint64_t v___x_3979_; uint64_t v_fold_3980_; uint64_t v___x_3981_; uint64_t v___x_3982_; uint64_t v___x_3983_; size_t v___x_3984_; size_t v___x_3985_; size_t v___x_3986_; size_t v___x_3987_; size_t v___x_3988_; lean_object* v_bkt_3989_; uint8_t v___x_3990_; 
v___x_3978_ = 32ULL;
v___x_3979_ = lean_uint64_shift_right(v___y_3977_, v___x_3978_);
v_fold_3980_ = lean_uint64_xor(v___y_3977_, v___x_3979_);
v___x_3981_ = 16ULL;
v___x_3982_ = lean_uint64_shift_right(v_fold_3980_, v___x_3981_);
v___x_3983_ = lean_uint64_xor(v_fold_3980_, v___x_3982_);
v___x_3984_ = lean_uint64_to_usize(v___x_3983_);
v___x_3985_ = lean_usize_of_nat(v___x_3975_);
v___x_3986_ = ((size_t)1ULL);
v___x_3987_ = lean_usize_sub(v___x_3985_, v___x_3986_);
v___x_3988_ = lean_usize_land(v___x_3984_, v___x_3987_);
v_bkt_3989_ = lean_array_uget_borrowed(v_buckets_3974_, v___x_3988_);
v___x_3990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3972_, v_bkt_3989_);
if (v___x_3990_ == 0)
{
return v_m_3971_;
}
else
{
lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4003_; 
lean_inc(v_bkt_3989_);
lean_inc_ref(v_buckets_3974_);
lean_inc(v_size_3973_);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_m_3971_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; lean_object* v_unused_4005_; 
v_unused_4004_ = lean_ctor_get(v_m_3971_, 1);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v_m_3971_, 0);
lean_dec(v_unused_4005_);
v___x_3992_ = v_m_3971_;
v_isShared_3993_ = v_isSharedCheck_4003_;
goto v_resetjp_3991_;
}
else
{
lean_dec(v_m_3971_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4003_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; lean_object* v_buckets_x27_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3994_ = lean_box(0);
v_buckets_x27_3995_ = lean_array_uset(v_buckets_3974_, v___x_3988_, v___x_3994_);
v___x_3996_ = lean_unsigned_to_nat(1u);
v___x_3997_ = lean_nat_sub(v_size_3973_, v___x_3996_);
lean_dec(v_size_3973_);
v___x_3998_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3972_, v_bkt_3989_);
v___x_3999_ = lean_array_uset(v_buckets_x27_3995_, v___x_3988_, v___x_3998_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 1, v___x_3999_);
lean_ctor_set(v___x_3992_, 0, v___x_3997_);
v___x_4001_ = v___x_3992_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4008_, v_a_4009_);
lean_dec(v_a_4009_);
return v_res_4010_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_buckets_4013_; lean_object* v___x_4014_; uint64_t v___y_4016_; 
v_buckets_4013_ = lean_ctor_get(v_m_4011_, 1);
v___x_4014_ = lean_array_get_size(v_buckets_4013_);
if (lean_obj_tag(v_a_4012_) == 0)
{
uint64_t v___x_4030_; 
v___x_4030_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4016_ = v___x_4030_;
goto v___jp_4015_;
}
else
{
uint64_t v_hash_4031_; 
v_hash_4031_ = lean_ctor_get_uint64(v_a_4012_, sizeof(void*)*2);
v___y_4016_ = v_hash_4031_;
goto v___jp_4015_;
}
v___jp_4015_:
{
uint64_t v___x_4017_; uint64_t v___x_4018_; uint64_t v_fold_4019_; uint64_t v___x_4020_; uint64_t v___x_4021_; uint64_t v___x_4022_; size_t v___x_4023_; size_t v___x_4024_; size_t v___x_4025_; size_t v___x_4026_; size_t v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v___x_4017_ = 32ULL;
v___x_4018_ = lean_uint64_shift_right(v___y_4016_, v___x_4017_);
v_fold_4019_ = lean_uint64_xor(v___y_4016_, v___x_4018_);
v___x_4020_ = 16ULL;
v___x_4021_ = lean_uint64_shift_right(v_fold_4019_, v___x_4020_);
v___x_4022_ = lean_uint64_xor(v_fold_4019_, v___x_4021_);
v___x_4023_ = lean_uint64_to_usize(v___x_4022_);
v___x_4024_ = lean_usize_of_nat(v___x_4014_);
v___x_4025_ = ((size_t)1ULL);
v___x_4026_ = lean_usize_sub(v___x_4024_, v___x_4025_);
v___x_4027_ = lean_usize_land(v___x_4023_, v___x_4026_);
v___x_4028_ = lean_array_uget_borrowed(v_buckets_4013_, v___x_4027_);
v___x_4029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4012_, v___x_4028_);
return v___x_4029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4032_, lean_object* v_a_4033_){
_start:
{
uint8_t v_res_4034_; lean_object* v_r_4035_; 
v_res_4034_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4032_, v_a_4033_);
lean_dec(v_a_4033_);
lean_dec_ref(v_m_4032_);
v_r_4035_ = lean_box(v_res_4034_);
return v_r_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4036_, lean_object* v_as_4037_, size_t v_i_4038_, size_t v_stop_4039_, lean_object* v_b_4040_){
_start:
{
uint8_t v___x_4041_; 
v___x_4041_ = lean_usize_dec_eq(v_i_4038_, v_stop_4039_);
if (v___x_4041_ == 0)
{
size_t v___x_4042_; size_t v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = ((size_t)1ULL);
v___x_4043_ = lean_usize_sub(v_i_4038_, v___x_4042_);
v___x_4044_ = lean_array_uget(v_as_4037_, v___x_4043_);
if (lean_obj_tag(v___x_4044_) == 0)
{
v_i_4038_ = v___x_4043_;
goto _start;
}
else
{
lean_object* v_val_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4080_; 
v_val_4046_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4048_ = v___x_4044_;
v_isShared_4049_ = v_isSharedCheck_4080_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_val_4046_);
lean_dec(v___x_4044_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4080_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v_fst_4050_; lean_object* v_snd_4051_; lean_object* v___y_4053_; lean_object* v___y_4069_; lean_object* v_size_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_fst_4050_ = lean_ctor_get(v_b_4040_, 0);
v_snd_4051_ = lean_ctor_get(v_b_4040_, 1);
v_size_4075_ = lean_ctor_get(v_fst_4050_, 0);
v___x_4076_ = lean_unsigned_to_nat(0u);
v___x_4077_ = lean_nat_dec_eq(v_size_4075_, v___x_4076_);
if (v___x_4077_ == 0)
{
lean_object* v_index_4078_; 
v_index_4078_ = lean_ctor_get(v_val_4046_, 0);
lean_inc(v_index_4078_);
v___y_4069_ = v_index_4078_;
goto v___jp_4068_;
}
else
{
lean_object* v___x_4079_; 
lean_inc(v_snd_4051_);
lean_del_object(v___x_4048_);
lean_dec(v_val_4046_);
lean_dec_ref(v_b_4040_);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v_snd_4051_);
return v___x_4079_;
}
v___jp_4052_:
{
uint8_t v___x_4054_; 
v___x_4054_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4050_, v___y_4053_);
if (v___x_4054_ == 0)
{
lean_dec(v___y_4053_);
lean_dec(v_val_4046_);
v_i_4038_ = v___x_4043_;
goto _start;
}
else
{
lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4065_; 
lean_inc(v_snd_4051_);
lean_inc(v_fst_4050_);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_b_4040_);
if (v_isSharedCheck_4065_ == 0)
{
lean_object* v_unused_4066_; lean_object* v_unused_4067_; 
v_unused_4066_ = lean_ctor_get(v_b_4040_, 1);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_b_4040_, 0);
lean_dec(v_unused_4067_);
v___x_4057_ = v_b_4040_;
v_isShared_4058_ = v_isSharedCheck_4065_;
goto v_resetjp_4056_;
}
else
{
lean_dec(v_b_4040_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4065_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4062_; 
v___x_4059_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4050_, v___y_4053_);
lean_dec(v___y_4053_);
v___x_4060_ = lean_array_push(v_snd_4051_, v_val_4046_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 1, v___x_4060_);
lean_ctor_set(v___x_4057_, 0, v___x_4059_);
v___x_4062_ = v___x_4057_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4059_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
v_i_4038_ = v___x_4043_;
v_b_4040_ = v___x_4062_;
goto _start;
}
}
}
}
v___jp_4068_:
{
uint8_t v___x_4070_; 
v___x_4070_ = lean_nat_dec_lt(v___y_4069_, v_start_4036_);
lean_dec(v___y_4069_);
if (v___x_4070_ == 0)
{
lean_object* v_userName_4071_; 
lean_del_object(v___x_4048_);
v_userName_4071_ = lean_ctor_get(v_val_4046_, 2);
lean_inc(v_userName_4071_);
v___y_4053_ = v_userName_4071_;
goto v___jp_4052_;
}
else
{
lean_object* v___x_4073_; 
lean_inc(v_snd_4051_);
lean_dec(v_val_4046_);
lean_dec_ref(v_b_4040_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set_tag(v___x_4048_, 0);
lean_ctor_set(v___x_4048_, 0, v_snd_4051_);
v___x_4073_ = v___x_4048_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_snd_4051_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
}
else
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4081_, 0, v_b_4040_);
return v___x_4081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4082_, lean_object* v_as_4083_, lean_object* v_i_4084_, lean_object* v_stop_4085_, lean_object* v_b_4086_){
_start:
{
size_t v_i_boxed_4087_; size_t v_stop_boxed_4088_; lean_object* v_res_4089_; 
v_i_boxed_4087_ = lean_unbox_usize(v_i_4084_);
lean_dec(v_i_4084_);
v_stop_boxed_4088_ = lean_unbox_usize(v_stop_4085_);
lean_dec(v_stop_4085_);
v_res_4089_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4082_, v_as_4083_, v_i_boxed_4087_, v_stop_boxed_4088_, v_b_4086_);
lean_dec_ref(v_as_4083_);
lean_dec(v_start_4082_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4090_, lean_object* v_x_4091_, lean_object* v_x_4092_){
_start:
{
if (lean_obj_tag(v_x_4091_) == 0)
{
lean_object* v_cs_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4106_; 
v_cs_4093_ = lean_ctor_get(v_x_4091_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_x_4091_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4095_ = v_x_4091_;
v_isShared_4096_ = v_isSharedCheck_4106_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_cs_4093_);
lean_dec(v_x_4091_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4106_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v___x_4097_ = lean_array_get_size(v_cs_4093_);
v___x_4098_ = lean_unsigned_to_nat(0u);
v___x_4099_ = lean_nat_dec_lt(v___x_4098_, v___x_4097_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4101_; 
lean_dec_ref(v_cs_4093_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set_tag(v___x_4095_, 1);
lean_ctor_set(v___x_4095_, 0, v_x_4092_);
v___x_4101_ = v___x_4095_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_x_4092_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
else
{
size_t v___x_4103_; size_t v___x_4104_; lean_object* v___x_4105_; 
lean_del_object(v___x_4095_);
v___x_4103_ = lean_usize_of_nat(v___x_4097_);
v___x_4104_ = ((size_t)0ULL);
v___x_4105_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4090_, v_cs_4093_, v___x_4103_, v___x_4104_, v_x_4092_);
lean_dec_ref(v_cs_4093_);
return v___x_4105_;
}
}
}
else
{
lean_object* v_vs_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4120_; 
v_vs_4107_ = lean_ctor_get(v_x_4091_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_x_4091_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4109_ = v_x_4091_;
v_isShared_4110_ = v_isSharedCheck_4120_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_vs_4107_);
lean_dec(v_x_4091_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4120_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
v___x_4111_ = lean_array_get_size(v_vs_4107_);
v___x_4112_ = lean_unsigned_to_nat(0u);
v___x_4113_ = lean_nat_dec_lt(v___x_4112_, v___x_4111_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4115_; 
lean_dec_ref(v_vs_4107_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v_x_4092_);
v___x_4115_ = v___x_4109_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_x_4092_);
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
size_t v___x_4117_; size_t v___x_4118_; lean_object* v___x_4119_; 
lean_del_object(v___x_4109_);
v___x_4117_ = lean_usize_of_nat(v___x_4111_);
v___x_4118_ = ((size_t)0ULL);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4090_, v_vs_4107_, v___x_4117_, v___x_4118_, v_x_4092_);
lean_dec_ref(v_vs_4107_);
return v___x_4119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4121_, lean_object* v_as_4122_, size_t v_i_4123_, size_t v_stop_4124_, lean_object* v_b_4125_){
_start:
{
uint8_t v___x_4126_; 
v___x_4126_ = lean_usize_dec_eq(v_i_4123_, v_stop_4124_);
if (v___x_4126_ == 0)
{
size_t v___x_4127_; size_t v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4127_ = ((size_t)1ULL);
v___x_4128_ = lean_usize_sub(v_i_4123_, v___x_4127_);
v___x_4129_ = lean_array_uget_borrowed(v_as_4122_, v___x_4128_);
lean_inc(v___x_4129_);
v___x_4130_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4121_, v___x_4129_, v_b_4125_);
if (lean_obj_tag(v___x_4130_) == 0)
{
return v___x_4130_;
}
else
{
lean_object* v_a_4131_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref(v___x_4130_);
v_i_4123_ = v___x_4128_;
v_b_4125_ = v_a_4131_;
goto _start;
}
}
else
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4133_, 0, v_b_4125_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4134_, lean_object* v_as_4135_, lean_object* v_i_4136_, lean_object* v_stop_4137_, lean_object* v_b_4138_){
_start:
{
size_t v_i_boxed_4139_; size_t v_stop_boxed_4140_; lean_object* v_res_4141_; 
v_i_boxed_4139_ = lean_unbox_usize(v_i_4136_);
lean_dec(v_i_4136_);
v_stop_boxed_4140_ = lean_unbox_usize(v_stop_4137_);
lean_dec(v_stop_4137_);
v_res_4141_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4134_, v_as_4135_, v_i_boxed_4139_, v_stop_boxed_4140_, v_b_4138_);
lean_dec_ref(v_as_4135_);
lean_dec(v_start_4134_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4142_, lean_object* v_x_4143_, lean_object* v_x_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4142_, v_x_4143_, v_x_4144_);
lean_dec(v_start_4142_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4146_, lean_object* v_t_4147_, lean_object* v_init_4148_){
_start:
{
lean_object* v_root_4149_; lean_object* v_tail_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v_root_4149_ = lean_ctor_get(v_t_4147_, 0);
lean_inc_ref(v_root_4149_);
v_tail_4150_ = lean_ctor_get(v_t_4147_, 1);
lean_inc_ref(v_tail_4150_);
lean_dec_ref(v_t_4147_);
v___x_4151_ = lean_array_get_size(v_tail_4150_);
v___x_4152_ = lean_unsigned_to_nat(0u);
v___x_4153_ = lean_nat_dec_lt(v___x_4152_, v___x_4151_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; 
lean_dec_ref(v_tail_4150_);
v___x_4154_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4146_, v_root_4149_, v_init_4148_);
return v___x_4154_;
}
else
{
size_t v___x_4155_; size_t v___x_4156_; lean_object* v___x_4157_; 
v___x_4155_ = lean_usize_of_nat(v___x_4151_);
v___x_4156_ = ((size_t)0ULL);
v___x_4157_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4146_, v_tail_4150_, v___x_4155_, v___x_4156_, v_init_4148_);
lean_dec_ref(v_tail_4150_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_dec_ref(v_root_4149_);
return v___x_4157_;
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4159_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref(v___x_4157_);
v___x_4159_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4146_, v_root_4149_, v_a_4158_);
return v___x_4159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4160_, lean_object* v_t_4161_, lean_object* v_init_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4160_, v_t_4161_, v_init_4162_);
lean_dec(v_start_4160_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4164_, lean_object* v_lctx_4165_, lean_object* v_init_4166_){
_start:
{
lean_object* v_decls_4167_; lean_object* v___x_4168_; 
v_decls_4167_ = lean_ctor_get(v_lctx_4165_, 1);
lean_inc_ref(v_decls_4167_);
lean_dec_ref(v_lctx_4165_);
v___x_4168_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4164_, v_decls_4167_, v_init_4166_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4169_, lean_object* v_lctx_4170_, lean_object* v_init_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4169_, v_lctx_4170_, v_init_4171_);
lean_dec(v_start_4169_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4175_, lean_object* v_userNames_4176_, lean_object* v_start_4177_){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4179_, 0, v_userNames_4176_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4177_, v_lctx_4175_, v___x_4179_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4182_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref(v___x_4180_);
v___x_4182_ = l_Array_reverse___redArg(v_a_4181_);
return v___x_4182_;
}
else
{
lean_object* v_a_4183_; lean_object* v_snd_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v_a_4183_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4183_);
lean_dec_ref(v___x_4180_);
v_snd_4184_ = lean_ctor_get(v_a_4183_, 1);
lean_inc(v_snd_4184_);
lean_dec(v_a_4183_);
v___x_4185_ = l_Array_reverse___redArg(v_snd_4184_);
v___x_4186_ = l_Array_reverse___redArg(v___x_4185_);
return v___x_4186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4187_, lean_object* v_userNames_4188_, lean_object* v_start_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4187_, v_userNames_4188_, v_start_4189_);
lean_dec(v_start_4189_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4191_, lean_object* v_lctx_4192_, lean_object* v_userNames_4193_, lean_object* v_start_4194_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4192_, v_userNames_4193_, v_start_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4196_, lean_object* v_lctx_4197_, lean_object* v_userNames_4198_, lean_object* v_start_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4196_, v_lctx_4197_, v_userNames_4198_, v_start_4199_);
lean_dec(v_start_4199_);
return v_res_4200_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4201_, lean_object* v_m_4202_, lean_object* v_a_4203_){
_start:
{
uint8_t v___x_4204_; 
v___x_4204_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4202_, v_a_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4205_, lean_object* v_m_4206_, lean_object* v_a_4207_){
_start:
{
uint8_t v_res_4208_; lean_object* v_r_4209_; 
v_res_4208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4205_, v_m_4206_, v_a_4207_);
lean_dec(v_a_4207_);
lean_dec_ref(v_m_4206_);
v_r_4209_ = lean_box(v_res_4208_);
return v_r_4209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4210_, lean_object* v_m_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4211_, v_a_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4214_, lean_object* v_m_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4214_, v_m_4215_, v_a_4216_);
lean_dec(v_a_4216_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4218_, lean_object* v_start_4219_, lean_object* v_lctx_4220_, lean_object* v_init_4221_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4219_, v_lctx_4220_, v_init_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4223_, lean_object* v_start_4224_, lean_object* v_lctx_4225_, lean_object* v_init_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4223_, v_start_4224_, v_lctx_4225_, v_init_4226_);
lean_dec(v_start_4224_);
return v_res_4227_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4228_, lean_object* v_a_4229_, lean_object* v_x_4230_){
_start:
{
uint8_t v___x_4231_; 
v___x_4231_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4229_, v_x_4230_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4232_, lean_object* v_a_4233_, lean_object* v_x_4234_){
_start:
{
uint8_t v_res_4235_; lean_object* v_r_4236_; 
v_res_4235_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4232_, v_a_4233_, v_x_4234_);
lean_dec(v_x_4234_);
lean_dec(v_a_4233_);
v_r_4236_ = lean_box(v_res_4235_);
return v_r_4236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4237_, lean_object* v_a_4238_, lean_object* v_x_4239_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4238_, v_x_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4241_, lean_object* v_a_4242_, lean_object* v_x_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4241_, v_a_4242_, v_x_4243_);
lean_dec(v_a_4242_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4245_, lean_object* v_start_4246_, lean_object* v_t_4247_, lean_object* v_init_4248_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4246_, v_t_4247_, v_init_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4250_, lean_object* v_start_4251_, lean_object* v_t_4252_, lean_object* v_init_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4250_, v_start_4251_, v_t_4252_, v_init_4253_);
lean_dec(v_start_4251_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4255_, lean_object* v_start_4256_, lean_object* v_x_4257_, lean_object* v_x_4258_){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4256_, v_x_4257_, v_x_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4260_, lean_object* v_start_4261_, lean_object* v_x_4262_, lean_object* v_x_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4260_, v_start_4261_, v_x_4262_, v_x_4263_);
lean_dec(v_start_4261_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4265_, lean_object* v_start_4266_, lean_object* v_as_4267_, size_t v_i_4268_, size_t v_stop_4269_, lean_object* v_b_4270_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4266_, v_as_4267_, v_i_4268_, v_stop_4269_, v_b_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4272_, lean_object* v_start_4273_, lean_object* v_as_4274_, lean_object* v_i_4275_, lean_object* v_stop_4276_, lean_object* v_b_4277_){
_start:
{
size_t v_i_boxed_4278_; size_t v_stop_boxed_4279_; lean_object* v_res_4280_; 
v_i_boxed_4278_ = lean_unbox_usize(v_i_4275_);
lean_dec(v_i_4275_);
v_stop_boxed_4279_ = lean_unbox_usize(v_stop_4276_);
lean_dec(v_stop_4276_);
v_res_4280_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4272_, v_start_4273_, v_as_4274_, v_i_boxed_4278_, v_stop_boxed_4279_, v_b_4277_);
lean_dec_ref(v_as_4274_);
lean_dec(v_start_4273_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4281_, lean_object* v_start_4282_, lean_object* v_as_4283_, size_t v_i_4284_, size_t v_stop_4285_, lean_object* v_b_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4282_, v_as_4283_, v_i_4284_, v_stop_4285_, v_b_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4288_, lean_object* v_start_4289_, lean_object* v_as_4290_, lean_object* v_i_4291_, lean_object* v_stop_4292_, lean_object* v_b_4293_){
_start:
{
size_t v_i_boxed_4294_; size_t v_stop_boxed_4295_; lean_object* v_res_4296_; 
v_i_boxed_4294_ = lean_unbox_usize(v_i_4291_);
lean_dec(v_i_4291_);
v_stop_boxed_4295_ = lean_unbox_usize(v_stop_4292_);
lean_dec(v_stop_4292_);
v_res_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4288_, v_start_4289_, v_as_4290_, v_i_boxed_4294_, v_stop_boxed_4295_, v_b_4293_);
lean_dec_ref(v_as_4290_);
lean_dec(v_start_4289_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4297_, lean_object* v_inst_4298_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = lean_apply_2(v_inst_4297_, lean_box(0), v_inst_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4300_, lean_object* v_n_4301_, lean_object* v_inst_4302_, lean_object* v_inst_4303_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = lean_apply_2(v_inst_4302_, lean_box(0), v_inst_4303_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4305_, lean_object* v_d_x3f_4306_, lean_object* v_b_4307_){
_start:
{
if (lean_obj_tag(v_d_x3f_4306_) == 0)
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4308_, 0, v_b_4307_);
v___x_4309_ = lean_apply_2(v_toPure_4305_, lean_box(0), v___x_4308_);
return v___x_4309_;
}
else
{
lean_object* v_val_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4325_; 
v_val_4310_ = lean_ctor_get(v_d_x3f_4306_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v_d_x3f_4306_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4312_ = v_d_x3f_4306_;
v_isShared_4313_ = v_isSharedCheck_4325_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_val_4310_);
lean_dec(v_d_x3f_4306_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4325_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
uint8_t v___x_4314_; 
v___x_4314_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4310_);
if (v___x_4314_ == 0)
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
v___x_4315_ = l_Lean_LocalDecl_toExpr(v_val_4310_);
v___x_4316_ = lean_array_push(v_b_4307_, v___x_4315_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 0, v___x_4316_);
v___x_4318_ = v___x_4312_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
lean_object* v___x_4319_; 
v___x_4319_ = lean_apply_2(v_toPure_4305_, lean_box(0), v___x_4318_);
return v___x_4319_;
}
}
else
{
lean_object* v___x_4322_; 
lean_dec(v_val_4310_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 0, v_b_4307_);
v___x_4322_ = v___x_4312_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_b_4307_);
v___x_4322_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
lean_object* v___x_4323_; 
v___x_4323_ = lean_apply_2(v_toPure_4305_, lean_box(0), v___x_4322_);
return v___x_4323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4326_, lean_object* v_____s_4327_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = lean_apply_2(v_toPure_4326_, lean_box(0), v_____s_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4329_, lean_object* v_hs_4330_, lean_object* v___f_4331_, lean_object* v_toBind_4332_, lean_object* v___f_4333_, lean_object* v_____do__lift_4334_){
_start:
{
lean_object* v_decls_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v_decls_4335_ = lean_ctor_get(v_____do__lift_4334_, 1);
lean_inc_ref(v_decls_4335_);
lean_dec_ref(v_____do__lift_4334_);
v___x_4336_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4329_, v_decls_4335_, v_hs_4330_, v___f_4331_);
v___x_4337_ = lean_apply_4(v_toBind_4332_, lean_box(0), lean_box(0), v___x_4336_, v___f_4333_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4340_, lean_object* v_inst_4341_){
_start:
{
lean_object* v_toApplicative_4342_; lean_object* v_toBind_4343_; lean_object* v_toPure_4344_; lean_object* v_hs_4345_; lean_object* v___f_4346_; lean_object* v___f_4347_; lean_object* v___f_4348_; lean_object* v___x_4349_; 
v_toApplicative_4342_ = lean_ctor_get(v_inst_4340_, 0);
v_toBind_4343_ = lean_ctor_get(v_inst_4340_, 1);
lean_inc_n(v_toBind_4343_, 2);
v_toPure_4344_ = lean_ctor_get(v_toApplicative_4342_, 1);
v_hs_4345_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4344_, 2);
v___f_4346_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4346_, 0, v_toPure_4344_);
v___f_4347_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4347_, 0, v_toPure_4344_);
v___f_4348_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4348_, 0, v_inst_4340_);
lean_closure_set(v___f_4348_, 1, v_hs_4345_);
lean_closure_set(v___f_4348_, 2, v___f_4346_);
lean_closure_set(v___f_4348_, 3, v_toBind_4343_);
lean_closure_set(v___f_4348_, 4, v___f_4347_);
v___x_4349_ = lean_apply_4(v_toBind_4343_, lean_box(0), lean_box(0), v_inst_4341_, v___f_4348_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4350_, lean_object* v_inst_4351_, lean_object* v_inst_4352_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Lean_getLocalHyps___redArg(v_inst_4351_, v_inst_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4354_, lean_object* v_e_4355_, lean_object* v_d_4356_){
_start:
{
lean_object* v___y_4358_; lean_object* v_fvarId_4390_; 
v_fvarId_4390_ = lean_ctor_get(v_d_4356_, 1);
lean_inc(v_fvarId_4390_);
v___y_4358_ = v_fvarId_4390_;
goto v___jp_4357_;
v___jp_4357_:
{
uint8_t v___x_4359_; 
v___x_4359_ = l_Lean_instBEqFVarId_beq(v___y_4358_, v_fvarId_4354_);
lean_dec(v___y_4358_);
if (v___x_4359_ == 0)
{
if (lean_obj_tag(v_d_4356_) == 0)
{
lean_object* v_index_4360_; lean_object* v_fvarId_4361_; lean_object* v_userName_4362_; lean_object* v_type_4363_; uint8_t v_bi_4364_; uint8_t v_kind_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4373_; 
v_index_4360_ = lean_ctor_get(v_d_4356_, 0);
v_fvarId_4361_ = lean_ctor_get(v_d_4356_, 1);
v_userName_4362_ = lean_ctor_get(v_d_4356_, 2);
v_type_4363_ = lean_ctor_get(v_d_4356_, 3);
v_bi_4364_ = lean_ctor_get_uint8(v_d_4356_, sizeof(void*)*4);
v_kind_4365_ = lean_ctor_get_uint8(v_d_4356_, sizeof(void*)*4 + 1);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_d_4356_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4367_ = v_d_4356_;
v_isShared_4368_ = v_isSharedCheck_4373_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_type_4363_);
lean_inc(v_userName_4362_);
lean_inc(v_fvarId_4361_);
lean_inc(v_index_4360_);
lean_dec(v_d_4356_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4373_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4369_; lean_object* v___x_4371_; 
v___x_4369_ = l_Lean_Expr_replaceFVarId(v_type_4363_, v_fvarId_4354_, v_e_4355_);
lean_dec_ref(v_type_4363_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 3, v___x_4369_);
v___x_4371_ = v___x_4367_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_index_4360_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v_fvarId_4361_);
lean_ctor_set(v_reuseFailAlloc_4372_, 2, v_userName_4362_);
lean_ctor_set(v_reuseFailAlloc_4372_, 3, v___x_4369_);
lean_ctor_set_uint8(v_reuseFailAlloc_4372_, sizeof(void*)*4, v_bi_4364_);
lean_ctor_set_uint8(v_reuseFailAlloc_4372_, sizeof(void*)*4 + 1, v_kind_4365_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
else
{
lean_object* v_index_4374_; lean_object* v_fvarId_4375_; lean_object* v_userName_4376_; lean_object* v_type_4377_; lean_object* v_value_4378_; uint8_t v_nondep_4379_; uint8_t v_kind_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4389_; 
v_index_4374_ = lean_ctor_get(v_d_4356_, 0);
v_fvarId_4375_ = lean_ctor_get(v_d_4356_, 1);
v_userName_4376_ = lean_ctor_get(v_d_4356_, 2);
v_type_4377_ = lean_ctor_get(v_d_4356_, 3);
v_value_4378_ = lean_ctor_get(v_d_4356_, 4);
v_nondep_4379_ = lean_ctor_get_uint8(v_d_4356_, sizeof(void*)*5);
v_kind_4380_ = lean_ctor_get_uint8(v_d_4356_, sizeof(void*)*5 + 1);
v_isSharedCheck_4389_ = !lean_is_exclusive(v_d_4356_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4382_ = v_d_4356_;
v_isShared_4383_ = v_isSharedCheck_4389_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_value_4378_);
lean_inc(v_type_4377_);
lean_inc(v_userName_4376_);
lean_inc(v_fvarId_4375_);
lean_inc(v_index_4374_);
lean_dec(v_d_4356_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4389_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
lean_inc(v_fvarId_4354_);
v___x_4384_ = l_Lean_Expr_replaceFVarId(v_type_4377_, v_fvarId_4354_, v_e_4355_);
lean_dec_ref(v_type_4377_);
v___x_4385_ = l_Lean_Expr_replaceFVarId(v_value_4378_, v_fvarId_4354_, v_e_4355_);
lean_dec_ref(v_value_4378_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 4, v___x_4385_);
lean_ctor_set(v___x_4382_, 3, v___x_4384_);
v___x_4387_ = v___x_4382_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_index_4374_);
lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_fvarId_4375_);
lean_ctor_set(v_reuseFailAlloc_4388_, 2, v_userName_4376_);
lean_ctor_set(v_reuseFailAlloc_4388_, 3, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4388_, 4, v___x_4385_);
lean_ctor_set_uint8(v_reuseFailAlloc_4388_, sizeof(void*)*5, v_nondep_4379_);
lean_ctor_set_uint8(v_reuseFailAlloc_4388_, sizeof(void*)*5 + 1, v_kind_4380_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
else
{
lean_dec(v_fvarId_4354_);
return v_d_4356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4391_, lean_object* v_e_4392_, lean_object* v_d_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4391_, v_e_4392_, v_d_4393_);
lean_dec_ref(v_e_4392_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4395_, lean_object* v_e_4396_, lean_object* v_x_4397_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4395_, v_e_4396_, v_x_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4399_, lean_object* v_e_4400_, lean_object* v_x_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4399_, v_e_4400_, v_x_4401_);
lean_dec_ref(v_e_4400_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4403_, lean_object* v_e_4404_, size_t v_sz_4405_, size_t v_i_4406_, lean_object* v_bs_4407_){
_start:
{
uint8_t v___x_4408_; 
v___x_4408_ = lean_usize_dec_lt(v_i_4406_, v_sz_4405_);
if (v___x_4408_ == 0)
{
lean_dec(v_fvarId_4403_);
return v_bs_4407_;
}
else
{
lean_object* v_v_4409_; lean_object* v___x_4410_; lean_object* v_bs_x27_4411_; lean_object* v___y_4413_; 
v_v_4409_ = lean_array_uget(v_bs_4407_, v_i_4406_);
v___x_4410_ = lean_unsigned_to_nat(0u);
v_bs_x27_4411_ = lean_array_uset(v_bs_4407_, v_i_4406_, v___x_4410_);
if (lean_obj_tag(v_v_4409_) == 0)
{
v___y_4413_ = v_v_4409_;
goto v___jp_4412_;
}
else
{
lean_object* v_val_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4426_; 
v_val_4418_ = lean_ctor_get(v_v_4409_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_v_4409_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4420_ = v_v_4409_;
v_isShared_4421_ = v_isSharedCheck_4426_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_val_4418_);
lean_dec(v_v_4409_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4426_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4424_; 
lean_inc(v_fvarId_4403_);
v___x_4422_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4403_, v_e_4404_, v_val_4418_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4422_);
v___x_4424_ = v___x_4420_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
v___y_4413_ = v___x_4424_;
goto v___jp_4412_;
}
}
}
v___jp_4412_:
{
size_t v___x_4414_; size_t v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = ((size_t)1ULL);
v___x_4415_ = lean_usize_add(v_i_4406_, v___x_4414_);
v___x_4416_ = lean_array_uset(v_bs_x27_4411_, v_i_4406_, v___y_4413_);
v_i_4406_ = v___x_4415_;
v_bs_4407_ = v___x_4416_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4427_, lean_object* v_e_4428_, lean_object* v_sz_4429_, lean_object* v_i_4430_, lean_object* v_bs_4431_){
_start:
{
size_t v_sz_boxed_4432_; size_t v_i_boxed_4433_; lean_object* v_res_4434_; 
v_sz_boxed_4432_ = lean_unbox_usize(v_sz_4429_);
lean_dec(v_sz_4429_);
v_i_boxed_4433_ = lean_unbox_usize(v_i_4430_);
lean_dec(v_i_4430_);
v_res_4434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4427_, v_e_4428_, v_sz_boxed_4432_, v_i_boxed_4433_, v_bs_4431_);
lean_dec_ref(v_e_4428_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4435_, lean_object* v_e_4436_, size_t v_sz_4437_, size_t v_i_4438_, lean_object* v_bs_4439_){
_start:
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_usize_dec_lt(v_i_4438_, v_sz_4437_);
if (v___x_4440_ == 0)
{
lean_dec(v_fvarId_4435_);
return v_bs_4439_;
}
else
{
lean_object* v_v_4441_; lean_object* v___x_4442_; lean_object* v_bs_x27_4443_; lean_object* v___x_4444_; size_t v___x_4445_; size_t v___x_4446_; lean_object* v___x_4447_; 
v_v_4441_ = lean_array_uget(v_bs_4439_, v_i_4438_);
v___x_4442_ = lean_unsigned_to_nat(0u);
v_bs_x27_4443_ = lean_array_uset(v_bs_4439_, v_i_4438_, v___x_4442_);
lean_inc(v_fvarId_4435_);
v___x_4444_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4435_, v_e_4436_, v_v_4441_);
v___x_4445_ = ((size_t)1ULL);
v___x_4446_ = lean_usize_add(v_i_4438_, v___x_4445_);
v___x_4447_ = lean_array_uset(v_bs_x27_4443_, v_i_4438_, v___x_4444_);
v_i_4438_ = v___x_4446_;
v_bs_4439_ = v___x_4447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4449_, lean_object* v_e_4450_, lean_object* v_x_4451_){
_start:
{
if (lean_obj_tag(v_x_4451_) == 0)
{
lean_object* v_cs_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4462_; 
v_cs_4452_ = lean_ctor_get(v_x_4451_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_x_4451_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4454_ = v_x_4451_;
v_isShared_4455_ = v_isSharedCheck_4462_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_cs_4452_);
lean_dec(v_x_4451_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4462_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
size_t v_sz_4456_; size_t v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4460_; 
v_sz_4456_ = lean_array_size(v_cs_4452_);
v___x_4457_ = ((size_t)0ULL);
v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4449_, v_e_4450_, v_sz_4456_, v___x_4457_, v_cs_4452_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 0, v___x_4458_);
v___x_4460_ = v___x_4454_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4458_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
else
{
lean_object* v_vs_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4473_; 
v_vs_4463_ = lean_ctor_get(v_x_4451_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_x_4451_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4465_ = v_x_4451_;
v_isShared_4466_ = v_isSharedCheck_4473_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_vs_4463_);
lean_dec(v_x_4451_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4473_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
size_t v_sz_4467_; size_t v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4471_; 
v_sz_4467_ = lean_array_size(v_vs_4463_);
v___x_4468_ = ((size_t)0ULL);
v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4449_, v_e_4450_, v_sz_4467_, v___x_4468_, v_vs_4463_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v___x_4469_);
v___x_4471_ = v___x_4465_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4474_, lean_object* v_e_4475_, lean_object* v_x_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4474_, v_e_4475_, v_x_4476_);
lean_dec_ref(v_e_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4478_, lean_object* v_e_4479_, lean_object* v_sz_4480_, lean_object* v_i_4481_, lean_object* v_bs_4482_){
_start:
{
size_t v_sz_boxed_4483_; size_t v_i_boxed_4484_; lean_object* v_res_4485_; 
v_sz_boxed_4483_ = lean_unbox_usize(v_sz_4480_);
lean_dec(v_sz_4480_);
v_i_boxed_4484_ = lean_unbox_usize(v_i_4481_);
lean_dec(v_i_4481_);
v_res_4485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4478_, v_e_4479_, v_sz_boxed_4483_, v_i_boxed_4484_, v_bs_4482_);
lean_dec_ref(v_e_4479_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4486_, lean_object* v_e_4487_, lean_object* v_t_4488_){
_start:
{
lean_object* v_root_4489_; lean_object* v_tail_4490_; lean_object* v_size_4491_; size_t v_shift_4492_; lean_object* v_tailOff_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4504_; 
v_root_4489_ = lean_ctor_get(v_t_4488_, 0);
v_tail_4490_ = lean_ctor_get(v_t_4488_, 1);
v_size_4491_ = lean_ctor_get(v_t_4488_, 2);
v_shift_4492_ = lean_ctor_get_usize(v_t_4488_, 4);
v_tailOff_4493_ = lean_ctor_get(v_t_4488_, 3);
v_isSharedCheck_4504_ = !lean_is_exclusive(v_t_4488_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4495_ = v_t_4488_;
v_isShared_4496_ = v_isSharedCheck_4504_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_tailOff_4493_);
lean_inc(v_size_4491_);
lean_inc(v_tail_4490_);
lean_inc(v_root_4489_);
lean_dec(v_t_4488_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4504_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4497_; size_t v_sz_4498_; size_t v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4502_; 
lean_inc(v_fvarId_4486_);
v___x_4497_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4486_, v_e_4487_, v_root_4489_);
v_sz_4498_ = lean_array_size(v_tail_4490_);
v___x_4499_ = ((size_t)0ULL);
v___x_4500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4486_, v_e_4487_, v_sz_4498_, v___x_4499_, v_tail_4490_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 1, v___x_4500_);
lean_ctor_set(v___x_4495_, 0, v___x_4497_);
v___x_4502_ = v___x_4495_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4497_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4503_, 2, v_size_4491_);
lean_ctor_set(v_reuseFailAlloc_4503_, 3, v_tailOff_4493_);
lean_ctor_set_usize(v_reuseFailAlloc_4503_, 4, v_shift_4492_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4505_, lean_object* v_e_4506_, lean_object* v_t_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4505_, v_e_4506_, v_t_4507_);
lean_dec_ref(v_e_4506_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4509_, lean_object* v_x_4510_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = lean_apply_1(v_f_4509_, v_x_4510_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4512_, lean_object* v_as_4513_, lean_object* v_i_4514_, lean_object* v_acc_4515_){
_start:
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = lean_array_get_size(v_as_4513_);
v___x_4517_ = lean_nat_dec_eq(v_i_4514_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4518_ = lean_array_fget_borrowed(v_as_4513_, v_i_4514_);
lean_inc(v_f_4512_);
lean_inc(v___x_4518_);
v___x_4519_ = lean_apply_1(v_f_4512_, v___x_4518_);
v___x_4520_ = lean_unsigned_to_nat(1u);
v___x_4521_ = lean_nat_add(v_i_4514_, v___x_4520_);
lean_dec(v_i_4514_);
v___x_4522_ = lean_array_push(v_acc_4515_, v___x_4519_);
v_i_4514_ = v___x_4521_;
v_acc_4515_ = v___x_4522_;
goto _start;
}
else
{
lean_dec(v_i_4514_);
lean_dec(v_f_4512_);
return v_acc_4515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4524_, lean_object* v_as_4525_, lean_object* v_i_4526_, lean_object* v_acc_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4524_, v_as_4525_, v_i_4526_, v_acc_4527_);
lean_dec_ref(v_as_4525_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4529_, lean_object* v_as_4530_){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4531_ = lean_unsigned_to_nat(0u);
v___x_4532_ = lean_array_get_size(v_as_4530_);
v___x_4533_ = lean_mk_empty_array_with_capacity(v___x_4532_);
v___x_4534_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4529_, v_as_4530_, v___x_4531_, v___x_4533_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4535_, lean_object* v_as_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4535_, v_as_4536_);
lean_dec_ref(v_as_4536_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4538_, size_t v_sz_4539_, size_t v_i_4540_, lean_object* v_bs_4541_){
_start:
{
uint8_t v___x_4542_; 
v___x_4542_ = lean_usize_dec_lt(v_i_4540_, v_sz_4539_);
if (v___x_4542_ == 0)
{
lean_dec(v_f_4538_);
return v_bs_4541_;
}
else
{
lean_object* v_v_4543_; lean_object* v___x_4544_; lean_object* v_bs_x27_4545_; lean_object* v___y_4547_; 
v_v_4543_ = lean_array_uget(v_bs_4541_, v_i_4540_);
v___x_4544_ = lean_unsigned_to_nat(0u);
v_bs_x27_4545_ = lean_array_uset(v_bs_4541_, v_i_4540_, v___x_4544_);
switch(lean_obj_tag(v_v_4543_))
{
case 0:
{
lean_object* v_key_4552_; lean_object* v_val_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4561_; 
v_key_4552_ = lean_ctor_get(v_v_4543_, 0);
v_val_4553_ = lean_ctor_get(v_v_4543_, 1);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_v_4543_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4555_ = v_v_4543_;
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_val_4553_);
lean_inc(v_key_4552_);
lean_dec(v_v_4543_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4557_; lean_object* v___x_4559_; 
lean_inc(v_f_4538_);
v___x_4557_ = lean_apply_1(v_f_4538_, v_val_4553_);
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 1, v___x_4557_);
v___x_4559_ = v___x_4555_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_key_4552_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v___x_4557_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
v___y_4547_ = v___x_4559_;
goto v___jp_4546_;
}
}
}
case 1:
{
lean_object* v_node_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4570_; 
v_node_4562_ = lean_ctor_get(v_v_4543_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v_v_4543_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4564_ = v_v_4543_;
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_node_4562_);
lean_dec(v_v_4543_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v___x_4568_; 
lean_inc(v_f_4538_);
v___x_4566_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4538_, v_node_4562_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v___x_4566_);
v___x_4568_ = v___x_4564_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
v___y_4547_ = v___x_4568_;
goto v___jp_4546_;
}
}
}
default: 
{
lean_object* v___x_4571_; 
v___x_4571_ = lean_box(2);
v___y_4547_ = v___x_4571_;
goto v___jp_4546_;
}
}
v___jp_4546_:
{
size_t v___x_4548_; size_t v___x_4549_; lean_object* v___x_4550_; 
v___x_4548_ = ((size_t)1ULL);
v___x_4549_ = lean_usize_add(v_i_4540_, v___x_4548_);
v___x_4550_ = lean_array_uset(v_bs_x27_4545_, v_i_4540_, v___y_4547_);
v_i_4540_ = v___x_4549_;
v_bs_4541_ = v___x_4550_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4572_, lean_object* v_n_4573_){
_start:
{
if (lean_obj_tag(v_n_4573_) == 0)
{
lean_object* v_es_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4584_; 
v_es_4574_ = lean_ctor_get(v_n_4573_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v_n_4573_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4576_ = v_n_4573_;
v_isShared_4577_ = v_isSharedCheck_4584_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_es_4574_);
lean_dec(v_n_4573_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4584_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
size_t v_sz_4578_; size_t v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
v_sz_4578_ = lean_array_size(v_es_4574_);
v___x_4579_ = ((size_t)0ULL);
v___x_4580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4572_, v_sz_4578_, v___x_4579_, v_es_4574_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4580_);
v___x_4582_ = v___x_4576_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
else
{
lean_object* v_ks_4585_; lean_object* v_vs_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4594_; 
v_ks_4585_ = lean_ctor_get(v_n_4573_, 0);
v_vs_4586_ = lean_ctor_get(v_n_4573_, 1);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_n_4573_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4588_ = v_n_4573_;
v_isShared_4589_ = v_isSharedCheck_4594_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_vs_4586_);
lean_inc(v_ks_4585_);
lean_dec(v_n_4573_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4594_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v_val_4590_; lean_object* v___x_4592_; 
v_val_4590_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4572_, v_vs_4586_);
lean_dec_ref(v_vs_4586_);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 1, v_val_4590_);
v___x_4592_ = v___x_4588_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_ks_4585_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_val_4590_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4595_, lean_object* v_sz_4596_, lean_object* v_i_4597_, lean_object* v_bs_4598_){
_start:
{
size_t v_sz_boxed_4599_; size_t v_i_boxed_4600_; lean_object* v_res_4601_; 
v_sz_boxed_4599_ = lean_unbox_usize(v_sz_4596_);
lean_dec(v_sz_4596_);
v_i_boxed_4600_ = lean_unbox_usize(v_i_4597_);
lean_dec(v_i_4597_);
v_res_4601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4595_, v_sz_boxed_4599_, v_i_boxed_4600_, v_bs_4598_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4602_, lean_object* v_f_4603_){
_start:
{
lean_object* v___f_4604_; lean_object* v___x_4605_; 
v___f_4604_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4604_, 0, v_f_4603_);
v___x_4605_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4604_, v_pm_4602_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4606_, lean_object* v_e_4607_, lean_object* v_lctx_4608_){
_start:
{
lean_object* v_lctx_4609_; lean_object* v_fvarIdToDecl_4610_; lean_object* v_decls_4611_; lean_object* v_auxDeclToFullName_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4622_; 
lean_inc(v_fvarId_4606_);
v_lctx_4609_ = lean_local_ctx_erase(v_lctx_4608_, v_fvarId_4606_);
v_fvarIdToDecl_4610_ = lean_ctor_get(v_lctx_4609_, 0);
v_decls_4611_ = lean_ctor_get(v_lctx_4609_, 1);
v_auxDeclToFullName_4612_ = lean_ctor_get(v_lctx_4609_, 2);
v_isSharedCheck_4622_ = !lean_is_exclusive(v_lctx_4609_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4614_ = v_lctx_4609_;
v_isShared_4615_ = v_isSharedCheck_4622_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_auxDeclToFullName_4612_);
lean_inc(v_decls_4611_);
lean_inc(v_fvarIdToDecl_4610_);
lean_dec(v_lctx_4609_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4622_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___f_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
lean_inc_ref(v_e_4607_);
lean_inc(v_fvarId_4606_);
v___f_4616_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4616_, 0, v_fvarId_4606_);
lean_closure_set(v___f_4616_, 1, v_e_4607_);
v___x_4617_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4610_, v___f_4616_);
v___x_4618_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4606_, v_e_4607_, v_decls_4611_);
lean_dec_ref(v_e_4607_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 1, v___x_4618_);
lean_ctor_set(v___x_4614_, 0, v___x_4617_);
v___x_4620_ = v___x_4614_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4617_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v___x_4618_);
lean_ctor_set(v_reuseFailAlloc_4621_, 2, v_auxDeclToFullName_4612_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4623_, lean_object* v_00_u03c3_4624_, lean_object* v_pm_4625_, lean_object* v_f_4626_){
_start:
{
lean_object* v___x_4627_; 
v___x_4627_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4625_, v_f_4626_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4628_, lean_object* v_f_4629_){
_start:
{
lean_object* v___x_4630_; 
v___x_4630_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4629_, v_pm_4628_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4631_, lean_object* v_00_u03c3_4632_, lean_object* v_pm_4633_, lean_object* v_f_4634_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4634_, v_pm_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4636_, lean_object* v_00_u03b2_4637_, lean_object* v_00_u03c3_4638_, lean_object* v_f_4639_, lean_object* v_n_4640_){
_start:
{
lean_object* v___x_4641_; 
v___x_4641_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4639_, v_n_4640_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4642_, lean_object* v_00_u03b2_4643_, lean_object* v_00_u03c3_4644_, lean_object* v_f_4645_, size_t v_sz_4646_, size_t v_i_4647_, lean_object* v_bs_4648_){
_start:
{
lean_object* v___x_4649_; 
v___x_4649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4645_, v_sz_4646_, v_i_4647_, v_bs_4648_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4650_, lean_object* v_00_u03b2_4651_, lean_object* v_00_u03c3_4652_, lean_object* v_f_4653_, lean_object* v_sz_4654_, lean_object* v_i_4655_, lean_object* v_bs_4656_){
_start:
{
size_t v_sz_boxed_4657_; size_t v_i_boxed_4658_; lean_object* v_res_4659_; 
v_sz_boxed_4657_ = lean_unbox_usize(v_sz_4654_);
lean_dec(v_sz_4654_);
v_i_boxed_4658_ = lean_unbox_usize(v_i_4655_);
lean_dec(v_i_4655_);
v_res_4659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4650_, v_00_u03b2_4651_, v_00_u03c3_4652_, v_f_4653_, v_sz_boxed_4657_, v_i_boxed_4658_, v_bs_4656_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4660_, lean_object* v_00_u03b2_4661_, lean_object* v_f_4662_, lean_object* v_as_4663_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4662_, v_as_4663_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4665_, lean_object* v_00_u03b2_4666_, lean_object* v_f_4667_, lean_object* v_as_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4665_, v_00_u03b2_4666_, v_f_4667_, v_as_4668_);
lean_dec_ref(v_as_4668_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4670_, lean_object* v_00_u03b2_4671_, lean_object* v_f_4672_, lean_object* v_as_4673_, lean_object* v_i_4674_, lean_object* v_acc_4675_, lean_object* v_hle_4676_){
_start:
{
lean_object* v___x_4677_; 
v___x_4677_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4672_, v_as_4673_, v_i_4674_, v_acc_4675_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4678_, lean_object* v_00_u03b2_4679_, lean_object* v_f_4680_, lean_object* v_as_4681_, lean_object* v_i_4682_, lean_object* v_acc_4683_, lean_object* v_hle_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4678_, v_00_u03b2_4679_, v_f_4680_, v_as_4681_, v_i_4682_, v_acc_4683_, v_hle_4684_);
lean_dec_ref(v_as_4681_);
return v_res_4685_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLocalDeclKind_default = _init_l_Lean_instInhabitedLocalDeclKind_default();
l_Lean_instInhabitedLocalDeclKind = _init_l_Lean_instInhabitedLocalDeclKind();
l_Lean_instInhabitedLocalDecl_default = _init_l_Lean_instInhabitedLocalDecl_default();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl_default);
l_Lean_instInhabitedLocalDecl = _init_l_Lean_instInhabitedLocalDecl();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl);
l_Lean_instInhabitedLocalContext_default = _init_l_Lean_instInhabitedLocalContext_default();
lean_mark_persistent(l_Lean_instInhabitedLocalContext_default);
l_Lean_instInhabitedLocalContext = _init_l_Lean_instInhabitedLocalContext();
lean_mark_persistent(l_Lean_instInhabitedLocalContext);
l_Lean_LocalContext_empty = _init_l_Lean_LocalContext_empty();
lean_mark_persistent(l_Lean_LocalContext_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LocalContext(builtin);
}
#ifdef __cplusplus
}
#endif
