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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getSanitizeNames(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg();
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_LocalContext_mkEmpty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkEmpty___closed__0;
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_LocalDeclKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_LocalDeclKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_LocalDeclKind_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_LocalDeclKind_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_LocalDeclKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_LocalDeclKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_LocalDeclKind_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_LocalDeclKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_24_){
_start:
{
lean_inc(v_default_24_);
return v_default_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_25_);
lean_dec(v_default_25_);
return v_res_26_;
}
}
lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_default_30_){
_start:
{
lean_inc(v_default_30_);
return v_default_30_;
}
}
LEAN_EXPORT void l_Lean_LocalDeclKind_default_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_default_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_LocalDeclKind_default_elim(lean_box(0), v_t_28_, lean_box(0), v_default_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_default_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_LocalDeclKind_default_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_default_35_);
lean_dec(v_default_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_38_){
_start:
{
lean_inc(v_implDetail_38_);
return v_implDetail_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_39_);
lean_dec(v_implDetail_39_);
return v_res_40_;
}
}
lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_implDetail_44_){
_start:
{
lean_inc(v_implDetail_44_);
return v_implDetail_44_;
}
}
LEAN_EXPORT void l_Lean_LocalDeclKind_implDetail_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_implDetail_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_LocalDeclKind_implDetail_elim(lean_box(0), v_t_42_, lean_box(0), v_implDetail_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_implDetail_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_implDetail_49_);
lean_dec(v_implDetail_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_52_){
_start:
{
lean_inc(v_auxDecl_52_);
return v_auxDecl_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_53_);
lean_dec(v_auxDecl_53_);
return v_res_54_;
}
}
lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_auxDecl_58_){
_start:
{
lean_inc(v_auxDecl_58_);
return v_auxDecl_58_;
}
}
LEAN_EXPORT void l_Lean_LocalDeclKind_auxDecl_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_auxDecl_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_LocalDeclKind_auxDecl_elim(lean_box(0), v_t_56_, lean_box(0), v_auxDecl_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_auxDecl_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_auxDecl_63_);
lean_dec(v_auxDecl_63_);
return v_res_65_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_to_int(v___x_79_);
return v___x_80_;
}
}
lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_81_, lean_object* v_prec_82_){
_start:
{
lean_object* v___y_84_; lean_object* v___y_91_; lean_object* v___y_98_; 
switch(v_x_81_)
{
case 0:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_82_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_84_ = v___x_106_;
goto v___jp_83_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_84_ = v___x_107_;
goto v___jp_83_;
}
}
case 1:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1024u);
v___x_109_ = lean_nat_dec_le(v___x_108_, v_prec_82_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_91_ = v___x_110_;
goto v___jp_90_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_91_ = v___x_111_;
goto v___jp_90_;
}
}
default: 
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(1024u);
v___x_113_ = lean_nat_dec_le(v___x_112_, v_prec_82_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_98_ = v___x_114_;
goto v___jp_97_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_98_ = v___x_115_;
goto v___jp_97_;
}
}
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_85_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___y_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = 0;
v___x_88_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = l_Repr_addAppParen(v___x_88_, v_prec_82_);
return v___x_89_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___y_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = 0;
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = l_Repr_addAppParen(v___x_95_, v_prec_82_);
return v___x_96_;
}
v___jp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_99_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_98_);
v___x_100_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_100_, 0, v___y_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = 0;
v___x_102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
v___x_103_ = l_Repr_addAppParen(v___x_102_, v_prec_82_);
return v___x_103_;
}
}
}
LEAN_EXPORT void l_Lean_instReprLocalDeclKind_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_81_ = stack[0].m_num;
lean_object* v_prec_82_ = stack[1].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_Lean_instReprLocalDeclKind_repr(v_x_81_, v_prec_82_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
uint8_t v_x_171__boxed_119_; lean_object* v_res_120_; 
v_x_171__boxed_119_ = lean_unbox(v_x_117_);
v_res_120_ = l_Lean_instReprLocalDeclKind_repr(v_x_171__boxed_119_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_120_;
}
}
uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_123_){
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
LEAN_EXPORT void l_Lean_LocalDeclKind_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_123_ = stack[0].m_obj;
uint8_t v_res_131_;
v_res_131_ = l_Lean_LocalDeclKind_ofNat(v_n_123_);
stack->m_num = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_LocalDeclKind_ofNat(v_n_132_);
lean_dec(v_n_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_135_, uint8_t v_y_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_137_ = lean_box(v_x_135_);
v___x_138_ = lean_obj_tag_nat(v___x_137_);
lean_dec(v___x_137_);
v___x_139_ = lean_box(v_y_136_);
v___x_140_ = lean_obj_tag_nat(v___x_139_);
lean_dec(v___x_139_);
v___x_141_ = lean_nat_dec_eq(v___x_138_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT void l_Lean_instDecidableEqLocalDeclKind_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_135_ = stack[0].m_num;
uint8_t v_y_136_ = stack[1].m_num;
uint8_t v_res_142_;
v_res_142_ = l_Lean_instDecidableEqLocalDeclKind(v_x_135_, v_y_136_);
stack->m_num = v_res_142_;
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_143_, lean_object* v_y_144_){
_start:
{
uint8_t v_x_23__boxed_145_; uint8_t v_y_24__boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_x_23__boxed_145_ = lean_unbox(v_x_143_);
v_y_24__boxed_146_ = lean_unbox(v_y_144_);
v_res_147_ = l_Lean_instDecidableEqLocalDeclKind(v_x_23__boxed_145_, v_y_24__boxed_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_149_){
_start:
{
switch(v_x_149_)
{
case 0:
{
uint64_t v___x_150_; 
v___x_150_ = 0ULL;
return v___x_150_;
}
case 1:
{
uint64_t v___x_151_; 
v___x_151_ = 1ULL;
return v___x_151_;
}
default: 
{
uint64_t v___x_152_; 
v___x_152_ = 2ULL;
return v___x_152_;
}
}
}
}
LEAN_EXPORT void l_Lean_instHashableLocalDeclKind_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_149_ = stack[0].m_num;
uint64_t v_res_153_;
v_res_153_ = l_Lean_instHashableLocalDeclKind_hash(v_x_149_);
stack->m_num = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_154_){
_start:
{
uint8_t v_x_40__boxed_155_; uint64_t v_res_156_; lean_object* v_r_157_; 
v_x_40__boxed_155_ = lean_unbox(v_x_154_);
v_res_156_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_155_);
v_r_157_ = lean_box_uint64(v_res_156_);
return v_r_157_;
}
}
uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object* v_binderName_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_Name_isImplementationDetail(v_binderName_160_);
if (v___x_161_ == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
else
{
uint8_t v___x_163_; 
v___x_163_ = 1;
return v___x_163_;
}
}
}
LEAN_EXPORT void l_Lean_LocalDeclKind_ofBinderName_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_160_ = stack[0].m_obj;
uint8_t v_res_164_;
v_res_164_ = l_Lean_LocalDeclKind_ofBinderName(v_binderName_160_);
stack->m_num = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object* v_binderName_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Lean_LocalDeclKind_ofBinderName(v_binderName_165_);
lean_dec(v_binderName_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___impl(lean_object* v_x_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_tag_nat(v_x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___impl___boxed(lean_object* v_x_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_LocalDecl_ctorIdx___impl(v_x_170_);
lean_dec_ref(v_x_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_172_, lean_object* v_k_173_){
_start:
{
if (lean_obj_tag(v_t_172_) == 0)
{
lean_object* v_index_174_; lean_object* v_fvarId_175_; lean_object* v_userName_176_; lean_object* v_type_177_; uint8_t v_bi_178_; uint8_t v_kind_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_index_174_ = lean_ctor_get(v_t_172_, 0);
lean_inc(v_index_174_);
v_fvarId_175_ = lean_ctor_get(v_t_172_, 1);
lean_inc(v_fvarId_175_);
v_userName_176_ = lean_ctor_get(v_t_172_, 2);
lean_inc(v_userName_176_);
v_type_177_ = lean_ctor_get(v_t_172_, 3);
lean_inc_ref(v_type_177_);
v_bi_178_ = lean_ctor_get_uint8(v_t_172_, sizeof(void*)*4);
v_kind_179_ = lean_ctor_get_uint8(v_t_172_, sizeof(void*)*4 + 1);
lean_dec_ref_known(v_t_172_, 4);
v___x_180_ = lean_box(v_bi_178_);
v___x_181_ = lean_box(v_kind_179_);
v___x_182_ = lean_apply_6(v_k_173_, v_index_174_, v_fvarId_175_, v_userName_176_, v_type_177_, v___x_180_, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_index_183_; lean_object* v_fvarId_184_; lean_object* v_userName_185_; lean_object* v_type_186_; lean_object* v_value_187_; uint8_t v_nondep_188_; uint8_t v_kind_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_index_183_ = lean_ctor_get(v_t_172_, 0);
lean_inc(v_index_183_);
v_fvarId_184_ = lean_ctor_get(v_t_172_, 1);
lean_inc(v_fvarId_184_);
v_userName_185_ = lean_ctor_get(v_t_172_, 2);
lean_inc(v_userName_185_);
v_type_186_ = lean_ctor_get(v_t_172_, 3);
lean_inc_ref(v_type_186_);
v_value_187_ = lean_ctor_get(v_t_172_, 4);
lean_inc_ref(v_value_187_);
v_nondep_188_ = lean_ctor_get_uint8(v_t_172_, sizeof(void*)*5);
v_kind_189_ = lean_ctor_get_uint8(v_t_172_, sizeof(void*)*5 + 1);
lean_dec_ref_known(v_t_172_, 5);
v___x_190_ = lean_box(v_nondep_188_);
v___x_191_ = lean_box(v_kind_189_);
v___x_192_ = lean_apply_7(v_k_173_, v_index_183_, v_fvarId_184_, v_userName_185_, v_type_186_, v_value_187_, v___x_190_, v___x_191_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_193_, lean_object* v_ctorIdx_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_k_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_195_, v_k_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_199_, lean_object* v_ctorIdx_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_k_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_LocalDecl_ctorElim(v_motive_199_, v_ctorIdx_200_, v_t_201_, v_h_202_, v_k_203_);
lean_dec(v_ctorIdx_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_205_, lean_object* v_cdecl_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_205_, v_cdecl_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_cdecl_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_209_, v_cdecl_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_213_, lean_object* v_ldecl_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_213_, v_ldecl_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_ldecl_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_217_, v_ldecl_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_box(0);
v___x_225_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_226_ = l_Lean_Expr_const___override(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_227_ = 0;
v___x_228_ = 0;
v___x_229_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_230_ = lean_box(0);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_230_);
lean_ctor_set(v___x_232_, 3, v___x_229_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*4, v___x_228_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*4 + 1, v___x_227_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_234_;
}
}
lean_object* lean_mk_local_decl(lean_object* v_index_235_, lean_object* v_fvarId_236_, lean_object* v_userName_237_, lean_object* v_type_238_, uint8_t v_bi_239_){
_start:
{
uint8_t v___x_240_; lean_object* v___x_241_; 
v___x_240_ = 0;
v___x_241_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_241_, 0, v_index_235_);
lean_ctor_set(v___x_241_, 1, v_fvarId_236_);
lean_ctor_set(v___x_241_, 2, v_userName_237_);
lean_ctor_set(v___x_241_, 3, v_type_238_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*4, v_bi_239_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*4 + 1, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT void lean_mk_local_decl_0interp(lean_interpreter_value* stack)
{
lean_object* v_index_235_ = stack[0].m_obj;
lean_object* v_fvarId_236_ = stack[1].m_obj;
lean_object* v_userName_237_ = stack[2].m_obj;
lean_object* v_type_238_ = stack[3].m_obj;
uint8_t v_bi_239_ = stack[4].m_num;
lean_object* v_res_242_;
v_res_242_ = lean_mk_local_decl(v_index_235_, v_fvarId_236_, v_userName_237_, v_type_238_, v_bi_239_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_243_, lean_object* v_fvarId_244_, lean_object* v_userName_245_, lean_object* v_type_246_, lean_object* v_bi_247_){
_start:
{
uint8_t v_bi_boxed_248_; lean_object* v_res_249_; 
v_bi_boxed_248_ = lean_unbox(v_bi_247_);
v_res_249_ = lean_mk_local_decl(v_index_243_, v_fvarId_244_, v_userName_245_, v_type_246_, v_bi_boxed_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_250_, lean_object* v_fvarId_251_, lean_object* v_userName_252_, lean_object* v_type_253_, lean_object* v_val_254_){
_start:
{
uint8_t v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; 
v___x_255_ = 0;
v___x_256_ = 0;
v___x_257_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_257_, 0, v_index_250_);
lean_ctor_set(v___x_257_, 1, v_fvarId_251_);
lean_ctor_set(v___x_257_, 2, v_userName_252_);
lean_ctor_set(v___x_257_, 3, v_type_253_);
lean_ctor_set(v___x_257_, 4, v_val_254_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*5, v___x_255_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*5 + 1, v___x_256_);
return v___x_257_;
}
}
uint8_t lean_local_decl_binder_info(lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
uint8_t v_bi_259_; 
v_bi_259_ = lean_ctor_get_uint8(v_x_258_, sizeof(void*)*4);
lean_dec_ref_known(v_x_258_, 4);
return v_bi_259_;
}
else
{
uint8_t v___x_260_; 
lean_dec_ref(v_x_258_);
v___x_260_ = 0;
return v___x_260_;
}
}
}
LEAN_EXPORT void lean_local_decl_binder_info_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_258_ = stack[0].m_obj;
uint8_t v_res_261_;
v_res_261_ = lean_local_decl_binder_info(v_x_258_);
stack->m_num = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = lean_local_decl_binder_info(v_x_262_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_265_, uint8_t v_x_266_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
uint8_t v___x_267_; 
v___x_267_ = 0;
return v___x_267_;
}
else
{
uint8_t v_nondep_268_; 
v_nondep_268_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*5);
if (v_nondep_268_ == 0)
{
uint8_t v___x_269_; 
v___x_269_ = 1;
return v___x_269_;
}
else
{
return v_x_266_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_isLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_265_ = stack[0].m_obj;
uint8_t v_x_266_ = stack[1].m_num;
uint8_t v_res_270_;
v_res_270_ = l_Lean_LocalDecl_isLet(v_x_265_, v_x_266_);
stack->m_num = v_res_270_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
uint8_t v_x_53__boxed_273_; uint8_t v_res_274_; lean_object* v_r_275_; 
v_x_53__boxed_273_ = lean_unbox(v_x_272_);
v_res_274_ = l_Lean_LocalDecl_isLet(v_x_271_, v_x_53__boxed_273_);
lean_dec_ref(v_x_271_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_276_){
_start:
{
lean_object* v_index_277_; 
v_index_277_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_index_277_);
return v_index_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_LocalDecl_index(v_x_278_);
lean_dec_ref(v_x_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v_fvarId_282_; lean_object* v_userName_283_; lean_object* v_type_284_; uint8_t v_bi_285_; uint8_t v_kind_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_fvarId_282_ = lean_ctor_get(v_x_280_, 1);
v_userName_283_ = lean_ctor_get(v_x_280_, 2);
v_type_284_ = lean_ctor_get(v_x_280_, 3);
v_bi_285_ = lean_ctor_get_uint8(v_x_280_, sizeof(void*)*4);
v_kind_286_ = lean_ctor_get_uint8(v_x_280_, sizeof(void*)*4 + 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_x_280_, 0);
lean_dec(v_unused_294_);
v___x_288_ = v_x_280_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_type_284_);
lean_inc(v_userName_283_);
lean_inc(v_fvarId_282_);
lean_dec(v_x_280_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_x_281_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_x_281_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_fvarId_282_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_userName_283_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_type_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*4, v_bi_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*4 + 1, v_kind_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v_fvarId_295_; lean_object* v_userName_296_; lean_object* v_type_297_; lean_object* v_value_298_; uint8_t v_nondep_299_; uint8_t v_kind_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_fvarId_295_ = lean_ctor_get(v_x_280_, 1);
v_userName_296_ = lean_ctor_get(v_x_280_, 2);
v_type_297_ = lean_ctor_get(v_x_280_, 3);
v_value_298_ = lean_ctor_get(v_x_280_, 4);
v_nondep_299_ = lean_ctor_get_uint8(v_x_280_, sizeof(void*)*5);
v_kind_300_ = lean_ctor_get_uint8(v_x_280_, sizeof(void*)*5 + 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v_x_280_, 0);
lean_dec(v_unused_308_);
v___x_302_ = v_x_280_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_value_298_);
lean_inc(v_type_297_);
lean_inc(v_userName_296_);
lean_inc(v_fvarId_295_);
lean_dec(v_x_280_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v_x_281_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_x_281_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_fvarId_295_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_userName_296_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_type_297_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_value_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*5, v_nondep_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_306_, sizeof(void*)*5 + 1, v_kind_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_309_){
_start:
{
lean_object* v_fvarId_310_; 
v_fvarId_310_ = lean_ctor_get(v_x_309_, 1);
lean_inc(v_fvarId_310_);
return v_fvarId_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_LocalDecl_fvarId(v_x_311_);
lean_dec_ref(v_x_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_313_){
_start:
{
lean_object* v_userName_314_; 
v_userName_314_ = lean_ctor_get(v_x_313_, 2);
lean_inc(v_userName_314_);
return v_userName_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_LocalDecl_userName(v_x_315_);
lean_dec_ref(v_x_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_317_){
_start:
{
lean_object* v_type_318_; 
v_type_318_ = lean_ctor_get(v_x_317_, 3);
lean_inc_ref(v_type_318_);
return v_type_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_LocalDecl_type(v_x_319_);
lean_dec_ref(v_x_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v_index_323_; lean_object* v_fvarId_324_; lean_object* v_userName_325_; uint8_t v_bi_326_; uint8_t v_kind_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_index_323_ = lean_ctor_get(v_x_321_, 0);
v_fvarId_324_ = lean_ctor_get(v_x_321_, 1);
v_userName_325_ = lean_ctor_get(v_x_321_, 2);
v_bi_326_ = lean_ctor_get_uint8(v_x_321_, sizeof(void*)*4);
v_kind_327_ = lean_ctor_get_uint8(v_x_321_, sizeof(void*)*4 + 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_x_321_, 3);
lean_dec(v_unused_335_);
v___x_329_ = v_x_321_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_userName_325_);
lean_inc(v_fvarId_324_);
lean_inc(v_index_323_);
lean_dec(v_x_321_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 3, v_x_322_);
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_index_323_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_fvarId_324_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_userName_325_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_x_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*4, v_bi_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*4 + 1, v_kind_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v_index_336_; lean_object* v_fvarId_337_; lean_object* v_userName_338_; lean_object* v_value_339_; uint8_t v_nondep_340_; uint8_t v_kind_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_index_336_ = lean_ctor_get(v_x_321_, 0);
v_fvarId_337_ = lean_ctor_get(v_x_321_, 1);
v_userName_338_ = lean_ctor_get(v_x_321_, 2);
v_value_339_ = lean_ctor_get(v_x_321_, 4);
v_nondep_340_ = lean_ctor_get_uint8(v_x_321_, sizeof(void*)*5);
v_kind_341_ = lean_ctor_get_uint8(v_x_321_, sizeof(void*)*5 + 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v_x_321_, 3);
lean_dec(v_unused_349_);
v___x_343_ = v_x_321_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_value_339_);
lean_inc(v_userName_338_);
lean_inc(v_fvarId_337_);
lean_inc(v_index_336_);
lean_dec(v_x_321_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 3, v_x_322_);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_index_336_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_fvarId_337_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_userName_338_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_x_322_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_value_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_347_, sizeof(void*)*5, v_nondep_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_347_, sizeof(void*)*5 + 1, v_kind_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
uint8_t v_bi_351_; 
v_bi_351_ = lean_ctor_get_uint8(v_x_350_, sizeof(void*)*4);
return v_bi_351_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = 0;
return v___x_352_;
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_binderInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_350_ = stack[0].m_obj;
uint8_t v_res_353_;
v_res_353_ = l_Lean_LocalDecl_binderInfo(v_x_350_);
stack->m_num = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_LocalDecl_binderInfo(v_x_354_);
lean_dec_ref(v_x_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
uint8_t v_kind_358_; 
v_kind_358_ = lean_ctor_get_uint8(v_x_357_, sizeof(void*)*4 + 1);
return v_kind_358_;
}
else
{
uint8_t v_kind_359_; 
v_kind_359_ = lean_ctor_get_uint8(v_x_357_, sizeof(void*)*5 + 1);
return v_kind_359_;
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_kind_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_357_ = stack[0].m_obj;
uint8_t v_res_360_;
v_res_360_ = l_Lean_LocalDecl_kind(v_x_357_);
stack->m_num = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_LocalDecl_kind(v_x_361_);
lean_dec_ref(v_x_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_364_){
_start:
{
uint8_t v___y_366_; 
if (lean_obj_tag(v_d_364_) == 0)
{
uint8_t v_kind_371_; 
v_kind_371_ = lean_ctor_get_uint8(v_d_364_, sizeof(void*)*4 + 1);
v___y_366_ = v_kind_371_;
goto v___jp_365_;
}
else
{
uint8_t v_kind_372_; 
v_kind_372_ = lean_ctor_get_uint8(v_d_364_, sizeof(void*)*5 + 1);
v___y_366_ = v_kind_372_;
goto v___jp_365_;
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_367_ = lean_box(v___y_366_);
v___x_368_ = lean_obj_tag_nat(v___x_367_);
lean_dec(v___x_367_);
v___x_369_ = lean_unsigned_to_nat(2u);
v___x_370_ = lean_nat_dec_eq(v___x_368_, v___x_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_isAuxDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_364_ = stack[0].m_obj;
uint8_t v_res_373_;
v_res_373_ = l_Lean_LocalDecl_isAuxDecl(v_d_364_);
stack->m_num = v_res_373_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Lean_LocalDecl_isAuxDecl(v_d_374_);
lean_dec_ref(v_d_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_377_){
_start:
{
uint8_t v___y_379_; 
if (lean_obj_tag(v_d_377_) == 0)
{
uint8_t v_kind_386_; 
v_kind_386_ = lean_ctor_get_uint8(v_d_377_, sizeof(void*)*4 + 1);
v___y_379_ = v_kind_386_;
goto v___jp_378_;
}
else
{
uint8_t v_kind_387_; 
v_kind_387_ = lean_ctor_get_uint8(v_d_377_, sizeof(void*)*5 + 1);
v___y_379_ = v_kind_387_;
goto v___jp_378_;
}
v___jp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_380_ = lean_box(v___y_379_);
v___x_381_ = lean_obj_tag_nat(v___x_380_);
lean_dec(v___x_380_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_nat_dec_eq(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; 
v___x_384_ = 1;
return v___x_384_;
}
else
{
uint8_t v___x_385_; 
v___x_385_ = 0;
return v___x_385_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_isImplementationDetail_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_377_ = stack[0].m_obj;
uint8_t v_res_388_;
v_res_388_ = l_Lean_LocalDecl_isImplementationDetail(v_d_377_);
stack->m_num = v_res_388_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Lean_LocalDecl_isImplementationDetail(v_d_389_);
lean_dec_ref(v_d_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_392_, uint8_t v_x_393_){
_start:
{
if (lean_obj_tag(v_x_392_) == 1)
{
uint8_t v_nondep_394_; 
v_nondep_394_ = lean_ctor_get_uint8(v_x_392_, sizeof(void*)*5);
if (v_nondep_394_ == 0)
{
lean_object* v_value_395_; lean_object* v___x_396_; 
v_value_395_ = lean_ctor_get(v_x_392_, 4);
lean_inc_ref(v_value_395_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_value_395_);
return v___x_396_;
}
else
{
if (v_x_393_ == 1)
{
lean_object* v_value_397_; lean_object* v___x_398_; 
v_value_397_ = lean_ctor_get(v_x_392_, 4);
lean_inc_ref(v_value_397_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v_value_397_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
}
}
else
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
return v___x_400_;
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_value_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_392_ = stack[0].m_obj;
uint8_t v_x_393_ = stack[1].m_num;
lean_object* v_res_401_;
v_res_401_ = l_Lean_LocalDecl_value_x3f(v_x_392_, v_x_393_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
uint8_t v_x_47__boxed_404_; lean_object* v_res_405_; 
v_x_47__boxed_404_ = lean_unbox(v_x_403_);
v_res_405_ = l_Lean_LocalDecl_value_x3f(v_x_402_, v_x_47__boxed_404_);
lean_dec_ref(v_x_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = l_Lean_instInhabitedExpr;
v___x_408_ = lean_panic_fn_borrowed(v___x_407_, v_msg_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_413_ = lean_unsigned_to_nat(54u);
v___x_414_ = lean_unsigned_to_nat(183u);
v___x_415_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_416_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_417_ = l_mkPanicMessageWithDecl(v___x_416_, v___x_415_, v___x_414_, v___x_413_, v___x_412_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_419_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_420_ = lean_unsigned_to_nat(54u);
v___x_421_ = lean_unsigned_to_nat(186u);
v___x_422_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_423_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_424_ = l_mkPanicMessageWithDecl(v___x_423_, v___x_422_, v___x_421_, v___x_420_, v___x_419_);
return v___x_424_;
}
}
lean_object* l_Lean_LocalDecl_value(lean_object* v_x_425_, uint8_t v_x_426_){
_start:
{
if (lean_obj_tag(v_x_425_) == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_428_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_427_);
return v___x_428_;
}
else
{
uint8_t v_nondep_429_; 
v_nondep_429_ = lean_ctor_get_uint8(v_x_425_, sizeof(void*)*5);
if (v_nondep_429_ == 0)
{
lean_object* v_value_430_; 
v_value_430_ = lean_ctor_get(v_x_425_, 4);
lean_inc_ref(v_value_430_);
return v_value_430_;
}
else
{
if (v_x_426_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_432_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_431_);
return v___x_432_;
}
else
{
lean_object* v_value_433_; 
v_value_433_ = lean_ctor_get(v_x_425_, 4);
lean_inc_ref(v_value_433_);
return v_value_433_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_value_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_425_ = stack[0].m_obj;
uint8_t v_x_426_ = stack[1].m_num;
lean_object* v_res_434_;
v_res_434_ = l_Lean_LocalDecl_value(v_x_425_, v_x_426_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_x_145__boxed_437_; lean_object* v_res_438_; 
v_x_145__boxed_437_ = lean_unbox(v_x_436_);
v_res_438_ = l_Lean_LocalDecl_value(v_x_435_, v_x_145__boxed_437_);
lean_dec_ref(v_x_435_);
return v_res_438_;
}
}
uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_439_, uint8_t v_x_440_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
else
{
uint8_t v_nondep_442_; 
v_nondep_442_ = lean_ctor_get_uint8(v_x_439_, sizeof(void*)*5);
if (v_nondep_442_ == 0)
{
uint8_t v___x_443_; 
v___x_443_ = 1;
return v___x_443_;
}
else
{
return v_x_440_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_hasValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_439_ = stack[0].m_obj;
uint8_t v_x_440_ = stack[1].m_num;
uint8_t v_res_444_;
v_res_444_ = l_Lean_LocalDecl_hasValue(v_x_439_, v_x_440_);
stack->m_num = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_x_72__boxed_447_; uint8_t v_res_448_; lean_object* v_r_449_; 
v_x_72__boxed_447_ = lean_unbox(v_x_446_);
v_res_448_ = l_Lean_LocalDecl_hasValue(v_x_445_, v_x_72__boxed_447_);
lean_dec_ref(v_x_445_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_450_) == 1)
{
lean_object* v_index_452_; lean_object* v_fvarId_453_; lean_object* v_userName_454_; lean_object* v_type_455_; uint8_t v_nondep_456_; uint8_t v_kind_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_index_452_ = lean_ctor_get(v_x_450_, 0);
v_fvarId_453_ = lean_ctor_get(v_x_450_, 1);
v_userName_454_ = lean_ctor_get(v_x_450_, 2);
v_type_455_ = lean_ctor_get(v_x_450_, 3);
v_nondep_456_ = lean_ctor_get_uint8(v_x_450_, sizeof(void*)*5);
v_kind_457_ = lean_ctor_get_uint8(v_x_450_, sizeof(void*)*5 + 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_x_450_, 4);
lean_dec(v_unused_465_);
v___x_459_ = v_x_450_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_type_455_);
lean_inc(v_userName_454_);
lean_inc(v_fvarId_453_);
lean_inc(v_index_452_);
lean_dec(v_x_450_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 4, v_x_451_);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_index_452_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_fvarId_453_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_userName_454_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_type_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_x_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*5, v_nondep_456_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*5 + 1, v_kind_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_dec_ref(v_x_451_);
return v_x_450_;
}
}
}
lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_466_, uint8_t v_x_467_){
_start:
{
if (lean_obj_tag(v_x_466_) == 1)
{
lean_object* v_index_468_; lean_object* v_fvarId_469_; lean_object* v_userName_470_; lean_object* v_type_471_; lean_object* v_value_472_; uint8_t v_kind_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_index_468_ = lean_ctor_get(v_x_466_, 0);
v_fvarId_469_ = lean_ctor_get(v_x_466_, 1);
v_userName_470_ = lean_ctor_get(v_x_466_, 2);
v_type_471_ = lean_ctor_get(v_x_466_, 3);
v_value_472_ = lean_ctor_get(v_x_466_, 4);
v_kind_473_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*5 + 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v_x_466_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_value_472_);
lean_inc(v_type_471_);
lean_inc(v_userName_470_);
lean_inc(v_fvarId_469_);
lean_inc(v_index_468_);
lean_dec(v_x_466_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_index_468_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_fvarId_469_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_userName_470_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_type_471_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v_value_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_479_, sizeof(void*)*5 + 1, v_kind_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*5, v_x_467_);
return v___x_478_;
}
}
}
else
{
return v_x_466_;
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_setNondep_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_466_ = stack[0].m_obj;
uint8_t v_x_467_ = stack[1].m_num;
lean_object* v_res_481_;
v_res_481_ = l_Lean_LocalDecl_setNondep(v_x_466_, v_x_467_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
uint8_t v_x_23__boxed_484_; lean_object* v_res_485_; 
v_x_23__boxed_484_ = lean_unbox(v_x_483_);
v_res_485_ = l_Lean_LocalDecl_setNondep(v_x_482_, v_x_23__boxed_484_);
return v_res_485_;
}
}
uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_486_) == 1)
{
uint8_t v_nondep_487_; 
v_nondep_487_ = lean_ctor_get_uint8(v_x_486_, sizeof(void*)*5);
return v_nondep_487_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = 0;
return v___x_488_;
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_isNondep_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_486_ = stack[0].m_obj;
uint8_t v_res_489_;
v_res_489_ = l_Lean_LocalDecl_isNondep(v_x_486_);
stack->m_num = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Lean_LocalDecl_isNondep(v_x_490_);
lean_dec_ref(v_x_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_index_495_; lean_object* v_fvarId_496_; lean_object* v_type_497_; uint8_t v_bi_498_; uint8_t v_kind_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_index_495_ = lean_ctor_get(v_x_493_, 0);
v_fvarId_496_ = lean_ctor_get(v_x_493_, 1);
v_type_497_ = lean_ctor_get(v_x_493_, 3);
v_bi_498_ = lean_ctor_get_uint8(v_x_493_, sizeof(void*)*4);
v_kind_499_ = lean_ctor_get_uint8(v_x_493_, sizeof(void*)*4 + 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_x_493_, 2);
lean_dec(v_unused_507_);
v___x_501_ = v_x_493_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_type_497_);
lean_inc(v_fvarId_496_);
lean_inc(v_index_495_);
lean_dec(v_x_493_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 2, v_x_494_);
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_index_495_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_fvarId_496_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_x_494_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_type_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*4, v_bi_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*4 + 1, v_kind_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v_index_508_; lean_object* v_fvarId_509_; lean_object* v_type_510_; lean_object* v_value_511_; uint8_t v_nondep_512_; uint8_t v_kind_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_index_508_ = lean_ctor_get(v_x_493_, 0);
v_fvarId_509_ = lean_ctor_get(v_x_493_, 1);
v_type_510_ = lean_ctor_get(v_x_493_, 3);
v_value_511_ = lean_ctor_get(v_x_493_, 4);
v_nondep_512_ = lean_ctor_get_uint8(v_x_493_, sizeof(void*)*5);
v_kind_513_ = lean_ctor_get_uint8(v_x_493_, sizeof(void*)*5 + 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v_x_493_, 2);
lean_dec(v_unused_521_);
v___x_515_ = v_x_493_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_value_511_);
lean_inc(v_type_510_);
lean_inc(v_fvarId_509_);
lean_inc(v_index_508_);
lean_dec(v_x_493_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 2, v_x_494_);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_index_508_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_fvarId_509_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_x_494_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_type_510_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_value_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_519_, sizeof(void*)*5, v_nondep_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_519_, sizeof(void*)*5 + 1, v_kind_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = l_Lean_instInhabitedLocalDecl_default;
v___x_524_ = lean_panic_fn_borrowed(v___x_523_, v_msg_522_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_527_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_528_ = lean_unsigned_to_nat(38u);
v___x_529_ = lean_unsigned_to_nat(248u);
v___x_530_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_531_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_532_ = l_mkPanicMessageWithDecl(v___x_531_, v___x_530_, v___x_529_, v___x_528_, v___x_527_);
return v___x_532_;
}
}
lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_533_, uint8_t v_x_534_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v_index_535_; lean_object* v_fvarId_536_; lean_object* v_userName_537_; lean_object* v_type_538_; uint8_t v_kind_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_index_535_ = lean_ctor_get(v_x_533_, 0);
v_fvarId_536_ = lean_ctor_get(v_x_533_, 1);
v_userName_537_ = lean_ctor_get(v_x_533_, 2);
v_type_538_ = lean_ctor_get(v_x_533_, 3);
v_kind_539_ = lean_ctor_get_uint8(v_x_533_, sizeof(void*)*4 + 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_x_533_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v_x_533_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_type_538_);
lean_inc(v_userName_537_);
lean_inc(v_fvarId_536_);
lean_inc(v_index_535_);
lean_dec(v_x_533_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_index_535_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_fvarId_536_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_userName_537_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_type_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_545_, sizeof(void*)*4 + 1, v_kind_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*4, v_x_534_);
return v___x_544_;
}
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref_known(v_x_533_, 5);
v___x_547_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_548_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_setBinderInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_533_ = stack[0].m_obj;
uint8_t v_x_534_ = stack[1].m_num;
lean_object* v_res_549_;
v_res_549_ = l_Lean_LocalDecl_setBinderInfo(v_x_533_, v_x_534_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
uint8_t v_x_86__boxed_552_; lean_object* v_res_553_; 
v_x_86__boxed_552_ = lean_unbox(v_x_551_);
v_res_553_ = l_Lean_LocalDecl_setBinderInfo(v_x_550_, v_x_86__boxed_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_554_){
_start:
{
lean_object* v_fvarId_555_; lean_object* v___x_556_; 
v_fvarId_555_ = lean_ctor_get(v_decl_554_, 1);
lean_inc(v_fvarId_555_);
lean_dec_ref(v_decl_554_);
v___x_556_ = l_Lean_mkFVar(v_fvarId_555_);
return v___x_556_;
}
}
uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
lean_object* v_type_558_; uint8_t v___x_559_; 
v_type_558_ = lean_ctor_get(v_x_557_, 3);
v___x_559_ = l_Lean_Expr_hasExprMVar(v_type_558_);
return v___x_559_;
}
else
{
lean_object* v_type_560_; lean_object* v_value_561_; uint8_t v___x_562_; 
v_type_560_ = lean_ctor_get(v_x_557_, 3);
v_value_561_ = lean_ctor_get(v_x_557_, 4);
v___x_562_ = l_Lean_Expr_hasExprMVar(v_type_560_);
if (v___x_562_ == 0)
{
uint8_t v___x_563_; 
v___x_563_ = l_Lean_Expr_hasExprMVar(v_value_561_);
return v___x_563_;
}
else
{
return v___x_562_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_hasExprMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_557_ = stack[0].m_obj;
uint8_t v_res_564_;
v_res_564_ = l_Lean_LocalDecl_hasExprMVar(v_x_557_);
stack->m_num = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_565_){
_start:
{
uint8_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = l_Lean_LocalDecl_hasExprMVar(v_x_565_);
lean_dec_ref(v_x_565_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_568_, uint8_t v_x_569_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v_index_570_; lean_object* v_fvarId_571_; lean_object* v_userName_572_; lean_object* v_type_573_; uint8_t v_bi_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_index_570_ = lean_ctor_get(v_x_568_, 0);
v_fvarId_571_ = lean_ctor_get(v_x_568_, 1);
v_userName_572_ = lean_ctor_get(v_x_568_, 2);
v_type_573_ = lean_ctor_get(v_x_568_, 3);
v_bi_574_ = lean_ctor_get_uint8(v_x_568_, sizeof(void*)*4);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v_x_568_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_type_573_);
lean_inc(v_userName_572_);
lean_inc(v_fvarId_571_);
lean_inc(v_index_570_);
lean_dec(v_x_568_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_index_570_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_fvarId_571_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_userName_572_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_type_573_);
lean_ctor_set_uint8(v_reuseFailAlloc_580_, sizeof(void*)*4, v_bi_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*4 + 1, v_x_569_);
return v___x_579_;
}
}
}
else
{
lean_object* v_index_582_; lean_object* v_fvarId_583_; lean_object* v_userName_584_; lean_object* v_type_585_; lean_object* v_value_586_; uint8_t v_nondep_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_index_582_ = lean_ctor_get(v_x_568_, 0);
v_fvarId_583_ = lean_ctor_get(v_x_568_, 1);
v_userName_584_ = lean_ctor_get(v_x_568_, 2);
v_type_585_ = lean_ctor_get(v_x_568_, 3);
v_value_586_ = lean_ctor_get(v_x_568_, 4);
v_nondep_587_ = lean_ctor_get_uint8(v_x_568_, sizeof(void*)*5);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v_x_568_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_value_586_);
lean_inc(v_type_585_);
lean_inc(v_userName_584_);
lean_inc(v_fvarId_583_);
lean_inc(v_index_582_);
lean_dec(v_x_568_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_index_582_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_fvarId_583_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_userName_584_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_type_585_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_value_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_593_, sizeof(void*)*5, v_nondep_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*5 + 1, v_x_569_);
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_LocalDecl_setKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_568_ = stack[0].m_obj;
uint8_t v_x_569_ = stack[1].m_num;
lean_object* v_res_595_;
v_res_595_ = l_Lean_LocalDecl_setKind(v_x_568_, v_x_569_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
uint8_t v_x_31__boxed_598_; lean_object* v_res_599_; 
v_x_31__boxed_598_ = lean_unbox(v_x_597_);
v_res_599_ = l_Lean_LocalDecl_setKind(v_x_596_, v_x_31__boxed_598_);
return v_res_599_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_600_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(32u);
v___x_604_ = lean_mk_empty_array_with_capacity(v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_606_ = ((size_t)5ULL);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_unsigned_to_nat(32u);
v___x_609_ = lean_mk_empty_array_with_capacity(v___x_608_);
v___x_610_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_611_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_607_);
lean_ctor_set(v___x_611_, 3, v___x_607_);
lean_ctor_set_usize(v___x_611_, 4, v___x_606_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = lean_box(1);
v___x_613_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_614_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
lean_ctor_set(v___x_615_, 2, v___x_612_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_instInhabitedLocalContext_default;
return v___x_617_;
}
}
lean_object* l_Lean_LocalContext_mkEmpty___redArg(){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_unsigned_to_nat(32u);
v___x_620_ = lean_mk_empty_array_with_capacity(v___x_619_);
lean_dec_ref(v___x_620_);
v___x_621_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_621_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_mkEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_622_;
v_res_622_ = l_Lean_LocalContext_mkEmpty___redArg();
stack->m_obj
 = v_res_622_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg___boxed(lean_object* v___dummy_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_LocalContext_mkEmpty___redArg();
return v_res_624_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__0(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_LocalContext_mkEmpty___redArg();
return v___x_625_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__0, &l_Lean_LocalContext_mkEmpty___closed__0_once, _init_l_Lean_LocalContext_mkEmpty___closed__0);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(32u);
v___x_629_ = lean_mk_empty_array_with_capacity(v___x_628_);
lean_dec_ref(v___x_629_);
v___x_630_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_630_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_631_ = stack[0].m_obj;
uint8_t v_res_633_;
v_res_633_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_631_);
stack->m_num = v_res_633_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_634_);
lean_dec_ref(v_x_634_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_637_, lean_object* v_x_638_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_638_);
return v___x_639_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_638_ = stack[1].m_obj;
uint8_t v_res_640_;
v_res_640_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_box(0), v_x_638_);
stack->m_num = v_res_640_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_641_, lean_object* v_x_642_){
_start:
{
uint8_t v_res_643_; lean_object* v_r_644_; 
v_res_643_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_641_, v_x_642_);
lean_dec_ref(v_x_642_);
v_r_644_ = lean_box(v_res_643_);
return v_r_644_;
}
}
uint8_t l_Lean_LocalContext_isEmpty(lean_object* v_lctx_645_){
_start:
{
lean_object* v_fvarIdToDecl_646_; uint8_t v___x_647_; 
v_fvarIdToDecl_646_ = lean_ctor_get(v_lctx_645_, 0);
v___x_647_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_646_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_645_ = stack[0].m_obj;
uint8_t v_res_648_;
v_res_648_ = l_Lean_LocalContext_isEmpty(v_lctx_645_);
stack->m_num = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Lean_LocalContext_isEmpty(v_lctx_649_);
lean_dec_ref(v_lctx_649_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v_ks_656_; lean_object* v_vs_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_681_; 
v_ks_656_ = lean_ctor_get(v_x_652_, 0);
v_vs_657_ = lean_ctor_get(v_x_652_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_681_ == 0)
{
v___x_659_ = v_x_652_;
v_isShared_660_ = v_isSharedCheck_681_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_vs_657_);
lean_inc(v_ks_656_);
lean_dec(v_x_652_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_681_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_ks_656_);
v___x_662_ = lean_nat_dec_lt(v_x_653_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
lean_dec(v_x_653_);
v___x_663_ = lean_array_push(v_ks_656_, v_x_654_);
v___x_664_ = lean_array_push(v_vs_657_, v_x_655_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_664_);
lean_ctor_set(v___x_659_, 0, v___x_663_);
v___x_666_ = v___x_659_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
else
{
lean_object* v_k_x27_668_; uint8_t v___x_669_; 
v_k_x27_668_ = lean_array_fget_borrowed(v_ks_656_, v_x_653_);
v___x_669_ = l_Lean_instBEqFVarId_beq(v_x_654_, v_k_x27_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_671_; 
if (v_isShared_660_ == 0)
{
v___x_671_ = v___x_659_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_ks_656_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_vs_657_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_add(v_x_653_, v___x_672_);
lean_dec(v_x_653_);
v_x_652_ = v___x_671_;
v_x_653_ = v___x_673_;
goto _start;
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_676_ = lean_array_fset(v_ks_656_, v_x_653_, v_x_654_);
v___x_677_ = lean_array_fset(v_vs_657_, v_x_653_, v_x_655_);
lean_dec(v_x_653_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_677_);
lean_ctor_set(v___x_659_, 0, v___x_676_);
v___x_679_ = v___x_659_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_682_, lean_object* v_k_683_, lean_object* v_v_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_682_, v___x_685_, v_k_683_, v_v_684_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_687_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_688_, size_t v_x_689_, size_t v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
if (lean_obj_tag(v_x_688_) == 0)
{
lean_object* v_es_693_; size_t v___x_694_; size_t v___x_695_; lean_object* v_j_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_es_693_ = lean_ctor_get(v_x_688_, 0);
v___x_694_ = ((size_t)31ULL);
v___x_695_ = lean_usize_land(v_x_689_, v___x_694_);
v_j_696_ = lean_usize_to_nat(v___x_695_);
v___x_697_ = lean_array_get_size(v_es_693_);
v___x_698_ = lean_nat_dec_lt(v_j_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_dec(v_j_696_);
lean_dec(v_x_692_);
lean_dec(v_x_691_);
return v_x_688_;
}
else
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_737_; 
lean_inc_ref(v_es_693_);
v_isSharedCheck_737_ = !lean_is_exclusive(v_x_688_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_x_688_, 0);
lean_dec(v_unused_738_);
v___x_700_ = v_x_688_;
v_isShared_701_ = v_isSharedCheck_737_;
goto v_resetjp_699_;
}
else
{
lean_dec(v_x_688_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_737_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_v_702_; lean_object* v___x_703_; lean_object* v_xs_x27_704_; lean_object* v___y_706_; 
v_v_702_ = lean_array_fget(v_es_693_, v_j_696_);
v___x_703_ = lean_box(0);
v_xs_x27_704_ = lean_array_fset(v_es_693_, v_j_696_, v___x_703_);
switch(lean_obj_tag(v_v_702_))
{
case 0:
{
lean_object* v_key_711_; lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_722_; 
v_key_711_ = lean_ctor_get(v_v_702_, 0);
v_val_712_ = lean_ctor_get(v_v_702_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_v_702_);
if (v_isSharedCheck_722_ == 0)
{
v___x_714_ = v_v_702_;
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_inc(v_key_711_);
lean_dec(v_v_702_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_instBEqFVarId_beq(v_x_691_, v_key_711_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_714_);
v___x_717_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_711_, v_val_712_, v_x_691_, v_x_692_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
v___y_706_ = v___x_718_;
goto v___jp_705_;
}
else
{
lean_object* v___x_720_; 
lean_dec(v_val_712_);
lean_dec(v_key_711_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_x_692_);
lean_ctor_set(v___x_714_, 0, v_x_691_);
v___x_720_ = v___x_714_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_x_691_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_x_692_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v___y_706_ = v___x_720_;
goto v___jp_705_;
}
}
}
}
case 1:
{
lean_object* v_node_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_735_; 
v_node_723_ = lean_ctor_get(v_v_702_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_v_702_);
if (v_isSharedCheck_735_ == 0)
{
v___x_725_ = v_v_702_;
v_isShared_726_ = v_isSharedCheck_735_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_node_723_);
lean_dec(v_v_702_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_735_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_727_ = ((size_t)5ULL);
v___x_728_ = lean_usize_shift_right(v_x_689_, v___x_727_);
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_x_690_, v___x_729_);
v___x_731_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_723_, v___x_728_, v___x_730_, v_x_691_, v_x_692_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_731_);
v___x_733_ = v___x_725_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
v___y_706_ = v___x_733_;
goto v___jp_705_;
}
}
}
default: 
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_x_691_);
lean_ctor_set(v___x_736_, 1, v_x_692_);
v___y_706_ = v___x_736_;
goto v___jp_705_;
}
}
v___jp_705_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_array_fset(v_xs_x27_704_, v_j_696_, v___y_706_);
lean_dec(v_j_696_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_707_);
v___x_709_ = v___x_700_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v_ks_739_; lean_object* v_vs_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_758_; 
v_ks_739_ = lean_ctor_get(v_x_688_, 0);
v_vs_740_ = lean_ctor_get(v_x_688_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_688_);
if (v_isSharedCheck_758_ == 0)
{
v___x_742_ = v_x_688_;
v_isShared_743_ = v_isSharedCheck_758_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_vs_740_);
lean_inc(v_ks_739_);
lean_dec(v_x_688_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_758_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_ks_739_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_vs_740_);
v___x_745_ = v_reuseFailAlloc_757_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v_newNode_746_; size_t v___x_747_; uint8_t v___x_748_; 
v_newNode_746_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_745_, v_x_691_, v_x_692_);
v___x_747_ = ((size_t)7ULL);
v___x_748_ = lean_usize_dec_le(v___x_747_, v_x_690_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_749_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_746_);
v___x_750_ = lean_unsigned_to_nat(4u);
v___x_751_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
lean_dec(v___x_749_);
if (v___x_751_ == 0)
{
lean_object* v_ks_752_; lean_object* v_vs_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_ks_752_ = lean_ctor_get(v_newNode_746_, 0);
lean_inc_ref(v_ks_752_);
v_vs_753_ = lean_ctor_get(v_newNode_746_, 1);
lean_inc_ref(v_vs_753_);
lean_dec_ref(v_newNode_746_);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_690_, v_ks_752_, v_vs_753_, v___x_754_, v___x_755_);
lean_dec_ref(v_vs_753_);
lean_dec_ref(v_ks_752_);
return v___x_756_;
}
else
{
return v_newNode_746_;
}
}
else
{
return v_newNode_746_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_688_ = stack[0].m_obj;
size_t v_x_689_ = stack[1].m_num;
size_t v_x_690_ = stack[2].m_num;
lean_object* v_x_691_ = stack[3].m_obj;
lean_object* v_x_692_ = stack[4].m_obj;
lean_object* v_res_759_;
v_res_759_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_688_, v_x_689_, v_x_690_, v_x_691_, v_x_692_);
stack->m_obj
 = v_res_759_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_760_, lean_object* v_keys_761_, lean_object* v_vals_762_, lean_object* v_i_763_, lean_object* v_entries_764_){
_start:
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = lean_array_get_size(v_keys_761_);
v___x_766_ = lean_nat_dec_lt(v_i_763_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v_i_763_);
return v_entries_764_;
}
else
{
lean_object* v_k_767_; lean_object* v_v_768_; uint64_t v___x_769_; size_t v_h_770_; size_t v___x_771_; lean_object* v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v_h_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_k_767_ = lean_array_fget_borrowed(v_keys_761_, v_i_763_);
v_v_768_ = lean_array_fget_borrowed(v_vals_762_, v_i_763_);
v___x_769_ = l_Lean_instHashableFVarId_hash(v_k_767_);
v_h_770_ = lean_uint64_to_usize(v___x_769_);
v___x_771_ = ((size_t)5ULL);
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_sub(v_depth_760_, v___x_773_);
v___x_775_ = lean_usize_mul(v___x_771_, v___x_774_);
v_h_776_ = lean_usize_shift_right(v_h_770_, v___x_775_);
v___x_777_ = lean_nat_add(v_i_763_, v___x_772_);
lean_dec(v_i_763_);
lean_inc(v_v_768_);
lean_inc(v_k_767_);
v___x_778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_764_, v_h_776_, v_depth_760_, v_k_767_, v_v_768_);
v_i_763_ = v___x_777_;
v_entries_764_ = v___x_778_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_760_ = stack[0].m_num;
lean_object* v_keys_761_ = stack[1].m_obj;
lean_object* v_vals_762_ = stack[2].m_obj;
lean_object* v_i_763_ = stack[3].m_obj;
lean_object* v_entries_764_ = stack[4].m_obj;
lean_object* v_res_780_;
v_res_780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_760_, v_keys_761_, v_vals_762_, v_i_763_, v_entries_764_);
stack->m_obj
 = v_res_780_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_781_, lean_object* v_keys_782_, lean_object* v_vals_783_, lean_object* v_i_784_, lean_object* v_entries_785_){
_start:
{
size_t v_depth_boxed_786_; lean_object* v_res_787_; 
v_depth_boxed_786_ = lean_unbox_usize(v_depth_781_);
lean_dec(v_depth_781_);
v_res_787_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_786_, v_keys_782_, v_vals_783_, v_i_784_, v_entries_785_);
lean_dec_ref(v_vals_783_);
lean_dec_ref(v_keys_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
size_t v_x_396__boxed_793_; size_t v_x_397__boxed_794_; lean_object* v_res_795_; 
v_x_396__boxed_793_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_x_397__boxed_794_ = lean_unbox_usize(v_x_790_);
lean_dec(v_x_790_);
v_res_795_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_788_, v_x_396__boxed_793_, v_x_397__boxed_794_, v_x_791_, v_x_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
uint64_t v___x_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v___x_799_ = l_Lean_instHashableFVarId_hash(v_x_797_);
v___x_800_ = lean_uint64_to_usize(v___x_799_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_796_, v___x_800_, v___x_801_, v_x_797_, v_x_798_);
return v___x_802_;
}
}
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_803_, lean_object* v_fvarId_804_, lean_object* v_userName_805_, lean_object* v_type_806_, uint8_t v_bi_807_, uint8_t v_kind_808_){
_start:
{
lean_object* v_decls_809_; lean_object* v_fvarIdToDecl_810_; lean_object* v_auxDeclToFullName_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_823_; 
v_decls_809_ = lean_ctor_get(v_lctx_803_, 1);
v_fvarIdToDecl_810_ = lean_ctor_get(v_lctx_803_, 0);
v_auxDeclToFullName_811_ = lean_ctor_get(v_lctx_803_, 2);
v_isSharedCheck_823_ = !lean_is_exclusive(v_lctx_803_);
if (v_isSharedCheck_823_ == 0)
{
v___x_813_ = v_lctx_803_;
v_isShared_814_ = v_isSharedCheck_823_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_auxDeclToFullName_811_);
lean_inc(v_decls_809_);
lean_inc(v_fvarIdToDecl_810_);
lean_dec(v_lctx_803_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_823_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_size_815_; lean_object* v_decl_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v_size_815_ = lean_ctor_get(v_decls_809_, 2);
lean_inc(v_fvarId_804_);
lean_inc(v_size_815_);
v_decl_816_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_816_, 0, v_size_815_);
lean_ctor_set(v_decl_816_, 1, v_fvarId_804_);
lean_ctor_set(v_decl_816_, 2, v_userName_805_);
lean_ctor_set(v_decl_816_, 3, v_type_806_);
lean_ctor_set_uint8(v_decl_816_, sizeof(void*)*4, v_bi_807_);
lean_ctor_set_uint8(v_decl_816_, sizeof(void*)*4 + 1, v_kind_808_);
lean_inc_ref(v_decl_816_);
v___x_817_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_810_, v_fvarId_804_, v_decl_816_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_decl_816_);
v___x_819_ = l_Lean_PersistentArray_push___redArg(v_decls_809_, v___x_818_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_819_);
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_821_ = v___x_813_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_auxDeclToFullName_811_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_mkLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_803_ = stack[0].m_obj;
lean_object* v_fvarId_804_ = stack[1].m_obj;
lean_object* v_userName_805_ = stack[2].m_obj;
lean_object* v_type_806_ = stack[3].m_obj;
uint8_t v_bi_807_ = stack[4].m_num;
uint8_t v_kind_808_ = stack[5].m_num;
lean_object* v_res_824_;
v_res_824_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_803_, v_fvarId_804_, v_userName_805_, v_type_806_, v_bi_807_, v_kind_808_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_825_, lean_object* v_fvarId_826_, lean_object* v_userName_827_, lean_object* v_type_828_, lean_object* v_bi_829_, lean_object* v_kind_830_){
_start:
{
uint8_t v_bi_boxed_831_; uint8_t v_kind_boxed_832_; lean_object* v_res_833_; 
v_bi_boxed_831_ = lean_unbox(v_bi_829_);
v_kind_boxed_832_ = lean_unbox(v_kind_830_);
v_res_833_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_825_, v_fvarId_826_, v_userName_827_, v_type_828_, v_bi_boxed_831_, v_kind_boxed_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_835_, v_x_836_, v_x_837_);
return v___x_838_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_839_, lean_object* v_x_840_, size_t v_x_841_, size_t v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_840_, v_x_841_, v_x_842_, v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_840_ = stack[1].m_obj;
size_t v_x_841_ = stack[2].m_num;
size_t v_x_842_ = stack[3].m_num;
lean_object* v_x_843_ = stack[4].m_obj;
lean_object* v_x_844_ = stack[5].m_obj;
lean_object* v_res_846_;
v_res_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_box(0), v_x_840_, v_x_841_, v_x_842_, v_x_843_, v_x_844_);
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
size_t v_x_704__boxed_853_; size_t v_x_705__boxed_854_; lean_object* v_res_855_; 
v_x_704__boxed_853_ = lean_unbox_usize(v_x_849_);
lean_dec(v_x_849_);
v_x_705__boxed_854_ = lean_unbox_usize(v_x_850_);
lean_dec(v_x_850_);
v_res_855_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_847_, v_x_848_, v_x_704__boxed_853_, v_x_705__boxed_854_, v_x_851_, v_x_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_856_, lean_object* v_n_857_, lean_object* v_k_858_, lean_object* v_v_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_857_, v_k_858_, v_v_859_);
return v___x_860_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_861_, size_t v_depth_862_, lean_object* v_keys_863_, lean_object* v_vals_864_, lean_object* v_heq_865_, lean_object* v_i_866_, lean_object* v_entries_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_862_, v_keys_863_, v_vals_864_, v_i_866_, v_entries_867_);
return v___x_868_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_862_ = stack[1].m_num;
lean_object* v_keys_863_ = stack[2].m_obj;
lean_object* v_vals_864_ = stack[3].m_obj;
lean_object* v_i_866_ = stack[5].m_obj;
lean_object* v_entries_867_ = stack[6].m_obj;
lean_object* v_res_869_;
v_res_869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_box(0), v_depth_862_, v_keys_863_, v_vals_864_, lean_box(0), v_i_866_, v_entries_867_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_870_, lean_object* v_depth_871_, lean_object* v_keys_872_, lean_object* v_vals_873_, lean_object* v_heq_874_, lean_object* v_i_875_, lean_object* v_entries_876_){
_start:
{
size_t v_depth_boxed_877_; lean_object* v_res_878_; 
v_depth_boxed_877_ = lean_unbox_usize(v_depth_871_);
lean_dec(v_depth_871_);
v_res_878_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_870_, v_depth_boxed_877_, v_keys_872_, v_vals_873_, v_heq_874_, v_i_875_, v_entries_876_);
lean_dec_ref(v_vals_873_);
lean_dec_ref(v_keys_872_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_880_, v_x_881_, v_x_882_, v_x_883_);
return v___x_884_;
}
}
lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_885_, lean_object* v_fvarId_886_, lean_object* v_userName_887_, lean_object* v_type_888_, uint8_t v_bi_889_){
_start:
{
uint8_t v___x_890_; lean_object* v___x_891_; 
v___x_890_ = 0;
v___x_891_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_885_, v_fvarId_886_, v_userName_887_, v_type_888_, v_bi_889_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT void lean_local_ctx_mk_local_decl_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_885_ = stack[0].m_obj;
lean_object* v_fvarId_886_ = stack[1].m_obj;
lean_object* v_userName_887_ = stack[2].m_obj;
lean_object* v_type_888_ = stack[3].m_obj;
uint8_t v_bi_889_ = stack[4].m_num;
lean_object* v_res_892_;
v_res_892_ = lean_local_ctx_mk_local_decl(v_lctx_885_, v_fvarId_886_, v_userName_887_, v_type_888_, v_bi_889_);
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_893_, lean_object* v_fvarId_894_, lean_object* v_userName_895_, lean_object* v_type_896_, lean_object* v_bi_897_){
_start:
{
uint8_t v_bi_boxed_898_; lean_object* v_res_899_; 
v_bi_boxed_898_ = lean_unbox(v_bi_897_);
v_res_899_ = lean_local_ctx_mk_local_decl(v_lctx_893_, v_fvarId_894_, v_userName_895_, v_type_896_, v_bi_boxed_898_);
return v_res_899_;
}
}
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_900_, lean_object* v_fvarId_901_, lean_object* v_userName_902_, lean_object* v_type_903_, lean_object* v_value_904_, uint8_t v_nondep_905_, uint8_t v_kind_906_){
_start:
{
lean_object* v_decls_907_; lean_object* v_fvarIdToDecl_908_; lean_object* v_auxDeclToFullName_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v_decls_907_ = lean_ctor_get(v_lctx_900_, 1);
v_fvarIdToDecl_908_ = lean_ctor_get(v_lctx_900_, 0);
v_auxDeclToFullName_909_ = lean_ctor_get(v_lctx_900_, 2);
v_isSharedCheck_921_ = !lean_is_exclusive(v_lctx_900_);
if (v_isSharedCheck_921_ == 0)
{
v___x_911_ = v_lctx_900_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_auxDeclToFullName_909_);
lean_inc(v_decls_907_);
lean_inc(v_fvarIdToDecl_908_);
lean_dec(v_lctx_900_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_size_913_; lean_object* v_decl_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v_size_913_ = lean_ctor_get(v_decls_907_, 2);
lean_inc(v_fvarId_901_);
lean_inc(v_size_913_);
v_decl_914_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_914_, 0, v_size_913_);
lean_ctor_set(v_decl_914_, 1, v_fvarId_901_);
lean_ctor_set(v_decl_914_, 2, v_userName_902_);
lean_ctor_set(v_decl_914_, 3, v_type_903_);
lean_ctor_set(v_decl_914_, 4, v_value_904_);
lean_ctor_set_uint8(v_decl_914_, sizeof(void*)*5, v_nondep_905_);
lean_ctor_set_uint8(v_decl_914_, sizeof(void*)*5 + 1, v_kind_906_);
lean_inc_ref(v_decl_914_);
v___x_915_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_908_, v_fvarId_901_, v_decl_914_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_decl_914_);
v___x_917_ = l_Lean_PersistentArray_push___redArg(v_decls_907_, v___x_916_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_917_);
lean_ctor_set(v___x_911_, 0, v___x_915_);
v___x_919_ = v___x_911_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_auxDeclToFullName_909_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_mkLetDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_900_ = stack[0].m_obj;
lean_object* v_fvarId_901_ = stack[1].m_obj;
lean_object* v_userName_902_ = stack[2].m_obj;
lean_object* v_type_903_ = stack[3].m_obj;
lean_object* v_value_904_ = stack[4].m_obj;
uint8_t v_nondep_905_ = stack[5].m_num;
uint8_t v_kind_906_ = stack[6].m_num;
lean_object* v_res_922_;
v_res_922_ = l_Lean_LocalContext_mkLetDecl(v_lctx_900_, v_fvarId_901_, v_userName_902_, v_type_903_, v_value_904_, v_nondep_905_, v_kind_906_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_923_, lean_object* v_fvarId_924_, lean_object* v_userName_925_, lean_object* v_type_926_, lean_object* v_value_927_, lean_object* v_nondep_928_, lean_object* v_kind_929_){
_start:
{
uint8_t v_nondep_boxed_930_; uint8_t v_kind_boxed_931_; lean_object* v_res_932_; 
v_nondep_boxed_930_ = lean_unbox(v_nondep_928_);
v_kind_boxed_931_ = lean_unbox(v_kind_929_);
v_res_932_ = l_Lean_LocalContext_mkLetDecl(v_lctx_923_, v_fvarId_924_, v_userName_925_, v_type_926_, v_value_927_, v_nondep_boxed_930_, v_kind_boxed_931_);
return v_res_932_;
}
}
lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_933_, lean_object* v_fvarId_934_, lean_object* v_userName_935_, lean_object* v_type_936_, lean_object* v_value_937_, uint8_t v_nondep_938_){
_start:
{
uint8_t v___x_939_; lean_object* v___x_940_; 
v___x_939_ = 0;
v___x_940_ = l_Lean_LocalContext_mkLetDecl(v_lctx_933_, v_fvarId_934_, v_userName_935_, v_type_936_, v_value_937_, v_nondep_938_, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT void lean_local_ctx_mk_let_decl_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_933_ = stack[0].m_obj;
lean_object* v_fvarId_934_ = stack[1].m_obj;
lean_object* v_userName_935_ = stack[2].m_obj;
lean_object* v_type_936_ = stack[3].m_obj;
lean_object* v_value_937_ = stack[4].m_obj;
uint8_t v_nondep_938_ = stack[5].m_num;
lean_object* v_res_941_;
v_res_941_ = lean_local_ctx_mk_let_decl(v_lctx_933_, v_fvarId_934_, v_userName_935_, v_type_936_, v_value_937_, v_nondep_938_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_942_, lean_object* v_fvarId_943_, lean_object* v_userName_944_, lean_object* v_type_945_, lean_object* v_value_946_, lean_object* v_nondep_947_){
_start:
{
uint8_t v_nondep_boxed_948_; lean_object* v_res_949_; 
v_nondep_boxed_948_ = lean_unbox(v_nondep_947_);
v_res_949_ = lean_local_ctx_mk_let_decl(v_lctx_942_, v_fvarId_943_, v_userName_944_, v_type_945_, v_value_946_, v_nondep_boxed_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_950_, lean_object* v_fvarId_951_, lean_object* v_userName_952_, lean_object* v_type_953_, lean_object* v_fullName_954_){
_start:
{
lean_object* v_decls_955_; lean_object* v_fvarIdToDecl_956_; lean_object* v_auxDeclToFullName_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_972_; 
v_decls_955_ = lean_ctor_get(v_lctx_950_, 1);
v_fvarIdToDecl_956_ = lean_ctor_get(v_lctx_950_, 0);
v_auxDeclToFullName_957_ = lean_ctor_get(v_lctx_950_, 2);
v_isSharedCheck_972_ = !lean_is_exclusive(v_lctx_950_);
if (v_isSharedCheck_972_ == 0)
{
v___x_959_ = v_lctx_950_;
v_isShared_960_ = v_isSharedCheck_972_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_auxDeclToFullName_957_);
lean_inc(v_decls_955_);
lean_inc(v_fvarIdToDecl_956_);
lean_dec(v_lctx_950_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_972_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_size_961_; uint8_t v___x_962_; uint8_t v___x_963_; lean_object* v_decl_964_; lean_object* v_auxDeclToFullName_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v_size_961_ = lean_ctor_get(v_decls_955_, 2);
v___x_962_ = 0;
v___x_963_ = 2;
lean_inc_n(v_fvarId_951_, 2);
lean_inc(v_size_961_);
v_decl_964_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_964_, 0, v_size_961_);
lean_ctor_set(v_decl_964_, 1, v_fvarId_951_);
lean_ctor_set(v_decl_964_, 2, v_userName_952_);
lean_ctor_set(v_decl_964_, 3, v_type_953_);
lean_ctor_set_uint8(v_decl_964_, sizeof(void*)*4, v___x_962_);
lean_ctor_set_uint8(v_decl_964_, sizeof(void*)*4 + 1, v___x_963_);
v_auxDeclToFullName_965_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_951_, v_fullName_954_, v_auxDeclToFullName_957_);
lean_inc_ref(v_decl_964_);
v___x_966_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_956_, v_fvarId_951_, v_decl_964_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_decl_964_);
v___x_968_ = l_Lean_PersistentArray_push___redArg(v_decls_955_, v___x_967_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 2, v_auxDeclToFullName_965_);
lean_ctor_set(v___x_959_, 1, v___x_968_);
lean_ctor_set(v___x_959_, 0, v___x_966_);
v___x_970_ = v___x_959_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_auxDeclToFullName_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_973_, lean_object* v_newDecl_974_){
_start:
{
lean_object* v_decls_975_; lean_object* v_fvarIdToDecl_976_; lean_object* v_auxDeclToFullName_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_992_; 
v_decls_975_ = lean_ctor_get(v_lctx_973_, 1);
v_fvarIdToDecl_976_ = lean_ctor_get(v_lctx_973_, 0);
v_auxDeclToFullName_977_ = lean_ctor_get(v_lctx_973_, 2);
v_isSharedCheck_992_ = !lean_is_exclusive(v_lctx_973_);
if (v_isSharedCheck_992_ == 0)
{
v___x_979_ = v_lctx_973_;
v_isShared_980_ = v_isSharedCheck_992_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_auxDeclToFullName_977_);
lean_inc(v_decls_975_);
lean_inc(v_fvarIdToDecl_976_);
lean_dec(v_lctx_973_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_992_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_size_981_; lean_object* v_newDecl_982_; lean_object* v___y_984_; lean_object* v_fvarId_991_; 
v_size_981_ = lean_ctor_get(v_decls_975_, 2);
lean_inc(v_size_981_);
v_newDecl_982_ = l_Lean_LocalDecl_setIndex(v_newDecl_974_, v_size_981_);
v_fvarId_991_ = lean_ctor_get(v_newDecl_982_, 1);
lean_inc(v_fvarId_991_);
v___y_984_ = v_fvarId_991_;
goto v___jp_983_;
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
lean_inc_ref(v_newDecl_982_);
v___x_985_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_976_, v___y_984_, v_newDecl_982_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_newDecl_982_);
v___x_987_ = l_Lean_PersistentArray_push___redArg(v_decls_975_, v___x_986_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_987_);
lean_ctor_set(v___x_979_, 0, v___x_985_);
v___x_989_ = v___x_979_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_auxDeclToFullName_977_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_993_, lean_object* v_vals_994_, lean_object* v_i_995_, lean_object* v_k_996_){
_start:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_array_get_size(v_keys_993_);
v___x_998_ = lean_nat_dec_lt(v_i_995_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
lean_dec(v_i_995_);
v___x_999_ = lean_box(0);
return v___x_999_;
}
else
{
lean_object* v_k_x27_1000_; uint8_t v___x_1001_; 
v_k_x27_1000_ = lean_array_fget_borrowed(v_keys_993_, v_i_995_);
v___x_1001_ = l_Lean_instBEqFVarId_beq(v_k_996_, v_k_x27_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_i_995_, v___x_1002_);
lean_dec(v_i_995_);
v_i_995_ = v___x_1003_;
goto _start;
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_array_fget_borrowed(v_vals_994_, v_i_995_);
lean_dec(v_i_995_);
lean_inc(v___x_1005_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1007_, lean_object* v_vals_1008_, lean_object* v_i_1009_, lean_object* v_k_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1007_, v_vals_1008_, v_i_1009_, v_k_1010_);
lean_dec(v_k_1010_);
lean_dec_ref(v_vals_1008_);
lean_dec_ref(v_keys_1007_);
return v_res_1011_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_1012_, size_t v_x_1013_, lean_object* v_x_1014_){
_start:
{
if (lean_obj_tag(v_x_1012_) == 0)
{
lean_object* v_es_1015_; lean_object* v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; lean_object* v_j_1019_; lean_object* v___x_1020_; 
v_es_1015_ = lean_ctor_get(v_x_1012_, 0);
v___x_1016_ = lean_box(2);
v___x_1017_ = ((size_t)31ULL);
v___x_1018_ = lean_usize_land(v_x_1013_, v___x_1017_);
v_j_1019_ = lean_usize_to_nat(v___x_1018_);
v___x_1020_ = lean_array_get_borrowed(v___x_1016_, v_es_1015_, v_j_1019_);
lean_dec(v_j_1019_);
switch(lean_obj_tag(v___x_1020_))
{
case 0:
{
lean_object* v_key_1021_; lean_object* v_val_1022_; uint8_t v___x_1023_; 
v_key_1021_ = lean_ctor_get(v___x_1020_, 0);
v_val_1022_ = lean_ctor_get(v___x_1020_, 1);
v___x_1023_ = l_Lean_instBEqFVarId_beq(v_x_1014_, v_key_1021_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_box(0);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; 
lean_inc(v_val_1022_);
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_val_1022_);
return v___x_1025_;
}
}
case 1:
{
lean_object* v_node_1026_; size_t v___x_1027_; size_t v___x_1028_; 
v_node_1026_ = lean_ctor_get(v___x_1020_, 0);
v___x_1027_ = ((size_t)5ULL);
v___x_1028_ = lean_usize_shift_right(v_x_1013_, v___x_1027_);
v_x_1012_ = v_node_1026_;
v_x_1013_ = v___x_1028_;
goto _start;
}
default: 
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_box(0);
return v___x_1030_;
}
}
}
else
{
lean_object* v_ks_1031_; lean_object* v_vs_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_ks_1031_ = lean_ctor_get(v_x_1012_, 0);
v_vs_1032_ = lean_ctor_get(v_x_1012_, 1);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1031_, v_vs_1032_, v___x_1033_, v_x_1014_);
return v___x_1034_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1012_ = stack[0].m_obj;
size_t v_x_1013_ = stack[1].m_num;
lean_object* v_x_1014_ = stack[2].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1012_, v_x_1013_, v_x_1014_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
size_t v_x_144__boxed_1039_; lean_object* v_res_1040_; 
v_x_144__boxed_1039_ = lean_unbox_usize(v_x_1037_);
lean_dec(v_x_1037_);
v_res_1040_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1036_, v_x_144__boxed_1039_, v_x_1038_);
lean_dec(v_x_1038_);
lean_dec_ref(v_x_1036_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
uint64_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = l_Lean_instHashableFVarId_hash(v_x_1042_);
v___x_1044_ = lean_uint64_to_usize(v___x_1043_);
v___x_1045_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1041_, v___x_1044_, v_x_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1046_, v_x_1047_);
lean_dec(v_x_1047_);
lean_dec_ref(v_x_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1049_, lean_object* v_fvarId_1050_){
_start:
{
lean_object* v_fvarIdToDecl_1051_; lean_object* v___x_1052_; 
v_fvarIdToDecl_1051_ = lean_ctor_get(v_lctx_1049_, 0);
lean_inc_ref(v_fvarIdToDecl_1051_);
lean_dec_ref(v_lctx_1049_);
v___x_1052_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1051_, v_fvarId_1050_);
lean_dec(v_fvarId_1050_);
lean_dec_ref(v_fvarIdToDecl_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1054_, v_x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1057_, v_x_1058_, v_x_1059_);
lean_dec(v_x_1059_);
lean_dec_ref(v_x_1058_);
return v_res_1060_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1061_, lean_object* v_x_1062_, size_t v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1062_, v_x_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1062_ = stack[1].m_obj;
size_t v_x_1063_ = stack[2].m_num;
lean_object* v_x_1064_ = stack[3].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_box(0), v_x_1062_, v_x_1063_, v_x_1064_);
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
size_t v_x_251__boxed_1071_; lean_object* v_res_1072_; 
v_x_251__boxed_1071_ = lean_unbox_usize(v_x_1069_);
lean_dec(v_x_1069_);
v_res_1072_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1067_, v_x_1068_, v_x_251__boxed_1071_, v_x_1070_);
lean_dec(v_x_1070_);
lean_dec_ref(v_x_1068_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1073_, lean_object* v_keys_1074_, lean_object* v_vals_1075_, lean_object* v_heq_1076_, lean_object* v_i_1077_, lean_object* v_k_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1074_, v_vals_1075_, v_i_1077_, v_k_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1080_, lean_object* v_keys_1081_, lean_object* v_vals_1082_, lean_object* v_heq_1083_, lean_object* v_i_1084_, lean_object* v_k_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1080_, v_keys_1081_, v_vals_1082_, v_heq_1083_, v_i_1084_, v_k_1085_);
lean_dec(v_k_1085_);
lean_dec_ref(v_vals_1082_);
lean_dec_ref(v_keys_1081_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1087_, lean_object* v_e_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = l_Lean_Expr_fvarId_x21(v_e_1088_);
v___x_1090_ = lean_local_ctx_find(v_lctx_1087_, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1091_, lean_object* v_e_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1091_, v_e_1092_);
lean_dec_ref(v_e_1092_);
return v_res_1093_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1096_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1097_ = lean_unsigned_to_nat(14u);
v___x_1098_ = lean_unsigned_to_nat(350u);
v___x_1099_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1100_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1101_ = l_mkPanicMessageWithDecl(v___x_1100_, v___x_1099_, v___x_1098_, v___x_1097_, v___x_1096_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1102_, lean_object* v_fvarId_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_local_ctx_find(v_lctx_1102_, v_fvarId_1103_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1106_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v_val_1107_; 
v_val_1107_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v___x_1104_, 1);
return v_val_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1108_, lean_object* v_e_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = l_Lean_Expr_fvarId_x21(v_e_1109_);
v___x_1111_ = l_Lean_LocalContext_get_x21(v_lctx_1108_, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1112_, lean_object* v_e_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1112_, v_e_1113_);
lean_dec_ref(v_e_1113_);
return v_res_1114_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1115_, lean_object* v_i_1116_, lean_object* v_k_1117_){
_start:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = lean_array_get_size(v_keys_1115_);
v___x_1119_ = lean_nat_dec_lt(v_i_1116_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v_i_1116_);
return v___x_1119_;
}
else
{
lean_object* v_k_x27_1120_; uint8_t v___x_1121_; 
v_k_x27_1120_ = lean_array_fget_borrowed(v_keys_1115_, v_i_1116_);
v___x_1121_ = l_Lean_instBEqFVarId_beq(v_k_1117_, v_k_x27_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_add(v_i_1116_, v___x_1122_);
lean_dec(v_i_1116_);
v_i_1116_ = v___x_1123_;
goto _start;
}
else
{
lean_dec(v_i_1116_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1115_ = stack[0].m_obj;
lean_object* v_i_1116_ = stack[1].m_obj;
lean_object* v_k_1117_ = stack[2].m_obj;
uint8_t v_res_1125_;
v_res_1125_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1115_, v_i_1116_, v_k_1117_);
stack->m_num = v_res_1125_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1126_, lean_object* v_i_1127_, lean_object* v_k_1128_){
_start:
{
uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1126_, v_i_1127_, v_k_1128_);
lean_dec(v_k_1128_);
lean_dec_ref(v_keys_1126_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1131_, size_t v_x_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v_es_1134_; lean_object* v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v_j_1138_; lean_object* v___x_1139_; 
v_es_1134_ = lean_ctor_get(v_x_1131_, 0);
v___x_1135_ = lean_box(2);
v___x_1136_ = ((size_t)31ULL);
v___x_1137_ = lean_usize_land(v_x_1132_, v___x_1136_);
v_j_1138_ = lean_usize_to_nat(v___x_1137_);
v___x_1139_ = lean_array_get_borrowed(v___x_1135_, v_es_1134_, v_j_1138_);
lean_dec(v_j_1138_);
switch(lean_obj_tag(v___x_1139_))
{
case 0:
{
lean_object* v_key_1140_; uint8_t v___x_1141_; 
v_key_1140_ = lean_ctor_get(v___x_1139_, 0);
v___x_1141_ = l_Lean_instBEqFVarId_beq(v_x_1133_, v_key_1140_);
return v___x_1141_;
}
case 1:
{
lean_object* v_node_1142_; size_t v___x_1143_; size_t v___x_1144_; 
v_node_1142_ = lean_ctor_get(v___x_1139_, 0);
v___x_1143_ = ((size_t)5ULL);
v___x_1144_ = lean_usize_shift_right(v_x_1132_, v___x_1143_);
v_x_1131_ = v_node_1142_;
v_x_1132_ = v___x_1144_;
goto _start;
}
default: 
{
uint8_t v___x_1146_; 
v___x_1146_ = 0;
return v___x_1146_;
}
}
}
else
{
lean_object* v_ks_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_ks_1147_ = lean_ctor_get(v_x_1131_, 0);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1147_, v___x_1148_, v_x_1133_);
return v___x_1149_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1131_ = stack[0].m_obj;
size_t v_x_1132_ = stack[1].m_num;
lean_object* v_x_1133_ = stack[2].m_obj;
uint8_t v_res_1150_;
v_res_1150_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1131_, v_x_1132_, v_x_1133_);
stack->m_num = v_res_1150_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_){
_start:
{
size_t v_x_125__boxed_1154_; uint8_t v_res_1155_; lean_object* v_r_1156_; 
v_x_125__boxed_1154_ = lean_unbox_usize(v_x_1152_);
lean_dec(v_x_1152_);
v_res_1155_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1151_, v_x_125__boxed_1154_, v_x_1153_);
lean_dec(v_x_1153_);
lean_dec_ref(v_x_1151_);
v_r_1156_ = lean_box(v_res_1155_);
return v_r_1156_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
uint64_t v___x_1159_; size_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1159_ = l_Lean_instHashableFVarId_hash(v_x_1158_);
v___x_1160_ = lean_uint64_to_usize(v___x_1159_);
v___x_1161_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1157_, v___x_1160_, v_x_1158_);
return v___x_1161_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1157_ = stack[0].m_obj;
lean_object* v_x_1158_ = stack[1].m_obj;
uint8_t v_res_1162_;
v_res_1162_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1157_, v_x_1158_);
stack->m_num = v_res_1162_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
uint8_t v_res_1165_; lean_object* v_r_1166_; 
v_res_1165_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1163_, v_x_1164_);
lean_dec(v_x_1164_);
lean_dec_ref(v_x_1163_);
v_r_1166_ = lean_box(v_res_1165_);
return v_r_1166_;
}
}
uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1167_, lean_object* v_fvarId_1168_){
_start:
{
lean_object* v_fvarIdToDecl_1169_; uint8_t v___x_1170_; 
v_fvarIdToDecl_1169_ = lean_ctor_get(v_lctx_1167_, 0);
v___x_1170_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1169_, v_fvarId_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1167_ = stack[0].m_obj;
lean_object* v_fvarId_1168_ = stack[1].m_obj;
uint8_t v_res_1171_;
v_res_1171_ = l_Lean_LocalContext_contains(v_lctx_1167_, v_fvarId_1168_);
stack->m_num = v_res_1171_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1172_, lean_object* v_fvarId_1173_){
_start:
{
uint8_t v_res_1174_; lean_object* v_r_1175_; 
v_res_1174_ = l_Lean_LocalContext_contains(v_lctx_1172_, v_fvarId_1173_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_lctx_1172_);
v_r_1175_ = lean_box(v_res_1174_);
return v_r_1175_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1177_, v_x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1177_ = stack[1].m_obj;
lean_object* v_x_1178_ = stack[2].m_obj;
uint8_t v_res_1180_;
v_res_1180_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_box(0), v_x_1177_, v_x_1178_);
stack->m_num = v_res_1180_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_){
_start:
{
uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_res_1184_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1181_, v_x_1182_, v_x_1183_);
lean_dec(v_x_1183_);
lean_dec_ref(v_x_1182_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1186_, lean_object* v_x_1187_, size_t v_x_1188_, lean_object* v_x_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1187_, v_x_1188_, v_x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1187_ = stack[1].m_obj;
size_t v_x_1188_ = stack[2].m_num;
lean_object* v_x_1189_ = stack[3].m_obj;
uint8_t v_res_1191_;
v_res_1191_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_box(0), v_x_1187_, v_x_1188_, v_x_1189_);
stack->m_num = v_res_1191_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_){
_start:
{
size_t v_x_222__boxed_1196_; uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_x_222__boxed_1196_ = lean_unbox_usize(v_x_1194_);
lean_dec(v_x_1194_);
v_res_1197_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1192_, v_x_1193_, v_x_222__boxed_1196_, v_x_1195_);
lean_dec(v_x_1195_);
lean_dec_ref(v_x_1193_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1199_, lean_object* v_keys_1200_, lean_object* v_vals_1201_, lean_object* v_heq_1202_, lean_object* v_i_1203_, lean_object* v_k_1204_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1200_, v_i_1203_, v_k_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1200_ = stack[1].m_obj;
lean_object* v_vals_1201_ = stack[2].m_obj;
lean_object* v_i_1203_ = stack[4].m_obj;
lean_object* v_k_1204_ = stack[5].m_obj;
uint8_t v_res_1206_;
v_res_1206_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_box(0), v_keys_1200_, v_vals_1201_, lean_box(0), v_i_1203_, v_k_1204_);
stack->m_num = v_res_1206_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1207_, lean_object* v_keys_1208_, lean_object* v_vals_1209_, lean_object* v_heq_1210_, lean_object* v_i_1211_, lean_object* v_k_1212_){
_start:
{
uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_res_1213_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1207_, v_keys_1208_, v_vals_1209_, v_heq_1210_, v_i_1211_, v_k_1212_);
lean_dec(v_k_1212_);
lean_dec_ref(v_vals_1209_);
lean_dec_ref(v_keys_1208_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1215_, lean_object* v_e_1216_){
_start:
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = l_Lean_Expr_fvarId_x21(v_e_1216_);
v___x_1218_ = l_Lean_LocalContext_contains(v_lctx_1215_, v___x_1217_);
lean_dec(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_containsFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1215_ = stack[0].m_obj;
lean_object* v_e_1216_ = stack[1].m_obj;
uint8_t v_res_1219_;
v_res_1219_ = l_Lean_LocalContext_containsFVar(v_lctx_1215_, v_e_1216_);
stack->m_num = v_res_1219_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1220_, lean_object* v_e_1221_){
_start:
{
uint8_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Lean_LocalContext_containsFVar(v_lctx_1220_, v_e_1221_);
lean_dec_ref(v_e_1221_);
lean_dec_ref(v_lctx_1220_);
v_r_1223_ = lean_box(v_res_1222_);
return v_r_1223_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1224_, size_t v_i_1225_, size_t v_stop_1226_, lean_object* v_b_1227_){
_start:
{
lean_object* v___y_1229_; uint8_t v___x_1233_; 
v___x_1233_ = lean_usize_dec_eq(v_i_1225_, v_stop_1226_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_array_uget_borrowed(v_as_1224_, v_i_1225_);
if (lean_obj_tag(v___x_1234_) == 0)
{
v___y_1229_ = v_b_1227_;
goto v___jp_1228_;
}
else
{
lean_object* v_val_1235_; lean_object* v_fvarId_1236_; lean_object* v___x_1237_; 
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
v_fvarId_1236_ = lean_ctor_get(v_val_1235_, 1);
lean_inc(v_fvarId_1236_);
v___x_1237_ = lean_array_push(v_b_1227_, v_fvarId_1236_);
v___y_1229_ = v___x_1237_;
goto v___jp_1228_;
}
}
else
{
return v_b_1227_;
}
v___jp_1228_:
{
size_t v___x_1230_; size_t v___x_1231_; 
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_add(v_i_1225_, v___x_1230_);
v_i_1225_ = v___x_1231_;
v_b_1227_ = v___y_1229_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1224_ = stack[0].m_obj;
size_t v_i_1225_ = stack[1].m_num;
size_t v_stop_1226_ = stack[2].m_num;
lean_object* v_b_1227_ = stack[3].m_obj;
lean_object* v_res_1238_;
v_res_1238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1224_, v_i_1225_, v_stop_1226_, v_b_1227_);
stack->m_obj
 = v_res_1238_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1239_, lean_object* v_i_1240_, lean_object* v_stop_1241_, lean_object* v_b_1242_){
_start:
{
size_t v_i_boxed_1243_; size_t v_stop_boxed_1244_; lean_object* v_res_1245_; 
v_i_boxed_1243_ = lean_unbox_usize(v_i_1240_);
lean_dec(v_i_1240_);
v_stop_boxed_1244_ = lean_unbox_usize(v_stop_1241_);
lean_dec(v_stop_1241_);
v_res_1245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1239_, v_i_boxed_1243_, v_stop_boxed_1244_, v_b_1242_);
lean_dec_ref(v_as_1239_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v_cs_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_cs_1248_ = lean_ctor_get(v_x_1246_, 0);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_array_get_size(v_cs_1248_);
v___x_1251_ = lean_nat_dec_lt(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
return v_x_1247_;
}
else
{
size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = ((size_t)0ULL);
v___x_1253_ = lean_usize_of_nat(v___x_1250_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1248_, v___x_1252_, v___x_1253_, v_x_1247_);
return v___x_1254_;
}
}
else
{
lean_object* v_vs_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_vs_1255_ = lean_ctor_get(v_x_1246_, 0);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_array_get_size(v_vs_1255_);
v___x_1258_ = lean_nat_dec_lt(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
return v_x_1247_;
}
else
{
size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((size_t)0ULL);
v___x_1260_ = lean_usize_of_nat(v___x_1257_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1255_, v___x_1259_, v___x_1260_, v_x_1247_);
return v___x_1261_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1262_, size_t v_i_1263_, size_t v_stop_1264_, lean_object* v_b_1265_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_eq(v_i_1263_, v_stop_1264_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; 
v___x_1267_ = lean_array_uget_borrowed(v_as_1262_, v_i_1263_);
v___x_1268_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1267_, v_b_1265_);
v___x_1269_ = ((size_t)1ULL);
v___x_1270_ = lean_usize_add(v_i_1263_, v___x_1269_);
v_i_1263_ = v___x_1270_;
v_b_1265_ = v___x_1268_;
goto _start;
}
else
{
return v_b_1265_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1262_ = stack[0].m_obj;
size_t v_i_1263_ = stack[1].m_num;
size_t v_stop_1264_ = stack[2].m_num;
lean_object* v_b_1265_ = stack[3].m_obj;
lean_object* v_res_1272_;
v_res_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1262_, v_i_1263_, v_stop_1264_, v_b_1265_);
stack->m_obj
 = v_res_1272_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1273_, lean_object* v_i_1274_, lean_object* v_stop_1275_, lean_object* v_b_1276_){
_start:
{
size_t v_i_boxed_1277_; size_t v_stop_boxed_1278_; lean_object* v_res_1279_; 
v_i_boxed_1277_ = lean_unbox_usize(v_i_1274_);
lean_dec(v_i_1274_);
v_stop_boxed_1278_ = lean_unbox_usize(v_stop_1275_);
lean_dec(v_stop_1275_);
v_res_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1273_, v_i_boxed_1277_, v_stop_boxed_1278_, v_b_1276_);
lean_dec_ref(v_as_1273_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1280_, v_x_1281_);
lean_dec_ref(v_x_1280_);
return v_res_1282_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1283_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1284_, size_t v_x_1285_, size_t v_x_1286_, lean_object* v_x_1287_){
_start:
{
if (lean_obj_tag(v_x_1284_) == 0)
{
lean_object* v_cs_1288_; lean_object* v___x_1289_; size_t v___x_1290_; lean_object* v_j_1291_; lean_object* v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_cs_1288_ = lean_ctor_get(v_x_1284_, 0);
v___x_1289_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1290_ = lean_usize_shift_right(v_x_1285_, v_x_1286_);
v_j_1291_ = lean_usize_to_nat(v___x_1290_);
v___x_1292_ = lean_array_get_borrowed(v___x_1289_, v_cs_1288_, v_j_1291_);
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_shift_left(v___x_1293_, v_x_1286_);
v___x_1295_ = lean_usize_sub(v___x_1294_, v___x_1293_);
v___x_1296_ = lean_usize_land(v_x_1285_, v___x_1295_);
v___x_1297_ = ((size_t)5ULL);
v___x_1298_ = lean_usize_sub(v_x_1286_, v___x_1297_);
v___x_1299_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1292_, v___x_1296_, v___x_1298_, v_x_1287_);
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_add(v_j_1291_, v___x_1300_);
lean_dec(v_j_1291_);
v___x_1302_ = lean_array_get_size(v_cs_1288_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec(v___x_1301_);
return v___x_1299_;
}
else
{
size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_usize_of_nat(v___x_1301_);
lean_dec(v___x_1301_);
v___x_1305_ = lean_usize_of_nat(v___x_1302_);
v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1288_, v___x_1304_, v___x_1305_, v___x_1299_);
return v___x_1306_;
}
}
else
{
lean_object* v_vs_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_vs_1307_ = lean_ctor_get(v_x_1284_, 0);
v___x_1308_ = lean_usize_to_nat(v_x_1285_);
v___x_1309_ = lean_array_get_size(v_vs_1307_);
v___x_1310_ = lean_nat_dec_lt(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec(v___x_1308_);
return v_x_1287_;
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_usize_of_nat(v___x_1308_);
lean_dec(v___x_1308_);
v___x_1312_ = lean_usize_of_nat(v___x_1309_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1307_, v___x_1311_, v___x_1312_, v_x_1287_);
return v___x_1313_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1284_ = stack[0].m_obj;
size_t v_x_1285_ = stack[1].m_num;
size_t v_x_1286_ = stack[2].m_num;
lean_object* v_x_1287_ = stack[3].m_obj;
lean_object* v_res_1314_;
v_res_1314_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1284_, v_x_1285_, v_x_1286_, v_x_1287_);
stack->m_obj
 = v_res_1314_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
size_t v_x_1294__boxed_1319_; size_t v_x_1295__boxed_1320_; lean_object* v_res_1321_; 
v_x_1294__boxed_1319_ = lean_unbox_usize(v_x_1316_);
lean_dec(v_x_1316_);
v_x_1295__boxed_1320_ = lean_unbox_usize(v_x_1317_);
lean_dec(v_x_1317_);
v_res_1321_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1315_, v_x_1294__boxed_1319_, v_x_1295__boxed_1320_, v_x_1318_);
lean_dec_ref(v_x_1315_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1322_, lean_object* v_init_1323_, lean_object* v_start_1324_){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_nat_dec_eq(v_start_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v_root_1327_; lean_object* v_tail_1328_; size_t v_shift_1329_; lean_object* v_tailOff_1330_; uint8_t v___x_1331_; 
v_root_1327_ = lean_ctor_get(v_t_1322_, 0);
v_tail_1328_ = lean_ctor_get(v_t_1322_, 1);
v_shift_1329_ = lean_ctor_get_usize(v_t_1322_, 4);
v_tailOff_1330_ = lean_ctor_get(v_t_1322_, 3);
v___x_1331_ = lean_nat_dec_le(v_tailOff_1330_, v_start_1324_);
if (v___x_1331_ == 0)
{
size_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1332_ = lean_usize_of_nat(v_start_1324_);
v___x_1333_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1327_, v___x_1332_, v_shift_1329_, v_init_1323_);
v___x_1334_ = lean_array_get_size(v_tail_1328_);
v___x_1335_ = lean_nat_dec_lt(v___x_1325_, v___x_1334_);
if (v___x_1335_ == 0)
{
return v___x_1333_;
}
else
{
size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = lean_usize_of_nat(v___x_1334_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1328_, v___x_1336_, v___x_1337_, v___x_1333_);
return v___x_1338_;
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1339_ = lean_nat_sub(v_start_1324_, v_tailOff_1330_);
v___x_1340_ = lean_array_get_size(v_tail_1328_);
v___x_1341_ = lean_nat_dec_lt(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec(v___x_1339_);
return v_init_1323_;
}
else
{
size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = lean_usize_of_nat(v___x_1339_);
lean_dec(v___x_1339_);
v___x_1343_ = lean_usize_of_nat(v___x_1340_);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1328_, v___x_1342_, v___x_1343_, v_init_1323_);
return v___x_1344_;
}
}
}
else
{
lean_object* v_root_1345_; lean_object* v_tail_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_root_1345_ = lean_ctor_get(v_t_1322_, 0);
v_tail_1346_ = lean_ctor_get(v_t_1322_, 1);
v___x_1347_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1345_, v_init_1323_);
v___x_1348_ = lean_array_get_size(v_tail_1346_);
v___x_1349_ = lean_nat_dec_lt(v___x_1325_, v___x_1348_);
if (v___x_1349_ == 0)
{
return v___x_1347_;
}
else
{
size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = lean_usize_of_nat(v___x_1348_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1346_, v___x_1350_, v___x_1351_, v___x_1347_);
return v___x_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1353_, lean_object* v_init_1354_, lean_object* v_start_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1353_, v_init_1354_, v_start_1355_);
lean_dec(v_start_1355_);
lean_dec_ref(v_t_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1359_){
_start:
{
lean_object* v_decls_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_decls_1360_ = lean_ctor_get(v_lctx_1359_, 1);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1363_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1360_, v___x_1362_, v___x_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_LocalContext_getFVarIds(v_lctx_1364_);
lean_dec_ref(v_lctx_1364_);
return v_res_1365_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1366_, size_t v_i_1367_, lean_object* v_bs_1368_){
_start:
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_usize_dec_lt(v_i_1367_, v_sz_1366_);
if (v___x_1369_ == 0)
{
return v_bs_1368_;
}
else
{
lean_object* v_v_1370_; lean_object* v___x_1371_; lean_object* v_bs_x27_1372_; lean_object* v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
v_v_1370_ = lean_array_uget(v_bs_1368_, v_i_1367_);
v___x_1371_ = lean_unsigned_to_nat(0u);
v_bs_x27_1372_ = lean_array_uset(v_bs_1368_, v_i_1367_, v___x_1371_);
v___x_1373_ = l_Lean_mkFVar(v_v_1370_);
v___x_1374_ = ((size_t)1ULL);
v___x_1375_ = lean_usize_add(v_i_1367_, v___x_1374_);
v___x_1376_ = lean_array_uset(v_bs_x27_1372_, v_i_1367_, v___x_1373_);
v_i_1367_ = v___x_1375_;
v_bs_1368_ = v___x_1376_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1366_ = stack[0].m_num;
size_t v_i_1367_ = stack[1].m_num;
lean_object* v_bs_1368_ = stack[2].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1366_, v_i_1367_, v_bs_1368_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1379_, lean_object* v_i_1380_, lean_object* v_bs_1381_){
_start:
{
size_t v_sz_boxed_1382_; size_t v_i_boxed_1383_; lean_object* v_res_1384_; 
v_sz_boxed_1382_ = lean_unbox_usize(v_sz_1379_);
lean_dec(v_sz_1379_);
v_i_boxed_1383_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1382_, v_i_boxed_1383_, v_bs_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1385_){
_start:
{
lean_object* v___x_1386_; size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1386_ = l_Lean_LocalContext_getFVarIds(v_lctx_1385_);
v_sz_1387_ = lean_array_size(v___x_1386_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1387_, v___x_1388_, v___x_1386_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_LocalContext_getFVars(v_lctx_1390_);
lean_dec_ref(v_lctx_1390_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1392_){
_start:
{
lean_object* v_size_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_size_1393_ = lean_ctor_get(v_a_1392_, 2);
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = lean_nat_dec_eq(v_size_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_sub(v_size_1393_, v___x_1397_);
v___x_1399_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1396_, v_a_1392_, v___x_1398_);
lean_dec(v___x_1398_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_PersistentArray_pop___redArg(v_a_1392_);
v_a_1392_ = v___x_1400_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1399_, 1);
return v_a_1392_;
}
}
else
{
return v_a_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1402_, lean_object* v_t_1403_){
_start:
{
if (lean_obj_tag(v_t_1403_) == 0)
{
lean_object* v_k_1404_; lean_object* v_v_1405_; lean_object* v_l_1406_; lean_object* v_r_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_2061_; 
v_k_1404_ = lean_ctor_get(v_t_1403_, 1);
v_v_1405_ = lean_ctor_get(v_t_1403_, 2);
v_l_1406_ = lean_ctor_get(v_t_1403_, 3);
v_r_1407_ = lean_ctor_get(v_t_1403_, 4);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_t_1403_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_t_1403_, 0);
lean_dec(v_unused_2062_);
v___x_1409_ = v_t_1403_;
v_isShared_1410_ = v_isSharedCheck_2061_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_r_1407_);
lean_inc(v_l_1406_);
lean_inc(v_v_1405_);
lean_inc(v_k_1404_);
lean_dec(v_t_1403_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_2061_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
uint8_t v___x_1411_; 
v___x_1411_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1402_, v_k_1404_);
switch(v___x_1411_)
{
case 0:
{
lean_object* v_impl_1412_; lean_object* v___x_1413_; 
v_impl_1412_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1402_, v_l_1406_);
v___x_1413_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1412_) == 0)
{
if (lean_obj_tag(v_r_1407_) == 0)
{
lean_object* v_size_1414_; lean_object* v_size_1415_; lean_object* v_k_1416_; lean_object* v_v_1417_; lean_object* v_l_1418_; lean_object* v_r_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_size_1414_ = lean_ctor_get(v_impl_1412_, 0);
v_size_1415_ = lean_ctor_get(v_r_1407_, 0);
v_k_1416_ = lean_ctor_get(v_r_1407_, 1);
v_v_1417_ = lean_ctor_get(v_r_1407_, 2);
v_l_1418_ = lean_ctor_get(v_r_1407_, 3);
lean_inc(v_l_1418_);
v_r_1419_ = lean_ctor_get(v_r_1407_, 4);
v___x_1420_ = lean_unsigned_to_nat(3u);
v___x_1421_ = lean_nat_mul(v___x_1420_, v_size_1414_);
v___x_1422_ = lean_nat_dec_lt(v___x_1421_, v_size_1415_);
lean_dec(v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
lean_dec(v_l_1418_);
v___x_1423_ = lean_nat_add(v___x_1413_, v_size_1414_);
v___x_1424_ = lean_nat_add(v___x_1423_, v_size_1415_);
lean_dec(v___x_1423_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 3, v_impl_1412_);
lean_ctor_set(v___x_1409_, 0, v___x_1424_);
v___x_1426_ = v___x_1409_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v_impl_1412_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_r_1407_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1491_; 
lean_inc(v_r_1419_);
lean_inc(v_v_1417_);
lean_inc(v_k_1416_);
lean_inc(v_size_1415_);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; 
v_unused_1492_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_r_1407_, 2);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_r_1407_, 1);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_r_1407_, 0);
lean_dec(v_unused_1496_);
v___x_1429_ = v_r_1407_;
v_isShared_1430_ = v_isSharedCheck_1491_;
goto v_resetjp_1428_;
}
else
{
lean_dec(v_r_1407_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1491_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_size_1431_; lean_object* v_k_1432_; lean_object* v_v_1433_; lean_object* v_l_1434_; lean_object* v_r_1435_; lean_object* v_size_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_size_1431_ = lean_ctor_get(v_l_1418_, 0);
v_k_1432_ = lean_ctor_get(v_l_1418_, 1);
v_v_1433_ = lean_ctor_get(v_l_1418_, 2);
v_l_1434_ = lean_ctor_get(v_l_1418_, 3);
v_r_1435_ = lean_ctor_get(v_l_1418_, 4);
v_size_1436_ = lean_ctor_get(v_r_1419_, 0);
v___x_1437_ = lean_unsigned_to_nat(2u);
v___x_1438_ = lean_nat_mul(v___x_1437_, v_size_1436_);
v___x_1439_ = lean_nat_dec_lt(v_size_1431_, v___x_1438_);
lean_dec(v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1467_; 
lean_inc(v_r_1435_);
lean_inc(v_l_1434_);
lean_inc(v_v_1433_);
lean_inc(v_k_1432_);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_l_1418_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1468_ = lean_ctor_get(v_l_1418_, 4);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_l_1418_, 3);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_l_1418_, 2);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_l_1418_, 1);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_l_1418_, 0);
lean_dec(v_unused_1472_);
v___x_1441_ = v_l_1418_;
v_isShared_1442_ = v_isSharedCheck_1467_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v_l_1418_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1467_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1457_; 
v___x_1443_ = lean_nat_add(v___x_1413_, v_size_1414_);
v___x_1444_ = lean_nat_add(v___x_1443_, v_size_1415_);
lean_dec(v_size_1415_);
if (lean_obj_tag(v_l_1434_) == 0)
{
lean_object* v_size_1465_; 
v_size_1465_ = lean_ctor_get(v_l_1434_, 0);
lean_inc(v_size_1465_);
v___y_1457_ = v_size_1465_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___y_1457_ = v___x_1466_;
goto v___jp_1456_;
}
v___jp_1445_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_nat_add(v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec(v___y_1447_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_r_1419_);
lean_ctor_set(v___x_1441_, 3, v_r_1435_);
lean_ctor_set(v___x_1441_, 2, v_v_1417_);
lean_ctor_set(v___x_1441_, 1, v_k_1416_);
lean_ctor_set(v___x_1441_, 0, v___x_1449_);
v___x_1451_ = v___x_1441_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1416_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1417_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_r_1435_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_r_1419_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 4, v___x_1451_);
lean_ctor_set(v___x_1429_, 3, v___y_1446_);
lean_ctor_set(v___x_1429_, 2, v_v_1433_);
lean_ctor_set(v___x_1429_, 1, v_k_1432_);
lean_ctor_set(v___x_1429_, 0, v___x_1444_);
v___x_1453_ = v___x_1429_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1432_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1433_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v___y_1446_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
v___jp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_nat_add(v___x_1443_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec(v___x_1443_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_l_1434_);
lean_ctor_set(v___x_1409_, 3, v_impl_1412_);
lean_ctor_set(v___x_1409_, 0, v___x_1458_);
v___x_1460_ = v___x_1409_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_impl_1412_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_l_1434_);
v___x_1460_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_nat_add(v___x_1413_, v_size_1436_);
if (lean_obj_tag(v_r_1435_) == 0)
{
lean_object* v_size_1462_; 
v_size_1462_ = lean_ctor_get(v_r_1435_, 0);
lean_inc(v_size_1462_);
v___y_1446_ = v___x_1460_;
v___y_1447_ = v___x_1461_;
v___y_1448_ = v_size_1462_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___y_1446_ = v___x_1460_;
v___y_1447_ = v___x_1461_;
v___y_1448_ = v___x_1463_;
goto v___jp_1445_;
}
}
}
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_del_object(v___x_1409_);
v___x_1473_ = lean_nat_add(v___x_1413_, v_size_1414_);
v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1415_);
lean_dec(v_size_1415_);
v___x_1475_ = lean_nat_add(v___x_1473_, v_size_1431_);
lean_dec(v___x_1473_);
lean_inc_ref(v_impl_1412_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 4, v_l_1418_);
lean_ctor_set(v___x_1429_, 3, v_impl_1412_);
lean_ctor_set(v___x_1429_, 2, v_v_1405_);
lean_ctor_set(v___x_1429_, 1, v_k_1404_);
lean_ctor_set(v___x_1429_, 0, v___x_1475_);
v___x_1477_ = v___x_1429_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_impl_1412_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_l_1418_);
v___x_1477_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v_isSharedCheck_1484_ = !lean_is_exclusive(v_impl_1412_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1485_ = lean_ctor_get(v_impl_1412_, 4);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_impl_1412_, 3);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_impl_1412_, 2);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_impl_1412_, 1);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_impl_1412_, 0);
lean_dec(v_unused_1489_);
v___x_1479_ = v_impl_1412_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_dec(v_impl_1412_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 4, v_r_1419_);
lean_ctor_set(v___x_1479_, 3, v___x_1477_);
lean_ctor_set(v___x_1479_, 2, v_v_1417_);
lean_ctor_set(v___x_1479_, 1, v_k_1416_);
lean_ctor_set(v___x_1479_, 0, v___x_1474_);
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1416_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1417_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v_r_1419_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v_size_1497_ = lean_ctor_get(v_impl_1412_, 0);
v___x_1498_ = lean_nat_add(v___x_1413_, v_size_1497_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 3, v_impl_1412_);
lean_ctor_set(v___x_1409_, 0, v___x_1498_);
v___x_1500_ = v___x_1409_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_impl_1412_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_r_1407_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
if (lean_obj_tag(v_r_1407_) == 0)
{
lean_object* v_l_1502_; 
v_l_1502_ = lean_ctor_get(v_r_1407_, 3);
lean_inc(v_l_1502_);
if (lean_obj_tag(v_l_1502_) == 0)
{
lean_object* v_r_1503_; 
v_r_1503_ = lean_ctor_get(v_r_1407_, 4);
lean_inc(v_r_1503_);
if (lean_obj_tag(v_r_1503_) == 0)
{
lean_object* v_size_1504_; lean_object* v_k_1505_; lean_object* v_v_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1519_; 
v_size_1504_ = lean_ctor_get(v_r_1407_, 0);
v_k_1505_ = lean_ctor_get(v_r_1407_, 1);
v_v_1506_ = lean_ctor_get(v_r_1407_, 2);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; lean_object* v_unused_1521_; 
v_unused_1520_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1521_);
v___x_1508_ = v_r_1407_;
v_isShared_1509_ = v_isSharedCheck_1519_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_v_1506_);
lean_inc(v_k_1505_);
lean_inc(v_size_1504_);
lean_dec(v_r_1407_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1519_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_size_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v_size_1510_ = lean_ctor_get(v_l_1502_, 0);
v___x_1511_ = lean_nat_add(v___x_1413_, v_size_1504_);
lean_dec(v_size_1504_);
v___x_1512_ = lean_nat_add(v___x_1413_, v_size_1510_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_l_1502_);
lean_ctor_set(v___x_1508_, 3, v_impl_1412_);
lean_ctor_set(v___x_1508_, 2, v_v_1405_);
lean_ctor_set(v___x_1508_, 1, v_k_1404_);
lean_ctor_set(v___x_1508_, 0, v___x_1512_);
v___x_1514_ = v___x_1508_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_impl_1412_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_l_1502_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_r_1503_);
lean_ctor_set(v___x_1409_, 3, v___x_1514_);
lean_ctor_set(v___x_1409_, 2, v_v_1506_);
lean_ctor_set(v___x_1409_, 1, v_k_1505_);
lean_ctor_set(v___x_1409_, 0, v___x_1511_);
v___x_1516_ = v___x_1409_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1505_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1506_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_r_1503_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_k_1522_; lean_object* v_v_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1546_; 
v_k_1522_ = lean_ctor_get(v_r_1407_, 1);
v_v_1523_ = lean_ctor_get(v_r_1407_, 2);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; lean_object* v_unused_1548_; lean_object* v_unused_1549_; 
v_unused_1547_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_r_1407_, 0);
lean_dec(v_unused_1549_);
v___x_1525_ = v_r_1407_;
v_isShared_1526_ = v_isSharedCheck_1546_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_v_1523_);
lean_inc(v_k_1522_);
lean_dec(v_r_1407_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1546_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_k_1527_; lean_object* v_v_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1542_; 
v_k_1527_ = lean_ctor_get(v_l_1502_, 1);
v_v_1528_ = lean_ctor_get(v_l_1502_, 2);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_l_1502_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; lean_object* v_unused_1544_; lean_object* v_unused_1545_; 
v_unused_1543_ = lean_ctor_get(v_l_1502_, 4);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_l_1502_, 3);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_l_1502_, 0);
lean_dec(v_unused_1545_);
v___x_1530_ = v_l_1502_;
v_isShared_1531_ = v_isSharedCheck_1542_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_v_1528_);
lean_inc(v_k_1527_);
lean_dec(v_l_1502_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1542_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = lean_unsigned_to_nat(3u);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 4, v_r_1503_);
lean_ctor_set(v___x_1530_, 3, v_r_1503_);
lean_ctor_set(v___x_1530_, 2, v_v_1405_);
lean_ctor_set(v___x_1530_, 1, v_k_1404_);
lean_ctor_set(v___x_1530_, 0, v___x_1413_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_r_1503_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_r_1503_);
v___x_1534_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 3, v_r_1503_);
lean_ctor_set(v___x_1525_, 0, v___x_1413_);
v___x_1536_ = v___x_1525_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_k_1522_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_v_1523_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_r_1503_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_r_1503_);
v___x_1536_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_1536_);
lean_ctor_set(v___x_1409_, 3, v___x_1534_);
lean_ctor_set(v___x_1409_, 2, v_v_1528_);
lean_ctor_set(v___x_1409_, 1, v_k_1527_);
lean_ctor_set(v___x_1409_, 0, v___x_1532_);
v___x_1538_ = v___x_1409_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1527_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1528_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1550_; 
v_r_1550_ = lean_ctor_get(v_r_1407_, 4);
lean_inc(v_r_1550_);
if (lean_obj_tag(v_r_1550_) == 0)
{
lean_object* v_k_1551_; lean_object* v_v_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1563_; 
v_k_1551_ = lean_ctor_get(v_r_1407_, 1);
v_v_1552_ = lean_ctor_get(v_r_1407_, 2);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; lean_object* v_unused_1565_; lean_object* v_unused_1566_; 
v_unused_1564_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_r_1407_, 0);
lean_dec(v_unused_1566_);
v___x_1554_ = v_r_1407_;
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_v_1552_);
lean_inc(v_k_1551_);
lean_dec(v_r_1407_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_unsigned_to_nat(3u);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v_l_1502_);
lean_ctor_set(v___x_1554_, 2, v_v_1405_);
lean_ctor_set(v___x_1554_, 1, v_k_1404_);
lean_ctor_set(v___x_1554_, 0, v___x_1413_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_l_1502_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_l_1502_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_r_1550_);
lean_ctor_set(v___x_1409_, 3, v___x_1558_);
lean_ctor_set(v___x_1409_, 2, v_v_1552_);
lean_ctor_set(v___x_1409_, 1, v_k_1551_);
lean_ctor_set(v___x_1409_, 0, v___x_1556_);
v___x_1560_ = v___x_1409_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_k_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_v_1552_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_r_1550_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_size_1567_; lean_object* v_k_1568_; lean_object* v_v_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1580_; 
v_size_1567_ = lean_ctor_get(v_r_1407_, 0);
v_k_1568_ = lean_ctor_get(v_r_1407_, 1);
v_v_1569_ = lean_ctor_get(v_r_1407_, 2);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; 
v_unused_1581_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1582_);
v___x_1571_ = v_r_1407_;
v_isShared_1572_ = v_isSharedCheck_1580_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_v_1569_);
lean_inc(v_k_1568_);
lean_inc(v_size_1567_);
lean_dec(v_r_1407_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1580_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 3, v_r_1550_);
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_size_1567_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1568_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1569_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_r_1550_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v_r_1550_);
v___x_1574_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = lean_unsigned_to_nat(2u);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_1574_);
lean_ctor_set(v___x_1409_, 3, v_r_1550_);
lean_ctor_set(v___x_1409_, 0, v___x_1575_);
v___x_1577_ = v___x_1409_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_r_1550_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v___x_1574_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
else
{
lean_object* v___x_1584_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 3, v_r_1407_);
lean_ctor_set(v___x_1409_, 0, v___x_1413_);
v___x_1584_ = v___x_1409_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_r_1407_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_r_1407_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1409_);
lean_dec(v_v_1405_);
lean_dec(v_k_1404_);
if (lean_obj_tag(v_l_1406_) == 0)
{
if (lean_obj_tag(v_r_1407_) == 0)
{
lean_object* v_size_1586_; lean_object* v_k_1587_; lean_object* v_v_1588_; lean_object* v_l_1589_; lean_object* v_r_1590_; lean_object* v_size_1591_; lean_object* v_k_1592_; lean_object* v_v_1593_; lean_object* v_l_1594_; lean_object* v_r_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_size_1586_ = lean_ctor_get(v_l_1406_, 0);
v_k_1587_ = lean_ctor_get(v_l_1406_, 1);
v_v_1588_ = lean_ctor_get(v_l_1406_, 2);
v_l_1589_ = lean_ctor_get(v_l_1406_, 3);
v_r_1590_ = lean_ctor_get(v_l_1406_, 4);
lean_inc(v_r_1590_);
v_size_1591_ = lean_ctor_get(v_r_1407_, 0);
v_k_1592_ = lean_ctor_get(v_r_1407_, 1);
v_v_1593_ = lean_ctor_get(v_r_1407_, 2);
v_l_1594_ = lean_ctor_get(v_r_1407_, 3);
lean_inc(v_l_1594_);
v_r_1595_ = lean_ctor_get(v_r_1407_, 4);
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_nat_dec_lt(v_size_1586_, v_size_1591_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1733_; 
lean_inc(v_l_1589_);
lean_inc(v_v_1588_);
lean_inc(v_k_1587_);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_l_1406_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; lean_object* v_unused_1735_; lean_object* v_unused_1736_; lean_object* v_unused_1737_; lean_object* v_unused_1738_; 
v_unused_1734_ = lean_ctor_get(v_l_1406_, 4);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_l_1406_, 3);
lean_dec(v_unused_1735_);
v_unused_1736_ = lean_ctor_get(v_l_1406_, 2);
lean_dec(v_unused_1736_);
v_unused_1737_ = lean_ctor_get(v_l_1406_, 1);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_l_1406_, 0);
lean_dec(v_unused_1738_);
v___x_1599_ = v_l_1406_;
v_isShared_1600_ = v_isSharedCheck_1733_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v_l_1406_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1733_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v_tree_1602_; 
v___x_1601_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1587_, v_v_1588_, v_l_1589_, v_r_1590_);
v_tree_1602_ = lean_ctor_get(v___x_1601_, 2);
if (lean_obj_tag(v_tree_1602_) == 0)
{
lean_object* v_k_1603_; lean_object* v_v_1604_; lean_object* v_size_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
lean_inc_ref(v_tree_1602_);
v_k_1603_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_k_1603_);
v_v_1604_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_v_1604_);
lean_dec_ref(v___x_1601_);
v_size_1605_ = lean_ctor_get(v_tree_1602_, 0);
v___x_1606_ = lean_unsigned_to_nat(3u);
v___x_1607_ = lean_nat_mul(v___x_1606_, v_size_1605_);
v___x_1608_ = lean_nat_dec_lt(v___x_1607_, v_size_1591_);
lean_dec(v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
lean_dec(v_l_1594_);
v___x_1609_ = lean_nat_add(v___x_1596_, v_size_1605_);
v___x_1610_ = lean_nat_add(v___x_1609_, v_size_1591_);
lean_dec(v___x_1609_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v_r_1407_);
lean_ctor_set(v___x_1599_, 3, v_tree_1602_);
lean_ctor_set(v___x_1599_, 2, v_v_1604_);
lean_ctor_set(v___x_1599_, 1, v_k_1603_);
lean_ctor_set(v___x_1599_, 0, v___x_1610_);
v___x_1612_ = v___x_1599_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1603_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1604_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_tree_1602_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_r_1407_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
else
{
lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1668_; 
lean_inc(v_r_1595_);
lean_inc(v_v_1593_);
lean_inc(v_k_1592_);
lean_inc(v_size_1591_);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; 
v_unused_1669_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_r_1407_, 2);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_r_1407_, 1);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_r_1407_, 0);
lean_dec(v_unused_1673_);
v___x_1615_ = v_r_1407_;
v_isShared_1616_ = v_isSharedCheck_1668_;
goto v_resetjp_1614_;
}
else
{
lean_dec(v_r_1407_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1668_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_size_1617_; lean_object* v_k_1618_; lean_object* v_v_1619_; lean_object* v_l_1620_; lean_object* v_r_1621_; lean_object* v_size_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_size_1617_ = lean_ctor_get(v_l_1594_, 0);
v_k_1618_ = lean_ctor_get(v_l_1594_, 1);
v_v_1619_ = lean_ctor_get(v_l_1594_, 2);
v_l_1620_ = lean_ctor_get(v_l_1594_, 3);
v_r_1621_ = lean_ctor_get(v_l_1594_, 4);
v_size_1622_ = lean_ctor_get(v_r_1595_, 0);
v___x_1623_ = lean_unsigned_to_nat(2u);
v___x_1624_ = lean_nat_mul(v___x_1623_, v_size_1622_);
v___x_1625_ = lean_nat_dec_lt(v_size_1617_, v___x_1624_);
lean_dec(v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1653_; 
lean_inc(v_r_1621_);
lean_inc(v_l_1620_);
lean_inc(v_v_1619_);
lean_inc(v_k_1618_);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_l_1594_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; lean_object* v_unused_1658_; 
v_unused_1654_ = lean_ctor_get(v_l_1594_, 4);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_l_1594_, 3);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_l_1594_, 2);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_l_1594_, 1);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_l_1594_, 0);
lean_dec(v_unused_1658_);
v___x_1627_ = v_l_1594_;
v_isShared_1628_ = v_isSharedCheck_1653_;
goto v_resetjp_1626_;
}
else
{
lean_dec(v_l_1594_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1653_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1643_; 
v___x_1629_ = lean_nat_add(v___x_1596_, v_size_1605_);
v___x_1630_ = lean_nat_add(v___x_1629_, v_size_1591_);
lean_dec(v_size_1591_);
if (lean_obj_tag(v_l_1620_) == 0)
{
lean_object* v_size_1651_; 
v_size_1651_ = lean_ctor_get(v_l_1620_, 0);
lean_inc(v_size_1651_);
v___y_1643_ = v_size_1651_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_unsigned_to_nat(0u);
v___y_1643_ = v___x_1652_;
goto v___jp_1642_;
}
v___jp_1631_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1635_ = lean_nat_add(v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec(v___y_1633_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 4, v_r_1595_);
lean_ctor_set(v___x_1627_, 3, v_r_1621_);
lean_ctor_set(v___x_1627_, 2, v_v_1593_);
lean_ctor_set(v___x_1627_, 1, v_k_1592_);
lean_ctor_set(v___x_1627_, 0, v___x_1635_);
v___x_1637_ = v___x_1627_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_r_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_r_1595_);
v___x_1637_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 4, v___x_1637_);
lean_ctor_set(v___x_1615_, 3, v___y_1632_);
lean_ctor_set(v___x_1615_, 2, v_v_1619_);
lean_ctor_set(v___x_1615_, 1, v_k_1618_);
lean_ctor_set(v___x_1615_, 0, v___x_1630_);
v___x_1639_ = v___x_1615_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1618_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1619_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v___y_1632_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
v___jp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_nat_add(v___x_1629_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec(v___x_1629_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v_l_1620_);
lean_ctor_set(v___x_1599_, 3, v_tree_1602_);
lean_ctor_set(v___x_1599_, 2, v_v_1604_);
lean_ctor_set(v___x_1599_, 1, v_k_1603_);
lean_ctor_set(v___x_1599_, 0, v___x_1644_);
v___x_1646_ = v___x_1599_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1603_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1604_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_tree_1602_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_l_1620_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_nat_add(v___x_1596_, v_size_1622_);
if (lean_obj_tag(v_r_1621_) == 0)
{
lean_object* v_size_1648_; 
v_size_1648_ = lean_ctor_get(v_r_1621_, 0);
lean_inc(v_size_1648_);
v___y_1632_ = v___x_1646_;
v___y_1633_ = v___x_1647_;
v___y_1634_ = v_size_1648_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_unsigned_to_nat(0u);
v___y_1632_ = v___x_1646_;
v___y_1633_ = v___x_1647_;
v___y_1634_ = v___x_1649_;
goto v___jp_1631_;
}
}
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1659_ = lean_nat_add(v___x_1596_, v_size_1605_);
v___x_1660_ = lean_nat_add(v___x_1659_, v_size_1591_);
lean_dec(v_size_1591_);
v___x_1661_ = lean_nat_add(v___x_1659_, v_size_1617_);
lean_dec(v___x_1659_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 4, v_l_1594_);
lean_ctor_set(v___x_1615_, 3, v_tree_1602_);
lean_ctor_set(v___x_1615_, 2, v_v_1604_);
lean_ctor_set(v___x_1615_, 1, v_k_1603_);
lean_ctor_set(v___x_1615_, 0, v___x_1661_);
v___x_1663_ = v___x_1615_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1603_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1604_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_tree_1602_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_l_1594_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v_r_1595_);
lean_ctor_set(v___x_1599_, 3, v___x_1663_);
lean_ctor_set(v___x_1599_, 2, v_v_1593_);
lean_ctor_set(v___x_1599_, 1, v_k_1592_);
lean_ctor_set(v___x_1599_, 0, v___x_1660_);
v___x_1665_ = v___x_1599_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_r_1595_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
else
{
lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1727_; 
lean_inc(v_r_1595_);
lean_inc(v_v_1593_);
lean_inc(v_k_1592_);
lean_inc(v_size_1591_);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; lean_object* v_unused_1729_; lean_object* v_unused_1730_; lean_object* v_unused_1731_; lean_object* v_unused_1732_; 
v_unused_1728_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1729_);
v_unused_1730_ = lean_ctor_get(v_r_1407_, 2);
lean_dec(v_unused_1730_);
v_unused_1731_ = lean_ctor_get(v_r_1407_, 1);
lean_dec(v_unused_1731_);
v_unused_1732_ = lean_ctor_get(v_r_1407_, 0);
lean_dec(v_unused_1732_);
v___x_1675_ = v_r_1407_;
v_isShared_1676_ = v_isSharedCheck_1727_;
goto v_resetjp_1674_;
}
else
{
lean_dec(v_r_1407_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1727_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
if (lean_obj_tag(v_l_1594_) == 0)
{
if (lean_obj_tag(v_r_1595_) == 0)
{
lean_object* v_k_1677_; lean_object* v_v_1678_; lean_object* v_size_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
lean_inc(v_tree_1602_);
v_k_1677_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_k_1677_);
v_v_1678_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_v_1678_);
lean_dec_ref(v___x_1601_);
v_size_1679_ = lean_ctor_get(v_l_1594_, 0);
v___x_1680_ = lean_nat_add(v___x_1596_, v_size_1591_);
lean_dec(v_size_1591_);
v___x_1681_ = lean_nat_add(v___x_1596_, v_size_1679_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 4, v_l_1594_);
lean_ctor_set(v___x_1675_, 3, v_tree_1602_);
lean_ctor_set(v___x_1675_, 2, v_v_1678_);
lean_ctor_set(v___x_1675_, 1, v_k_1677_);
lean_ctor_set(v___x_1675_, 0, v___x_1681_);
v___x_1683_ = v___x_1675_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1677_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_tree_1602_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_l_1594_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v_r_1595_);
lean_ctor_set(v___x_1599_, 3, v___x_1683_);
lean_ctor_set(v___x_1599_, 2, v_v_1593_);
lean_ctor_set(v___x_1599_, 1, v_k_1592_);
lean_ctor_set(v___x_1599_, 0, v___x_1680_);
v___x_1685_ = v___x_1599_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_r_1595_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_object* v_k_1688_; lean_object* v_v_1689_; lean_object* v_k_1690_; lean_object* v_v_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_size_1591_);
v_k_1688_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_k_1688_);
v_v_1689_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_v_1689_);
lean_dec_ref(v___x_1601_);
v_k_1690_ = lean_ctor_get(v_l_1594_, 1);
v_v_1691_ = lean_ctor_get(v_l_1594_, 2);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_l_1594_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; 
v_unused_1706_ = lean_ctor_get(v_l_1594_, 4);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_l_1594_, 3);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_l_1594_, 0);
lean_dec(v_unused_1708_);
v___x_1693_ = v_l_1594_;
v_isShared_1694_ = v_isSharedCheck_1705_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_v_1691_);
lean_inc(v_k_1690_);
lean_dec(v_l_1594_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1705_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_unsigned_to_nat(3u);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 4, v_r_1595_);
lean_ctor_set(v___x_1693_, 3, v_r_1595_);
lean_ctor_set(v___x_1693_, 2, v_v_1689_);
lean_ctor_set(v___x_1693_, 1, v_k_1688_);
lean_ctor_set(v___x_1693_, 0, v___x_1596_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_k_1688_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_v_1689_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_r_1595_);
lean_ctor_set(v_reuseFailAlloc_1704_, 4, v_r_1595_);
v___x_1697_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1699_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 3, v_r_1595_);
lean_ctor_set(v___x_1675_, 0, v___x_1596_);
v___x_1699_ = v___x_1675_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_r_1595_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_r_1595_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v___x_1699_);
lean_ctor_set(v___x_1599_, 3, v___x_1697_);
lean_ctor_set(v___x_1599_, 2, v_v_1691_);
lean_ctor_set(v___x_1599_, 1, v_k_1690_);
lean_ctor_set(v___x_1599_, 0, v___x_1695_);
v___x_1701_ = v___x_1599_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_k_1690_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_v_1691_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1595_) == 0)
{
lean_object* v_k_1709_; lean_object* v_v_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_dec(v_size_1591_);
v_k_1709_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_k_1709_);
v_v_1710_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_v_1710_);
lean_dec_ref(v___x_1601_);
v___x_1711_ = lean_unsigned_to_nat(3u);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 4, v_l_1594_);
lean_ctor_set(v___x_1675_, 2, v_v_1710_);
lean_ctor_set(v___x_1675_, 1, v_k_1709_);
lean_ctor_set(v___x_1675_, 0, v___x_1596_);
v___x_1713_ = v___x_1675_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_k_1709_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_v_1710_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_l_1594_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v_l_1594_);
v___x_1713_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1715_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v_r_1595_);
lean_ctor_set(v___x_1599_, 3, v___x_1713_);
lean_ctor_set(v___x_1599_, 2, v_v_1593_);
lean_ctor_set(v___x_1599_, 1, v_k_1592_);
lean_ctor_set(v___x_1599_, 0, v___x_1711_);
v___x_1715_ = v___x_1599_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v_r_1595_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_k_1718_; lean_object* v_v_1719_; lean_object* v___x_1721_; 
v_k_1718_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_k_1718_);
v_v_1719_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_v_1719_);
lean_dec_ref(v___x_1601_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 3, v_r_1595_);
v___x_1721_ = v___x_1675_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_size_1591_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_r_1595_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_r_1595_);
v___x_1721_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_unsigned_to_nat(2u);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 4, v___x_1721_);
lean_ctor_set(v___x_1599_, 3, v_r_1595_);
lean_ctor_set(v___x_1599_, 2, v_v_1719_);
lean_ctor_set(v___x_1599_, 1, v_k_1718_);
lean_ctor_set(v___x_1599_, 0, v___x_1722_);
v___x_1724_ = v___x_1599_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_r_1595_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___x_1721_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
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
lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1891_; 
lean_inc(v_r_1595_);
lean_inc(v_v_1593_);
lean_inc(v_k_1592_);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; lean_object* v_unused_1893_; lean_object* v_unused_1894_; lean_object* v_unused_1895_; lean_object* v_unused_1896_; 
v_unused_1892_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1892_);
v_unused_1893_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1893_);
v_unused_1894_ = lean_ctor_get(v_r_1407_, 2);
lean_dec(v_unused_1894_);
v_unused_1895_ = lean_ctor_get(v_r_1407_, 1);
lean_dec(v_unused_1895_);
v_unused_1896_ = lean_ctor_get(v_r_1407_, 0);
lean_dec(v_unused_1896_);
v___x_1740_ = v_r_1407_;
v_isShared_1741_ = v_isSharedCheck_1891_;
goto v_resetjp_1739_;
}
else
{
lean_dec(v_r_1407_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1891_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v_tree_1743_; 
v___x_1742_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1592_, v_v_1593_, v_l_1594_, v_r_1595_);
v_tree_1743_ = lean_ctor_get(v___x_1742_, 2);
lean_inc(v_tree_1743_);
if (lean_obj_tag(v_tree_1743_) == 0)
{
lean_object* v_k_1744_; lean_object* v_v_1745_; lean_object* v_size_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_k_1744_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_k_1744_);
v_v_1745_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_v_1745_);
lean_dec_ref(v___x_1742_);
v_size_1746_ = lean_ctor_get(v_tree_1743_, 0);
v___x_1747_ = lean_unsigned_to_nat(3u);
v___x_1748_ = lean_nat_mul(v___x_1747_, v_size_1746_);
v___x_1749_ = lean_nat_dec_lt(v___x_1748_, v_size_1586_);
lean_dec(v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
lean_dec(v_r_1590_);
v___x_1750_ = lean_nat_add(v___x_1596_, v_size_1586_);
v___x_1751_ = lean_nat_add(v___x_1750_, v_size_1746_);
lean_dec(v___x_1750_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v_tree_1743_);
lean_ctor_set(v___x_1740_, 3, v_l_1406_);
lean_ctor_set(v___x_1740_, 2, v_v_1745_);
lean_ctor_set(v___x_1740_, 1, v_k_1744_);
lean_ctor_set(v___x_1740_, 0, v___x_1751_);
v___x_1753_ = v___x_1740_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_k_1744_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_v_1745_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v_tree_1743_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
else
{
lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1820_; 
lean_inc(v_l_1589_);
lean_inc(v_v_1588_);
lean_inc(v_k_1587_);
lean_inc(v_size_1586_);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_l_1406_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; lean_object* v_unused_1822_; lean_object* v_unused_1823_; lean_object* v_unused_1824_; lean_object* v_unused_1825_; 
v_unused_1821_ = lean_ctor_get(v_l_1406_, 4);
lean_dec(v_unused_1821_);
v_unused_1822_ = lean_ctor_get(v_l_1406_, 3);
lean_dec(v_unused_1822_);
v_unused_1823_ = lean_ctor_get(v_l_1406_, 2);
lean_dec(v_unused_1823_);
v_unused_1824_ = lean_ctor_get(v_l_1406_, 1);
lean_dec(v_unused_1824_);
v_unused_1825_ = lean_ctor_get(v_l_1406_, 0);
lean_dec(v_unused_1825_);
v___x_1756_ = v_l_1406_;
v_isShared_1757_ = v_isSharedCheck_1820_;
goto v_resetjp_1755_;
}
else
{
lean_dec(v_l_1406_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1820_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_size_1758_; lean_object* v_size_1759_; lean_object* v_k_1760_; lean_object* v_v_1761_; lean_object* v_l_1762_; lean_object* v_r_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_size_1758_ = lean_ctor_get(v_l_1589_, 0);
v_size_1759_ = lean_ctor_get(v_r_1590_, 0);
v_k_1760_ = lean_ctor_get(v_r_1590_, 1);
v_v_1761_ = lean_ctor_get(v_r_1590_, 2);
v_l_1762_ = lean_ctor_get(v_r_1590_, 3);
v_r_1763_ = lean_ctor_get(v_r_1590_, 4);
v___x_1764_ = lean_unsigned_to_nat(2u);
v___x_1765_ = lean_nat_mul(v___x_1764_, v_size_1758_);
v___x_1766_ = lean_nat_dec_lt(v_size_1759_, v___x_1765_);
lean_dec(v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1804_; 
lean_inc(v_r_1763_);
lean_inc(v_l_1762_);
lean_inc(v_v_1761_);
lean_inc(v_k_1760_);
lean_del_object(v___x_1756_);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_r_1590_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; lean_object* v_unused_1806_; lean_object* v_unused_1807_; lean_object* v_unused_1808_; lean_object* v_unused_1809_; 
v_unused_1805_ = lean_ctor_get(v_r_1590_, 4);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v_r_1590_, 3);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_r_1590_, 2);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v_r_1590_, 1);
lean_dec(v_unused_1808_);
v_unused_1809_ = lean_ctor_get(v_r_1590_, 0);
lean_dec(v_unused_1809_);
v___x_1768_ = v_r_1590_;
v_isShared_1769_ = v_isSharedCheck_1804_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v_r_1590_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1804_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___x_1792_; lean_object* v___y_1794_; 
v___x_1770_ = lean_nat_add(v___x_1596_, v_size_1586_);
lean_dec(v_size_1586_);
v___x_1771_ = lean_nat_add(v___x_1770_, v_size_1746_);
lean_dec(v___x_1770_);
v___x_1792_ = lean_nat_add(v___x_1596_, v_size_1758_);
if (lean_obj_tag(v_l_1762_) == 0)
{
lean_object* v_size_1802_; 
v_size_1802_ = lean_ctor_get(v_l_1762_, 0);
lean_inc(v_size_1802_);
v___y_1794_ = v_size_1802_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_unsigned_to_nat(0u);
v___y_1794_ = v___x_1803_;
goto v___jp_1793_;
}
v___jp_1772_:
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = lean_nat_add(v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec(v___y_1774_);
lean_inc_ref(v_tree_1743_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 4, v_tree_1743_);
lean_ctor_set(v___x_1768_, 3, v_r_1763_);
lean_ctor_set(v___x_1768_, 2, v_v_1745_);
lean_ctor_set(v___x_1768_, 1, v_k_1744_);
lean_ctor_set(v___x_1768_, 0, v___x_1776_);
v___x_1778_ = v___x_1768_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_k_1744_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_v_1745_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_r_1763_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_tree_1743_);
v___x_1778_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_isSharedCheck_1785_ = !lean_is_exclusive(v_tree_1743_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; lean_object* v_unused_1787_; lean_object* v_unused_1788_; lean_object* v_unused_1789_; lean_object* v_unused_1790_; 
v_unused_1786_ = lean_ctor_get(v_tree_1743_, 4);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v_tree_1743_, 3);
lean_dec(v_unused_1787_);
v_unused_1788_ = lean_ctor_get(v_tree_1743_, 2);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v_tree_1743_, 1);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_tree_1743_, 0);
lean_dec(v_unused_1790_);
v___x_1780_ = v_tree_1743_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_dec(v_tree_1743_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 4, v___x_1778_);
lean_ctor_set(v___x_1780_, 3, v___y_1773_);
lean_ctor_set(v___x_1780_, 2, v_v_1761_);
lean_ctor_set(v___x_1780_, 1, v_k_1760_);
lean_ctor_set(v___x_1780_, 0, v___x_1771_);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_k_1760_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_v_1761_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v___y_1773_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v___x_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
v___jp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = lean_nat_add(v___x_1792_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec(v___x_1792_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v_l_1762_);
lean_ctor_set(v___x_1740_, 3, v_l_1589_);
lean_ctor_set(v___x_1740_, 2, v_v_1588_);
lean_ctor_set(v___x_1740_, 1, v_k_1587_);
lean_ctor_set(v___x_1740_, 0, v___x_1795_);
v___x_1797_ = v___x_1740_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_l_1589_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v_l_1762_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_nat_add(v___x_1596_, v_size_1746_);
if (lean_obj_tag(v_r_1763_) == 0)
{
lean_object* v_size_1799_; 
v_size_1799_ = lean_ctor_get(v_r_1763_, 0);
lean_inc(v_size_1799_);
v___y_1773_ = v___x_1797_;
v___y_1774_ = v___x_1798_;
v___y_1775_ = v_size_1799_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___y_1773_ = v___x_1797_;
v___y_1774_ = v___x_1798_;
v___y_1775_ = v___x_1800_;
goto v___jp_1772_;
}
}
}
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1810_ = lean_nat_add(v___x_1596_, v_size_1586_);
lean_dec(v_size_1586_);
v___x_1811_ = lean_nat_add(v___x_1810_, v_size_1746_);
lean_dec(v___x_1810_);
v___x_1812_ = lean_nat_add(v___x_1596_, v_size_1746_);
v___x_1813_ = lean_nat_add(v___x_1812_, v_size_1759_);
lean_dec(v___x_1812_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v_tree_1743_);
lean_ctor_set(v___x_1740_, 3, v_r_1590_);
lean_ctor_set(v___x_1740_, 2, v_v_1745_);
lean_ctor_set(v___x_1740_, 1, v_k_1744_);
lean_ctor_set(v___x_1740_, 0, v___x_1813_);
v___x_1815_ = v___x_1740_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_k_1744_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_v_1745_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_r_1590_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v_tree_1743_);
v___x_1815_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1817_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 4, v___x_1815_);
lean_ctor_set(v___x_1756_, 0, v___x_1811_);
v___x_1817_ = v___x_1756_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_l_1589_);
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
}
}
}
else
{
if (lean_obj_tag(v_l_1589_) == 0)
{
lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1849_; 
lean_inc_ref(v_l_1589_);
lean_inc(v_v_1588_);
lean_inc(v_k_1587_);
lean_inc(v_size_1586_);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_l_1406_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; 
v_unused_1850_ = lean_ctor_get(v_l_1406_, 4);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_l_1406_, 3);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_l_1406_, 2);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_l_1406_, 1);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_l_1406_, 0);
lean_dec(v_unused_1854_);
v___x_1827_ = v_l_1406_;
v_isShared_1828_ = v_isSharedCheck_1849_;
goto v_resetjp_1826_;
}
else
{
lean_dec(v_l_1406_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1849_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
if (lean_obj_tag(v_r_1590_) == 0)
{
lean_object* v_k_1829_; lean_object* v_v_1830_; lean_object* v_size_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v_k_1829_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_k_1829_);
v_v_1830_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_v_1830_);
lean_dec_ref(v___x_1742_);
v_size_1831_ = lean_ctor_get(v_r_1590_, 0);
v___x_1832_ = lean_nat_add(v___x_1596_, v_size_1586_);
lean_dec(v_size_1586_);
v___x_1833_ = lean_nat_add(v___x_1596_, v_size_1831_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v_tree_1743_);
lean_ctor_set(v___x_1740_, 3, v_r_1590_);
lean_ctor_set(v___x_1740_, 2, v_v_1830_);
lean_ctor_set(v___x_1740_, 1, v_k_1829_);
lean_ctor_set(v___x_1740_, 0, v___x_1833_);
v___x_1835_ = v___x_1740_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_k_1829_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_v_1830_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v_r_1590_);
lean_ctor_set(v_reuseFailAlloc_1839_, 4, v_tree_1743_);
v___x_1835_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 4, v___x_1835_);
lean_ctor_set(v___x_1827_, 0, v___x_1832_);
v___x_1837_ = v___x_1827_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1838_, 3, v_l_1589_);
lean_ctor_set(v_reuseFailAlloc_1838_, 4, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v_k_1840_; lean_object* v_v_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_dec(v_size_1586_);
v_k_1840_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_k_1840_);
v_v_1841_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_v_1841_);
lean_dec_ref(v___x_1742_);
v___x_1842_ = lean_unsigned_to_nat(3u);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v_r_1590_);
lean_ctor_set(v___x_1740_, 3, v_r_1590_);
lean_ctor_set(v___x_1740_, 2, v_v_1841_);
lean_ctor_set(v___x_1740_, 1, v_k_1840_);
lean_ctor_set(v___x_1740_, 0, v___x_1596_);
v___x_1844_ = v___x_1740_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_k_1840_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_v_1841_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_r_1590_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_r_1590_);
v___x_1844_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 4, v___x_1844_);
lean_ctor_set(v___x_1827_, 0, v___x_1842_);
v___x_1846_ = v___x_1827_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_l_1589_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1590_) == 0)
{
lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1879_; 
lean_inc(v_l_1589_);
lean_inc(v_v_1588_);
lean_inc(v_k_1587_);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_l_1406_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; lean_object* v_unused_1881_; lean_object* v_unused_1882_; lean_object* v_unused_1883_; lean_object* v_unused_1884_; 
v_unused_1880_ = lean_ctor_get(v_l_1406_, 4);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_l_1406_, 3);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_l_1406_, 2);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_l_1406_, 1);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_l_1406_, 0);
lean_dec(v_unused_1884_);
v___x_1856_ = v_l_1406_;
v_isShared_1857_ = v_isSharedCheck_1879_;
goto v_resetjp_1855_;
}
else
{
lean_dec(v_l_1406_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1879_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_k_1858_; lean_object* v_v_1859_; lean_object* v_k_1860_; lean_object* v_v_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1875_; 
v_k_1858_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_k_1858_);
v_v_1859_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_v_1859_);
lean_dec_ref(v___x_1742_);
v_k_1860_ = lean_ctor_get(v_r_1590_, 1);
v_v_1861_ = lean_ctor_get(v_r_1590_, 2);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_r_1590_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; lean_object* v_unused_1877_; lean_object* v_unused_1878_; 
v_unused_1876_ = lean_ctor_get(v_r_1590_, 4);
lean_dec(v_unused_1876_);
v_unused_1877_ = lean_ctor_get(v_r_1590_, 3);
lean_dec(v_unused_1877_);
v_unused_1878_ = lean_ctor_get(v_r_1590_, 0);
lean_dec(v_unused_1878_);
v___x_1863_ = v_r_1590_;
v_isShared_1864_ = v_isSharedCheck_1875_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_v_1861_);
lean_inc(v_k_1860_);
lean_dec(v_r_1590_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1875_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = lean_unsigned_to_nat(3u);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 4, v_l_1589_);
lean_ctor_set(v___x_1863_, 3, v_l_1589_);
lean_ctor_set(v___x_1863_, 2, v_v_1588_);
lean_ctor_set(v___x_1863_, 1, v_k_1587_);
lean_ctor_set(v___x_1863_, 0, v___x_1596_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_l_1589_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_l_1589_);
v___x_1867_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v_l_1589_);
lean_ctor_set(v___x_1740_, 3, v_l_1589_);
lean_ctor_set(v___x_1740_, 2, v_v_1859_);
lean_ctor_set(v___x_1740_, 1, v_k_1858_);
lean_ctor_set(v___x_1740_, 0, v___x_1596_);
v___x_1869_ = v___x_1740_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_k_1858_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_v_1859_);
lean_ctor_set(v_reuseFailAlloc_1873_, 3, v_l_1589_);
lean_ctor_set(v_reuseFailAlloc_1873_, 4, v_l_1589_);
v___x_1869_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1871_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 4, v___x_1869_);
lean_ctor_set(v___x_1856_, 3, v___x_1867_);
lean_ctor_set(v___x_1856_, 2, v_v_1861_);
lean_ctor_set(v___x_1856_, 1, v_k_1860_);
lean_ctor_set(v___x_1856_, 0, v___x_1865_);
v___x_1871_ = v___x_1856_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_k_1860_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_v_1861_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1872_, 4, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
else
{
lean_object* v_k_1885_; lean_object* v_v_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v_k_1885_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_k_1885_);
v_v_1886_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_v_1886_);
lean_dec_ref(v___x_1742_);
v___x_1887_ = lean_unsigned_to_nat(2u);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v_r_1590_);
lean_ctor_set(v___x_1740_, 3, v_l_1406_);
lean_ctor_set(v___x_1740_, 2, v_v_1886_);
lean_ctor_set(v___x_1740_, 1, v_k_1885_);
lean_ctor_set(v___x_1740_, 0, v___x_1887_);
v___x_1889_ = v___x_1740_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_k_1885_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_v_1886_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_r_1590_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
}
else
{
return v_l_1406_;
}
}
else
{
return v_r_1407_;
}
}
default: 
{
lean_object* v_impl_1897_; lean_object* v___x_1898_; 
v_impl_1897_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1402_, v_r_1407_);
v___x_1898_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1897_) == 0)
{
if (lean_obj_tag(v_l_1406_) == 0)
{
lean_object* v_size_1899_; lean_object* v_size_1900_; lean_object* v_k_1901_; lean_object* v_v_1902_; lean_object* v_l_1903_; lean_object* v_r_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_size_1899_ = lean_ctor_get(v_impl_1897_, 0);
v_size_1900_ = lean_ctor_get(v_l_1406_, 0);
v_k_1901_ = lean_ctor_get(v_l_1406_, 1);
v_v_1902_ = lean_ctor_get(v_l_1406_, 2);
v_l_1903_ = lean_ctor_get(v_l_1406_, 3);
v_r_1904_ = lean_ctor_get(v_l_1406_, 4);
lean_inc(v_r_1904_);
v___x_1905_ = lean_unsigned_to_nat(3u);
v___x_1906_ = lean_nat_mul(v___x_1905_, v_size_1899_);
v___x_1907_ = lean_nat_dec_lt(v___x_1906_, v_size_1900_);
lean_dec(v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec(v_r_1904_);
v___x_1908_ = lean_nat_add(v___x_1898_, v_size_1900_);
v___x_1909_ = lean_nat_add(v___x_1908_, v_size_1899_);
lean_dec(v___x_1908_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_impl_1897_);
lean_ctor_set(v___x_1409_, 0, v___x_1909_);
v___x_1911_ = v___x_1409_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_impl_1897_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1978_; 
lean_inc(v_l_1903_);
lean_inc(v_v_1902_);
lean_inc(v_k_1901_);
lean_inc(v_size_1900_);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_l_1406_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; lean_object* v_unused_1980_; lean_object* v_unused_1981_; lean_object* v_unused_1982_; lean_object* v_unused_1983_; 
v_unused_1979_ = lean_ctor_get(v_l_1406_, 4);
lean_dec(v_unused_1979_);
v_unused_1980_ = lean_ctor_get(v_l_1406_, 3);
lean_dec(v_unused_1980_);
v_unused_1981_ = lean_ctor_get(v_l_1406_, 2);
lean_dec(v_unused_1981_);
v_unused_1982_ = lean_ctor_get(v_l_1406_, 1);
lean_dec(v_unused_1982_);
v_unused_1983_ = lean_ctor_get(v_l_1406_, 0);
lean_dec(v_unused_1983_);
v___x_1914_ = v_l_1406_;
v_isShared_1915_ = v_isSharedCheck_1978_;
goto v_resetjp_1913_;
}
else
{
lean_dec(v_l_1406_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1978_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_size_1916_; lean_object* v_size_1917_; lean_object* v_k_1918_; lean_object* v_v_1919_; lean_object* v_l_1920_; lean_object* v_r_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_size_1916_ = lean_ctor_get(v_l_1903_, 0);
v_size_1917_ = lean_ctor_get(v_r_1904_, 0);
v_k_1918_ = lean_ctor_get(v_r_1904_, 1);
v_v_1919_ = lean_ctor_get(v_r_1904_, 2);
v_l_1920_ = lean_ctor_get(v_r_1904_, 3);
v_r_1921_ = lean_ctor_get(v_r_1904_, 4);
v___x_1922_ = lean_unsigned_to_nat(2u);
v___x_1923_ = lean_nat_mul(v___x_1922_, v_size_1916_);
v___x_1924_ = lean_nat_dec_lt(v_size_1917_, v___x_1923_);
lean_dec(v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1953_; 
lean_inc(v_r_1921_);
lean_inc(v_l_1920_);
lean_inc(v_v_1919_);
lean_inc(v_k_1918_);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_r_1904_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; lean_object* v_unused_1955_; lean_object* v_unused_1956_; lean_object* v_unused_1957_; lean_object* v_unused_1958_; 
v_unused_1954_ = lean_ctor_get(v_r_1904_, 4);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_r_1904_, 3);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_r_1904_, 2);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_r_1904_, 1);
lean_dec(v_unused_1957_);
v_unused_1958_ = lean_ctor_get(v_r_1904_, 0);
lean_dec(v_unused_1958_);
v___x_1926_ = v_r_1904_;
v_isShared_1927_ = v_isSharedCheck_1953_;
goto v_resetjp_1925_;
}
else
{
lean_dec(v_r_1904_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1953_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___x_1941_; lean_object* v___y_1943_; 
v___x_1928_ = lean_nat_add(v___x_1898_, v_size_1900_);
lean_dec(v_size_1900_);
v___x_1929_ = lean_nat_add(v___x_1928_, v_size_1899_);
lean_dec(v___x_1928_);
v___x_1941_ = lean_nat_add(v___x_1898_, v_size_1916_);
if (lean_obj_tag(v_l_1920_) == 0)
{
lean_object* v_size_1951_; 
v_size_1951_ = lean_ctor_get(v_l_1920_, 0);
lean_inc(v_size_1951_);
v___y_1943_ = v_size_1951_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_unsigned_to_nat(0u);
v___y_1943_ = v___x_1952_;
goto v___jp_1942_;
}
v___jp_1930_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_nat_add(v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec(v___y_1932_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 4, v_impl_1897_);
lean_ctor_set(v___x_1926_, 3, v_r_1921_);
lean_ctor_set(v___x_1926_, 2, v_v_1405_);
lean_ctor_set(v___x_1926_, 1, v_k_1404_);
lean_ctor_set(v___x_1926_, 0, v___x_1934_);
v___x_1936_ = v___x_1926_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_r_1921_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_impl_1897_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 4, v___x_1936_);
lean_ctor_set(v___x_1914_, 3, v___y_1931_);
lean_ctor_set(v___x_1914_, 2, v_v_1919_);
lean_ctor_set(v___x_1914_, 1, v_k_1918_);
lean_ctor_set(v___x_1914_, 0, v___x_1929_);
v___x_1938_ = v___x_1914_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v___y_1931_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
v___jp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = lean_nat_add(v___x_1941_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec(v___x_1941_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_l_1920_);
lean_ctor_set(v___x_1409_, 3, v_l_1903_);
lean_ctor_set(v___x_1409_, 2, v_v_1902_);
lean_ctor_set(v___x_1409_, 1, v_k_1901_);
lean_ctor_set(v___x_1409_, 0, v___x_1944_);
v___x_1946_ = v___x_1409_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_k_1901_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_v_1902_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_l_1903_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_l_1920_);
v___x_1946_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_nat_add(v___x_1898_, v_size_1899_);
if (lean_obj_tag(v_r_1921_) == 0)
{
lean_object* v_size_1948_; 
v_size_1948_ = lean_ctor_get(v_r_1921_, 0);
lean_inc(v_size_1948_);
v___y_1931_ = v___x_1946_;
v___y_1932_ = v___x_1947_;
v___y_1933_ = v_size_1948_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_unsigned_to_nat(0u);
v___y_1931_ = v___x_1946_;
v___y_1932_ = v___x_1947_;
v___y_1933_ = v___x_1949_;
goto v___jp_1930_;
}
}
}
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_del_object(v___x_1409_);
v___x_1959_ = lean_nat_add(v___x_1898_, v_size_1900_);
lean_dec(v_size_1900_);
v___x_1960_ = lean_nat_add(v___x_1959_, v_size_1899_);
lean_dec(v___x_1959_);
v___x_1961_ = lean_nat_add(v___x_1898_, v_size_1899_);
v___x_1962_ = lean_nat_add(v___x_1961_, v_size_1917_);
lean_dec(v___x_1961_);
lean_inc_ref(v_impl_1897_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 4, v_impl_1897_);
lean_ctor_set(v___x_1914_, 3, v_r_1904_);
lean_ctor_set(v___x_1914_, 2, v_v_1405_);
lean_ctor_set(v___x_1914_, 1, v_k_1404_);
lean_ctor_set(v___x_1914_, 0, v___x_1962_);
v___x_1964_ = v___x_1914_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_r_1904_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v_impl_1897_);
v___x_1964_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_isSharedCheck_1971_ = !lean_is_exclusive(v_impl_1897_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; lean_object* v_unused_1973_; lean_object* v_unused_1974_; lean_object* v_unused_1975_; lean_object* v_unused_1976_; 
v_unused_1972_ = lean_ctor_get(v_impl_1897_, 4);
lean_dec(v_unused_1972_);
v_unused_1973_ = lean_ctor_get(v_impl_1897_, 3);
lean_dec(v_unused_1973_);
v_unused_1974_ = lean_ctor_get(v_impl_1897_, 2);
lean_dec(v_unused_1974_);
v_unused_1975_ = lean_ctor_get(v_impl_1897_, 1);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_impl_1897_, 0);
lean_dec(v_unused_1976_);
v___x_1966_ = v_impl_1897_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v_impl_1897_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v___x_1964_);
lean_ctor_set(v___x_1966_, 3, v_l_1903_);
lean_ctor_set(v___x_1966_, 2, v_v_1902_);
lean_ctor_set(v___x_1966_, 1, v_k_1901_);
lean_ctor_set(v___x_1966_, 0, v___x_1960_);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_k_1901_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_v_1902_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_l_1903_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v___x_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v_size_1984_ = lean_ctor_get(v_impl_1897_, 0);
v___x_1985_ = lean_nat_add(v___x_1898_, v_size_1984_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_impl_1897_);
lean_ctor_set(v___x_1409_, 0, v___x_1985_);
v___x_1987_ = v___x_1409_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_impl_1897_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
if (lean_obj_tag(v_l_1406_) == 0)
{
lean_object* v_l_1989_; 
v_l_1989_ = lean_ctor_get(v_l_1406_, 3);
if (lean_obj_tag(v_l_1989_) == 0)
{
lean_object* v_r_1990_; 
lean_inc_ref(v_l_1989_);
v_r_1990_ = lean_ctor_get(v_l_1406_, 4);
lean_inc(v_r_1990_);
if (lean_obj_tag(v_r_1990_) == 0)
{
lean_object* v_size_1991_; lean_object* v_k_1992_; lean_object* v_v_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2006_; 
v_size_1991_ = lean_ctor_get(v_l_1406_, 0);
v_k_1992_ = lean_ctor_get(v_l_1406_, 1);
v_v_1993_ = lean_ctor_get(v_l_1406_, 2);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_l_1406_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; lean_object* v_unused_2008_; 
v_unused_2007_ = lean_ctor_get(v_l_1406_, 4);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_l_1406_, 3);
lean_dec(v_unused_2008_);
v___x_1995_ = v_l_1406_;
v_isShared_1996_ = v_isSharedCheck_2006_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_v_1993_);
lean_inc(v_k_1992_);
lean_inc(v_size_1991_);
lean_dec(v_l_1406_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2006_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_size_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v_size_1997_ = lean_ctor_get(v_r_1990_, 0);
v___x_1998_ = lean_nat_add(v___x_1898_, v_size_1991_);
lean_dec(v_size_1991_);
v___x_1999_ = lean_nat_add(v___x_1898_, v_size_1997_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 4, v_impl_1897_);
lean_ctor_set(v___x_1995_, 3, v_r_1990_);
lean_ctor_set(v___x_1995_, 2, v_v_1405_);
lean_ctor_set(v___x_1995_, 1, v_k_1404_);
lean_ctor_set(v___x_1995_, 0, v___x_1999_);
v___x_2001_ = v___x_1995_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_r_1990_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_impl_1897_);
v___x_2001_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2003_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_2001_);
lean_ctor_set(v___x_1409_, 3, v_l_1989_);
lean_ctor_set(v___x_1409_, 2, v_v_1993_);
lean_ctor_set(v___x_1409_, 1, v_k_1992_);
lean_ctor_set(v___x_1409_, 0, v___x_1998_);
v___x_2003_ = v___x_1409_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_l_1989_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
else
{
lean_object* v_k_2009_; lean_object* v_v_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2021_; 
v_k_2009_ = lean_ctor_get(v_l_1406_, 1);
v_v_2010_ = lean_ctor_get(v_l_1406_, 2);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_l_1406_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; lean_object* v_unused_2023_; lean_object* v_unused_2024_; 
v_unused_2022_ = lean_ctor_get(v_l_1406_, 4);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_l_1406_, 3);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_l_1406_, 0);
lean_dec(v_unused_2024_);
v___x_2012_ = v_l_1406_;
v_isShared_2013_ = v_isSharedCheck_2021_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_v_2010_);
lean_inc(v_k_2009_);
lean_dec(v_l_1406_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2021_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_unsigned_to_nat(3u);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 3, v_r_1990_);
lean_ctor_set(v___x_2012_, 2, v_v_1405_);
lean_ctor_set(v___x_2012_, 1, v_k_1404_);
lean_ctor_set(v___x_2012_, 0, v___x_1898_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_2020_, 3, v_r_1990_);
lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_r_1990_);
v___x_2016_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2018_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_2016_);
lean_ctor_set(v___x_1409_, 3, v_l_1989_);
lean_ctor_set(v___x_1409_, 2, v_v_2010_);
lean_ctor_set(v___x_1409_, 1, v_k_2009_);
lean_ctor_set(v___x_1409_, 0, v___x_2014_);
v___x_2018_ = v___x_1409_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_k_2009_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_v_2010_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_l_1989_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v_r_2025_; 
v_r_2025_ = lean_ctor_get(v_l_1406_, 4);
lean_inc(v_r_2025_);
if (lean_obj_tag(v_r_2025_) == 0)
{
lean_object* v_k_2026_; lean_object* v_v_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2050_; 
lean_inc(v_l_1989_);
v_k_2026_ = lean_ctor_get(v_l_1406_, 1);
v_v_2027_ = lean_ctor_get(v_l_1406_, 2);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_l_1406_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; lean_object* v_unused_2052_; lean_object* v_unused_2053_; 
v_unused_2051_ = lean_ctor_get(v_l_1406_, 4);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_l_1406_, 3);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_l_1406_, 0);
lean_dec(v_unused_2053_);
v___x_2029_ = v_l_1406_;
v_isShared_2030_ = v_isSharedCheck_2050_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_v_2027_);
lean_inc(v_k_2026_);
lean_dec(v_l_1406_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2050_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_k_2031_; lean_object* v_v_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2046_; 
v_k_2031_ = lean_ctor_get(v_r_2025_, 1);
v_v_2032_ = lean_ctor_get(v_r_2025_, 2);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_r_2025_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; 
v_unused_2047_ = lean_ctor_get(v_r_2025_, 4);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_r_2025_, 3);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_r_2025_, 0);
lean_dec(v_unused_2049_);
v___x_2034_ = v_r_2025_;
v_isShared_2035_ = v_isSharedCheck_2046_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_v_2032_);
lean_inc(v_k_2031_);
lean_dec(v_r_2025_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2046_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_unsigned_to_nat(3u);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_l_1989_);
lean_ctor_set(v___x_2034_, 3, v_l_1989_);
lean_ctor_set(v___x_2034_, 2, v_v_2027_);
lean_ctor_set(v___x_2034_, 1, v_k_2026_);
lean_ctor_set(v___x_2034_, 0, v___x_1898_);
v___x_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_k_2026_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_v_2027_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_l_1989_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v_l_1989_);
v___x_2038_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_l_1989_);
lean_ctor_set(v___x_2029_, 2, v_v_1405_);
lean_ctor_set(v___x_2029_, 1, v_k_1404_);
lean_ctor_set(v___x_2029_, 0, v___x_1898_);
v___x_2040_ = v___x_2029_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_l_1989_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_l_1989_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_2040_);
lean_ctor_set(v___x_1409_, 3, v___x_2038_);
lean_ctor_set(v___x_1409_, 2, v_v_2032_);
lean_ctor_set(v___x_1409_, 1, v_k_2031_);
lean_ctor_set(v___x_1409_, 0, v___x_2036_);
v___x_2042_ = v___x_1409_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = lean_unsigned_to_nat(2u);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_r_2025_);
lean_ctor_set(v___x_1409_, 0, v___x_2054_);
v___x_2056_ = v___x_1409_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_r_2025_);
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
lean_object* v___x_2059_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_l_1406_);
lean_ctor_set(v___x_1409_, 0, v___x_1898_);
v___x_2059_ = v___x_1409_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v_l_1406_);
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
}
}
}
else
{
return v_t_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2063_, lean_object* v_t_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2063_, v_t_2064_);
lean_dec(v_k_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2066_, lean_object* v_v_2067_, lean_object* v_i_2068_){
_start:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = lean_array_get_size(v_xs_2066_);
v___x_2070_ = lean_nat_dec_lt(v_i_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_i_2068_);
v___x_2071_ = lean_box(0);
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2072_ = lean_array_fget_borrowed(v_xs_2066_, v_i_2068_);
v___x_2073_ = l_Lean_instBEqFVarId_beq(v___x_2072_, v_v_2067_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_nat_add(v_i_2068_, v___x_2074_);
lean_dec(v_i_2068_);
v_i_2068_ = v___x_2075_;
goto _start;
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_i_2068_);
return v___x_2077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2078_, lean_object* v_v_2079_, lean_object* v_i_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2078_, v_v_2079_, v_i_2080_);
lean_dec(v_v_2079_);
lean_dec_ref(v_xs_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2082_, lean_object* v_v_2083_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2082_, v_v_2083_, v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2086_, lean_object* v_v_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2086_, v_v_2087_);
lean_dec(v_v_2087_);
lean_dec_ref(v_xs_2086_);
return v_res_2088_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2089_, size_t v_x_2090_, lean_object* v_x_2091_){
_start:
{
if (lean_obj_tag(v_x_2089_) == 0)
{
lean_object* v_es_2092_; lean_object* v___x_2093_; size_t v___x_2094_; size_t v___x_2095_; lean_object* v_j_2096_; lean_object* v_entry_2097_; 
v_es_2092_ = lean_ctor_get(v_x_2089_, 0);
v___x_2093_ = lean_box(2);
v___x_2094_ = ((size_t)31ULL);
v___x_2095_ = lean_usize_land(v_x_2090_, v___x_2094_);
v_j_2096_ = lean_usize_to_nat(v___x_2095_);
v_entry_2097_ = lean_array_get(v___x_2093_, v_es_2092_, v_j_2096_);
switch(lean_obj_tag(v_entry_2097_))
{
case 0:
{
lean_object* v_key_2098_; uint8_t v___x_2099_; 
v_key_2098_ = lean_ctor_get(v_entry_2097_, 0);
lean_inc(v_key_2098_);
lean_dec_ref_known(v_entry_2097_, 2);
v___x_2099_ = l_Lean_instBEqFVarId_beq(v_x_2091_, v_key_2098_);
lean_dec(v_key_2098_);
if (v___x_2099_ == 0)
{
lean_dec(v_j_2096_);
return v_x_2089_;
}
else
{
lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2107_; 
lean_inc_ref(v_es_2092_);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v_x_2089_, 0);
lean_dec(v_unused_2108_);
v___x_2101_ = v_x_2089_;
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
else
{
lean_dec(v_x_2089_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_array_set(v_es_2092_, v_j_2096_, v___x_2093_);
lean_dec(v_j_2096_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2103_);
v___x_2105_ = v___x_2101_;
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
}
case 1:
{
lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2143_; 
lean_inc_ref(v_es_2092_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v_x_2089_, 0);
lean_dec(v_unused_2144_);
v___x_2110_ = v_x_2089_;
v_isShared_2111_ = v_isSharedCheck_2143_;
goto v_resetjp_2109_;
}
else
{
lean_dec(v_x_2089_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2143_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_node_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2142_; 
v_node_2112_ = lean_ctor_get(v_entry_2097_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_entry_2097_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2114_ = v_entry_2097_;
v_isShared_2115_ = v_isSharedCheck_2142_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_node_2112_);
lean_dec(v_entry_2097_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2142_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
size_t v___x_2116_; lean_object* v_entries_2117_; size_t v___x_2118_; lean_object* v_newNode_2119_; lean_object* v___x_2120_; 
v___x_2116_ = ((size_t)5ULL);
v_entries_2117_ = lean_array_set(v_es_2092_, v_j_2096_, v___x_2093_);
v___x_2118_ = lean_usize_shift_right(v_x_2090_, v___x_2116_);
v_newNode_2119_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2112_, v___x_2118_, v_x_2091_);
lean_inc_ref(v_newNode_2119_);
v___x_2120_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2119_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v___x_2122_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v_newNode_2119_);
v___x_2122_ = v___x_2114_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_newNode_2119_);
v___x_2122_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_array_set(v_entries_2117_, v_j_2096_, v___x_2122_);
lean_dec(v_j_2096_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2123_);
v___x_2125_ = v___x_2110_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
lean_object* v_val_2128_; lean_object* v_fst_2129_; lean_object* v_snd_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_newNode_2119_);
lean_del_object(v___x_2114_);
v_val_2128_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_val_2128_);
lean_dec_ref_known(v___x_2120_, 1);
v_fst_2129_ = lean_ctor_get(v_val_2128_, 0);
v_snd_2130_ = lean_ctor_get(v_val_2128_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_val_2128_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2132_ = v_val_2128_;
v_isShared_2133_ = v_isSharedCheck_2141_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_snd_2130_);
lean_inc(v_fst_2129_);
lean_dec(v_val_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2141_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_fst_2129_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_snd_2130_);
v___x_2135_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = lean_array_set(v_entries_2117_, v_j_2096_, v___x_2135_);
lean_dec(v_j_2096_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2136_);
v___x_2138_ = v___x_2110_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
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
}
default: 
{
lean_dec(v_j_2096_);
return v_x_2089_;
}
}
}
else
{
lean_object* v_ks_2145_; lean_object* v_vs_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2160_; 
v_ks_2145_ = lean_ctor_get(v_x_2089_, 0);
v_vs_2146_ = lean_ctor_get(v_x_2089_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2148_ = v_x_2089_;
v_isShared_2149_ = v_isSharedCheck_2160_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_vs_2146_);
lean_inc(v_ks_2145_);
lean_dec(v_x_2089_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2160_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2145_, v_x_2091_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v___x_2152_; 
if (v_isShared_2149_ == 0)
{
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_ks_2145_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_vs_2146_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
else
{
lean_object* v_val_2154_; lean_object* v_keys_x27_2155_; lean_object* v_vals_x27_2156_; lean_object* v___x_2158_; 
v_val_2154_ = lean_ctor_get(v___x_2150_, 0);
lean_inc_n(v_val_2154_, 2);
lean_dec_ref_known(v___x_2150_, 1);
v_keys_x27_2155_ = l_Array_eraseIdx___redArg(v_ks_2145_, v_val_2154_);
v_vals_x27_2156_ = l_Array_eraseIdx___redArg(v_vs_2146_, v_val_2154_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v_vals_x27_2156_);
lean_ctor_set(v___x_2148_, 0, v_keys_x27_2155_);
v___x_2158_ = v___x_2148_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_keys_x27_2155_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_vals_x27_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2089_ = stack[0].m_obj;
size_t v_x_2090_ = stack[1].m_num;
lean_object* v_x_2091_ = stack[2].m_obj;
lean_object* v_res_2161_;
v_res_2161_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2089_, v_x_2090_, v_x_2091_);
stack->m_obj
 = v_res_2161_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
size_t v_x_3310__boxed_2165_; lean_object* v_res_2166_; 
v_x_3310__boxed_2165_ = lean_unbox_usize(v_x_2163_);
lean_dec(v_x_2163_);
v_res_2166_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2162_, v_x_3310__boxed_2165_, v_x_2164_);
lean_dec(v_x_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
uint64_t v___x_2169_; size_t v_h_2170_; lean_object* v___x_2171_; 
v___x_2169_ = l_Lean_instHashableFVarId_hash(v_x_2168_);
v_h_2170_ = lean_uint64_to_usize(v___x_2169_);
v___x_2171_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2167_, v_h_2170_, v_x_2168_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2172_, v_x_2173_);
lean_dec(v_x_2173_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase(lean_object* v_lctx_2175_, lean_object* v_fvarId_2176_){
_start:
{
lean_object* v_fvarIdToDecl_2177_; lean_object* v_decls_2178_; lean_object* v_auxDeclToFullName_2179_; lean_object* v___x_2180_; 
v_fvarIdToDecl_2177_ = lean_ctor_get(v_lctx_2175_, 0);
v_decls_2178_ = lean_ctor_get(v_lctx_2175_, 1);
v_auxDeclToFullName_2179_ = lean_ctor_get(v_lctx_2175_, 2);
v___x_2180_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2177_, v_fvarId_2176_);
if (lean_obj_tag(v___x_2180_) == 0)
{
return v_lctx_2175_;
}
else
{
lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2200_; 
lean_inc(v_auxDeclToFullName_2179_);
lean_inc_ref(v_decls_2178_);
lean_inc_ref(v_fvarIdToDecl_2177_);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_lctx_2175_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; lean_object* v_unused_2202_; lean_object* v_unused_2203_; 
v_unused_2201_ = lean_ctor_get(v_lctx_2175_, 2);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_lctx_2175_, 1);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_lctx_2175_, 0);
lean_dec(v_unused_2203_);
v___x_2182_ = v_lctx_2175_;
v_isShared_2183_ = v_isSharedCheck_2200_;
goto v_resetjp_2181_;
}
else
{
lean_dec(v_lctx_2175_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2200_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_val_2184_; lean_object* v___x_2185_; lean_object* v___y_2187_; lean_object* v_index_2199_; 
v_val_2184_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2185_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2177_, v_fvarId_2176_);
v_index_2199_ = lean_ctor_get(v_val_2184_, 0);
lean_inc(v_index_2199_);
v___y_2187_ = v_index_2199_;
goto v___jp_2186_;
v___jp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2188_ = lean_box(0);
v___x_2189_ = l_Lean_PersistentArray_set___redArg(v_decls_2178_, v___y_2187_, v___x_2188_);
lean_dec(v___y_2187_);
v___x_2190_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2189_);
v___x_2191_ = l_Lean_LocalDecl_isAuxDecl(v_val_2184_);
lean_dec(v_val_2184_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2193_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 1, v___x_2190_);
lean_ctor_set(v___x_2182_, 0, v___x_2185_);
v___x_2193_ = v___x_2182_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_auxDeclToFullName_2179_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2176_, v_auxDeclToFullName_2179_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 2, v___x_2195_);
lean_ctor_set(v___x_2182_, 1, v___x_2190_);
lean_ctor_set(v___x_2182_, 0, v___x_2185_);
v___x_2197_ = v___x_2182_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase___boxed(lean_object* v_lctx_2204_, lean_object* v_fvarId_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_LocalContext_erase(v_lctx_2204_, v_fvarId_2205_);
lean_dec(v_fvarId_2205_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2208_, v_x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2211_, v_x_2212_, v_x_2213_);
lean_dec(v_x_2213_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2215_, lean_object* v_k_2216_, lean_object* v_t_2217_, lean_object* v_h_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2216_, v_t_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2220_, lean_object* v_k_2221_, lean_object* v_t_2222_, lean_object* v_h_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2220_, v_k_2221_, v_t_2222_, v_h_2223_);
lean_dec(v_k_2221_);
return v_res_2224_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2225_, lean_object* v_x_2226_, size_t v_x_2227_, lean_object* v_x_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2226_, v_x_2227_, v_x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2226_ = stack[1].m_obj;
size_t v_x_2227_ = stack[2].m_num;
lean_object* v_x_2228_ = stack[3].m_obj;
lean_object* v_res_2230_;
v_res_2230_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_box(0), v_x_2226_, v_x_2227_, v_x_2228_);
stack->m_obj
 = v_res_2230_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
size_t v_x_3640__boxed_2235_; lean_object* v_res_2236_; 
v_x_3640__boxed_2235_ = lean_unbox_usize(v_x_2233_);
lean_dec(v_x_2233_);
v_res_2236_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2231_, v_x_2232_, v_x_3640__boxed_2235_, v_x_2234_);
lean_dec(v_x_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2237_){
_start:
{
lean_object* v_decls_2238_; lean_object* v_fvarIdToDecl_2239_; lean_object* v_auxDeclToFullName_2240_; lean_object* v_size_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v_decls_2238_ = lean_ctor_get(v_lctx_2237_, 1);
v_fvarIdToDecl_2239_ = lean_ctor_get(v_lctx_2237_, 0);
v_auxDeclToFullName_2240_ = lean_ctor_get(v_lctx_2237_, 2);
v_size_2241_ = lean_ctor_get(v_decls_2238_, 2);
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2243_ = lean_nat_dec_eq(v_size_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_sub(v_size_2241_, v___x_2245_);
v___x_2247_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2244_, v_decls_2238_, v___x_2246_);
lean_dec(v___x_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
return v_lctx_2237_;
}
else
{
lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2266_; 
lean_inc(v_auxDeclToFullName_2240_);
lean_inc_ref(v_fvarIdToDecl_2239_);
lean_inc_ref(v_decls_2238_);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_lctx_2237_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; lean_object* v_unused_2268_; lean_object* v_unused_2269_; 
v_unused_2267_ = lean_ctor_get(v_lctx_2237_, 2);
lean_dec(v_unused_2267_);
v_unused_2268_ = lean_ctor_get(v_lctx_2237_, 1);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_lctx_2237_, 0);
lean_dec(v_unused_2269_);
v___x_2249_ = v_lctx_2237_;
v_isShared_2250_ = v_isSharedCheck_2266_;
goto v_resetjp_2248_;
}
else
{
lean_dec(v_lctx_2237_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2266_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_val_2251_; lean_object* v___y_2253_; lean_object* v_fvarId_2265_; 
v_val_2251_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2251_);
lean_dec_ref_known(v___x_2247_, 1);
v_fvarId_2265_ = lean_ctor_get(v_val_2251_, 1);
lean_inc(v_fvarId_2265_);
v___y_2253_ = v_fvarId_2265_;
goto v___jp_2252_;
v___jp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2254_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2239_, v___y_2253_);
v___x_2255_ = l_Lean_PersistentArray_pop___redArg(v_decls_2238_);
v___x_2256_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2255_);
v___x_2257_ = l_Lean_LocalDecl_isAuxDecl(v_val_2251_);
lean_dec(v_val_2251_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2259_; 
lean_dec(v___y_2253_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v___x_2256_);
lean_ctor_set(v___x_2249_, 0, v___x_2254_);
v___x_2259_ = v___x_2249_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_auxDeclToFullName_2240_);
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
lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2261_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2253_, v_auxDeclToFullName_2240_);
lean_dec(v___y_2253_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 2, v___x_2261_);
lean_ctor_set(v___x_2249_, 1, v___x_2256_);
lean_ctor_set(v___x_2249_, 0, v___x_2254_);
v___x_2263_ = v___x_2249_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
else
{
return v_lctx_2237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2270_, lean_object* v_as_2271_, lean_object* v_i_2272_){
_start:
{
lean_object* v_zero_2273_; uint8_t v_isZero_2274_; 
v_zero_2273_ = lean_unsigned_to_nat(0u);
v_isZero_2274_ = lean_nat_dec_eq(v_i_2272_, v_zero_2273_);
if (v_isZero_2274_ == 1)
{
lean_object* v___x_2275_; 
lean_dec(v_i_2272_);
v___x_2275_ = lean_box(0);
return v___x_2275_;
}
else
{
lean_object* v_one_2276_; lean_object* v_n_2277_; lean_object* v___y_2279_; lean_object* v___x_2281_; lean_object* v___y_2283_; 
v_one_2276_ = lean_unsigned_to_nat(1u);
v_n_2277_ = lean_nat_sub(v_i_2272_, v_one_2276_);
lean_dec(v_i_2272_);
v___x_2281_ = lean_array_fget_borrowed(v_as_2271_, v_n_2277_);
if (lean_obj_tag(v___x_2281_) == 0)
{
v___y_2279_ = v___x_2281_;
goto v___jp_2278_;
}
else
{
lean_object* v_val_2286_; lean_object* v_userName_2287_; 
v_val_2286_ = lean_ctor_get(v___x_2281_, 0);
v_userName_2287_ = lean_ctor_get(v_val_2286_, 2);
v___y_2283_ = v_userName_2287_;
goto v___jp_2282_;
}
v___jp_2278_:
{
if (lean_obj_tag(v___y_2279_) == 0)
{
v_i_2272_ = v_n_2277_;
goto _start;
}
else
{
lean_dec(v_n_2277_);
lean_inc_ref(v___y_2279_);
return v___y_2279_;
}
}
v___jp_2282_:
{
uint8_t v___x_2284_; 
v___x_2284_ = lean_name_eq(v___y_2283_, v_userName_2270_);
if (v___x_2284_ == 0)
{
v_i_2272_ = v_n_2277_;
goto _start;
}
else
{
v___y_2279_ = v___x_2281_;
goto v___jp_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2288_, lean_object* v_as_2289_, lean_object* v_i_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2288_, v_as_2289_, v_i_2290_);
lean_dec_ref(v_as_2289_);
lean_dec(v_userName_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2292_, lean_object* v_as_2293_, lean_object* v_i_2294_){
_start:
{
lean_object* v_zero_2295_; uint8_t v_isZero_2296_; 
v_zero_2295_ = lean_unsigned_to_nat(0u);
v_isZero_2296_ = lean_nat_dec_eq(v_i_2294_, v_zero_2295_);
if (v_isZero_2296_ == 1)
{
lean_object* v___x_2297_; 
lean_dec(v_i_2294_);
v___x_2297_ = lean_box(0);
return v___x_2297_;
}
else
{
lean_object* v_one_2298_; lean_object* v_n_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_one_2298_ = lean_unsigned_to_nat(1u);
v_n_2299_ = lean_nat_sub(v_i_2294_, v_one_2298_);
lean_dec(v_i_2294_);
v___x_2300_ = lean_array_fget_borrowed(v_as_2293_, v_n_2299_);
v___x_2301_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2292_, v___x_2300_);
if (lean_obj_tag(v___x_2301_) == 0)
{
v_i_2294_ = v_n_2299_;
goto _start;
}
else
{
lean_dec(v_n_2299_);
return v___x_2301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2303_, lean_object* v_x_2304_){
_start:
{
if (lean_obj_tag(v_x_2304_) == 0)
{
lean_object* v_cs_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_cs_2305_ = lean_ctor_get(v_x_2304_, 0);
v___x_2306_ = lean_array_get_size(v_cs_2305_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2303_, v_cs_2305_, v___x_2306_);
return v___x_2307_;
}
else
{
lean_object* v_vs_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_vs_2308_ = lean_ctor_get(v_x_2304_, 0);
v___x_2309_ = lean_array_get_size(v_vs_2308_);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2303_, v_vs_2308_, v___x_2309_);
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2311_, v_x_2312_);
lean_dec_ref(v_x_2312_);
lean_dec(v_userName_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2314_, lean_object* v_as_2315_, lean_object* v_i_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2314_, v_as_2315_, v_i_2316_);
lean_dec_ref(v_as_2315_);
lean_dec(v_userName_2314_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2318_, lean_object* v_t_2319_){
_start:
{
lean_object* v_root_2320_; lean_object* v_tail_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_root_2320_ = lean_ctor_get(v_t_2319_, 0);
v_tail_2321_ = lean_ctor_get(v_t_2319_, 1);
v___x_2322_ = lean_array_get_size(v_tail_2321_);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2318_, v_tail_2321_, v___x_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2318_, v_root_2320_);
return v___x_2324_;
}
else
{
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2325_, lean_object* v_t_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2325_, v_t_2326_);
lean_dec_ref(v_t_2326_);
lean_dec(v_userName_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2328_, lean_object* v_userName_2329_){
_start:
{
lean_object* v_decls_2330_; lean_object* v___x_2331_; 
v_decls_2330_ = lean_ctor_get(v_lctx_2328_, 1);
v___x_2331_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2329_, v_decls_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2332_, lean_object* v_userName_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2332_, v_userName_2333_);
lean_dec(v_userName_2333_);
lean_dec_ref(v_lctx_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2335_, lean_object* v_as_2336_, lean_object* v_i_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2335_, v_as_2336_, v_i_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2340_, lean_object* v_as_2341_, lean_object* v_i_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2340_, v_as_2341_, v_i_2342_, v_a_2343_);
lean_dec_ref(v_as_2341_);
lean_dec(v_userName_2340_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2345_, lean_object* v_as_2346_, lean_object* v_i_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2345_, v_as_2346_, v_i_2347_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2350_, lean_object* v_as_2351_, lean_object* v_i_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2350_, v_as_2351_, v_i_2352_, v_a_2353_);
lean_dec_ref(v_as_2351_);
lean_dec(v_userName_2350_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2358_, lean_object* v_userName_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2358_, v_userName_2359_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2361_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2362_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2363_ = lean_unsigned_to_nat(412u);
v___x_2364_ = lean_unsigned_to_nat(17u);
v___x_2365_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2366_ = 1;
v___x_2367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2359_, v___x_2366_);
v___x_2368_ = lean_string_append(v___x_2365_, v___x_2367_);
lean_dec_ref(v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2370_ = lean_string_append(v___x_2368_, v___x_2369_);
v___x_2371_ = l_mkPanicMessageWithDecl(v___x_2361_, v___x_2362_, v___x_2363_, v___x_2364_, v___x_2370_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2371_);
return v___x_2372_;
}
else
{
lean_object* v_val_2373_; 
lean_dec(v_userName_2359_);
v_val_2373_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_val_2373_);
lean_dec_ref_known(v___x_2360_, 1);
return v_val_2373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2374_, lean_object* v_userName_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2374_, v_userName_2375_);
lean_dec_ref(v_lctx_2374_);
return v_res_2376_;
}
}
uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2377_, lean_object* v_userName_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2377_, v_userName_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
uint8_t v___x_2380_; 
v___x_2380_ = 0;
return v___x_2380_;
}
else
{
uint8_t v___x_2381_; 
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = 1;
return v___x_2381_;
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_usesUserName_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2377_ = stack[0].m_obj;
lean_object* v_userName_2378_ = stack[1].m_obj;
uint8_t v_res_2382_;
v_res_2382_ = l_Lean_LocalContext_usesUserName(v_lctx_2377_, v_userName_2378_);
stack->m_num = v_res_2382_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2383_, lean_object* v_userName_2384_){
_start:
{
uint8_t v_res_2385_; lean_object* v_r_2386_; 
v_res_2385_ = l_Lean_LocalContext_usesUserName(v_lctx_2383_, v_userName_2384_);
lean_dec(v_userName_2384_);
lean_dec_ref(v_lctx_2383_);
v_r_2386_ = lean_box(v_res_2385_);
return v_r_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2387_, lean_object* v_suggestion_2388_, lean_object* v_i_2389_){
_start:
{
lean_object* v_curr_2390_; uint8_t v___x_2391_; 
lean_inc(v_i_2389_);
lean_inc(v_suggestion_2388_);
v_curr_2390_ = lean_name_append_index_after(v_suggestion_2388_, v_i_2389_);
v___x_2391_ = l_Lean_LocalContext_usesUserName(v_lctx_2387_, v_curr_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v_suggestion_2388_);
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_nat_add(v_i_2389_, v___x_2392_);
lean_dec(v_i_2389_);
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v_curr_2390_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_dec(v_curr_2390_);
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2396_ = lean_nat_add(v_i_2389_, v___x_2395_);
lean_dec(v_i_2389_);
v_i_2389_ = v___x_2396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2398_, lean_object* v_suggestion_2399_, lean_object* v_i_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2398_, v_suggestion_2399_, v_i_2400_);
lean_dec_ref(v_lctx_2398_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2402_, lean_object* v_suggestion_2403_){
_start:
{
lean_object* v_suggestion_2404_; uint8_t v___x_2405_; 
v_suggestion_2404_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2403_);
v___x_2405_ = l_Lean_LocalContext_usesUserName(v_lctx_2402_, v_suggestion_2404_);
if (v___x_2405_ == 0)
{
return v_suggestion_2404_;
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v_fst_2408_; 
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2402_, v_suggestion_2404_, v___x_2406_);
v_fst_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_fst_2408_);
lean_dec_ref(v___x_2407_);
return v_fst_2408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2409_, lean_object* v_suggestion_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_LocalContext_getUnusedName(v_lctx_2409_, v_suggestion_2410_);
lean_dec(v_suggestion_2410_);
lean_dec_ref(v_lctx_2409_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2412_){
_start:
{
lean_object* v_decls_2413_; lean_object* v_size_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
v_decls_2413_ = lean_ctor_get(v_lctx_2412_, 1);
v_size_2414_ = lean_ctor_get(v_decls_2413_, 2);
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_nat_sub(v_size_2414_, v___x_2416_);
v___x_2418_ = lean_nat_dec_lt(v___x_2417_, v_size_2414_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
lean_dec(v___x_2417_);
v___x_2419_ = l_outOfBounds___redArg(v___x_2415_);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2415_, v_decls_2413_, v___x_2417_);
lean_dec(v___x_2417_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_LocalContext_lastDecl(v_lctx_2421_);
lean_dec_ref(v_lctx_2421_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2423_, lean_object* v_fvarId_2424_, lean_object* v_userName_2425_){
_start:
{
lean_object* v_fvarIdToDecl_2426_; lean_object* v_decls_2427_; lean_object* v_auxDeclToFullName_2428_; lean_object* v_decl_2429_; lean_object* v_decl_2430_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2438_; lean_object* v_fvarId_2441_; 
v_fvarIdToDecl_2426_ = lean_ctor_get(v_lctx_2423_, 0);
lean_inc_ref(v_fvarIdToDecl_2426_);
v_decls_2427_ = lean_ctor_get(v_lctx_2423_, 1);
lean_inc_ref(v_decls_2427_);
v_auxDeclToFullName_2428_ = lean_ctor_get(v_lctx_2423_, 2);
lean_inc(v_auxDeclToFullName_2428_);
v_decl_2429_ = l_Lean_LocalContext_get_x21(v_lctx_2423_, v_fvarId_2424_);
v_decl_2430_ = l_Lean_LocalDecl_setUserName(v_decl_2429_, v_userName_2425_);
v_fvarId_2441_ = lean_ctor_get(v_decl_2430_, 1);
lean_inc(v_fvarId_2441_);
v___y_2438_ = v_fvarId_2441_;
goto v___jp_2437_;
v___jp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_decl_2430_);
v___x_2435_ = l_Lean_PersistentArray_set___redArg(v_decls_2427_, v___y_2433_, v___x_2434_);
lean_dec(v___y_2433_);
v___x_2436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2436_, 0, v___y_2432_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
lean_ctor_set(v___x_2436_, 2, v_auxDeclToFullName_2428_);
return v___x_2436_;
}
v___jp_2437_:
{
lean_object* v___x_2439_; lean_object* v_index_2440_; 
lean_inc_ref(v_decl_2430_);
v___x_2439_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2426_, v___y_2438_, v_decl_2430_);
v_index_2440_ = lean_ctor_get(v_decl_2430_, 0);
lean_inc(v_index_2440_);
v___y_2432_ = v___x_2439_;
v___y_2433_ = v_index_2440_;
goto v___jp_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2442_, lean_object* v_fromName_2443_, lean_object* v_toName_2444_){
_start:
{
lean_object* v_fvarIdToDecl_2445_; lean_object* v_decls_2446_; lean_object* v_auxDeclToFullName_2447_; lean_object* v___x_2448_; 
v_fvarIdToDecl_2445_ = lean_ctor_get(v_lctx_2442_, 0);
v_decls_2446_ = lean_ctor_get(v_lctx_2442_, 1);
v_auxDeclToFullName_2447_ = lean_ctor_get(v_lctx_2442_, 2);
v___x_2448_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2442_, v_fromName_2443_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_dec(v_toName_2444_);
return v_lctx_2442_;
}
else
{
lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2473_; 
lean_inc(v_auxDeclToFullName_2447_);
lean_inc_ref(v_decls_2446_);
lean_inc_ref(v_fvarIdToDecl_2445_);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_lctx_2442_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; lean_object* v_unused_2475_; lean_object* v_unused_2476_; 
v_unused_2474_ = lean_ctor_get(v_lctx_2442_, 2);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_lctx_2442_, 1);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_lctx_2442_, 0);
lean_dec(v_unused_2476_);
v___x_2450_ = v_lctx_2442_;
v_isShared_2451_ = v_isSharedCheck_2473_;
goto v_resetjp_2449_;
}
else
{
lean_dec(v_lctx_2442_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2473_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_val_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2472_; 
v_val_2452_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2454_ = v___x_2448_;
v_isShared_2455_ = v_isSharedCheck_2472_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_val_2452_);
lean_dec(v___x_2448_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2472_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v_decl_2456_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2468_; lean_object* v_fvarId_2471_; 
v_decl_2456_ = l_Lean_LocalDecl_setUserName(v_val_2452_, v_toName_2444_);
v_fvarId_2471_ = lean_ctor_get(v_decl_2456_, 1);
lean_inc(v_fvarId_2471_);
v___y_2468_ = v_fvarId_2471_;
goto v___jp_2467_;
v___jp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v_decl_2456_);
v___x_2461_ = v___x_2454_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_decl_2456_);
v___x_2461_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = l_Lean_PersistentArray_set___redArg(v_decls_2446_, v___y_2459_, v___x_2461_);
lean_dec(v___y_2459_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2462_);
lean_ctor_set(v___x_2450_, 0, v___y_2458_);
v___x_2464_ = v___x_2450_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___y_2458_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_auxDeclToFullName_2447_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
v___jp_2467_:
{
lean_object* v___x_2469_; lean_object* v_index_2470_; 
lean_inc_ref(v_decl_2456_);
v___x_2469_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2445_, v___y_2468_, v_decl_2456_);
v_index_2470_ = lean_ctor_get(v_decl_2456_, 0);
lean_inc(v_index_2470_);
v___y_2458_ = v___x_2469_;
v___y_2459_ = v_index_2470_;
goto v___jp_2457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2477_, lean_object* v_fromName_2478_, lean_object* v_toName_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_LocalContext_renameUserName(v_lctx_2477_, v_fromName_2478_, v_toName_2479_);
lean_dec(v_fromName_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2483_, lean_object* v_fvarId_2484_, lean_object* v_f_2485_){
_start:
{
lean_object* v_fvarIdToDecl_2486_; lean_object* v_decls_2487_; lean_object* v_auxDeclToFullName_2488_; lean_object* v___x_2489_; 
v_fvarIdToDecl_2486_ = lean_ctor_get(v_lctx_2483_, 0);
v_decls_2487_ = lean_ctor_get(v_lctx_2483_, 1);
v_auxDeclToFullName_2488_ = lean_ctor_get(v_lctx_2483_, 2);
lean_inc_ref(v_lctx_2483_);
v___x_2489_ = lean_local_ctx_find(v_lctx_2483_, v_fvarId_2484_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_dec_ref(v_f_2485_);
return v_lctx_2483_;
}
else
{
lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2516_; 
lean_inc(v_auxDeclToFullName_2488_);
lean_inc_ref(v_decls_2487_);
lean_inc_ref(v_fvarIdToDecl_2486_);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_lctx_2483_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; lean_object* v_unused_2518_; lean_object* v_unused_2519_; 
v_unused_2517_ = lean_ctor_get(v_lctx_2483_, 2);
lean_dec(v_unused_2517_);
v_unused_2518_ = lean_ctor_get(v_lctx_2483_, 1);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_lctx_2483_, 0);
lean_dec(v_unused_2519_);
v___x_2491_ = v_lctx_2483_;
v_isShared_2492_ = v_isSharedCheck_2516_;
goto v_resetjp_2490_;
}
else
{
lean_dec(v_lctx_2483_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2516_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_val_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2515_; 
v_val_2493_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2495_ = v___x_2489_;
v_isShared_2496_ = v_isSharedCheck_2515_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_val_2493_);
lean_dec(v___x_2489_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2515_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v_decl_2499_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2511_; lean_object* v_fvarId_2514_; 
v___x_2497_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2498_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2499_ = lean_apply_1(v_f_2485_, v_val_2493_);
v_fvarId_2514_ = lean_ctor_get(v_decl_2499_, 1);
lean_inc(v_fvarId_2514_);
v___y_2511_ = v_fvarId_2514_;
goto v___jp_2510_;
v___jp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v_decl_2499_);
v___x_2504_ = v___x_2495_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_decl_2499_);
v___x_2504_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2505_ = l_Lean_PersistentArray_set___redArg(v_decls_2487_, v___y_2502_, v___x_2504_);
lean_dec(v___y_2502_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v___x_2505_);
lean_ctor_set(v___x_2491_, 0, v___y_2501_);
v___x_2507_ = v___x_2491_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___y_2501_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_auxDeclToFullName_2488_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
v___jp_2510_:
{
lean_object* v___x_2512_; lean_object* v_index_2513_; 
lean_inc_ref(v_decl_2499_);
v___x_2512_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2497_, v___x_2498_, v_fvarIdToDecl_2486_, v___y_2511_, v_decl_2499_);
v_index_2513_ = lean_ctor_get(v_decl_2499_, 0);
lean_inc(v_index_2513_);
v___y_2501_ = v___x_2512_;
v___y_2502_ = v_index_2513_;
goto v___jp_2500_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2520_, lean_object* v_as_2521_, size_t v_i_2522_, size_t v_stop_2523_, lean_object* v_b_2524_){
_start:
{
lean_object* v___y_2526_; uint8_t v___x_2530_; 
v___x_2530_ = lean_usize_dec_eq(v_i_2522_, v_stop_2523_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_array_uget(v_as_2521_, v_i_2522_);
if (lean_obj_tag(v___x_2531_) == 0)
{
v___y_2526_ = v_b_2524_;
goto v___jp_2525_;
}
else
{
lean_object* v_val_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2559_; 
v_val_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2559_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_val_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2559_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_fvarIdToDecl_2536_; lean_object* v_decls_2537_; lean_object* v_auxDeclToFullName_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2558_; 
v_fvarIdToDecl_2536_ = lean_ctor_get(v_b_2524_, 0);
v_decls_2537_ = lean_ctor_get(v_b_2524_, 1);
v_auxDeclToFullName_2538_ = lean_ctor_get(v_b_2524_, 2);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_b_2524_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2540_ = v_b_2524_;
v_isShared_2541_ = v_isSharedCheck_2558_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_auxDeclToFullName_2538_);
lean_inc(v_decls_2537_);
lean_inc(v_fvarIdToDecl_2536_);
lean_dec(v_b_2524_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2558_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_decl_2542_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2554_; lean_object* v_fvarId_2557_; 
lean_inc_ref(v_f_2520_);
v_decl_2542_ = lean_apply_1(v_f_2520_, v_val_2532_);
v_fvarId_2557_ = lean_ctor_get(v_decl_2542_, 1);
lean_inc(v_fvarId_2557_);
v___y_2554_ = v_fvarId_2557_;
goto v___jp_2553_;
v___jp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v_decl_2542_);
v___x_2547_ = v___x_2534_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_decl_2542_);
v___x_2547_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = l_Lean_PersistentArray_set___redArg(v_decls_2537_, v___y_2545_, v___x_2547_);
lean_dec(v___y_2545_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 1, v___x_2548_);
lean_ctor_set(v___x_2540_, 0, v___y_2544_);
v___x_2550_ = v___x_2540_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___y_2544_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_auxDeclToFullName_2538_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
v___y_2526_ = v___x_2550_;
goto v___jp_2525_;
}
}
}
v___jp_2553_:
{
lean_object* v___x_2555_; lean_object* v_index_2556_; 
lean_inc_ref(v_decl_2542_);
v___x_2555_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2536_, v___y_2554_, v_decl_2542_);
v_index_2556_ = lean_ctor_get(v_decl_2542_, 0);
lean_inc(v_index_2556_);
v___y_2544_ = v___x_2555_;
v___y_2545_ = v_index_2556_;
goto v___jp_2543_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2520_);
return v_b_2524_;
}
v___jp_2525_:
{
size_t v___x_2527_; size_t v___x_2528_; 
v___x_2527_ = ((size_t)1ULL);
v___x_2528_ = lean_usize_add(v_i_2522_, v___x_2527_);
v_i_2522_ = v___x_2528_;
v_b_2524_ = v___y_2526_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2520_ = stack[0].m_obj;
lean_object* v_as_2521_ = stack[1].m_obj;
size_t v_i_2522_ = stack[2].m_num;
size_t v_stop_2523_ = stack[3].m_num;
lean_object* v_b_2524_ = stack[4].m_obj;
lean_object* v_res_2560_;
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2520_, v_as_2521_, v_i_2522_, v_stop_2523_, v_b_2524_);
stack->m_obj
 = v_res_2560_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2561_, lean_object* v_as_2562_, lean_object* v_i_2563_, lean_object* v_stop_2564_, lean_object* v_b_2565_){
_start:
{
size_t v_i_boxed_2566_; size_t v_stop_boxed_2567_; lean_object* v_res_2568_; 
v_i_boxed_2566_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_stop_boxed_2567_ = lean_unbox_usize(v_stop_2564_);
lean_dec(v_stop_2564_);
v_res_2568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2561_, v_as_2562_, v_i_boxed_2566_, v_stop_boxed_2567_, v_b_2565_);
lean_dec_ref(v_as_2562_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_){
_start:
{
if (lean_obj_tag(v_x_2570_) == 0)
{
lean_object* v_cs_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_cs_2572_ = lean_ctor_get(v_x_2570_, 0);
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = lean_array_get_size(v_cs_2572_);
v___x_2575_ = lean_nat_dec_lt(v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_dec_ref(v_f_2569_);
return v_x_2571_;
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = lean_usize_of_nat(v___x_2574_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2569_, v_cs_2572_, v___x_2576_, v___x_2577_, v_x_2571_);
return v___x_2578_;
}
}
else
{
lean_object* v_vs_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v_vs_2579_ = lean_ctor_get(v_x_2570_, 0);
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = lean_array_get_size(v_vs_2579_);
v___x_2582_ = lean_nat_dec_lt(v___x_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_dec_ref(v_f_2569_);
return v_x_2571_;
}
else
{
size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = lean_usize_of_nat(v___x_2581_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2569_, v_vs_2579_, v___x_2583_, v___x_2584_, v_x_2571_);
return v___x_2585_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2586_, lean_object* v_as_2587_, size_t v_i_2588_, size_t v_stop_2589_, lean_object* v_b_2590_){
_start:
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_usize_dec_eq(v_i_2588_, v_stop_2589_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; size_t v___x_2594_; size_t v___x_2595_; 
v___x_2592_ = lean_array_uget_borrowed(v_as_2587_, v_i_2588_);
lean_inc_ref(v_f_2586_);
v___x_2593_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2586_, v___x_2592_, v_b_2590_);
v___x_2594_ = ((size_t)1ULL);
v___x_2595_ = lean_usize_add(v_i_2588_, v___x_2594_);
v_i_2588_ = v___x_2595_;
v_b_2590_ = v___x_2593_;
goto _start;
}
else
{
lean_dec_ref(v_f_2586_);
return v_b_2590_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2586_ = stack[0].m_obj;
lean_object* v_as_2587_ = stack[1].m_obj;
size_t v_i_2588_ = stack[2].m_num;
size_t v_stop_2589_ = stack[3].m_num;
lean_object* v_b_2590_ = stack[4].m_obj;
lean_object* v_res_2597_;
v_res_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2586_, v_as_2587_, v_i_2588_, v_stop_2589_, v_b_2590_);
stack->m_obj
 = v_res_2597_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2598_, lean_object* v_as_2599_, lean_object* v_i_2600_, lean_object* v_stop_2601_, lean_object* v_b_2602_){
_start:
{
size_t v_i_boxed_2603_; size_t v_stop_boxed_2604_; lean_object* v_res_2605_; 
v_i_boxed_2603_ = lean_unbox_usize(v_i_2600_);
lean_dec(v_i_2600_);
v_stop_boxed_2604_ = lean_unbox_usize(v_stop_2601_);
lean_dec(v_stop_2601_);
v_res_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2598_, v_as_2599_, v_i_boxed_2603_, v_stop_boxed_2604_, v_b_2602_);
lean_dec_ref(v_as_2599_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2606_, v_x_2607_, v_x_2608_);
lean_dec_ref(v_x_2607_);
return v_res_2609_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2610_, lean_object* v_x_2611_, size_t v_x_2612_, size_t v_x_2613_, lean_object* v_x_2614_){
_start:
{
if (lean_obj_tag(v_x_2611_) == 0)
{
lean_object* v_cs_2615_; lean_object* v___x_2616_; size_t v___x_2617_; lean_object* v_j_2618_; lean_object* v___x_2619_; size_t v___x_2620_; size_t v___x_2621_; size_t v___x_2622_; size_t v___x_2623_; size_t v___x_2624_; size_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v_cs_2615_ = lean_ctor_get(v_x_2611_, 0);
v___x_2616_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2617_ = lean_usize_shift_right(v_x_2612_, v_x_2613_);
v_j_2618_ = lean_usize_to_nat(v___x_2617_);
v___x_2619_ = lean_array_get_borrowed(v___x_2616_, v_cs_2615_, v_j_2618_);
v___x_2620_ = ((size_t)1ULL);
v___x_2621_ = lean_usize_shift_left(v___x_2620_, v_x_2613_);
v___x_2622_ = lean_usize_sub(v___x_2621_, v___x_2620_);
v___x_2623_ = lean_usize_land(v_x_2612_, v___x_2622_);
v___x_2624_ = ((size_t)5ULL);
v___x_2625_ = lean_usize_sub(v_x_2613_, v___x_2624_);
lean_inc_ref(v_f_2610_);
v___x_2626_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2610_, v___x_2619_, v___x_2623_, v___x_2625_, v_x_2614_);
v___x_2627_ = lean_unsigned_to_nat(1u);
v___x_2628_ = lean_nat_add(v_j_2618_, v___x_2627_);
lean_dec(v_j_2618_);
v___x_2629_ = lean_array_get_size(v_cs_2615_);
v___x_2630_ = lean_nat_dec_lt(v___x_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_dec(v___x_2628_);
lean_dec_ref(v_f_2610_);
return v___x_2626_;
}
else
{
size_t v___x_2631_; size_t v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = lean_usize_of_nat(v___x_2628_);
lean_dec(v___x_2628_);
v___x_2632_ = lean_usize_of_nat(v___x_2629_);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2610_, v_cs_2615_, v___x_2631_, v___x_2632_, v___x_2626_);
return v___x_2633_;
}
}
else
{
lean_object* v_vs_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v_vs_2634_ = lean_ctor_get(v_x_2611_, 0);
v___x_2635_ = lean_usize_to_nat(v_x_2612_);
v___x_2636_ = lean_array_get_size(v_vs_2634_);
v___x_2637_ = lean_nat_dec_lt(v___x_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_dec(v___x_2635_);
lean_dec_ref(v_f_2610_);
return v_x_2614_;
}
else
{
size_t v___x_2638_; size_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_usize_of_nat(v___x_2635_);
lean_dec(v___x_2635_);
v___x_2639_ = lean_usize_of_nat(v___x_2636_);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2610_, v_vs_2634_, v___x_2638_, v___x_2639_, v_x_2614_);
return v___x_2640_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2610_ = stack[0].m_obj;
lean_object* v_x_2611_ = stack[1].m_obj;
size_t v_x_2612_ = stack[2].m_num;
size_t v_x_2613_ = stack[3].m_num;
lean_object* v_x_2614_ = stack[4].m_obj;
lean_object* v_res_2641_;
v_res_2641_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2610_, v_x_2611_, v_x_2612_, v_x_2613_, v_x_2614_);
stack->m_obj
 = v_res_2641_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_){
_start:
{
size_t v_x_1547__boxed_2647_; size_t v_x_1548__boxed_2648_; lean_object* v_res_2649_; 
v_x_1547__boxed_2647_ = lean_unbox_usize(v_x_2644_);
lean_dec(v_x_2644_);
v_x_1548__boxed_2648_ = lean_unbox_usize(v_x_2645_);
lean_dec(v_x_2645_);
v_res_2649_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2642_, v_x_2643_, v_x_1547__boxed_2647_, v_x_1548__boxed_2648_, v_x_2646_);
lean_dec_ref(v_x_2643_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2650_, lean_object* v_t_2651_, lean_object* v_init_2652_, lean_object* v_start_2653_){
_start:
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_nat_dec_eq(v_start_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v_root_2656_; lean_object* v_tail_2657_; size_t v_shift_2658_; lean_object* v_tailOff_2659_; uint8_t v___x_2660_; 
v_root_2656_ = lean_ctor_get(v_t_2651_, 0);
v_tail_2657_ = lean_ctor_get(v_t_2651_, 1);
v_shift_2658_ = lean_ctor_get_usize(v_t_2651_, 4);
v_tailOff_2659_ = lean_ctor_get(v_t_2651_, 3);
v___x_2660_ = lean_nat_dec_le(v_tailOff_2659_, v_start_2653_);
if (v___x_2660_ == 0)
{
size_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2661_ = lean_usize_of_nat(v_start_2653_);
lean_inc_ref(v_f_2650_);
v___x_2662_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2650_, v_root_2656_, v___x_2661_, v_shift_2658_, v_init_2652_);
v___x_2663_ = lean_array_get_size(v_tail_2657_);
v___x_2664_ = lean_nat_dec_lt(v___x_2654_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_dec_ref(v_f_2650_);
return v___x_2662_;
}
else
{
size_t v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = ((size_t)0ULL);
v___x_2666_ = lean_usize_of_nat(v___x_2663_);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2650_, v_tail_2657_, v___x_2665_, v___x_2666_, v___x_2662_);
return v___x_2667_;
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2668_ = lean_nat_sub(v_start_2653_, v_tailOff_2659_);
v___x_2669_ = lean_array_get_size(v_tail_2657_);
v___x_2670_ = lean_nat_dec_lt(v___x_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_dec(v___x_2668_);
lean_dec_ref(v_f_2650_);
return v_init_2652_;
}
else
{
size_t v___x_2671_; size_t v___x_2672_; lean_object* v___x_2673_; 
v___x_2671_ = lean_usize_of_nat(v___x_2668_);
lean_dec(v___x_2668_);
v___x_2672_ = lean_usize_of_nat(v___x_2669_);
v___x_2673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2650_, v_tail_2657_, v___x_2671_, v___x_2672_, v_init_2652_);
return v___x_2673_;
}
}
}
else
{
lean_object* v_root_2674_; lean_object* v_tail_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_root_2674_ = lean_ctor_get(v_t_2651_, 0);
v_tail_2675_ = lean_ctor_get(v_t_2651_, 1);
lean_inc_ref(v_f_2650_);
v___x_2676_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2650_, v_root_2674_, v_init_2652_);
v___x_2677_ = lean_array_get_size(v_tail_2675_);
v___x_2678_ = lean_nat_dec_lt(v___x_2654_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v_f_2650_);
return v___x_2676_;
}
else
{
size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2677_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2650_, v_tail_2675_, v___x_2679_, v___x_2680_, v___x_2676_);
return v___x_2681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2682_, lean_object* v_t_2683_, lean_object* v_init_2684_, lean_object* v_start_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2682_, v_t_2683_, v_init_2684_, v_start_2685_);
lean_dec(v_start_2685_);
lean_dec_ref(v_t_2683_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2687_, lean_object* v_f_2688_){
_start:
{
lean_object* v_decls_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_decls_2689_ = lean_ctor_get(v_lctx_2687_, 1);
lean_inc_ref(v_decls_2689_);
v___x_2690_ = lean_unsigned_to_nat(0u);
v___x_2691_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2688_, v_decls_2689_, v_lctx_2687_, v___x_2690_);
lean_dec_ref(v_decls_2689_);
return v___x_2691_;
}
}
lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2692_, lean_object* v_fvarId_2693_, uint8_t v_kind_2694_){
_start:
{
lean_object* v_fvarIdToDecl_2695_; lean_object* v_decls_2696_; lean_object* v_auxDeclToFullName_2697_; lean_object* v___x_2698_; 
v_fvarIdToDecl_2695_ = lean_ctor_get(v_lctx_2692_, 0);
v_decls_2696_ = lean_ctor_get(v_lctx_2692_, 1);
v_auxDeclToFullName_2697_ = lean_ctor_get(v_lctx_2692_, 2);
lean_inc_ref(v_lctx_2692_);
v___x_2698_ = lean_local_ctx_find(v_lctx_2692_, v_fvarId_2693_);
if (lean_obj_tag(v___x_2698_) == 0)
{
return v_lctx_2692_;
}
else
{
lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2723_; 
lean_inc(v_auxDeclToFullName_2697_);
lean_inc_ref(v_decls_2696_);
lean_inc_ref(v_fvarIdToDecl_2695_);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_lctx_2692_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; lean_object* v_unused_2725_; lean_object* v_unused_2726_; 
v_unused_2724_ = lean_ctor_get(v_lctx_2692_, 2);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_lctx_2692_, 1);
lean_dec(v_unused_2725_);
v_unused_2726_ = lean_ctor_get(v_lctx_2692_, 0);
lean_dec(v_unused_2726_);
v___x_2700_ = v_lctx_2692_;
v_isShared_2701_ = v_isSharedCheck_2723_;
goto v_resetjp_2699_;
}
else
{
lean_dec(v_lctx_2692_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2723_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_val_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2722_; 
v_val_2702_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2704_ = v___x_2698_;
v_isShared_2705_ = v_isSharedCheck_2722_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_val_2702_);
lean_dec(v___x_2698_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2722_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v_decl_2706_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2718_; lean_object* v_fvarId_2721_; 
v_decl_2706_ = l_Lean_LocalDecl_setKind(v_val_2702_, v_kind_2694_);
v_fvarId_2721_ = lean_ctor_get(v_decl_2706_, 1);
lean_inc(v_fvarId_2721_);
v___y_2718_ = v_fvarId_2721_;
goto v___jp_2717_;
v___jp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v_decl_2706_);
v___x_2711_ = v___x_2704_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_decl_2706_);
v___x_2711_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2712_ = l_Lean_PersistentArray_set___redArg(v_decls_2696_, v___y_2709_, v___x_2711_);
lean_dec(v___y_2709_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v___x_2712_);
lean_ctor_set(v___x_2700_, 0, v___y_2708_);
v___x_2714_ = v___x_2700_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___y_2708_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_auxDeclToFullName_2697_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
v___jp_2717_:
{
lean_object* v___x_2719_; lean_object* v_index_2720_; 
lean_inc_ref(v_decl_2706_);
v___x_2719_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2695_, v___y_2718_, v_decl_2706_);
v_index_2720_ = lean_ctor_get(v_decl_2706_, 0);
lean_inc(v_index_2720_);
v___y_2708_ = v___x_2719_;
v___y_2709_ = v_index_2720_;
goto v___jp_2707_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_setKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2692_ = stack[0].m_obj;
lean_object* v_fvarId_2693_ = stack[1].m_obj;
uint8_t v_kind_2694_ = stack[2].m_num;
lean_object* v_res_2727_;
v_res_2727_ = l_Lean_LocalContext_setKind(v_lctx_2692_, v_fvarId_2693_, v_kind_2694_);
stack->m_obj
 = v_res_2727_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2728_, lean_object* v_fvarId_2729_, lean_object* v_kind_2730_){
_start:
{
uint8_t v_kind_boxed_2731_; lean_object* v_res_2732_; 
v_kind_boxed_2731_ = lean_unbox(v_kind_2730_);
v_res_2732_ = l_Lean_LocalContext_setKind(v_lctx_2728_, v_fvarId_2729_, v_kind_boxed_2731_);
return v_res_2732_;
}
}
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2733_, lean_object* v_fvarId_2734_, uint8_t v_bi_2735_){
_start:
{
lean_object* v_fvarIdToDecl_2736_; lean_object* v_decls_2737_; lean_object* v_auxDeclToFullName_2738_; lean_object* v___x_2739_; 
v_fvarIdToDecl_2736_ = lean_ctor_get(v_lctx_2733_, 0);
v_decls_2737_ = lean_ctor_get(v_lctx_2733_, 1);
v_auxDeclToFullName_2738_ = lean_ctor_get(v_lctx_2733_, 2);
lean_inc_ref(v_lctx_2733_);
v___x_2739_ = lean_local_ctx_find(v_lctx_2733_, v_fvarId_2734_);
if (lean_obj_tag(v___x_2739_) == 0)
{
return v_lctx_2733_;
}
else
{
lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2764_; 
lean_inc(v_auxDeclToFullName_2738_);
lean_inc_ref(v_decls_2737_);
lean_inc_ref(v_fvarIdToDecl_2736_);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_lctx_2733_);
if (v_isSharedCheck_2764_ == 0)
{
lean_object* v_unused_2765_; lean_object* v_unused_2766_; lean_object* v_unused_2767_; 
v_unused_2765_ = lean_ctor_get(v_lctx_2733_, 2);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v_lctx_2733_, 1);
lean_dec(v_unused_2766_);
v_unused_2767_ = lean_ctor_get(v_lctx_2733_, 0);
lean_dec(v_unused_2767_);
v___x_2741_ = v_lctx_2733_;
v_isShared_2742_ = v_isSharedCheck_2764_;
goto v_resetjp_2740_;
}
else
{
lean_dec(v_lctx_2733_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2764_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_val_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2763_; 
v_val_2743_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2745_ = v___x_2739_;
v_isShared_2746_ = v_isSharedCheck_2763_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_val_2743_);
lean_dec(v___x_2739_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2763_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_decl_2747_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2759_; lean_object* v_fvarId_2762_; 
v_decl_2747_ = l_Lean_LocalDecl_setBinderInfo(v_val_2743_, v_bi_2735_);
v_fvarId_2762_ = lean_ctor_get(v_decl_2747_, 1);
lean_inc(v_fvarId_2762_);
v___y_2759_ = v_fvarId_2762_;
goto v___jp_2758_;
v___jp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v_decl_2747_);
v___x_2752_ = v___x_2745_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_decl_2747_);
v___x_2752_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2753_ = l_Lean_PersistentArray_set___redArg(v_decls_2737_, v___y_2750_, v___x_2752_);
lean_dec(v___y_2750_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 1, v___x_2753_);
lean_ctor_set(v___x_2741_, 0, v___y_2749_);
v___x_2755_ = v___x_2741_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___y_2749_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_auxDeclToFullName_2738_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
v___jp_2758_:
{
lean_object* v___x_2760_; lean_object* v_index_2761_; 
lean_inc_ref(v_decl_2747_);
v___x_2760_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2736_, v___y_2759_, v_decl_2747_);
v_index_2761_ = lean_ctor_get(v_decl_2747_, 0);
lean_inc(v_index_2761_);
v___y_2749_ = v___x_2760_;
v___y_2750_ = v_index_2761_;
goto v___jp_2748_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_setBinderInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2733_ = stack[0].m_obj;
lean_object* v_fvarId_2734_ = stack[1].m_obj;
uint8_t v_bi_2735_ = stack[2].m_num;
lean_object* v_res_2768_;
v_res_2768_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2733_, v_fvarId_2734_, v_bi_2735_);
stack->m_obj
 = v_res_2768_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2769_, lean_object* v_fvarId_2770_, lean_object* v_bi_2771_){
_start:
{
uint8_t v_bi_boxed_2772_; lean_object* v_res_2773_; 
v_bi_boxed_2772_ = lean_unbox(v_bi_2771_);
v_res_2773_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2769_, v_fvarId_2770_, v_bi_boxed_2772_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2774_, lean_object* v_fvarId_2775_, lean_object* v_type_2776_){
_start:
{
lean_object* v_fvarIdToDecl_2777_; lean_object* v_decls_2778_; lean_object* v_auxDeclToFullName_2779_; lean_object* v___x_2780_; 
v_fvarIdToDecl_2777_ = lean_ctor_get(v_lctx_2774_, 0);
v_decls_2778_ = lean_ctor_get(v_lctx_2774_, 1);
v_auxDeclToFullName_2779_ = lean_ctor_get(v_lctx_2774_, 2);
lean_inc_ref(v_lctx_2774_);
v___x_2780_ = lean_local_ctx_find(v_lctx_2774_, v_fvarId_2775_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_dec_ref(v_type_2776_);
return v_lctx_2774_;
}
else
{
lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2805_; 
lean_inc(v_auxDeclToFullName_2779_);
lean_inc_ref(v_decls_2778_);
lean_inc_ref(v_fvarIdToDecl_2777_);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_lctx_2774_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; lean_object* v_unused_2807_; lean_object* v_unused_2808_; 
v_unused_2806_ = lean_ctor_get(v_lctx_2774_, 2);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_lctx_2774_, 1);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_lctx_2774_, 0);
lean_dec(v_unused_2808_);
v___x_2782_ = v_lctx_2774_;
v_isShared_2783_ = v_isSharedCheck_2805_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v_lctx_2774_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2805_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v_val_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2804_; 
v_val_2784_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2786_ = v___x_2780_;
v_isShared_2787_ = v_isSharedCheck_2804_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_val_2784_);
lean_dec(v___x_2780_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2804_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v_decl_2788_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2800_; lean_object* v_fvarId_2803_; 
v_decl_2788_ = l_Lean_LocalDecl_setType(v_val_2784_, v_type_2776_);
v_fvarId_2803_ = lean_ctor_get(v_decl_2788_, 1);
lean_inc(v_fvarId_2803_);
v___y_2800_ = v_fvarId_2803_;
goto v___jp_2799_;
v___jp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v_decl_2788_);
v___x_2793_ = v___x_2786_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_decl_2788_);
v___x_2793_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2794_ = l_Lean_PersistentArray_set___redArg(v_decls_2778_, v___y_2791_, v___x_2793_);
lean_dec(v___y_2791_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 1, v___x_2794_);
lean_ctor_set(v___x_2782_, 0, v___y_2790_);
v___x_2796_ = v___x_2782_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___y_2790_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_auxDeclToFullName_2779_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
v___jp_2799_:
{
lean_object* v___x_2801_; lean_object* v_index_2802_; 
lean_inc_ref(v_decl_2788_);
v___x_2801_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2777_, v___y_2800_, v_decl_2788_);
v_index_2802_ = lean_ctor_get(v_decl_2788_, 0);
lean_inc(v_index_2802_);
v___y_2790_ = v___x_2801_;
v___y_2791_ = v_index_2802_;
goto v___jp_2789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2809_){
_start:
{
lean_object* v_decls_2810_; lean_object* v_size_2811_; 
v_decls_2810_ = lean_ctor_get(v_lctx_2809_, 1);
lean_inc_ref(v_decls_2810_);
lean_dec_ref(v_lctx_2809_);
v_size_2811_ = lean_ctor_get(v_decls_2810_, 2);
lean_inc(v_size_2811_);
lean_dec_ref(v_decls_2810_);
return v_size_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2812_, lean_object* v_i_2813_){
_start:
{
lean_object* v_decls_2814_; lean_object* v_size_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v_decls_2814_ = lean_ctor_get(v_lctx_2812_, 1);
v_size_2815_ = lean_ctor_get(v_decls_2814_, 2);
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_nat_dec_lt(v_i_2813_, v_size_2815_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
v___x_2818_ = l_outOfBounds___redArg(v___x_2816_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2816_, v_decls_2814_, v_i_2813_);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2820_, lean_object* v_i_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2820_, v_i_2821_);
lean_dec(v_i_2821_);
lean_dec_ref(v_lctx_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2823_, lean_object* v_f_2824_, lean_object* v_b_2825_, lean_object* v_decl_2826_){
_start:
{
if (lean_obj_tag(v_decl_2826_) == 0)
{
lean_object* v___x_2827_; 
lean_dec(v_f_2824_);
v___x_2827_ = lean_apply_2(v_toPure_2823_, lean_box(0), v_b_2825_);
return v___x_2827_;
}
else
{
lean_object* v_val_2828_; lean_object* v___x_2829_; 
lean_dec(v_toPure_2823_);
v_val_2828_ = lean_ctor_get(v_decl_2826_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v_decl_2826_, 1);
v___x_2829_ = lean_apply_2(v_f_2824_, v_b_2825_, v_val_2828_);
return v___x_2829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2830_, lean_object* v_lctx_2831_, lean_object* v_f_2832_, lean_object* v_init_2833_, lean_object* v_start_2834_){
_start:
{
lean_object* v_toApplicative_2835_; lean_object* v_decls_2836_; lean_object* v_toPure_2837_; lean_object* v___f_2838_; lean_object* v___x_2839_; 
v_toApplicative_2835_ = lean_ctor_get(v_inst_2830_, 0);
v_decls_2836_ = lean_ctor_get(v_lctx_2831_, 1);
lean_inc_ref(v_decls_2836_);
lean_dec_ref(v_lctx_2831_);
v_toPure_2837_ = lean_ctor_get(v_toApplicative_2835_, 1);
lean_inc(v_toPure_2837_);
v___f_2838_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2838_, 0, v_toPure_2837_);
lean_closure_set(v___f_2838_, 1, v_f_2832_);
v___x_2839_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2830_, v_decls_2836_, v___f_2838_, v_init_2833_, v_start_2834_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2840_, lean_object* v_lctx_2841_, lean_object* v_f_2842_, lean_object* v_init_2843_, lean_object* v_start_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2840_, v_lctx_2841_, v_f_2842_, v_init_2843_, v_start_2844_);
lean_dec(v_start_2844_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2846_, lean_object* v_00_u03b2_2847_, lean_object* v_inst_2848_, lean_object* v_lctx_2849_, lean_object* v_f_2850_, lean_object* v_init_2851_, lean_object* v_start_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2848_, v_lctx_2849_, v_f_2850_, v_init_2851_, v_start_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2854_, lean_object* v_00_u03b2_2855_, lean_object* v_inst_2856_, lean_object* v_lctx_2857_, lean_object* v_f_2858_, lean_object* v_init_2859_, lean_object* v_start_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_LocalContext_foldlM(v_m_2854_, v_00_u03b2_2855_, v_inst_2856_, v_lctx_2857_, v_f_2858_, v_init_2859_, v_start_2860_);
lean_dec(v_start_2860_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2862_, lean_object* v_f_2863_, lean_object* v_decl_2864_, lean_object* v_b_2865_){
_start:
{
if (lean_obj_tag(v_decl_2864_) == 0)
{
lean_object* v___x_2866_; 
lean_dec(v_f_2863_);
v___x_2866_ = lean_apply_2(v_toPure_2862_, lean_box(0), v_b_2865_);
return v___x_2866_;
}
else
{
lean_object* v_val_2867_; lean_object* v___x_2868_; 
lean_dec(v_toPure_2862_);
v_val_2867_ = lean_ctor_get(v_decl_2864_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v_decl_2864_, 1);
v___x_2868_ = lean_apply_2(v_f_2863_, v_val_2867_, v_b_2865_);
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2869_, lean_object* v_lctx_2870_, lean_object* v_f_2871_, lean_object* v_init_2872_){
_start:
{
lean_object* v_toApplicative_2873_; lean_object* v_decls_2874_; lean_object* v_toPure_2875_; lean_object* v___f_2876_; lean_object* v___x_2877_; 
v_toApplicative_2873_ = lean_ctor_get(v_inst_2869_, 0);
v_decls_2874_ = lean_ctor_get(v_lctx_2870_, 1);
lean_inc_ref(v_decls_2874_);
lean_dec_ref(v_lctx_2870_);
v_toPure_2875_ = lean_ctor_get(v_toApplicative_2873_, 1);
lean_inc(v_toPure_2875_);
v___f_2876_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2876_, 0, v_toPure_2875_);
lean_closure_set(v___f_2876_, 1, v_f_2871_);
v___x_2877_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2869_, v_decls_2874_, v___f_2876_, v_init_2872_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2878_, lean_object* v_00_u03b2_2879_, lean_object* v_inst_2880_, lean_object* v_lctx_2881_, lean_object* v_f_2882_, lean_object* v_init_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2880_, v_lctx_2881_, v_f_2882_, v_init_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2885_, lean_object* v_f_2886_, lean_object* v_decl_2887_){
_start:
{
if (lean_obj_tag(v_decl_2887_) == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec(v_f_2886_);
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_apply_2(v_toPure_2885_, lean_box(0), v___x_2888_);
return v___x_2889_;
}
else
{
lean_object* v_val_2890_; lean_object* v___x_2891_; 
lean_dec(v_toPure_2885_);
v_val_2890_ = lean_ctor_get(v_decl_2887_, 0);
lean_inc(v_val_2890_);
lean_dec_ref_known(v_decl_2887_, 1);
v___x_2891_ = lean_apply_1(v_f_2886_, v_val_2890_);
return v___x_2891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2892_, lean_object* v_lctx_2893_, lean_object* v_f_2894_, lean_object* v_start_2895_){
_start:
{
lean_object* v_toApplicative_2896_; lean_object* v_decls_2897_; lean_object* v_toPure_2898_; lean_object* v___f_2899_; lean_object* v___x_2900_; 
v_toApplicative_2896_ = lean_ctor_get(v_inst_2892_, 0);
v_decls_2897_ = lean_ctor_get(v_lctx_2893_, 1);
lean_inc_ref(v_decls_2897_);
lean_dec_ref(v_lctx_2893_);
v_toPure_2898_ = lean_ctor_get(v_toApplicative_2896_, 1);
lean_inc(v_toPure_2898_);
v___f_2899_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2899_, 0, v_toPure_2898_);
lean_closure_set(v___f_2899_, 1, v_f_2894_);
v___x_2900_ = l_Lean_PersistentArray_forM___redArg(v_inst_2892_, v_decls_2897_, v___f_2899_, v_start_2895_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2901_, lean_object* v_lctx_2902_, lean_object* v_f_2903_, lean_object* v_start_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_LocalContext_forM___redArg(v_inst_2901_, v_lctx_2902_, v_f_2903_, v_start_2904_);
lean_dec(v_start_2904_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2906_, lean_object* v_inst_2907_, lean_object* v_lctx_2908_, lean_object* v_f_2909_, lean_object* v_start_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_LocalContext_forM___redArg(v_inst_2907_, v_lctx_2908_, v_f_2909_, v_start_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2912_, lean_object* v_inst_2913_, lean_object* v_lctx_2914_, lean_object* v_f_2915_, lean_object* v_start_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_LocalContext_forM(v_m_2912_, v_inst_2913_, v_lctx_2914_, v_f_2915_, v_start_2916_);
lean_dec(v_start_2916_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2918_, lean_object* v_f_2919_, lean_object* v_decl_2920_){
_start:
{
if (lean_obj_tag(v_decl_2920_) == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v_f_2919_);
v___x_2921_ = lean_box(0);
v___x_2922_ = lean_apply_2(v_toPure_2918_, lean_box(0), v___x_2921_);
return v___x_2922_;
}
else
{
lean_object* v_val_2923_; lean_object* v___x_2924_; 
lean_dec(v_toPure_2918_);
v_val_2923_ = lean_ctor_get(v_decl_2920_, 0);
lean_inc(v_val_2923_);
lean_dec_ref_known(v_decl_2920_, 1);
v___x_2924_ = lean_apply_1(v_f_2919_, v_val_2923_);
return v___x_2924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2925_, lean_object* v_lctx_2926_, lean_object* v_f_2927_){
_start:
{
lean_object* v_toApplicative_2928_; lean_object* v_decls_2929_; lean_object* v_toPure_2930_; lean_object* v___f_2931_; lean_object* v___x_2932_; 
v_toApplicative_2928_ = lean_ctor_get(v_inst_2925_, 0);
v_decls_2929_ = lean_ctor_get(v_lctx_2926_, 1);
lean_inc_ref(v_decls_2929_);
lean_dec_ref(v_lctx_2926_);
v_toPure_2930_ = lean_ctor_get(v_toApplicative_2928_, 1);
lean_inc(v_toPure_2930_);
v___f_2931_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2931_, 0, v_toPure_2930_);
lean_closure_set(v___f_2931_, 1, v_f_2927_);
v___x_2932_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2925_, v_decls_2929_, v___f_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2933_, lean_object* v_00_u03b2_2934_, lean_object* v_inst_2935_, lean_object* v_lctx_2936_, lean_object* v_f_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2935_, v_lctx_2936_, v_f_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2939_, lean_object* v_lctx_2940_, lean_object* v_f_2941_){
_start:
{
lean_object* v_toApplicative_2942_; lean_object* v_decls_2943_; lean_object* v_toPure_2944_; lean_object* v___f_2945_; lean_object* v___x_2946_; 
v_toApplicative_2942_ = lean_ctor_get(v_inst_2939_, 0);
v_decls_2943_ = lean_ctor_get(v_lctx_2940_, 1);
lean_inc_ref(v_decls_2943_);
lean_dec_ref(v_lctx_2940_);
v_toPure_2944_ = lean_ctor_get(v_toApplicative_2942_, 1);
lean_inc(v_toPure_2944_);
v___f_2945_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2945_, 0, v_toPure_2944_);
lean_closure_set(v___f_2945_, 1, v_f_2941_);
v___x_2946_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2939_, v_decls_2943_, v___f_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2947_, lean_object* v_00_u03b2_2948_, lean_object* v_inst_2949_, lean_object* v_lctx_2950_, lean_object* v_f_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2949_, v_lctx_2950_, v_f_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2953_, lean_object* v_f_2954_, lean_object* v_d_x3f_2955_, lean_object* v_b_2956_){
_start:
{
if (lean_obj_tag(v_d_x3f_2955_) == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_dec(v_f_2954_);
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_b_2956_);
v___x_2958_ = lean_apply_2(v_toPure_2953_, lean_box(0), v___x_2957_);
return v___x_2958_;
}
else
{
lean_object* v_val_2959_; lean_object* v___x_2960_; 
lean_dec(v_toPure_2953_);
v_val_2959_ = lean_ctor_get(v_d_x3f_2955_, 0);
lean_inc(v_val_2959_);
lean_dec_ref_known(v_d_x3f_2955_, 1);
v___x_2960_ = lean_apply_2(v_f_2954_, v_val_2959_, v_b_2956_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2961_, lean_object* v_inst_2962_, lean_object* v_00_u03b2_2963_, lean_object* v_lctx_2964_, lean_object* v_init_2965_, lean_object* v_f_2966_){
_start:
{
lean_object* v_decls_2967_; lean_object* v___f_2968_; lean_object* v___x_2969_; 
v_decls_2967_ = lean_ctor_get(v_lctx_2964_, 1);
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2968_, 0, v_toPure_2961_);
lean_closure_set(v___f_2968_, 1, v_f_2966_);
v___x_2969_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2962_, v_decls_2967_, v_init_2965_, v___f_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2970_, lean_object* v_inst_2971_, lean_object* v_00_u03b2_2972_, lean_object* v_lctx_2973_, lean_object* v_init_2974_, lean_object* v_f_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2970_, v_inst_2971_, v_00_u03b2_2972_, v_lctx_2973_, v_init_2974_, v_f_2975_);
lean_dec_ref(v_lctx_2973_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2977_){
_start:
{
lean_object* v_toApplicative_2978_; lean_object* v_toPure_2979_; lean_object* v___f_2980_; 
v_toApplicative_2978_ = lean_ctor_get(v_inst_2977_, 0);
v_toPure_2979_ = lean_ctor_get(v_toApplicative_2978_, 1);
lean_inc(v_toPure_2979_);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2980_, 0, v_toPure_2979_);
lean_closure_set(v___f_2980_, 1, v_inst_2977_);
return v___f_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2981_, lean_object* v_inst_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2984_, lean_object* v_x1_2985_, lean_object* v_x2_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_apply_2(v_f_2984_, v_x1_2985_, v_x2_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_3007_, lean_object* v_f_3008_, lean_object* v_init_3009_, lean_object* v_start_3010_){
_start:
{
lean_object* v___f_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___f_3011_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3011_, 0, v_f_3008_);
v___x_3012_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3013_ = l_Lean_LocalContext_foldlM___redArg(v___x_3012_, v_lctx_3007_, v___f_3011_, v_init_3009_, v_start_3010_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_3014_, lean_object* v_f_3015_, lean_object* v_init_3016_, lean_object* v_start_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_LocalContext_foldl___redArg(v_lctx_3014_, v_f_3015_, v_init_3016_, v_start_3017_);
lean_dec(v_start_3017_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_3019_, lean_object* v_lctx_3020_, lean_object* v_f_3021_, lean_object* v_init_3022_, lean_object* v_start_3023_){
_start:
{
lean_object* v___f_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___f_3024_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3024_, 0, v_f_3021_);
v___x_3025_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3026_ = l_Lean_LocalContext_foldlM___redArg(v___x_3025_, v_lctx_3020_, v___f_3024_, v_init_3022_, v_start_3023_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_3027_, lean_object* v_lctx_3028_, lean_object* v_f_3029_, lean_object* v_init_3030_, lean_object* v_start_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_LocalContext_foldl(v_00_u03b2_3027_, v_lctx_3028_, v_f_3029_, v_init_3030_, v_start_3031_);
lean_dec(v_start_3031_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_3033_, lean_object* v_x1_3034_, lean_object* v_x2_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_apply_2(v_f_3033_, v_x1_3034_, v_x2_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_3037_, lean_object* v_f_3038_, lean_object* v_init_3039_){
_start:
{
lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___f_3040_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3040_, 0, v_f_3038_);
v___x_3041_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3042_ = l_Lean_LocalContext_foldrM___redArg(v___x_3041_, v_lctx_3037_, v___f_3040_, v_init_3039_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_3043_, lean_object* v_lctx_3044_, lean_object* v_f_3045_, lean_object* v_init_3046_){
_start:
{
lean_object* v___f_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___f_3047_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3047_, 0, v_f_3045_);
v___x_3048_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3049_ = l_Lean_LocalContext_foldrM___redArg(v___x_3048_, v_lctx_3044_, v___f_3047_, v_init_3046_);
return v___x_3049_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_3050_, size_t v_i_3051_, size_t v_stop_3052_, lean_object* v_b_3053_){
_start:
{
lean_object* v___y_3055_; uint8_t v___x_3059_; 
v___x_3059_ = lean_usize_dec_eq(v_i_3051_, v_stop_3052_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_array_uget_borrowed(v_as_3050_, v_i_3051_);
if (lean_obj_tag(v___x_3060_) == 0)
{
v___y_3055_ = v_b_3053_;
goto v___jp_3054_;
}
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_unsigned_to_nat(1u);
v___x_3062_ = lean_nat_add(v_b_3053_, v___x_3061_);
lean_dec(v_b_3053_);
v___y_3055_ = v___x_3062_;
goto v___jp_3054_;
}
}
else
{
return v_b_3053_;
}
v___jp_3054_:
{
size_t v___x_3056_; size_t v___x_3057_; 
v___x_3056_ = ((size_t)1ULL);
v___x_3057_ = lean_usize_add(v_i_3051_, v___x_3056_);
v_i_3051_ = v___x_3057_;
v_b_3053_ = v___y_3055_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3050_ = stack[0].m_obj;
size_t v_i_3051_ = stack[1].m_num;
size_t v_stop_3052_ = stack[2].m_num;
lean_object* v_b_3053_ = stack[3].m_obj;
lean_object* v_res_3063_;
v_res_3063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3050_, v_i_3051_, v_stop_3052_, v_b_3053_);
stack->m_obj
 = v_res_3063_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3064_, lean_object* v_i_3065_, lean_object* v_stop_3066_, lean_object* v_b_3067_){
_start:
{
size_t v_i_boxed_3068_; size_t v_stop_boxed_3069_; lean_object* v_res_3070_; 
v_i_boxed_3068_ = lean_unbox_usize(v_i_3065_);
lean_dec(v_i_3065_);
v_stop_boxed_3069_ = lean_unbox_usize(v_stop_3066_);
lean_dec(v_stop_3066_);
v_res_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3064_, v_i_boxed_3068_, v_stop_boxed_3069_, v_b_3067_);
lean_dec_ref(v_as_3064_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3071_, lean_object* v_x_3072_){
_start:
{
if (lean_obj_tag(v_x_3071_) == 0)
{
lean_object* v_cs_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v_cs_3073_ = lean_ctor_get(v_x_3071_, 0);
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_array_get_size(v_cs_3073_);
v___x_3076_ = lean_nat_dec_lt(v___x_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
return v_x_3072_;
}
else
{
size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((size_t)0ULL);
v___x_3078_ = lean_usize_of_nat(v___x_3075_);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3073_, v___x_3077_, v___x_3078_, v_x_3072_);
return v___x_3079_;
}
}
else
{
lean_object* v_vs_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_vs_3080_ = lean_ctor_get(v_x_3071_, 0);
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = lean_array_get_size(v_vs_3080_);
v___x_3083_ = lean_nat_dec_lt(v___x_3081_, v___x_3082_);
if (v___x_3083_ == 0)
{
return v_x_3072_;
}
else
{
size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = ((size_t)0ULL);
v___x_3085_ = lean_usize_of_nat(v___x_3082_);
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3080_, v___x_3084_, v___x_3085_, v_x_3072_);
return v___x_3086_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3087_, size_t v_i_3088_, size_t v_stop_3089_, lean_object* v_b_3090_){
_start:
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_usize_dec_eq(v_i_3088_, v_stop_3089_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; size_t v___x_3094_; size_t v___x_3095_; 
v___x_3092_ = lean_array_uget_borrowed(v_as_3087_, v_i_3088_);
v___x_3093_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3092_, v_b_3090_);
v___x_3094_ = ((size_t)1ULL);
v___x_3095_ = lean_usize_add(v_i_3088_, v___x_3094_);
v_i_3088_ = v___x_3095_;
v_b_3090_ = v___x_3093_;
goto _start;
}
else
{
return v_b_3090_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3087_ = stack[0].m_obj;
size_t v_i_3088_ = stack[1].m_num;
size_t v_stop_3089_ = stack[2].m_num;
lean_object* v_b_3090_ = stack[3].m_obj;
lean_object* v_res_3097_;
v_res_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3087_, v_i_3088_, v_stop_3089_, v_b_3090_);
stack->m_obj
 = v_res_3097_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3098_, lean_object* v_i_3099_, lean_object* v_stop_3100_, lean_object* v_b_3101_){
_start:
{
size_t v_i_boxed_3102_; size_t v_stop_boxed_3103_; lean_object* v_res_3104_; 
v_i_boxed_3102_ = lean_unbox_usize(v_i_3099_);
lean_dec(v_i_3099_);
v_stop_boxed_3103_ = lean_unbox_usize(v_stop_3100_);
lean_dec(v_stop_3100_);
v_res_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3098_, v_i_boxed_3102_, v_stop_boxed_3103_, v_b_3101_);
lean_dec_ref(v_as_3098_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3105_, lean_object* v_x_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3105_, v_x_3106_);
lean_dec_ref(v_x_3105_);
return v_res_3107_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3108_, size_t v_x_3109_, size_t v_x_3110_, lean_object* v_x_3111_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 0)
{
lean_object* v_cs_3112_; lean_object* v___x_3113_; size_t v___x_3114_; lean_object* v_j_3115_; lean_object* v___x_3116_; size_t v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; size_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v_cs_3112_ = lean_ctor_get(v_x_3108_, 0);
v___x_3113_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3114_ = lean_usize_shift_right(v_x_3109_, v_x_3110_);
v_j_3115_ = lean_usize_to_nat(v___x_3114_);
v___x_3116_ = lean_array_get_borrowed(v___x_3113_, v_cs_3112_, v_j_3115_);
v___x_3117_ = ((size_t)1ULL);
v___x_3118_ = lean_usize_shift_left(v___x_3117_, v_x_3110_);
v___x_3119_ = lean_usize_sub(v___x_3118_, v___x_3117_);
v___x_3120_ = lean_usize_land(v_x_3109_, v___x_3119_);
v___x_3121_ = ((size_t)5ULL);
v___x_3122_ = lean_usize_sub(v_x_3110_, v___x_3121_);
v___x_3123_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3116_, v___x_3120_, v___x_3122_, v_x_3111_);
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_add(v_j_3115_, v___x_3124_);
lean_dec(v_j_3115_);
v___x_3126_ = lean_array_get_size(v_cs_3112_);
v___x_3127_ = lean_nat_dec_lt(v___x_3125_, v___x_3126_);
if (v___x_3127_ == 0)
{
lean_dec(v___x_3125_);
return v___x_3123_;
}
else
{
size_t v___x_3128_; size_t v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_usize_of_nat(v___x_3125_);
lean_dec(v___x_3125_);
v___x_3129_ = lean_usize_of_nat(v___x_3126_);
v___x_3130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3112_, v___x_3128_, v___x_3129_, v___x_3123_);
return v___x_3130_;
}
}
else
{
lean_object* v_vs_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v_vs_3131_ = lean_ctor_get(v_x_3108_, 0);
v___x_3132_ = lean_usize_to_nat(v_x_3109_);
v___x_3133_ = lean_array_get_size(v_vs_3131_);
v___x_3134_ = lean_nat_dec_lt(v___x_3132_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_dec(v___x_3132_);
return v_x_3111_;
}
else
{
size_t v___x_3135_; size_t v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_usize_of_nat(v___x_3132_);
lean_dec(v___x_3132_);
v___x_3136_ = lean_usize_of_nat(v___x_3133_);
v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3131_, v___x_3135_, v___x_3136_, v_x_3111_);
return v___x_3137_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3108_ = stack[0].m_obj;
size_t v_x_3109_ = stack[1].m_num;
size_t v_x_3110_ = stack[2].m_num;
lean_object* v_x_3111_ = stack[3].m_obj;
lean_object* v_res_3138_;
v_res_3138_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3108_, v_x_3109_, v_x_3110_, v_x_3111_);
stack->m_obj
 = v_res_3138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_, lean_object* v_x_3142_){
_start:
{
size_t v_x_1218__boxed_3143_; size_t v_x_1219__boxed_3144_; lean_object* v_res_3145_; 
v_x_1218__boxed_3143_ = lean_unbox_usize(v_x_3140_);
lean_dec(v_x_3140_);
v_x_1219__boxed_3144_ = lean_unbox_usize(v_x_3141_);
lean_dec(v_x_3141_);
v_res_3145_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3139_, v_x_1218__boxed_3143_, v_x_1219__boxed_3144_, v_x_3142_);
lean_dec_ref(v_x_3139_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3146_, lean_object* v_init_3147_, lean_object* v_start_3148_){
_start:
{
lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = lean_unsigned_to_nat(0u);
v___x_3150_ = lean_nat_dec_eq(v_start_3148_, v___x_3149_);
if (v___x_3150_ == 0)
{
lean_object* v_root_3151_; lean_object* v_tail_3152_; size_t v_shift_3153_; lean_object* v_tailOff_3154_; uint8_t v___x_3155_; 
v_root_3151_ = lean_ctor_get(v_t_3146_, 0);
v_tail_3152_ = lean_ctor_get(v_t_3146_, 1);
v_shift_3153_ = lean_ctor_get_usize(v_t_3146_, 4);
v_tailOff_3154_ = lean_ctor_get(v_t_3146_, 3);
v___x_3155_ = lean_nat_dec_le(v_tailOff_3154_, v_start_3148_);
if (v___x_3155_ == 0)
{
size_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3156_ = lean_usize_of_nat(v_start_3148_);
v___x_3157_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3151_, v___x_3156_, v_shift_3153_, v_init_3147_);
v___x_3158_ = lean_array_get_size(v_tail_3152_);
v___x_3159_ = lean_nat_dec_lt(v___x_3149_, v___x_3158_);
if (v___x_3159_ == 0)
{
return v___x_3157_;
}
else
{
size_t v___x_3160_; size_t v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = ((size_t)0ULL);
v___x_3161_ = lean_usize_of_nat(v___x_3158_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3152_, v___x_3160_, v___x_3161_, v___x_3157_);
return v___x_3162_;
}
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3163_ = lean_nat_sub(v_start_3148_, v_tailOff_3154_);
v___x_3164_ = lean_array_get_size(v_tail_3152_);
v___x_3165_ = lean_nat_dec_lt(v___x_3163_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_dec(v___x_3163_);
return v_init_3147_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = lean_usize_of_nat(v___x_3163_);
lean_dec(v___x_3163_);
v___x_3167_ = lean_usize_of_nat(v___x_3164_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3152_, v___x_3166_, v___x_3167_, v_init_3147_);
return v___x_3168_;
}
}
}
else
{
lean_object* v_root_3169_; lean_object* v_tail_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_root_3169_ = lean_ctor_get(v_t_3146_, 0);
v_tail_3170_ = lean_ctor_get(v_t_3146_, 1);
v___x_3171_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3169_, v_init_3147_);
v___x_3172_ = lean_array_get_size(v_tail_3170_);
v___x_3173_ = lean_nat_dec_lt(v___x_3149_, v___x_3172_);
if (v___x_3173_ == 0)
{
return v___x_3171_;
}
else
{
size_t v___x_3174_; size_t v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = ((size_t)0ULL);
v___x_3175_ = lean_usize_of_nat(v___x_3172_);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3170_, v___x_3174_, v___x_3175_, v___x_3171_);
return v___x_3176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3177_, lean_object* v_init_3178_, lean_object* v_start_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3177_, v_init_3178_, v_start_3179_);
lean_dec(v_start_3179_);
lean_dec_ref(v_t_3177_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3181_, lean_object* v_init_3182_, lean_object* v_start_3183_){
_start:
{
lean_object* v_decls_3184_; lean_object* v___x_3185_; 
v_decls_3184_ = lean_ctor_get(v_lctx_3181_, 1);
v___x_3185_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3184_, v_init_3182_, v_start_3183_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3186_, lean_object* v_init_3187_, lean_object* v_start_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3186_, v_init_3187_, v_start_3188_);
lean_dec(v_start_3188_);
lean_dec_ref(v_lctx_3186_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3190_){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3190_, v___x_3191_, v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_LocalContext_size(v_lctx_3193_);
lean_dec_ref(v_lctx_3193_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3195_, lean_object* v_x_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_apply_1(v_f_3195_, v_x_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3198_, lean_object* v_f_3199_){
_start:
{
lean_object* v___f_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___f_3200_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3200_, 0, v_f_3199_);
v___x_3201_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3202_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3201_, v_lctx_3198_, v___f_3200_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3203_, lean_object* v_lctx_3204_, lean_object* v_f_3205_){
_start:
{
lean_object* v___f_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___f_3206_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3206_, 0, v_f_3205_);
v___x_3207_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3208_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3207_, v_lctx_3204_, v___f_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3209_, lean_object* v_f_3210_){
_start:
{
lean_object* v___f_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3211_, 0, v_f_3210_);
v___x_3212_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3213_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3212_, v_lctx_3209_, v___f_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3214_, lean_object* v_lctx_3215_, lean_object* v_f_3216_){
_start:
{
lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3217_, 0, v_f_3216_);
v___x_3218_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3219_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3218_, v_lctx_3215_, v___f_3217_);
return v___x_3219_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3220_, lean_object* v_as_3221_, size_t v_i_3222_, size_t v_stop_3223_){
_start:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_usize_dec_eq(v_i_3222_, v_stop_3223_);
if (v___x_3224_ == 0)
{
uint8_t v___x_3225_; uint8_t v___y_3227_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v_fvarId_3233_; uint8_t v___x_3234_; 
v___x_3225_ = 1;
v___x_3231_ = lean_array_uget_borrowed(v_as_3221_, v_i_3222_);
v___x_3232_ = l_Lean_Expr_fvarId_x21(v___x_3231_);
v_fvarId_3233_ = lean_ctor_get(v_val_3220_, 1);
v___x_3234_ = l_Lean_instBEqFVarId_beq(v___x_3232_, v_fvarId_3233_);
lean_dec(v___x_3232_);
v___y_3227_ = v___x_3234_;
goto v___jp_3226_;
v___jp_3226_:
{
if (v___y_3227_ == 0)
{
size_t v___x_3228_; size_t v___x_3229_; 
v___x_3228_ = ((size_t)1ULL);
v___x_3229_ = lean_usize_add(v_i_3222_, v___x_3228_);
v_i_3222_ = v___x_3229_;
goto _start;
}
else
{
return v___x_3225_;
}
}
}
else
{
uint8_t v___x_3235_; 
v___x_3235_ = 0;
return v___x_3235_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3220_ = stack[0].m_obj;
lean_object* v_as_3221_ = stack[1].m_obj;
size_t v_i_3222_ = stack[2].m_num;
size_t v_stop_3223_ = stack[3].m_num;
uint8_t v_res_3236_;
v_res_3236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3220_, v_as_3221_, v_i_3222_, v_stop_3223_);
stack->m_num = v_res_3236_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3237_, lean_object* v_as_3238_, lean_object* v_i_3239_, lean_object* v_stop_3240_){
_start:
{
size_t v_i_boxed_3241_; size_t v_stop_boxed_3242_; uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_i_boxed_3241_ = lean_unbox_usize(v_i_3239_);
lean_dec(v_i_3239_);
v_stop_boxed_3242_ = lean_unbox_usize(v_stop_3240_);
lean_dec(v_stop_3240_);
v_res_3243_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3237_, v_as_3238_, v_i_boxed_3241_, v_stop_boxed_3242_);
lean_dec_ref(v_as_3238_);
lean_dec_ref(v_val_3237_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3245_, lean_object* v_a_u2082_3246_, lean_object* v_exceptFVars_3247_, lean_object* v_i_3248_, lean_object* v_j_3249_){
_start:
{
lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v_size_3265_; uint8_t v___x_3266_; 
v_size_3265_ = lean_ctor_get(v_a_u2081_3245_, 2);
v___x_3266_ = lean_nat_dec_lt(v_i_3248_, v_size_3265_);
if (v___x_3266_ == 0)
{
uint8_t v___x_3267_; 
lean_dec(v_j_3249_);
lean_dec(v_i_3248_);
v___x_3267_ = 1;
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = lean_box(0);
v___x_3269_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3268_, v_a_u2081_3245_, v_i_3248_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_unsigned_to_nat(1u);
v___x_3271_ = lean_nat_add(v_i_3248_, v___x_3270_);
lean_dec(v_i_3248_);
v_i_3248_ = v___x_3271_;
goto _start;
}
else
{
lean_object* v_val_3273_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_val_3273_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_val_3273_);
lean_dec_ref_known(v___x_3269_, 1);
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = lean_array_get_size(v_exceptFVars_3247_);
v___x_3285_ = lean_nat_dec_lt(v___x_3283_, v___x_3284_);
if (v___x_3285_ == 0)
{
goto v___jp_3274_;
}
else
{
if (v___x_3285_ == 0)
{
goto v___jp_3274_;
}
else
{
size_t v___x_3286_; size_t v___x_3287_; uint8_t v___x_3288_; 
v___x_3286_ = ((size_t)0ULL);
v___x_3287_ = lean_usize_of_nat(v___x_3284_);
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3273_, v_exceptFVars_3247_, v___x_3286_, v___x_3287_);
if (v___x_3288_ == 0)
{
goto v___jp_3274_;
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v_val_3273_);
v___x_3289_ = lean_unsigned_to_nat(1u);
v___x_3290_ = lean_nat_add(v_i_3248_, v___x_3289_);
lean_dec(v_i_3248_);
v_i_3248_ = v___x_3290_;
goto _start;
}
}
}
v___jp_3274_:
{
lean_object* v_size_3275_; uint8_t v___x_3276_; 
v_size_3275_ = lean_ctor_get(v_a_u2082_3246_, 2);
v___x_3276_ = lean_nat_dec_lt(v_j_3249_, v_size_3275_);
if (v___x_3276_ == 0)
{
lean_dec(v_val_3273_);
lean_dec(v_j_3249_);
lean_dec(v_i_3248_);
return v___x_3276_;
}
else
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3268_, v_a_u2082_3246_, v_j_3249_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_dec(v_val_3273_);
v___x_3278_ = lean_unsigned_to_nat(1u);
v___x_3279_ = lean_nat_add(v_j_3249_, v___x_3278_);
lean_dec(v_j_3249_);
v_j_3249_ = v___x_3279_;
goto _start;
}
else
{
lean_object* v_val_3281_; lean_object* v_fvarId_3282_; 
v_val_3281_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_val_3281_);
lean_dec_ref_known(v___x_3277_, 1);
v_fvarId_3282_ = lean_ctor_get(v_val_3273_, 1);
lean_inc(v_fvarId_3282_);
lean_dec(v_val_3273_);
v___y_3262_ = v_val_3281_;
v___y_3263_ = v_fvarId_3282_;
goto v___jp_3261_;
}
}
}
}
}
v___jp_3250_:
{
uint8_t v___x_3253_; 
v___x_3253_ = l_Lean_instBEqFVarId_beq(v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_unsigned_to_nat(1u);
v___x_3255_ = lean_nat_add(v_j_3249_, v___x_3254_);
lean_dec(v_j_3249_);
v_j_3249_ = v___x_3255_;
goto _start;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_unsigned_to_nat(1u);
v___x_3258_ = lean_nat_add(v_i_3248_, v___x_3257_);
lean_dec(v_i_3248_);
v___x_3259_ = lean_nat_add(v_j_3249_, v___x_3257_);
lean_dec(v_j_3249_);
v_i_3248_ = v___x_3258_;
v_j_3249_ = v___x_3259_;
goto _start;
}
}
v___jp_3261_:
{
lean_object* v_fvarId_3264_; 
v_fvarId_3264_ = lean_ctor_get(v___y_3262_, 1);
lean_inc(v_fvarId_3264_);
lean_dec_ref(v___y_3262_);
v___y_3251_ = v___y_3263_;
v___y_3252_ = v_fvarId_3264_;
goto v___jp_3250_;
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_isSubPrefixOfAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_u2081_3245_ = stack[0].m_obj;
lean_object* v_a_u2082_3246_ = stack[1].m_obj;
lean_object* v_exceptFVars_3247_ = stack[2].m_obj;
lean_object* v_i_3248_ = stack[3].m_obj;
lean_object* v_j_3249_ = stack[4].m_obj;
uint8_t v_res_3292_;
v_res_3292_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3245_, v_a_u2082_3246_, v_exceptFVars_3247_, v_i_3248_, v_j_3249_);
stack->m_num = v_res_3292_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3293_, lean_object* v_a_u2082_3294_, lean_object* v_exceptFVars_3295_, lean_object* v_i_3296_, lean_object* v_j_3297_){
_start:
{
uint8_t v_res_3298_; lean_object* v_r_3299_; 
v_res_3298_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3293_, v_a_u2082_3294_, v_exceptFVars_3295_, v_i_3296_, v_j_3297_);
lean_dec_ref(v_exceptFVars_3295_);
lean_dec_ref(v_a_u2082_3294_);
lean_dec_ref(v_a_u2081_3293_);
v_r_3299_ = lean_box(v_res_3298_);
return v_r_3299_;
}
}
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3300_, lean_object* v_lctx_u2082_3301_, lean_object* v_exceptFVars_3302_){
_start:
{
lean_object* v_decls_3303_; lean_object* v_decls_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
v_decls_3303_ = lean_ctor_get(v_lctx_u2081_3300_, 1);
v_decls_3304_ = lean_ctor_get(v_lctx_u2082_3301_, 1);
v___x_3305_ = lean_unsigned_to_nat(0u);
v___x_3306_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3303_, v_decls_3304_, v_exceptFVars_3302_, v___x_3305_, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_isSubPrefixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_u2081_3300_ = stack[0].m_obj;
lean_object* v_lctx_u2082_3301_ = stack[1].m_obj;
lean_object* v_exceptFVars_3302_ = stack[2].m_obj;
uint8_t v_res_3307_;
v_res_3307_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3300_, v_lctx_u2082_3301_, v_exceptFVars_3302_);
stack->m_num = v_res_3307_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3308_, lean_object* v_lctx_u2082_3309_, lean_object* v_exceptFVars_3310_){
_start:
{
uint8_t v_res_3311_; lean_object* v_r_3312_; 
v_res_3311_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3308_, v_lctx_u2082_3309_, v_exceptFVars_3310_);
lean_dec_ref(v_exceptFVars_3310_);
lean_dec_ref(v_lctx_u2082_3309_);
lean_dec_ref(v_lctx_u2081_3308_);
v_r_3312_ = lean_box(v_res_3311_);
return v_r_3312_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3314_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3315_ = lean_unsigned_to_nat(14u);
v___x_3316_ = lean_unsigned_to_nat(585u);
v___x_3317_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3318_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3319_ = l_mkPanicMessageWithDecl(v___x_3318_, v___x_3317_, v___x_3316_, v___x_3315_, v___x_3314_);
return v___x_3319_;
}
}
lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3320_, lean_object* v_lctx_3321_, lean_object* v___x_3322_, uint8_t v_isLambda_3323_, uint8_t v_usedLetOnly_3324_, uint8_t v_generalizeNondepLet_3325_, lean_object* v_i_3326_, lean_object* v_x_3327_, lean_object* v_b_3328_){
_start:
{
lean_object* v_n_3330_; lean_object* v_ty_3331_; uint8_t v_bi_3332_; lean_object* v_x_3336_; lean_object* v___x_3337_; 
v_x_3336_ = lean_array_fget_borrowed(v_xs_3320_, v_i_3326_);
v___x_3337_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3321_, v_x_3336_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec_ref(v_b_3328_);
v___x_3338_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3339_ = l_panic___redArg(v___x_3322_, v___x_3338_);
return v___x_3339_;
}
else
{
lean_object* v_val_3340_; 
v_val_3340_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___x_3337_, 1);
if (lean_obj_tag(v_val_3340_) == 0)
{
lean_object* v_userName_3341_; lean_object* v_type_3342_; uint8_t v_bi_3343_; 
v_userName_3341_ = lean_ctor_get(v_val_3340_, 2);
lean_inc(v_userName_3341_);
v_type_3342_ = lean_ctor_get(v_val_3340_, 3);
lean_inc_ref(v_type_3342_);
v_bi_3343_ = lean_ctor_get_uint8(v_val_3340_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3340_, 4);
v_n_3330_ = v_userName_3341_;
v_ty_3331_ = v_type_3342_;
v_bi_3332_ = v_bi_3343_;
goto v___jp_3329_;
}
else
{
lean_object* v_userName_3344_; lean_object* v_type_3345_; lean_object* v_value_3346_; uint8_t v_nondep_3347_; uint8_t v___y_3353_; 
v_userName_3344_ = lean_ctor_get(v_val_3340_, 2);
lean_inc(v_userName_3344_);
v_type_3345_ = lean_ctor_get(v_val_3340_, 3);
lean_inc_ref(v_type_3345_);
v_value_3346_ = lean_ctor_get(v_val_3340_, 4);
lean_inc_ref(v_value_3346_);
v_nondep_3347_ = lean_ctor_get_uint8(v_val_3340_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3340_, 5);
if (v_nondep_3347_ == 0)
{
v___y_3353_ = v_nondep_3347_;
goto v___jp_3352_;
}
else
{
if (v_generalizeNondepLet_3325_ == 0)
{
v___y_3353_ = v_generalizeNondepLet_3325_;
goto v___jp_3352_;
}
else
{
uint8_t v___x_3358_; 
lean_dec_ref(v_value_3346_);
v___x_3358_ = 0;
v_n_3330_ = v_userName_3344_;
v_ty_3331_ = v_type_3345_;
v_bi_3332_ = v___x_3358_;
goto v___jp_3329_;
}
}
v___jp_3348_:
{
lean_object* v_ty_3349_; lean_object* v_val_3350_; lean_object* v___x_3351_; 
v_ty_3349_ = lean_expr_abstract_range(v_type_3345_, v_i_3326_, v_xs_3320_);
lean_dec_ref(v_type_3345_);
v_val_3350_ = lean_expr_abstract_range(v_value_3346_, v_i_3326_, v_xs_3320_);
lean_dec_ref(v_value_3346_);
v___x_3351_ = l_Lean_Expr_letE___override(v_userName_3344_, v_ty_3349_, v_val_3350_, v_b_3328_, v_nondep_3347_);
return v___x_3351_;
}
v___jp_3352_:
{
if (v_usedLetOnly_3324_ == 0)
{
goto v___jp_3348_;
}
else
{
if (v___y_3353_ == 0)
{
lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3354_ = lean_unsigned_to_nat(0u);
v___x_3355_ = lean_expr_has_loose_bvar(v_b_3328_, v___x_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec_ref(v_value_3346_);
lean_dec_ref(v_type_3345_);
lean_dec(v_userName_3344_);
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_expr_lower_loose_bvars(v_b_3328_, v___x_3356_, v___x_3356_);
lean_dec_ref(v_b_3328_);
return v___x_3357_;
}
else
{
goto v___jp_3348_;
}
}
else
{
goto v___jp_3348_;
}
}
}
}
}
v___jp_3329_:
{
lean_object* v_ty_3333_; 
v_ty_3333_ = lean_expr_abstract_range(v_ty_3331_, v_i_3326_, v_xs_3320_);
lean_dec_ref(v_ty_3331_);
if (v_isLambda_3323_ == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_mkForall(v_n_3330_, v_bi_3332_, v_ty_3333_, v_b_3328_);
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_mkLambda(v_n_3330_, v_bi_3332_, v_ty_3333_, v_b_3328_);
return v___x_3335_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_mkBinding___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3320_ = stack[0].m_obj;
lean_object* v_lctx_3321_ = stack[1].m_obj;
lean_object* v___x_3322_ = stack[2].m_obj;
uint8_t v_isLambda_3323_ = stack[3].m_num;
uint8_t v_usedLetOnly_3324_ = stack[4].m_num;
uint8_t v_generalizeNondepLet_3325_ = stack[5].m_num;
lean_object* v_i_3326_ = stack[6].m_obj;
lean_object* v_b_3328_ = stack[8].m_obj;
lean_object* v_res_3359_;
v_res_3359_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3320_, v_lctx_3321_, v___x_3322_, v_isLambda_3323_, v_usedLetOnly_3324_, v_generalizeNondepLet_3325_, v_i_3326_, lean_box(0), v_b_3328_);
stack->m_obj
 = v_res_3359_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3360_, lean_object* v_lctx_3361_, lean_object* v___x_3362_, lean_object* v_isLambda_3363_, lean_object* v_usedLetOnly_3364_, lean_object* v_generalizeNondepLet_3365_, lean_object* v_i_3366_, lean_object* v_x_3367_, lean_object* v_b_3368_){
_start:
{
uint8_t v_isLambda_boxed_3369_; uint8_t v_usedLetOnly_boxed_3370_; uint8_t v_generalizeNondepLet_boxed_3371_; lean_object* v_res_3372_; 
v_isLambda_boxed_3369_ = lean_unbox(v_isLambda_3363_);
v_usedLetOnly_boxed_3370_ = lean_unbox(v_usedLetOnly_3364_);
v_generalizeNondepLet_boxed_3371_ = lean_unbox(v_generalizeNondepLet_3365_);
v_res_3372_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3360_, v_lctx_3361_, v___x_3362_, v_isLambda_boxed_3369_, v_usedLetOnly_boxed_3370_, v_generalizeNondepLet_boxed_3371_, v_i_3366_, v_x_3367_, v_b_3368_);
lean_dec(v_i_3366_);
lean_dec_ref(v___x_3362_);
lean_dec_ref(v_xs_3360_);
return v_res_3372_;
}
}
lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3373_, lean_object* v_lctx_3374_, lean_object* v_xs_3375_, lean_object* v_b_3376_, uint8_t v_usedLetOnly_3377_, uint8_t v_generalizeNondepLet_3378_){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___f_3383_; lean_object* v_b_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3379_ = l_Lean_instInhabitedExpr;
v___x_3380_ = lean_box(v_isLambda_3373_);
v___x_3381_ = lean_box(v_usedLetOnly_3377_);
v___x_3382_ = lean_box(v_generalizeNondepLet_3378_);
lean_inc_ref(v_xs_3375_);
v___f_3383_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3383_, 0, v_xs_3375_);
lean_closure_set(v___f_3383_, 1, v_lctx_3374_);
lean_closure_set(v___f_3383_, 2, v___x_3379_);
lean_closure_set(v___f_3383_, 3, v___x_3380_);
lean_closure_set(v___f_3383_, 4, v___x_3381_);
lean_closure_set(v___f_3383_, 5, v___x_3382_);
v_b_3384_ = lean_expr_abstract(v_b_3376_, v_xs_3375_);
v___x_3385_ = lean_array_get_size(v_xs_3375_);
lean_dec_ref(v_xs_3375_);
v___x_3386_ = l_Nat_foldRev___redArg(v___x_3385_, v___f_3383_, v_b_3384_);
return v___x_3386_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_mkBinding_0interp(lean_interpreter_value* stack)
{
uint8_t v_isLambda_3373_ = stack[0].m_num;
lean_object* v_lctx_3374_ = stack[1].m_obj;
lean_object* v_xs_3375_ = stack[2].m_obj;
lean_object* v_b_3376_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3377_ = stack[4].m_num;
uint8_t v_generalizeNondepLet_3378_ = stack[5].m_num;
lean_object* v_res_3387_;
v_res_3387_ = l_Lean_LocalContext_mkBinding(v_isLambda_3373_, v_lctx_3374_, v_xs_3375_, v_b_3376_, v_usedLetOnly_3377_, v_generalizeNondepLet_3378_);
stack->m_obj
 = v_res_3387_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3388_, lean_object* v_lctx_3389_, lean_object* v_xs_3390_, lean_object* v_b_3391_, lean_object* v_usedLetOnly_3392_, lean_object* v_generalizeNondepLet_3393_){
_start:
{
uint8_t v_isLambda_boxed_3394_; uint8_t v_usedLetOnly_boxed_3395_; uint8_t v_generalizeNondepLet_boxed_3396_; lean_object* v_res_3397_; 
v_isLambda_boxed_3394_ = lean_unbox(v_isLambda_3388_);
v_usedLetOnly_boxed_3395_ = lean_unbox(v_usedLetOnly_3392_);
v_generalizeNondepLet_boxed_3396_ = lean_unbox(v_generalizeNondepLet_3393_);
v_res_3397_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3394_, v_lctx_3389_, v_xs_3390_, v_b_3391_, v_usedLetOnly_boxed_3395_, v_generalizeNondepLet_boxed_3396_);
lean_dec_ref(v_b_3391_);
return v_res_3397_;
}
}
lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3398_, lean_object* v_lctx_3399_, uint8_t v_usedLetOnly_3400_, uint8_t v_generalizeNondepLet_3401_, lean_object* v_x_3402_, lean_object* v_x_3403_){
_start:
{
lean_object* v_zero_3404_; uint8_t v_isZero_3405_; 
v_zero_3404_ = lean_unsigned_to_nat(0u);
v_isZero_3405_ = lean_nat_dec_eq(v_x_3402_, v_zero_3404_);
if (v_isZero_3405_ == 1)
{
lean_dec(v_x_3402_);
lean_dec_ref(v_lctx_3399_);
return v_x_3403_;
}
else
{
lean_object* v_one_3406_; lean_object* v_n_3407_; lean_object* v_n_3409_; lean_object* v_ty_3410_; uint8_t v_bi_3411_; lean_object* v_x_3415_; lean_object* v___x_3416_; 
v_one_3406_ = lean_unsigned_to_nat(1u);
v_n_3407_ = lean_nat_sub(v_x_3402_, v_one_3406_);
lean_dec(v_x_3402_);
v_x_3415_ = lean_array_fget_borrowed(v_xs_3398_, v_n_3407_);
lean_inc_ref(v_lctx_3399_);
v___x_3416_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3399_, v_x_3415_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref(v_x_3403_);
v___x_3417_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3418_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3417_);
v_x_3402_ = v_n_3407_;
v_x_3403_ = v___x_3418_;
goto _start;
}
else
{
lean_object* v_val_3420_; 
v_val_3420_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_val_3420_);
lean_dec_ref_known(v___x_3416_, 1);
if (lean_obj_tag(v_val_3420_) == 0)
{
lean_object* v_userName_3421_; lean_object* v_type_3422_; uint8_t v_bi_3423_; 
v_userName_3421_ = lean_ctor_get(v_val_3420_, 2);
lean_inc(v_userName_3421_);
v_type_3422_ = lean_ctor_get(v_val_3420_, 3);
lean_inc_ref(v_type_3422_);
v_bi_3423_ = lean_ctor_get_uint8(v_val_3420_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3420_, 4);
v_n_3409_ = v_userName_3421_;
v_ty_3410_ = v_type_3422_;
v_bi_3411_ = v_bi_3423_;
goto v___jp_3408_;
}
else
{
lean_object* v_userName_3424_; lean_object* v_type_3425_; lean_object* v_value_3426_; uint8_t v_nondep_3427_; uint8_t v___y_3434_; 
v_userName_3424_ = lean_ctor_get(v_val_3420_, 2);
lean_inc(v_userName_3424_);
v_type_3425_ = lean_ctor_get(v_val_3420_, 3);
lean_inc_ref(v_type_3425_);
v_value_3426_ = lean_ctor_get(v_val_3420_, 4);
lean_inc_ref(v_value_3426_);
v_nondep_3427_ = lean_ctor_get_uint8(v_val_3420_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3420_, 5);
if (v_nondep_3427_ == 0)
{
v___y_3434_ = v_nondep_3427_;
goto v___jp_3433_;
}
else
{
if (v_generalizeNondepLet_3401_ == 0)
{
v___y_3434_ = v_generalizeNondepLet_3401_;
goto v___jp_3433_;
}
else
{
uint8_t v___x_3438_; 
lean_dec_ref(v_value_3426_);
v___x_3438_ = 0;
v_n_3409_ = v_userName_3424_;
v_ty_3410_ = v_type_3425_;
v_bi_3411_ = v___x_3438_;
goto v___jp_3408_;
}
}
v___jp_3428_:
{
lean_object* v_ty_3429_; lean_object* v_val_3430_; lean_object* v___x_3431_; 
v_ty_3429_ = lean_expr_abstract_range(v_type_3425_, v_n_3407_, v_xs_3398_);
lean_dec_ref(v_type_3425_);
v_val_3430_ = lean_expr_abstract_range(v_value_3426_, v_n_3407_, v_xs_3398_);
lean_dec_ref(v_value_3426_);
v___x_3431_ = l_Lean_Expr_letE___override(v_userName_3424_, v_ty_3429_, v_val_3430_, v_x_3403_, v_nondep_3427_);
v_x_3402_ = v_n_3407_;
v_x_3403_ = v___x_3431_;
goto _start;
}
v___jp_3433_:
{
if (v_usedLetOnly_3400_ == 0)
{
goto v___jp_3428_;
}
else
{
if (v___y_3434_ == 0)
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_expr_has_loose_bvar(v_x_3403_, v_zero_3404_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; 
lean_dec_ref(v_value_3426_);
lean_dec_ref(v_type_3425_);
lean_dec(v_userName_3424_);
v___x_3436_ = lean_expr_lower_loose_bvars(v_x_3403_, v_one_3406_, v_one_3406_);
lean_dec_ref(v_x_3403_);
v_x_3402_ = v_n_3407_;
v_x_3403_ = v___x_3436_;
goto _start;
}
else
{
goto v___jp_3428_;
}
}
else
{
goto v___jp_3428_;
}
}
}
}
}
v___jp_3408_:
{
lean_object* v_ty_3412_; lean_object* v___x_3413_; 
v_ty_3412_ = lean_expr_abstract_range(v_ty_3410_, v_n_3407_, v_xs_3398_);
lean_dec_ref(v_ty_3410_);
v___x_3413_ = l_Lean_mkLambda(v_n_3409_, v_bi_3411_, v_ty_3412_, v_x_3403_);
v_x_3402_ = v_n_3407_;
v_x_3403_ = v___x_3413_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3398_ = stack[0].m_obj;
lean_object* v_lctx_3399_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3400_ = stack[2].m_num;
uint8_t v_generalizeNondepLet_3401_ = stack[3].m_num;
lean_object* v_x_3402_ = stack[4].m_obj;
lean_object* v_x_3403_ = stack[5].m_obj;
lean_object* v_res_3439_;
v_res_3439_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3398_, v_lctx_3399_, v_usedLetOnly_3400_, v_generalizeNondepLet_3401_, v_x_3402_, v_x_3403_);
stack->m_obj
 = v_res_3439_;
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3440_, lean_object* v_lctx_3441_, lean_object* v_usedLetOnly_3442_, lean_object* v_generalizeNondepLet_3443_, lean_object* v_x_3444_, lean_object* v_x_3445_){
_start:
{
uint8_t v_usedLetOnly_boxed_3446_; uint8_t v_generalizeNondepLet_boxed_3447_; lean_object* v_res_3448_; 
v_usedLetOnly_boxed_3446_ = lean_unbox(v_usedLetOnly_3442_);
v_generalizeNondepLet_boxed_3447_ = lean_unbox(v_generalizeNondepLet_3443_);
v_res_3448_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3440_, v_lctx_3441_, v_usedLetOnly_boxed_3446_, v_generalizeNondepLet_boxed_3447_, v_x_3444_, v_x_3445_);
lean_dec_ref(v_xs_3440_);
return v_res_3448_;
}
}
lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3449_, lean_object* v_lctx_3450_, uint8_t v_usedLetOnly_3451_, uint8_t v_generalizeNondepLet_3452_, lean_object* v_x_3453_, lean_object* v_x_3454_){
_start:
{
lean_object* v_zero_3455_; uint8_t v_isZero_3456_; 
v_zero_3455_ = lean_unsigned_to_nat(0u);
v_isZero_3456_ = lean_nat_dec_eq(v_x_3453_, v_zero_3455_);
if (v_isZero_3456_ == 1)
{
lean_dec_ref(v_lctx_3450_);
return v_x_3454_;
}
else
{
lean_object* v_one_3457_; lean_object* v_n_3458_; lean_object* v_n_3460_; lean_object* v_ty_3461_; uint8_t v_bi_3462_; lean_object* v_x_3466_; lean_object* v___x_3467_; 
v_one_3457_ = lean_unsigned_to_nat(1u);
v_n_3458_ = lean_nat_sub(v_x_3453_, v_one_3457_);
v_x_3466_ = lean_array_fget_borrowed(v_xs_3449_, v_n_3458_);
lean_inc_ref(v_lctx_3450_);
v___x_3467_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3450_, v_x_3466_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec_ref(v_x_3454_);
v___x_3468_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3469_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3468_);
v___x_3470_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3449_, v_lctx_3450_, v_usedLetOnly_3451_, v_generalizeNondepLet_3452_, v_n_3458_, v___x_3469_);
return v___x_3470_;
}
else
{
lean_object* v_val_3471_; 
v_val_3471_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_val_3471_);
lean_dec_ref_known(v___x_3467_, 1);
if (lean_obj_tag(v_val_3471_) == 0)
{
lean_object* v_userName_3472_; lean_object* v_type_3473_; uint8_t v_bi_3474_; 
v_userName_3472_ = lean_ctor_get(v_val_3471_, 2);
lean_inc(v_userName_3472_);
v_type_3473_ = lean_ctor_get(v_val_3471_, 3);
lean_inc_ref(v_type_3473_);
v_bi_3474_ = lean_ctor_get_uint8(v_val_3471_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3471_, 4);
v_n_3460_ = v_userName_3472_;
v_ty_3461_ = v_type_3473_;
v_bi_3462_ = v_bi_3474_;
goto v___jp_3459_;
}
else
{
lean_object* v_userName_3475_; lean_object* v_type_3476_; lean_object* v_value_3477_; uint8_t v_nondep_3478_; uint8_t v___y_3485_; 
v_userName_3475_ = lean_ctor_get(v_val_3471_, 2);
lean_inc(v_userName_3475_);
v_type_3476_ = lean_ctor_get(v_val_3471_, 3);
lean_inc_ref(v_type_3476_);
v_value_3477_ = lean_ctor_get(v_val_3471_, 4);
lean_inc_ref(v_value_3477_);
v_nondep_3478_ = lean_ctor_get_uint8(v_val_3471_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3471_, 5);
if (v_nondep_3478_ == 0)
{
v___y_3485_ = v_nondep_3478_;
goto v___jp_3484_;
}
else
{
if (v_generalizeNondepLet_3452_ == 0)
{
v___y_3485_ = v_generalizeNondepLet_3452_;
goto v___jp_3484_;
}
else
{
uint8_t v___x_3489_; 
lean_dec_ref(v_value_3477_);
v___x_3489_ = 0;
v_n_3460_ = v_userName_3475_;
v_ty_3461_ = v_type_3476_;
v_bi_3462_ = v___x_3489_;
goto v___jp_3459_;
}
}
v___jp_3479_:
{
lean_object* v_ty_3480_; lean_object* v_val_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_ty_3480_ = lean_expr_abstract_range(v_type_3476_, v_n_3458_, v_xs_3449_);
lean_dec_ref(v_type_3476_);
v_val_3481_ = lean_expr_abstract_range(v_value_3477_, v_n_3458_, v_xs_3449_);
lean_dec_ref(v_value_3477_);
v___x_3482_ = l_Lean_Expr_letE___override(v_userName_3475_, v_ty_3480_, v_val_3481_, v_x_3454_, v_nondep_3478_);
v___x_3483_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3449_, v_lctx_3450_, v_usedLetOnly_3451_, v_generalizeNondepLet_3452_, v_n_3458_, v___x_3482_);
return v___x_3483_;
}
v___jp_3484_:
{
if (v_usedLetOnly_3451_ == 0)
{
goto v___jp_3479_;
}
else
{
if (v___y_3485_ == 0)
{
uint8_t v___x_3486_; 
v___x_3486_ = lean_expr_has_loose_bvar(v_x_3454_, v_zero_3455_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v_value_3477_);
lean_dec_ref(v_type_3476_);
lean_dec(v_userName_3475_);
v___x_3487_ = lean_expr_lower_loose_bvars(v_x_3454_, v_one_3457_, v_one_3457_);
lean_dec_ref(v_x_3454_);
v___x_3488_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3449_, v_lctx_3450_, v_usedLetOnly_3451_, v_generalizeNondepLet_3452_, v_n_3458_, v___x_3487_);
return v___x_3488_;
}
else
{
goto v___jp_3479_;
}
}
else
{
goto v___jp_3479_;
}
}
}
}
}
v___jp_3459_:
{
lean_object* v_ty_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v_ty_3463_ = lean_expr_abstract_range(v_ty_3461_, v_n_3458_, v_xs_3449_);
lean_dec_ref(v_ty_3461_);
v___x_3464_ = l_Lean_mkLambda(v_n_3460_, v_bi_3462_, v_ty_3463_, v_x_3454_);
v___x_3465_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3449_, v_lctx_3450_, v_usedLetOnly_3451_, v_generalizeNondepLet_3452_, v_n_3458_, v___x_3464_);
return v___x_3465_;
}
}
}
}
LEAN_EXPORT void l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3449_ = stack[0].m_obj;
lean_object* v_lctx_3450_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3451_ = stack[2].m_num;
uint8_t v_generalizeNondepLet_3452_ = stack[3].m_num;
lean_object* v_x_3453_ = stack[4].m_obj;
lean_object* v_x_3454_ = stack[5].m_obj;
lean_object* v_res_3490_;
v_res_3490_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3449_, v_lctx_3450_, v_usedLetOnly_3451_, v_generalizeNondepLet_3452_, v_x_3453_, v_x_3454_);
stack->m_obj
 = v_res_3490_;
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3491_, lean_object* v_lctx_3492_, lean_object* v_usedLetOnly_3493_, lean_object* v_generalizeNondepLet_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
uint8_t v_usedLetOnly_boxed_3497_; uint8_t v_generalizeNondepLet_boxed_3498_; lean_object* v_res_3499_; 
v_usedLetOnly_boxed_3497_ = lean_unbox(v_usedLetOnly_3493_);
v_generalizeNondepLet_boxed_3498_ = lean_unbox(v_generalizeNondepLet_3494_);
v_res_3499_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3491_, v_lctx_3492_, v_usedLetOnly_boxed_3497_, v_generalizeNondepLet_boxed_3498_, v_x_3495_, v_x_3496_);
lean_dec(v_x_3495_);
lean_dec_ref(v_xs_3491_);
return v_res_3499_;
}
}
lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3500_, lean_object* v_xs_3501_, lean_object* v_b_3502_, uint8_t v_usedLetOnly_3503_, uint8_t v_generalizeNondepLet_3504_){
_start:
{
lean_object* v_b_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v_b_3505_ = lean_expr_abstract(v_b_3502_, v_xs_3501_);
v___x_3506_ = lean_array_get_size(v_xs_3501_);
v___x_3507_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3501_, v_lctx_3500_, v_usedLetOnly_3503_, v_generalizeNondepLet_3504_, v___x_3506_, v_b_3505_);
return v___x_3507_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_mkLambda_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_3500_ = stack[0].m_obj;
lean_object* v_xs_3501_ = stack[1].m_obj;
lean_object* v_b_3502_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3503_ = stack[3].m_num;
uint8_t v_generalizeNondepLet_3504_ = stack[4].m_num;
lean_object* v_res_3508_;
v_res_3508_ = l_Lean_LocalContext_mkLambda(v_lctx_3500_, v_xs_3501_, v_b_3502_, v_usedLetOnly_3503_, v_generalizeNondepLet_3504_);
stack->m_obj
 = v_res_3508_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3509_, lean_object* v_xs_3510_, lean_object* v_b_3511_, lean_object* v_usedLetOnly_3512_, lean_object* v_generalizeNondepLet_3513_){
_start:
{
uint8_t v_usedLetOnly_boxed_3514_; uint8_t v_generalizeNondepLet_boxed_3515_; lean_object* v_res_3516_; 
v_usedLetOnly_boxed_3514_ = lean_unbox(v_usedLetOnly_3512_);
v_generalizeNondepLet_boxed_3515_ = lean_unbox(v_generalizeNondepLet_3513_);
v_res_3516_ = l_Lean_LocalContext_mkLambda(v_lctx_3509_, v_xs_3510_, v_b_3511_, v_usedLetOnly_boxed_3514_, v_generalizeNondepLet_boxed_3515_);
lean_dec_ref(v_b_3511_);
lean_dec_ref(v_xs_3510_);
return v_res_3516_;
}
}
lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3517_, lean_object* v_lctx_3518_, uint8_t v_usedLetOnly_3519_, uint8_t v_generalizeNondepLet_3520_, lean_object* v_x_3521_, lean_object* v_x_3522_){
_start:
{
lean_object* v_zero_3523_; uint8_t v_isZero_3524_; 
v_zero_3523_ = lean_unsigned_to_nat(0u);
v_isZero_3524_ = lean_nat_dec_eq(v_x_3521_, v_zero_3523_);
if (v_isZero_3524_ == 1)
{
lean_dec(v_x_3521_);
lean_dec_ref(v_lctx_3518_);
return v_x_3522_;
}
else
{
lean_object* v_one_3525_; lean_object* v_n_3526_; lean_object* v_n_3528_; lean_object* v_ty_3529_; uint8_t v_bi_3530_; lean_object* v_x_3534_; lean_object* v___x_3535_; 
v_one_3525_ = lean_unsigned_to_nat(1u);
v_n_3526_ = lean_nat_sub(v_x_3521_, v_one_3525_);
lean_dec(v_x_3521_);
v_x_3534_ = lean_array_fget_borrowed(v_xs_3517_, v_n_3526_);
lean_inc_ref(v_lctx_3518_);
v___x_3535_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3518_, v_x_3534_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec_ref(v_x_3522_);
v___x_3536_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3537_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3536_);
v_x_3521_ = v_n_3526_;
v_x_3522_ = v___x_3537_;
goto _start;
}
else
{
lean_object* v_val_3539_; 
v_val_3539_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_val_3539_);
lean_dec_ref_known(v___x_3535_, 1);
if (lean_obj_tag(v_val_3539_) == 0)
{
lean_object* v_userName_3540_; lean_object* v_type_3541_; uint8_t v_bi_3542_; 
v_userName_3540_ = lean_ctor_get(v_val_3539_, 2);
lean_inc(v_userName_3540_);
v_type_3541_ = lean_ctor_get(v_val_3539_, 3);
lean_inc_ref(v_type_3541_);
v_bi_3542_ = lean_ctor_get_uint8(v_val_3539_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3539_, 4);
v_n_3528_ = v_userName_3540_;
v_ty_3529_ = v_type_3541_;
v_bi_3530_ = v_bi_3542_;
goto v___jp_3527_;
}
else
{
lean_object* v_userName_3543_; lean_object* v_type_3544_; lean_object* v_value_3545_; uint8_t v_nondep_3546_; uint8_t v___y_3553_; 
v_userName_3543_ = lean_ctor_get(v_val_3539_, 2);
lean_inc(v_userName_3543_);
v_type_3544_ = lean_ctor_get(v_val_3539_, 3);
lean_inc_ref(v_type_3544_);
v_value_3545_ = lean_ctor_get(v_val_3539_, 4);
lean_inc_ref(v_value_3545_);
v_nondep_3546_ = lean_ctor_get_uint8(v_val_3539_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3539_, 5);
if (v_nondep_3546_ == 0)
{
v___y_3553_ = v_nondep_3546_;
goto v___jp_3552_;
}
else
{
if (v_generalizeNondepLet_3520_ == 0)
{
v___y_3553_ = v_generalizeNondepLet_3520_;
goto v___jp_3552_;
}
else
{
uint8_t v___x_3557_; 
lean_dec_ref(v_value_3545_);
v___x_3557_ = 0;
v_n_3528_ = v_userName_3543_;
v_ty_3529_ = v_type_3544_;
v_bi_3530_ = v___x_3557_;
goto v___jp_3527_;
}
}
v___jp_3547_:
{
lean_object* v_ty_3548_; lean_object* v_val_3549_; lean_object* v___x_3550_; 
v_ty_3548_ = lean_expr_abstract_range(v_type_3544_, v_n_3526_, v_xs_3517_);
lean_dec_ref(v_type_3544_);
v_val_3549_ = lean_expr_abstract_range(v_value_3545_, v_n_3526_, v_xs_3517_);
lean_dec_ref(v_value_3545_);
v___x_3550_ = l_Lean_Expr_letE___override(v_userName_3543_, v_ty_3548_, v_val_3549_, v_x_3522_, v_nondep_3546_);
v_x_3521_ = v_n_3526_;
v_x_3522_ = v___x_3550_;
goto _start;
}
v___jp_3552_:
{
if (v_usedLetOnly_3519_ == 0)
{
goto v___jp_3547_;
}
else
{
if (v___y_3553_ == 0)
{
uint8_t v___x_3554_; 
v___x_3554_ = lean_expr_has_loose_bvar(v_x_3522_, v_zero_3523_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
lean_dec_ref(v_value_3545_);
lean_dec_ref(v_type_3544_);
lean_dec(v_userName_3543_);
v___x_3555_ = lean_expr_lower_loose_bvars(v_x_3522_, v_one_3525_, v_one_3525_);
lean_dec_ref(v_x_3522_);
v_x_3521_ = v_n_3526_;
v_x_3522_ = v___x_3555_;
goto _start;
}
else
{
goto v___jp_3547_;
}
}
else
{
goto v___jp_3547_;
}
}
}
}
}
v___jp_3527_:
{
lean_object* v_ty_3531_; lean_object* v___x_3532_; 
v_ty_3531_ = lean_expr_abstract_range(v_ty_3529_, v_n_3526_, v_xs_3517_);
lean_dec_ref(v_ty_3529_);
v___x_3532_ = l_Lean_mkForall(v_n_3528_, v_bi_3530_, v_ty_3531_, v_x_3522_);
v_x_3521_ = v_n_3526_;
v_x_3522_ = v___x_3532_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3517_ = stack[0].m_obj;
lean_object* v_lctx_3518_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3519_ = stack[2].m_num;
uint8_t v_generalizeNondepLet_3520_ = stack[3].m_num;
lean_object* v_x_3521_ = stack[4].m_obj;
lean_object* v_x_3522_ = stack[5].m_obj;
lean_object* v_res_3558_;
v_res_3558_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3517_, v_lctx_3518_, v_usedLetOnly_3519_, v_generalizeNondepLet_3520_, v_x_3521_, v_x_3522_);
stack->m_obj
 = v_res_3558_;
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3559_, lean_object* v_lctx_3560_, lean_object* v_usedLetOnly_3561_, lean_object* v_generalizeNondepLet_3562_, lean_object* v_x_3563_, lean_object* v_x_3564_){
_start:
{
uint8_t v_usedLetOnly_boxed_3565_; uint8_t v_generalizeNondepLet_boxed_3566_; lean_object* v_res_3567_; 
v_usedLetOnly_boxed_3565_ = lean_unbox(v_usedLetOnly_3561_);
v_generalizeNondepLet_boxed_3566_ = lean_unbox(v_generalizeNondepLet_3562_);
v_res_3567_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3559_, v_lctx_3560_, v_usedLetOnly_boxed_3565_, v_generalizeNondepLet_boxed_3566_, v_x_3563_, v_x_3564_);
lean_dec_ref(v_xs_3559_);
return v_res_3567_;
}
}
lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3568_, lean_object* v_lctx_3569_, uint8_t v_usedLetOnly_3570_, uint8_t v_generalizeNondepLet_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_){
_start:
{
lean_object* v_zero_3574_; uint8_t v_isZero_3575_; 
v_zero_3574_ = lean_unsigned_to_nat(0u);
v_isZero_3575_ = lean_nat_dec_eq(v_x_3572_, v_zero_3574_);
if (v_isZero_3575_ == 1)
{
lean_dec_ref(v_lctx_3569_);
return v_x_3573_;
}
else
{
lean_object* v_one_3576_; lean_object* v_n_3577_; lean_object* v_n_3579_; lean_object* v_ty_3580_; uint8_t v_bi_3581_; lean_object* v_x_3585_; lean_object* v___x_3586_; 
v_one_3576_ = lean_unsigned_to_nat(1u);
v_n_3577_ = lean_nat_sub(v_x_3572_, v_one_3576_);
v_x_3585_ = lean_array_fget_borrowed(v_xs_3568_, v_n_3577_);
lean_inc_ref(v_lctx_3569_);
v___x_3586_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3569_, v_x_3585_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_dec_ref(v_x_3573_);
v___x_3587_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3588_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3587_);
v___x_3589_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3568_, v_lctx_3569_, v_usedLetOnly_3570_, v_generalizeNondepLet_3571_, v_n_3577_, v___x_3588_);
return v___x_3589_;
}
else
{
lean_object* v_val_3590_; 
v_val_3590_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_val_3590_);
lean_dec_ref_known(v___x_3586_, 1);
if (lean_obj_tag(v_val_3590_) == 0)
{
lean_object* v_userName_3591_; lean_object* v_type_3592_; uint8_t v_bi_3593_; 
v_userName_3591_ = lean_ctor_get(v_val_3590_, 2);
lean_inc(v_userName_3591_);
v_type_3592_ = lean_ctor_get(v_val_3590_, 3);
lean_inc_ref(v_type_3592_);
v_bi_3593_ = lean_ctor_get_uint8(v_val_3590_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3590_, 4);
v_n_3579_ = v_userName_3591_;
v_ty_3580_ = v_type_3592_;
v_bi_3581_ = v_bi_3593_;
goto v___jp_3578_;
}
else
{
lean_object* v_userName_3594_; lean_object* v_type_3595_; lean_object* v_value_3596_; uint8_t v_nondep_3597_; uint8_t v___y_3604_; 
v_userName_3594_ = lean_ctor_get(v_val_3590_, 2);
lean_inc(v_userName_3594_);
v_type_3595_ = lean_ctor_get(v_val_3590_, 3);
lean_inc_ref(v_type_3595_);
v_value_3596_ = lean_ctor_get(v_val_3590_, 4);
lean_inc_ref(v_value_3596_);
v_nondep_3597_ = lean_ctor_get_uint8(v_val_3590_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3590_, 5);
if (v_nondep_3597_ == 0)
{
v___y_3604_ = v_nondep_3597_;
goto v___jp_3603_;
}
else
{
if (v_generalizeNondepLet_3571_ == 0)
{
v___y_3604_ = v_generalizeNondepLet_3571_;
goto v___jp_3603_;
}
else
{
uint8_t v___x_3608_; 
lean_dec_ref(v_value_3596_);
v___x_3608_ = 0;
v_n_3579_ = v_userName_3594_;
v_ty_3580_ = v_type_3595_;
v_bi_3581_ = v___x_3608_;
goto v___jp_3578_;
}
}
v___jp_3598_:
{
lean_object* v_ty_3599_; lean_object* v_val_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_ty_3599_ = lean_expr_abstract_range(v_type_3595_, v_n_3577_, v_xs_3568_);
lean_dec_ref(v_type_3595_);
v_val_3600_ = lean_expr_abstract_range(v_value_3596_, v_n_3577_, v_xs_3568_);
lean_dec_ref(v_value_3596_);
v___x_3601_ = l_Lean_Expr_letE___override(v_userName_3594_, v_ty_3599_, v_val_3600_, v_x_3573_, v_nondep_3597_);
v___x_3602_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3568_, v_lctx_3569_, v_usedLetOnly_3570_, v_generalizeNondepLet_3571_, v_n_3577_, v___x_3601_);
return v___x_3602_;
}
v___jp_3603_:
{
if (v_usedLetOnly_3570_ == 0)
{
goto v___jp_3598_;
}
else
{
if (v___y_3604_ == 0)
{
uint8_t v___x_3605_; 
v___x_3605_ = lean_expr_has_loose_bvar(v_x_3573_, v_zero_3574_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
lean_dec_ref(v_value_3596_);
lean_dec_ref(v_type_3595_);
lean_dec(v_userName_3594_);
v___x_3606_ = lean_expr_lower_loose_bvars(v_x_3573_, v_one_3576_, v_one_3576_);
lean_dec_ref(v_x_3573_);
v___x_3607_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3568_, v_lctx_3569_, v_usedLetOnly_3570_, v_generalizeNondepLet_3571_, v_n_3577_, v___x_3606_);
return v___x_3607_;
}
else
{
goto v___jp_3598_;
}
}
else
{
goto v___jp_3598_;
}
}
}
}
}
v___jp_3578_:
{
lean_object* v_ty_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_ty_3582_ = lean_expr_abstract_range(v_ty_3580_, v_n_3577_, v_xs_3568_);
lean_dec_ref(v_ty_3580_);
v___x_3583_ = l_Lean_mkForall(v_n_3579_, v_bi_3581_, v_ty_3582_, v_x_3573_);
v___x_3584_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3568_, v_lctx_3569_, v_usedLetOnly_3570_, v_generalizeNondepLet_3571_, v_n_3577_, v___x_3583_);
return v___x_3584_;
}
}
}
}
LEAN_EXPORT void l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3568_ = stack[0].m_obj;
lean_object* v_lctx_3569_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3570_ = stack[2].m_num;
uint8_t v_generalizeNondepLet_3571_ = stack[3].m_num;
lean_object* v_x_3572_ = stack[4].m_obj;
lean_object* v_x_3573_ = stack[5].m_obj;
lean_object* v_res_3609_;
v_res_3609_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3568_, v_lctx_3569_, v_usedLetOnly_3570_, v_generalizeNondepLet_3571_, v_x_3572_, v_x_3573_);
stack->m_obj
 = v_res_3609_;
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3610_, lean_object* v_lctx_3611_, lean_object* v_usedLetOnly_3612_, lean_object* v_generalizeNondepLet_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
uint8_t v_usedLetOnly_boxed_3616_; uint8_t v_generalizeNondepLet_boxed_3617_; lean_object* v_res_3618_; 
v_usedLetOnly_boxed_3616_ = lean_unbox(v_usedLetOnly_3612_);
v_generalizeNondepLet_boxed_3617_ = lean_unbox(v_generalizeNondepLet_3613_);
v_res_3618_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3610_, v_lctx_3611_, v_usedLetOnly_boxed_3616_, v_generalizeNondepLet_boxed_3617_, v_x_3614_, v_x_3615_);
lean_dec(v_x_3614_);
lean_dec_ref(v_xs_3610_);
return v_res_3618_;
}
}
lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3619_, lean_object* v_xs_3620_, lean_object* v_b_3621_, uint8_t v_usedLetOnly_3622_, uint8_t v_generalizeNondepLet_3623_){
_start:
{
lean_object* v_b_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_b_3624_ = lean_expr_abstract(v_b_3621_, v_xs_3620_);
v___x_3625_ = lean_array_get_size(v_xs_3620_);
v___x_3626_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3620_, v_lctx_3619_, v_usedLetOnly_3622_, v_generalizeNondepLet_3623_, v___x_3625_, v_b_3624_);
return v___x_3626_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_mkForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_3619_ = stack[0].m_obj;
lean_object* v_xs_3620_ = stack[1].m_obj;
lean_object* v_b_3621_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3622_ = stack[3].m_num;
uint8_t v_generalizeNondepLet_3623_ = stack[4].m_num;
lean_object* v_res_3627_;
v_res_3627_ = l_Lean_LocalContext_mkForall(v_lctx_3619_, v_xs_3620_, v_b_3621_, v_usedLetOnly_3622_, v_generalizeNondepLet_3623_);
stack->m_obj
 = v_res_3627_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3628_, lean_object* v_xs_3629_, lean_object* v_b_3630_, lean_object* v_usedLetOnly_3631_, lean_object* v_generalizeNondepLet_3632_){
_start:
{
uint8_t v_usedLetOnly_boxed_3633_; uint8_t v_generalizeNondepLet_boxed_3634_; lean_object* v_res_3635_; 
v_usedLetOnly_boxed_3633_ = lean_unbox(v_usedLetOnly_3631_);
v_generalizeNondepLet_boxed_3634_ = lean_unbox(v_generalizeNondepLet_3632_);
v_res_3635_ = l_Lean_LocalContext_mkForall(v_lctx_3628_, v_xs_3629_, v_b_3630_, v_usedLetOnly_boxed_3633_, v_generalizeNondepLet_boxed_3634_);
lean_dec_ref(v_b_3630_);
lean_dec_ref(v_xs_3629_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3636_, lean_object* v_p_3637_, lean_object* v_d_3638_){
_start:
{
if (lean_obj_tag(v_d_3638_) == 0)
{
uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec(v_p_3637_);
v___x_3639_ = 0;
v___x_3640_ = lean_box(v___x_3639_);
v___x_3641_ = lean_apply_2(v_toPure_3636_, lean_box(0), v___x_3640_);
return v___x_3641_;
}
else
{
lean_object* v_val_3642_; lean_object* v___x_3643_; 
lean_dec(v_toPure_3636_);
v_val_3642_ = lean_ctor_get(v_d_3638_, 0);
lean_inc(v_val_3642_);
lean_dec_ref_known(v_d_3638_, 1);
v___x_3643_ = lean_apply_1(v_p_3637_, v_val_3642_);
return v___x_3643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3644_, lean_object* v_lctx_3645_, lean_object* v_p_3646_){
_start:
{
lean_object* v_toApplicative_3647_; lean_object* v_decls_3648_; lean_object* v_toPure_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; 
v_toApplicative_3647_ = lean_ctor_get(v_inst_3644_, 0);
v_decls_3648_ = lean_ctor_get(v_lctx_3645_, 1);
lean_inc_ref(v_decls_3648_);
lean_dec_ref(v_lctx_3645_);
v_toPure_3649_ = lean_ctor_get(v_toApplicative_3647_, 1);
lean_inc(v_toPure_3649_);
v___f_3650_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3650_, 0, v_toPure_3649_);
lean_closure_set(v___f_3650_, 1, v_p_3646_);
v___x_3651_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3644_, v_decls_3648_, v___f_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3652_, lean_object* v_inst_3653_, lean_object* v_lctx_3654_, lean_object* v_p_3655_){
_start:
{
lean_object* v_toApplicative_3656_; lean_object* v_decls_3657_; lean_object* v_toPure_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; 
v_toApplicative_3656_ = lean_ctor_get(v_inst_3653_, 0);
v_decls_3657_ = lean_ctor_get(v_lctx_3654_, 1);
lean_inc_ref(v_decls_3657_);
lean_dec_ref(v_lctx_3654_);
v_toPure_3658_ = lean_ctor_get(v_toApplicative_3656_, 1);
lean_inc(v_toPure_3658_);
v___f_3659_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3659_, 0, v_toPure_3658_);
lean_closure_set(v___f_3659_, 1, v_p_3655_);
v___x_3660_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3653_, v_decls_3657_, v___f_3659_);
return v___x_3660_;
}
}
lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3661_, uint8_t v_b_3662_){
_start:
{
if (v_b_3662_ == 0)
{
uint8_t v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = 1;
v___x_3664_ = lean_box(v___x_3663_);
v___x_3665_ = lean_apply_2(v_toPure_3661_, lean_box(0), v___x_3664_);
return v___x_3665_;
}
else
{
uint8_t v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = 0;
v___x_3667_ = lean_box(v___x_3666_);
v___x_3668_ = lean_apply_2(v_toPure_3661_, lean_box(0), v___x_3667_);
return v___x_3668_;
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_allM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3661_ = stack[0].m_obj;
uint8_t v_b_3662_ = stack[1].m_num;
lean_object* v_res_3669_;
v_res_3669_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3661_, v_b_3662_);
stack->m_obj
 = v_res_3669_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3670_, lean_object* v_b_3671_){
_start:
{
uint8_t v_b_boxed_3672_; lean_object* v_res_3673_; 
v_b_boxed_3672_ = lean_unbox(v_b_3671_);
v_res_3673_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3670_, v_b_boxed_3672_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3674_, lean_object* v_toBind_3675_, lean_object* v___f_3676_, lean_object* v_p_3677_, lean_object* v_v_3678_){
_start:
{
if (lean_obj_tag(v_v_3678_) == 0)
{
uint8_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec(v_p_3677_);
v___x_3679_ = 1;
v___x_3680_ = lean_box(v___x_3679_);
v___x_3681_ = lean_apply_2(v_toPure_3674_, lean_box(0), v___x_3680_);
v___x_3682_ = lean_apply_4(v_toBind_3675_, lean_box(0), lean_box(0), v___x_3681_, v___f_3676_);
return v___x_3682_;
}
else
{
lean_object* v_val_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_dec(v_toPure_3674_);
v_val_3683_ = lean_ctor_get(v_v_3678_, 0);
lean_inc(v_val_3683_);
lean_dec_ref_known(v_v_3678_, 1);
v___x_3684_ = lean_apply_1(v_p_3677_, v_val_3683_);
v___x_3685_ = lean_apply_4(v_toBind_3675_, lean_box(0), lean_box(0), v___x_3684_, v___f_3676_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3686_, lean_object* v_lctx_3687_, lean_object* v_p_3688_){
_start:
{
lean_object* v_toApplicative_3689_; lean_object* v_decls_3690_; lean_object* v_toBind_3691_; lean_object* v_toPure_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_toApplicative_3689_ = lean_ctor_get(v_inst_3686_, 0);
v_decls_3690_ = lean_ctor_get(v_lctx_3687_, 1);
lean_inc_ref(v_decls_3690_);
lean_dec_ref(v_lctx_3687_);
v_toBind_3691_ = lean_ctor_get(v_inst_3686_, 1);
lean_inc_n(v_toBind_3691_, 2);
v_toPure_3692_ = lean_ctor_get(v_toApplicative_3689_, 1);
lean_inc_n(v_toPure_3692_, 2);
v___f_3693_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3693_, 0, v_toPure_3692_);
lean_inc_ref(v___f_3693_);
v___f_3694_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3694_, 0, v_toPure_3692_);
lean_closure_set(v___f_3694_, 1, v_toBind_3691_);
lean_closure_set(v___f_3694_, 2, v___f_3693_);
lean_closure_set(v___f_3694_, 3, v_p_3688_);
v___x_3695_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3686_, v_decls_3690_, v___f_3694_);
v___x_3696_ = lean_apply_4(v_toBind_3691_, lean_box(0), lean_box(0), v___x_3695_, v___f_3693_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3697_, lean_object* v_inst_3698_, lean_object* v_lctx_3699_, lean_object* v_p_3700_){
_start:
{
lean_object* v_toApplicative_3701_; lean_object* v_decls_3702_; lean_object* v_toBind_3703_; lean_object* v_toPure_3704_; lean_object* v___f_3705_; lean_object* v___f_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_toApplicative_3701_ = lean_ctor_get(v_inst_3698_, 0);
v_decls_3702_ = lean_ctor_get(v_lctx_3699_, 1);
lean_inc_ref(v_decls_3702_);
lean_dec_ref(v_lctx_3699_);
v_toBind_3703_ = lean_ctor_get(v_inst_3698_, 1);
lean_inc_n(v_toBind_3703_, 2);
v_toPure_3704_ = lean_ctor_get(v_toApplicative_3701_, 1);
lean_inc_n(v_toPure_3704_, 2);
v___f_3705_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3705_, 0, v_toPure_3704_);
lean_inc_ref(v___f_3705_);
v___f_3706_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3706_, 0, v_toPure_3704_);
lean_closure_set(v___f_3706_, 1, v_toBind_3703_);
lean_closure_set(v___f_3706_, 2, v___f_3705_);
lean_closure_set(v___f_3706_, 3, v_p_3700_);
v___x_3707_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3698_, v_decls_3702_, v___f_3706_);
v___x_3708_ = lean_apply_4(v_toBind_3703_, lean_box(0), lean_box(0), v___x_3707_, v___f_3705_);
return v___x_3708_;
}
}
uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3709_, lean_object* v_d_3710_){
_start:
{
if (lean_obj_tag(v_d_3710_) == 0)
{
uint8_t v___x_3711_; 
lean_dec_ref(v_p_3709_);
v___x_3711_ = 0;
return v___x_3711_;
}
else
{
lean_object* v_val_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v_val_3712_ = lean_ctor_get(v_d_3710_, 0);
lean_inc(v_val_3712_);
lean_dec_ref_known(v_d_3710_, 1);
v___x_3713_ = lean_apply_1(v_p_3709_, v_val_3712_);
v___x_3714_ = lean_unbox(v___x_3713_);
return v___x_3714_;
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_any___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3709_ = stack[0].m_obj;
lean_object* v_d_3710_ = stack[1].m_obj;
uint8_t v_res_3715_;
v_res_3715_ = l_Lean_LocalContext_any___lam__0(v_p_3709_, v_d_3710_);
stack->m_num = v_res_3715_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3716_, lean_object* v_d_3717_){
_start:
{
uint8_t v_res_3718_; lean_object* v_r_3719_; 
v_res_3718_ = l_Lean_LocalContext_any___lam__0(v_p_3716_, v_d_3717_);
v_r_3719_ = lean_box(v_res_3718_);
return v_r_3719_;
}
}
uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3720_, lean_object* v_p_3721_){
_start:
{
lean_object* v___x_3722_; lean_object* v_decls_3723_; lean_object* v___f_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; 
v___x_3722_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3723_ = lean_ctor_get(v_lctx_3720_, 1);
lean_inc_ref(v_decls_3723_);
lean_dec_ref(v_lctx_3720_);
v___f_3724_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3724_, 0, v_p_3721_);
v___x_3725_ = l_Lean_PersistentArray_anyM___redArg(v___x_3722_, v_decls_3723_, v___f_3724_);
v___x_3726_ = lean_unbox(v___x_3725_);
lean_dec(v___x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_3720_ = stack[0].m_obj;
lean_object* v_p_3721_ = stack[1].m_obj;
uint8_t v_res_3727_;
v_res_3727_ = l_Lean_LocalContext_any(v_lctx_3720_, v_p_3721_);
stack->m_num = v_res_3727_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3728_, lean_object* v_p_3729_){
_start:
{
uint8_t v_res_3730_; lean_object* v_r_3731_; 
v_res_3730_ = l_Lean_LocalContext_any(v_lctx_3728_, v_p_3729_);
v_r_3731_ = lean_box(v_res_3730_);
return v_r_3731_;
}
}
uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3732_, lean_object* v_v_3733_){
_start:
{
if (lean_obj_tag(v_v_3733_) == 0)
{
uint8_t v___x_3734_; 
lean_dec_ref(v_p_3732_);
v___x_3734_ = 0;
return v___x_3734_;
}
else
{
lean_object* v_val_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; 
v_val_3735_ = lean_ctor_get(v_v_3733_, 0);
lean_inc(v_val_3735_);
lean_dec_ref_known(v_v_3733_, 1);
v___x_3736_ = lean_apply_1(v_p_3732_, v_val_3735_);
v___x_3737_ = lean_unbox(v___x_3736_);
if (v___x_3737_ == 0)
{
uint8_t v___x_3738_; 
v___x_3738_ = 1;
return v___x_3738_;
}
else
{
uint8_t v___x_3739_; 
v___x_3739_ = 0;
return v___x_3739_;
}
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_all___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3732_ = stack[0].m_obj;
lean_object* v_v_3733_ = stack[1].m_obj;
uint8_t v_res_3740_;
v_res_3740_ = l_Lean_LocalContext_all___lam__0(v_p_3732_, v_v_3733_);
stack->m_num = v_res_3740_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3741_, lean_object* v_v_3742_){
_start:
{
uint8_t v_res_3743_; lean_object* v_r_3744_; 
v_res_3743_ = l_Lean_LocalContext_all___lam__0(v_p_3741_, v_v_3742_);
v_r_3744_ = lean_box(v_res_3743_);
return v_r_3744_;
}
}
uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3745_, lean_object* v_p_3746_){
_start:
{
lean_object* v___x_3747_; lean_object* v_decls_3748_; lean_object* v___f_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3747_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3748_ = lean_ctor_get(v_lctx_3745_, 1);
lean_inc_ref(v_decls_3748_);
lean_dec_ref(v_lctx_3745_);
v___f_3749_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3749_, 0, v_p_3746_);
v___x_3750_ = l_Lean_PersistentArray_anyM___redArg(v___x_3747_, v_decls_3748_, v___f_3749_);
v___x_3751_ = lean_unbox(v___x_3750_);
lean_dec(v___x_3750_);
if (v___x_3751_ == 0)
{
uint8_t v___x_3752_; 
v___x_3752_ = 1;
return v___x_3752_;
}
else
{
uint8_t v___x_3753_; 
v___x_3753_ = 0;
return v___x_3753_;
}
}
}
LEAN_EXPORT void l_Lean_LocalContext_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_3745_ = stack[0].m_obj;
lean_object* v_p_3746_ = stack[1].m_obj;
uint8_t v_res_3754_;
v_res_3754_ = l_Lean_LocalContext_all(v_lctx_3745_, v_p_3746_);
stack->m_num = v_res_3754_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3755_, lean_object* v_p_3756_){
_start:
{
uint8_t v_res_3757_; lean_object* v_r_3758_; 
v_res_3757_ = l_Lean_LocalContext_all(v_lctx_3755_, v_p_3756_);
v_r_3758_ = lean_box(v_res_3757_);
return v_r_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3759_, lean_object* v_a_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_zero_3763_; uint8_t v_isZero_3764_; 
v_zero_3763_ = lean_unsigned_to_nat(0u);
v_isZero_3764_ = lean_nat_dec_eq(v_i_3759_, v_zero_3763_);
if (v_isZero_3764_ == 1)
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_dec(v_i_3759_);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v_a_3760_);
lean_ctor_set(v___x_3765_, 1, v___y_3761_);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v___y_3762_);
return v___x_3766_;
}
else
{
lean_object* v_decls_3767_; lean_object* v_size_3768_; lean_object* v___x_3769_; lean_object* v_one_3770_; lean_object* v_n_3771_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3788_; lean_object* v___y_3789_; uint8_t v___y_3790_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3800_; uint8_t v___x_3804_; 
v_decls_3767_ = lean_ctor_get(v_a_3760_, 1);
v_size_3768_ = lean_ctor_get(v_decls_3767_, 2);
v___x_3769_ = lean_box(0);
v_one_3770_ = lean_unsigned_to_nat(1u);
v_n_3771_ = lean_nat_sub(v_i_3759_, v_one_3770_);
lean_dec(v_i_3759_);
v___x_3804_ = lean_nat_dec_lt(v_n_3771_, v_size_3768_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; 
v___x_3805_ = l_outOfBounds___redArg(v___x_3769_);
v___y_3800_ = v___x_3805_;
goto v___jp_3799_;
}
else
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3769_, v_decls_3767_, v_n_3771_);
v___y_3800_ = v___x_3806_;
goto v___jp_3799_;
}
v___jp_3772_:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_LocalContext_setUserName(v_a_3760_, v___y_3776_, v___y_3773_);
v_i_3759_ = v_n_3771_;
v_a_3760_ = v___x_3777_;
v___y_3761_ = v___y_3774_;
v___y_3762_ = v___y_3775_;
goto _start;
}
v___jp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v_fst_3784_; lean_object* v_snd_3785_; lean_object* v_fvarId_3786_; 
lean_inc(v___y_3781_);
v___x_3782_ = l_Lean_NameSet_insert(v___y_3761_, v___y_3781_);
v___x_3783_ = l_Lean_sanitizeName(v___y_3781_, v___y_3762_);
v_fst_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_fst_3784_);
v_snd_3785_ = lean_ctor_get(v___x_3783_, 1);
lean_inc(v_snd_3785_);
lean_dec_ref(v___x_3783_);
v_fvarId_3786_ = lean_ctor_get(v___y_3780_, 1);
lean_inc(v_fvarId_3786_);
lean_dec_ref(v___y_3780_);
v___y_3773_ = v_fst_3784_;
v___y_3774_ = v___x_3782_;
v___y_3775_ = v_snd_3785_;
v___y_3776_ = v_fvarId_3786_;
goto v___jp_3772_;
}
v___jp_3787_:
{
if (v___y_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_dec_ref(v___y_3788_);
v___x_3791_ = l_Lean_NameSet_insert(v___y_3761_, v___y_3789_);
v_i_3759_ = v_n_3771_;
v___y_3761_ = v___x_3791_;
goto _start;
}
else
{
v___y_3780_ = v___y_3788_;
v___y_3781_ = v___y_3789_;
goto v___jp_3779_;
}
}
v___jp_3793_:
{
uint8_t v___x_3796_; 
v___x_3796_ = l_Lean_Name_hasMacroScopes(v___y_3795_);
if (v___x_3796_ == 0)
{
lean_object* v_userName_3797_; uint8_t v___x_3798_; 
v_userName_3797_ = lean_ctor_get(v___y_3794_, 2);
v___x_3798_ = l_Lean_NameSet_contains(v___y_3761_, v_userName_3797_);
v___y_3788_ = v___y_3794_;
v___y_3789_ = v___y_3795_;
v___y_3790_ = v___x_3798_;
goto v___jp_3787_;
}
else
{
v___y_3780_ = v___y_3794_;
v___y_3781_ = v___y_3795_;
goto v___jp_3779_;
}
}
v___jp_3799_:
{
if (lean_obj_tag(v___y_3800_) == 0)
{
v_i_3759_ = v_n_3771_;
goto _start;
}
else
{
lean_object* v_val_3802_; lean_object* v_userName_3803_; 
v_val_3802_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_val_3802_);
lean_dec_ref_known(v___y_3800_, 1);
v_userName_3803_ = lean_ctor_get(v_val_3802_, 2);
lean_inc(v_userName_3803_);
v___y_3794_ = v_val_3802_;
v___y_3795_ = v_userName_3803_;
goto v___jp_3793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3807_, lean_object* v_a_3808_){
_start:
{
lean_object* v_options_3809_; uint8_t v___x_3810_; 
v_options_3809_ = lean_ctor_get(v_a_3808_, 0);
v___x_3810_ = l_Lean_getSanitizeNames(v_options_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v_lctx_3807_);
lean_ctor_set(v___x_3811_, 1, v_a_3808_);
return v___x_3811_;
}
else
{
lean_object* v_decls_3812_; lean_object* v_size_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v_fst_3816_; lean_object* v_snd_3817_; lean_object* v_fst_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
v_decls_3812_ = lean_ctor_get(v_lctx_3807_, 1);
v_size_3813_ = lean_ctor_get(v_decls_3812_, 2);
lean_inc(v_size_3813_);
v___x_3814_ = l_Lean_NameSet_empty;
v___x_3815_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3813_, v_lctx_3807_, v___x_3814_, v_a_3808_);
v_fst_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_fst_3816_);
v_snd_3817_ = lean_ctor_get(v___x_3815_, 1);
lean_inc(v_snd_3817_);
lean_dec_ref(v___x_3815_);
v_fst_3818_ = lean_ctor_get(v_fst_3816_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_fst_3816_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; 
v_unused_3826_ = lean_ctor_get(v_fst_3816_, 1);
lean_dec(v_unused_3826_);
v___x_3820_ = v_fst_3816_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_fst_3818_);
lean_dec(v_fst_3816_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 1, v_snd_3817_);
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_fst_3818_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_snd_3817_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3827_, lean_object* v_i_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3828_, v_a_3830_, v___y_3831_, v___y_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3834_, lean_object* v_i_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3834_, v_i_3835_, v_a_3836_, v_a_3837_, v___y_3838_, v___y_3839_);
lean_dec(v_n_3834_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3841_, lean_object* v_fvarId_3842_){
_start:
{
lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___x_3855_; 
lean_inc_ref(v_lctx_3841_);
v___x_3855_ = lean_local_ctx_find(v_lctx_3841_, v_fvarId_3842_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; 
lean_dec_ref(v_lctx_3841_);
v___x_3856_ = lean_box(0);
return v___x_3856_;
}
else
{
lean_object* v_val_3857_; lean_object* v___y_3859_; lean_object* v_userName_3864_; 
v_val_3857_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v___x_3855_, 1);
v_userName_3864_ = lean_ctor_get(v_val_3857_, 2);
lean_inc(v_userName_3864_);
v___y_3859_ = v_userName_3864_;
goto v___jp_3858_;
v___jp_3858_:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3841_, v___y_3859_);
lean_dec_ref(v_lctx_3841_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v___x_3861_; 
lean_dec(v___y_3859_);
lean_dec(v_val_3857_);
v___x_3861_ = lean_box(0);
return v___x_3861_;
}
else
{
lean_object* v_val_3862_; lean_object* v_fvarId_3863_; 
v_val_3862_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_val_3862_);
lean_dec_ref_known(v___x_3860_, 1);
v_fvarId_3863_ = lean_ctor_get(v_val_3857_, 1);
lean_inc(v_fvarId_3863_);
lean_dec(v_val_3857_);
v___y_3851_ = v___y_3859_;
v___y_3852_ = v_val_3862_;
v___y_3853_ = v_fvarId_3863_;
goto v___jp_3850_;
}
}
}
v___jp_3843_:
{
uint8_t v___x_3847_; 
v___x_3847_ = l_Lean_instBEqFVarId_beq(v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec(v___y_3845_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
lean_dec(v___y_3844_);
v___x_3848_ = lean_box(0);
return v___x_3848_;
}
else
{
lean_object* v___x_3849_; 
v___x_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___y_3844_);
return v___x_3849_;
}
}
v___jp_3850_:
{
lean_object* v_fvarId_3854_; 
v_fvarId_3854_ = lean_ctor_get(v___y_3852_, 1);
lean_inc(v_fvarId_3854_);
lean_dec_ref(v___y_3852_);
v___y_3844_ = v___y_3851_;
v___y_3845_ = v___y_3853_;
v___y_3846_ = v_fvarId_3854_;
goto v___jp_3843_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3865_, size_t v_i_3866_, lean_object* v_bs_3867_){
_start:
{
uint8_t v___x_3868_; 
v___x_3868_ = lean_usize_dec_lt(v_i_3866_, v_sz_3865_);
if (v___x_3868_ == 0)
{
return v_bs_3867_;
}
else
{
lean_object* v_v_3869_; lean_object* v_snd_3870_; lean_object* v___x_3871_; lean_object* v_bs_x27_3872_; size_t v___x_3873_; size_t v___x_3874_; lean_object* v___x_3875_; 
v_v_3869_ = lean_array_uget_borrowed(v_bs_3867_, v_i_3866_);
v_snd_3870_ = lean_ctor_get(v_v_3869_, 1);
lean_inc(v_snd_3870_);
v___x_3871_ = lean_unsigned_to_nat(0u);
v_bs_x27_3872_ = lean_array_uset(v_bs_3867_, v_i_3866_, v___x_3871_);
v___x_3873_ = ((size_t)1ULL);
v___x_3874_ = lean_usize_add(v_i_3866_, v___x_3873_);
v___x_3875_ = lean_array_uset(v_bs_x27_3872_, v_i_3866_, v_snd_3870_);
v_i_3866_ = v___x_3874_;
v_bs_3867_ = v___x_3875_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3865_ = stack[0].m_num;
size_t v_i_3866_ = stack[1].m_num;
lean_object* v_bs_3867_ = stack[2].m_obj;
lean_object* v_res_3877_;
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3865_, v_i_3866_, v_bs_3867_);
stack->m_obj
 = v_res_3877_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3878_, lean_object* v_i_3879_, lean_object* v_bs_3880_){
_start:
{
size_t v_sz_boxed_3881_; size_t v_i_boxed_3882_; lean_object* v_res_3883_; 
v_sz_boxed_3881_ = lean_unbox_usize(v_sz_3878_);
lean_dec(v_sz_3878_);
v_i_boxed_3882_ = lean_unbox_usize(v_i_3879_);
lean_dec(v_i_3879_);
v_res_3883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3881_, v_i_boxed_3882_, v_bs_3880_);
return v_res_3883_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3884_, size_t v_sz_3885_, size_t v_i_3886_, lean_object* v_bs_3887_){
_start:
{
uint8_t v___x_3888_; 
v___x_3888_ = lean_usize_dec_lt(v_i_3886_, v_sz_3885_);
if (v___x_3888_ == 0)
{
return v_bs_3887_;
}
else
{
lean_object* v_fvarIdToDecl_3889_; lean_object* v_v_3890_; lean_object* v___x_3891_; lean_object* v_bs_x27_3892_; lean_object* v___y_3894_; lean_object* v___x_3899_; 
v_fvarIdToDecl_3889_ = lean_ctor_get(v_lctx_3884_, 0);
v_v_3890_ = lean_array_uget(v_bs_3887_, v_i_3886_);
v___x_3891_ = lean_unsigned_to_nat(0u);
v_bs_x27_3892_ = lean_array_uset(v_bs_3887_, v_i_3886_, v___x_3891_);
v___x_3899_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3889_, v_v_3890_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3891_);
lean_ctor_set(v___x_3900_, 1, v_v_3890_);
v___y_3894_ = v___x_3900_;
goto v___jp_3893_;
}
else
{
lean_object* v_val_3901_; lean_object* v_index_3902_; lean_object* v___x_3903_; 
v_val_3901_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_val_3901_);
lean_dec_ref_known(v___x_3899_, 1);
v_index_3902_ = lean_ctor_get(v_val_3901_, 0);
lean_inc(v_index_3902_);
lean_dec(v_val_3901_);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v_index_3902_);
lean_ctor_set(v___x_3903_, 1, v_v_3890_);
v___y_3894_ = v___x_3903_;
goto v___jp_3893_;
}
v___jp_3893_:
{
size_t v___x_3895_; size_t v___x_3896_; lean_object* v___x_3897_; 
v___x_3895_ = ((size_t)1ULL);
v___x_3896_ = lean_usize_add(v_i_3886_, v___x_3895_);
v___x_3897_ = lean_array_uset(v_bs_x27_3892_, v_i_3886_, v___y_3894_);
v_i_3886_ = v___x_3896_;
v_bs_3887_ = v___x_3897_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_3884_ = stack[0].m_obj;
size_t v_sz_3885_ = stack[1].m_num;
size_t v_i_3886_ = stack[2].m_num;
lean_object* v_bs_3887_ = stack[3].m_obj;
lean_object* v_res_3904_;
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3884_, v_sz_3885_, v_i_3886_, v_bs_3887_);
stack->m_obj
 = v_res_3904_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3905_, lean_object* v_sz_3906_, lean_object* v_i_3907_, lean_object* v_bs_3908_){
_start:
{
size_t v_sz_boxed_3909_; size_t v_i_boxed_3910_; lean_object* v_res_3911_; 
v_sz_boxed_3909_ = lean_unbox_usize(v_sz_3906_);
lean_dec(v_sz_3906_);
v_i_boxed_3910_ = lean_unbox_usize(v_i_3907_);
lean_dec(v_i_3907_);
v_res_3911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3905_, v_sz_boxed_3909_, v_i_boxed_3910_, v_bs_3908_);
lean_dec_ref(v_lctx_3905_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3912_, lean_object* v_pivot_3913_, lean_object* v_as_3914_, lean_object* v_i_3915_, lean_object* v_k_3916_){
_start:
{
uint8_t v___x_3917_; 
v___x_3917_ = lean_nat_dec_lt(v_k_3916_, v_hi_3912_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_dec(v_k_3916_);
v___x_3918_ = lean_array_fswap(v_as_3914_, v_i_3915_, v_hi_3912_);
v___x_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3919_, 0, v_i_3915_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
return v___x_3919_;
}
else
{
lean_object* v___x_3920_; lean_object* v_fst_3921_; lean_object* v_fst_3922_; uint8_t v___x_3923_; 
v___x_3920_ = lean_array_fget_borrowed(v_as_3914_, v_k_3916_);
v_fst_3921_ = lean_ctor_get(v___x_3920_, 0);
v_fst_3922_ = lean_ctor_get(v_pivot_3913_, 0);
v___x_3923_ = lean_nat_dec_lt(v_fst_3921_, v_fst_3922_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = lean_nat_add(v_k_3916_, v___x_3924_);
lean_dec(v_k_3916_);
v_k_3916_ = v___x_3925_;
goto _start;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3927_ = lean_array_fswap(v_as_3914_, v_i_3915_, v_k_3916_);
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_3929_ = lean_nat_add(v_i_3915_, v___x_3928_);
lean_dec(v_i_3915_);
v___x_3930_ = lean_nat_add(v_k_3916_, v___x_3928_);
lean_dec(v_k_3916_);
v_as_3914_ = v___x_3927_;
v_i_3915_ = v___x_3929_;
v_k_3916_ = v___x_3930_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3932_, lean_object* v_pivot_3933_, lean_object* v_as_3934_, lean_object* v_i_3935_, lean_object* v_k_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3932_, v_pivot_3933_, v_as_3934_, v_i_3935_, v_k_3936_);
lean_dec_ref(v_pivot_3933_);
lean_dec(v_hi_3932_);
return v_res_3937_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3938_, lean_object* v_i_3939_){
_start:
{
lean_object* v_fst_3940_; lean_object* v_fst_3941_; uint8_t v___x_3942_; 
v_fst_3940_ = lean_ctor_get(v_h_3938_, 0);
v_fst_3941_ = lean_ctor_get(v_i_3939_, 0);
v___x_3942_ = lean_nat_dec_lt(v_fst_3940_, v_fst_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3938_ = stack[0].m_obj;
lean_object* v_i_3939_ = stack[1].m_obj;
uint8_t v_res_3943_;
v_res_3943_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3938_, v_i_3939_);
stack->m_num = v_res_3943_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3944_, lean_object* v_i_3945_){
_start:
{
uint8_t v_res_3946_; lean_object* v_r_3947_; 
v_res_3946_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3944_, v_i_3945_);
lean_dec_ref(v_i_3945_);
lean_dec_ref(v_h_3944_);
v_r_3947_ = lean_box(v_res_3946_);
return v_r_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3948_, lean_object* v_as_3949_, lean_object* v_lo_3950_, lean_object* v_hi_3951_){
_start:
{
lean_object* v___y_3953_; uint8_t v___x_3963_; 
v___x_3963_ = lean_nat_dec_lt(v_lo_3950_, v_hi_3951_);
if (v___x_3963_ == 0)
{
lean_dec(v_lo_3950_);
return v_as_3949_;
}
else
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v_mid_3966_; lean_object* v___y_3968_; lean_object* v___y_3974_; lean_object* v___x_3979_; lean_object* v___x_3980_; uint8_t v___x_3981_; 
v___x_3964_ = lean_nat_add(v_lo_3950_, v_hi_3951_);
v___x_3965_ = lean_unsigned_to_nat(1u);
v_mid_3966_ = lean_nat_shiftr(v___x_3964_, v___x_3965_);
lean_dec(v___x_3964_);
v___x_3979_ = lean_array_fget_borrowed(v_as_3949_, v_mid_3966_);
v___x_3980_ = lean_array_fget_borrowed(v_as_3949_, v_lo_3950_);
v___x_3981_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3979_, v___x_3980_);
if (v___x_3981_ == 0)
{
v___y_3974_ = v_as_3949_;
goto v___jp_3973_;
}
else
{
lean_object* v___x_3982_; 
v___x_3982_ = lean_array_fswap(v_as_3949_, v_lo_3950_, v_mid_3966_);
v___y_3974_ = v___x_3982_;
goto v___jp_3973_;
}
v___jp_3967_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3969_ = lean_array_fget_borrowed(v___y_3968_, v_mid_3966_);
v___x_3970_ = lean_array_fget_borrowed(v___y_3968_, v_hi_3951_);
v___x_3971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3969_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_dec(v_mid_3966_);
v___y_3953_ = v___y_3968_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_array_fswap(v___y_3968_, v_mid_3966_, v_hi_3951_);
lean_dec(v_mid_3966_);
v___y_3953_ = v___x_3972_;
goto v___jp_3952_;
}
}
v___jp_3973_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3975_ = lean_array_fget_borrowed(v___y_3974_, v_hi_3951_);
v___x_3976_ = lean_array_fget_borrowed(v___y_3974_, v_lo_3950_);
v___x_3977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3975_, v___x_3976_);
if (v___x_3977_ == 0)
{
v___y_3968_ = v___y_3974_;
goto v___jp_3967_;
}
else
{
lean_object* v___x_3978_; 
v___x_3978_ = lean_array_fswap(v___y_3974_, v_lo_3950_, v_hi_3951_);
v___y_3968_ = v___x_3978_;
goto v___jp_3967_;
}
}
}
v___jp_3952_:
{
lean_object* v_pivot_3954_; lean_object* v___x_3955_; lean_object* v_fst_3956_; lean_object* v_snd_3957_; uint8_t v___x_3958_; 
v_pivot_3954_ = lean_array_fget(v___y_3953_, v_hi_3951_);
lean_inc_n(v_lo_3950_, 2);
v___x_3955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3951_, v_pivot_3954_, v___y_3953_, v_lo_3950_, v_lo_3950_);
lean_dec(v_pivot_3954_);
v_fst_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_fst_3956_);
v_snd_3957_ = lean_ctor_get(v___x_3955_, 1);
lean_inc(v_snd_3957_);
lean_dec_ref(v___x_3955_);
v___x_3958_ = lean_nat_dec_le(v_hi_3951_, v_fst_3956_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3959_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3948_, v_snd_3957_, v_lo_3950_, v_fst_3956_);
v___x_3960_ = lean_unsigned_to_nat(1u);
v___x_3961_ = lean_nat_add(v_fst_3956_, v___x_3960_);
lean_dec(v_fst_3956_);
v_as_3949_ = v___x_3959_;
v_lo_3950_ = v___x_3961_;
goto _start;
}
else
{
lean_dec(v_fst_3956_);
lean_dec(v_lo_3950_);
return v_snd_3957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3983_, lean_object* v_as_3984_, lean_object* v_lo_3985_, lean_object* v_hi_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3983_, v_as_3984_, v_lo_3985_, v_hi_3986_);
lean_dec(v_hi_3986_);
lean_dec(v_n_3983_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3988_, lean_object* v_hyps_3989_){
_start:
{
lean_object* v___y_3991_; size_t v_sz_3995_; size_t v___x_3996_; lean_object* v_hyps_3997_; lean_object* v___x_3998_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v_sz_3995_ = lean_array_size(v_hyps_3989_);
v___x_3996_ = ((size_t)0ULL);
v_hyps_3997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3988_, v_sz_3995_, v___x_3996_, v_hyps_3989_);
v___x_3998_ = lean_array_get_size(v_hyps_3997_);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = lean_nat_dec_eq(v___x_3998_, v___x_4003_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___y_4008_; uint8_t v___x_4010_; 
v___x_4005_ = lean_unsigned_to_nat(1u);
v___x_4006_ = lean_nat_sub(v___x_3998_, v___x_4005_);
v___x_4010_ = lean_nat_dec_le(v___x_4003_, v___x_4006_);
if (v___x_4010_ == 0)
{
lean_inc(v___x_4006_);
v___y_4008_ = v___x_4006_;
goto v___jp_4007_;
}
else
{
v___y_4008_ = v___x_4003_;
goto v___jp_4007_;
}
v___jp_4007_:
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_nat_dec_le(v___y_4008_, v___x_4006_);
if (v___x_4009_ == 0)
{
lean_dec(v___x_4006_);
lean_inc(v___y_4008_);
v___y_4000_ = v___y_4008_;
v___y_4001_ = v___y_4008_;
goto v___jp_3999_;
}
else
{
v___y_4000_ = v___y_4008_;
v___y_4001_ = v___x_4006_;
goto v___jp_3999_;
}
}
}
else
{
v___y_3991_ = v_hyps_3997_;
goto v___jp_3990_;
}
v___jp_3990_:
{
size_t v_sz_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v_sz_3992_ = lean_array_size(v___y_3991_);
v___x_3993_ = ((size_t)0ULL);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3992_, v___x_3993_, v___y_3991_);
return v___x_3994_;
}
v___jp_3999_:
{
lean_object* v___x_4002_; 
v___x_4002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3998_, v_hyps_3997_, v___y_4000_, v___y_4001_);
lean_dec(v___y_4001_);
v___y_3991_ = v___x_4002_;
goto v___jp_3990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_4011_, lean_object* v_hyps_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_4011_, v_hyps_4012_);
lean_dec_ref(v_lctx_4011_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_4014_, lean_object* v_as_4015_, lean_object* v_lo_4016_, lean_object* v_hi_4017_, lean_object* v_w_4018_, lean_object* v_hlo_4019_, lean_object* v_hhi_4020_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_4014_, v_as_4015_, v_lo_4016_, v_hi_4017_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_4022_, lean_object* v_as_4023_, lean_object* v_lo_4024_, lean_object* v_hi_4025_, lean_object* v_w_4026_, lean_object* v_hlo_4027_, lean_object* v_hhi_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_4022_, v_as_4023_, v_lo_4024_, v_hi_4025_, v_w_4026_, v_hlo_4027_, v_hhi_4028_);
lean_dec(v_hi_4025_);
lean_dec(v_n_4022_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_4030_, lean_object* v_lo_4031_, lean_object* v_hi_4032_, lean_object* v_hhi_4033_, lean_object* v_pivot_4034_, lean_object* v_as_4035_, lean_object* v_i_4036_, lean_object* v_k_4037_, lean_object* v_ilo_4038_, lean_object* v_ik_4039_, lean_object* v_w_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_4032_, v_pivot_4034_, v_as_4035_, v_i_4036_, v_k_4037_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_4042_, lean_object* v_lo_4043_, lean_object* v_hi_4044_, lean_object* v_hhi_4045_, lean_object* v_pivot_4046_, lean_object* v_as_4047_, lean_object* v_i_4048_, lean_object* v_k_4049_, lean_object* v_ilo_4050_, lean_object* v_ik_4051_, lean_object* v_w_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_4042_, v_lo_4043_, v_hi_4044_, v_hhi_4045_, v_pivot_4046_, v_as_4047_, v_i_4048_, v_k_4049_, v_ilo_4050_, v_ik_4051_, v_w_4052_);
lean_dec_ref(v_pivot_4046_);
lean_dec(v_hi_4044_);
lean_dec(v_lo_4043_);
lean_dec(v_n_4042_);
return v_res_4053_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_4054_, lean_object* v_x_4055_){
_start:
{
if (lean_obj_tag(v_x_4055_) == 0)
{
uint8_t v___x_4056_; 
v___x_4056_ = 0;
return v___x_4056_;
}
else
{
lean_object* v_key_4057_; lean_object* v_tail_4058_; uint8_t v___x_4059_; 
v_key_4057_ = lean_ctor_get(v_x_4055_, 0);
v_tail_4058_ = lean_ctor_get(v_x_4055_, 2);
v___x_4059_ = lean_name_eq(v_key_4057_, v_a_4054_);
if (v___x_4059_ == 0)
{
v_x_4055_ = v_tail_4058_;
goto _start;
}
else
{
return v___x_4059_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4054_ = stack[0].m_obj;
lean_object* v_x_4055_ = stack[1].m_obj;
uint8_t v_res_4061_;
v_res_4061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4054_, v_x_4055_);
stack->m_num = v_res_4061_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_4062_, lean_object* v_x_4063_){
_start:
{
uint8_t v_res_4064_; lean_object* v_r_4065_; 
v_res_4064_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4062_, v_x_4063_);
lean_dec(v_x_4063_);
lean_dec(v_a_4062_);
v_r_4065_ = lean_box(v_res_4064_);
return v_r_4065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_4066_, lean_object* v_x_4067_){
_start:
{
if (lean_obj_tag(v_x_4067_) == 0)
{
return v_x_4067_;
}
else
{
lean_object* v_key_4068_; lean_object* v_value_4069_; lean_object* v_tail_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4079_; 
v_key_4068_ = lean_ctor_get(v_x_4067_, 0);
v_value_4069_ = lean_ctor_get(v_x_4067_, 1);
v_tail_4070_ = lean_ctor_get(v_x_4067_, 2);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_x_4067_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4072_ = v_x_4067_;
v_isShared_4073_ = v_isSharedCheck_4079_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_tail_4070_);
lean_inc(v_value_4069_);
lean_inc(v_key_4068_);
lean_dec(v_x_4067_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4079_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
uint8_t v___x_4074_; 
v___x_4074_ = lean_name_eq(v_key_4068_, v_a_4066_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4077_; 
v___x_4075_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4066_, v_tail_4070_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 2, v___x_4075_);
v___x_4077_ = v___x_4072_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_key_4068_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v_value_4069_);
lean_ctor_set(v_reuseFailAlloc_4078_, 2, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
else
{
lean_del_object(v___x_4072_);
lean_dec(v_value_4069_);
lean_dec(v_key_4068_);
return v_tail_4070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_4080_, lean_object* v_x_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4080_, v_x_4081_);
lean_dec(v_a_4080_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_size_4085_; lean_object* v_buckets_4086_; lean_object* v___x_4087_; uint64_t v___y_4089_; 
v_size_4085_ = lean_ctor_get(v_m_4083_, 0);
v_buckets_4086_ = lean_ctor_get(v_m_4083_, 1);
v___x_4087_ = lean_array_get_size(v_buckets_4086_);
if (lean_obj_tag(v_a_4084_) == 0)
{
uint64_t v___x_4118_; 
v___x_4118_ = 1723ULL;
v___y_4089_ = v___x_4118_;
goto v___jp_4088_;
}
else
{
uint64_t v_hash_4119_; 
v_hash_4119_ = lean_ctor_get_uint64(v_a_4084_, sizeof(void*)*2);
v___y_4089_ = v_hash_4119_;
goto v___jp_4088_;
}
v___jp_4088_:
{
uint64_t v___x_4090_; uint64_t v___x_4091_; uint64_t v_fold_4092_; uint64_t v___x_4093_; uint64_t v___x_4094_; uint64_t v___x_4095_; size_t v___x_4096_; size_t v___x_4097_; size_t v___x_4098_; size_t v___x_4099_; size_t v___x_4100_; lean_object* v_bkt_4101_; uint8_t v___x_4102_; 
v___x_4090_ = 32ULL;
v___x_4091_ = lean_uint64_shift_right(v___y_4089_, v___x_4090_);
v_fold_4092_ = lean_uint64_xor(v___y_4089_, v___x_4091_);
v___x_4093_ = 16ULL;
v___x_4094_ = lean_uint64_shift_right(v_fold_4092_, v___x_4093_);
v___x_4095_ = lean_uint64_xor(v_fold_4092_, v___x_4094_);
v___x_4096_ = lean_uint64_to_usize(v___x_4095_);
v___x_4097_ = lean_usize_of_nat(v___x_4087_);
v___x_4098_ = ((size_t)1ULL);
v___x_4099_ = lean_usize_sub(v___x_4097_, v___x_4098_);
v___x_4100_ = lean_usize_land(v___x_4096_, v___x_4099_);
v_bkt_4101_ = lean_array_uget_borrowed(v_buckets_4086_, v___x_4100_);
v___x_4102_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4084_, v_bkt_4101_);
if (v___x_4102_ == 0)
{
return v_m_4083_;
}
else
{
lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4115_; 
lean_inc(v_bkt_4101_);
lean_inc_ref(v_buckets_4086_);
lean_inc(v_size_4085_);
v_isSharedCheck_4115_ = !lean_is_exclusive(v_m_4083_);
if (v_isSharedCheck_4115_ == 0)
{
lean_object* v_unused_4116_; lean_object* v_unused_4117_; 
v_unused_4116_ = lean_ctor_get(v_m_4083_, 1);
lean_dec(v_unused_4116_);
v_unused_4117_ = lean_ctor_get(v_m_4083_, 0);
lean_dec(v_unused_4117_);
v___x_4104_ = v_m_4083_;
v_isShared_4105_ = v_isSharedCheck_4115_;
goto v_resetjp_4103_;
}
else
{
lean_dec(v_m_4083_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4115_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4106_; lean_object* v_buckets_x27_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4113_; 
v___x_4106_ = lean_box(0);
v_buckets_x27_4107_ = lean_array_uset(v_buckets_4086_, v___x_4100_, v___x_4106_);
v___x_4108_ = lean_unsigned_to_nat(1u);
v___x_4109_ = lean_nat_sub(v_size_4085_, v___x_4108_);
lean_dec(v_size_4085_);
v___x_4110_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4084_, v_bkt_4101_);
v___x_4111_ = lean_array_uset(v_buckets_x27_4107_, v___x_4100_, v___x_4110_);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 1, v___x_4111_);
lean_ctor_set(v___x_4104_, 0, v___x_4109_);
v___x_4113_ = v___x_4104_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4114_, 1, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4120_, v_a_4121_);
lean_dec(v_a_4121_);
return v_res_4122_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v_buckets_4125_; lean_object* v___x_4126_; uint64_t v___y_4128_; 
v_buckets_4125_ = lean_ctor_get(v_m_4123_, 1);
v___x_4126_ = lean_array_get_size(v_buckets_4125_);
if (lean_obj_tag(v_a_4124_) == 0)
{
uint64_t v___x_4142_; 
v___x_4142_ = 1723ULL;
v___y_4128_ = v___x_4142_;
goto v___jp_4127_;
}
else
{
uint64_t v_hash_4143_; 
v_hash_4143_ = lean_ctor_get_uint64(v_a_4124_, sizeof(void*)*2);
v___y_4128_ = v_hash_4143_;
goto v___jp_4127_;
}
v___jp_4127_:
{
uint64_t v___x_4129_; uint64_t v___x_4130_; uint64_t v_fold_4131_; uint64_t v___x_4132_; uint64_t v___x_4133_; uint64_t v___x_4134_; size_t v___x_4135_; size_t v___x_4136_; size_t v___x_4137_; size_t v___x_4138_; size_t v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4129_ = 32ULL;
v___x_4130_ = lean_uint64_shift_right(v___y_4128_, v___x_4129_);
v_fold_4131_ = lean_uint64_xor(v___y_4128_, v___x_4130_);
v___x_4132_ = 16ULL;
v___x_4133_ = lean_uint64_shift_right(v_fold_4131_, v___x_4132_);
v___x_4134_ = lean_uint64_xor(v_fold_4131_, v___x_4133_);
v___x_4135_ = lean_uint64_to_usize(v___x_4134_);
v___x_4136_ = lean_usize_of_nat(v___x_4126_);
v___x_4137_ = ((size_t)1ULL);
v___x_4138_ = lean_usize_sub(v___x_4136_, v___x_4137_);
v___x_4139_ = lean_usize_land(v___x_4135_, v___x_4138_);
v___x_4140_ = lean_array_uget_borrowed(v_buckets_4125_, v___x_4139_);
v___x_4141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4124_, v___x_4140_);
return v___x_4141_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_4123_ = stack[0].m_obj;
lean_object* v_a_4124_ = stack[1].m_obj;
uint8_t v_res_4144_;
v_res_4144_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4123_, v_a_4124_);
stack->m_num = v_res_4144_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4145_, lean_object* v_a_4146_){
_start:
{
uint8_t v_res_4147_; lean_object* v_r_4148_; 
v_res_4147_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4145_, v_a_4146_);
lean_dec(v_a_4146_);
lean_dec_ref(v_m_4145_);
v_r_4148_ = lean_box(v_res_4147_);
return v_r_4148_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4149_, lean_object* v_as_4150_, size_t v_i_4151_, size_t v_stop_4152_, lean_object* v_b_4153_){
_start:
{
uint8_t v___x_4154_; 
v___x_4154_ = lean_usize_dec_eq(v_i_4151_, v_stop_4152_);
if (v___x_4154_ == 0)
{
size_t v___x_4155_; size_t v___x_4156_; lean_object* v___x_4157_; 
v___x_4155_ = ((size_t)1ULL);
v___x_4156_ = lean_usize_sub(v_i_4151_, v___x_4155_);
v___x_4157_ = lean_array_uget(v_as_4150_, v___x_4156_);
if (lean_obj_tag(v___x_4157_) == 0)
{
v_i_4151_ = v___x_4156_;
goto _start;
}
else
{
lean_object* v_val_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4193_; 
v_val_4159_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4161_ = v___x_4157_;
v_isShared_4162_ = v_isSharedCheck_4193_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_val_4159_);
lean_dec(v___x_4157_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4193_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v_fst_4163_; lean_object* v_snd_4164_; lean_object* v___y_4166_; lean_object* v___y_4182_; lean_object* v_size_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v_fst_4163_ = lean_ctor_get(v_b_4153_, 0);
v_snd_4164_ = lean_ctor_get(v_b_4153_, 1);
v_size_4188_ = lean_ctor_get(v_fst_4163_, 0);
v___x_4189_ = lean_unsigned_to_nat(0u);
v___x_4190_ = lean_nat_dec_eq(v_size_4188_, v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v_index_4191_; 
v_index_4191_ = lean_ctor_get(v_val_4159_, 0);
lean_inc(v_index_4191_);
v___y_4182_ = v_index_4191_;
goto v___jp_4181_;
}
else
{
lean_object* v___x_4192_; 
lean_inc(v_snd_4164_);
lean_del_object(v___x_4161_);
lean_dec(v_val_4159_);
lean_dec_ref(v_b_4153_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v_snd_4164_);
return v___x_4192_;
}
v___jp_4165_:
{
uint8_t v___x_4167_; 
v___x_4167_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4163_, v___y_4166_);
if (v___x_4167_ == 0)
{
lean_dec(v___y_4166_);
lean_dec(v_val_4159_);
v_i_4151_ = v___x_4156_;
goto _start;
}
else
{
lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4178_; 
lean_inc(v_snd_4164_);
lean_inc(v_fst_4163_);
v_isSharedCheck_4178_ = !lean_is_exclusive(v_b_4153_);
if (v_isSharedCheck_4178_ == 0)
{
lean_object* v_unused_4179_; lean_object* v_unused_4180_; 
v_unused_4179_ = lean_ctor_get(v_b_4153_, 1);
lean_dec(v_unused_4179_);
v_unused_4180_ = lean_ctor_get(v_b_4153_, 0);
lean_dec(v_unused_4180_);
v___x_4170_ = v_b_4153_;
v_isShared_4171_ = v_isSharedCheck_4178_;
goto v_resetjp_4169_;
}
else
{
lean_dec(v_b_4153_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4178_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4172_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4163_, v___y_4166_);
lean_dec(v___y_4166_);
v___x_4173_ = lean_array_push(v_snd_4164_, v_val_4159_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 1, v___x_4173_);
lean_ctor_set(v___x_4170_, 0, v___x_4172_);
v___x_4175_ = v___x_4170_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4177_, 1, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
v_i_4151_ = v___x_4156_;
v_b_4153_ = v___x_4175_;
goto _start;
}
}
}
}
v___jp_4181_:
{
uint8_t v___x_4183_; 
v___x_4183_ = lean_nat_dec_lt(v___y_4182_, v_start_4149_);
lean_dec(v___y_4182_);
if (v___x_4183_ == 0)
{
lean_object* v_userName_4184_; 
lean_del_object(v___x_4161_);
v_userName_4184_ = lean_ctor_get(v_val_4159_, 2);
lean_inc(v_userName_4184_);
v___y_4166_ = v_userName_4184_;
goto v___jp_4165_;
}
else
{
lean_object* v___x_4186_; 
lean_inc(v_snd_4164_);
lean_dec(v_val_4159_);
lean_dec_ref(v_b_4153_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set_tag(v___x_4161_, 0);
lean_ctor_set(v___x_4161_, 0, v_snd_4164_);
v___x_4186_ = v___x_4161_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_snd_4164_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
}
else
{
lean_object* v___x_4194_; 
v___x_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4194_, 0, v_b_4153_);
return v___x_4194_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_4149_ = stack[0].m_obj;
lean_object* v_as_4150_ = stack[1].m_obj;
size_t v_i_4151_ = stack[2].m_num;
size_t v_stop_4152_ = stack[3].m_num;
lean_object* v_b_4153_ = stack[4].m_obj;
lean_object* v_res_4195_;
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4149_, v_as_4150_, v_i_4151_, v_stop_4152_, v_b_4153_);
stack->m_obj
 = v_res_4195_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4196_, lean_object* v_as_4197_, lean_object* v_i_4198_, lean_object* v_stop_4199_, lean_object* v_b_4200_){
_start:
{
size_t v_i_boxed_4201_; size_t v_stop_boxed_4202_; lean_object* v_res_4203_; 
v_i_boxed_4201_ = lean_unbox_usize(v_i_4198_);
lean_dec(v_i_4198_);
v_stop_boxed_4202_ = lean_unbox_usize(v_stop_4199_);
lean_dec(v_stop_4199_);
v_res_4203_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4196_, v_as_4197_, v_i_boxed_4201_, v_stop_boxed_4202_, v_b_4200_);
lean_dec_ref(v_as_4197_);
lean_dec(v_start_4196_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4204_, lean_object* v_x_4205_, lean_object* v_x_4206_){
_start:
{
if (lean_obj_tag(v_x_4205_) == 0)
{
lean_object* v_cs_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4220_; 
v_cs_4207_ = lean_ctor_get(v_x_4205_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v_x_4205_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4209_ = v_x_4205_;
v_isShared_4210_ = v_isSharedCheck_4220_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_cs_4207_);
lean_dec(v_x_4205_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4220_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4211_ = lean_array_get_size(v_cs_4207_);
v___x_4212_ = lean_unsigned_to_nat(0u);
v___x_4213_ = lean_nat_dec_lt(v___x_4212_, v___x_4211_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4215_; 
lean_dec_ref(v_cs_4207_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 1);
lean_ctor_set(v___x_4209_, 0, v_x_4206_);
v___x_4215_ = v___x_4209_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_x_4206_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
size_t v___x_4217_; size_t v___x_4218_; lean_object* v___x_4219_; 
lean_del_object(v___x_4209_);
v___x_4217_ = lean_usize_of_nat(v___x_4211_);
v___x_4218_ = ((size_t)0ULL);
v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4204_, v_cs_4207_, v___x_4217_, v___x_4218_, v_x_4206_);
lean_dec_ref(v_cs_4207_);
return v___x_4219_;
}
}
}
else
{
lean_object* v_vs_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4234_; 
v_vs_4221_ = lean_ctor_get(v_x_4205_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_x_4205_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4223_ = v_x_4205_;
v_isShared_4224_ = v_isSharedCheck_4234_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_vs_4221_);
lean_dec(v_x_4205_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4234_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; uint8_t v___x_4227_; 
v___x_4225_ = lean_array_get_size(v_vs_4221_);
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = lean_nat_dec_lt(v___x_4226_, v___x_4225_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4229_; 
lean_dec_ref(v_vs_4221_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v_x_4206_);
v___x_4229_ = v___x_4223_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_x_4206_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
else
{
size_t v___x_4231_; size_t v___x_4232_; lean_object* v___x_4233_; 
lean_del_object(v___x_4223_);
v___x_4231_ = lean_usize_of_nat(v___x_4225_);
v___x_4232_ = ((size_t)0ULL);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4204_, v_vs_4221_, v___x_4231_, v___x_4232_, v_x_4206_);
lean_dec_ref(v_vs_4221_);
return v___x_4233_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4235_, lean_object* v_as_4236_, size_t v_i_4237_, size_t v_stop_4238_, lean_object* v_b_4239_){
_start:
{
uint8_t v___x_4240_; 
v___x_4240_ = lean_usize_dec_eq(v_i_4237_, v_stop_4238_);
if (v___x_4240_ == 0)
{
size_t v___x_4241_; size_t v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4241_ = ((size_t)1ULL);
v___x_4242_ = lean_usize_sub(v_i_4237_, v___x_4241_);
v___x_4243_ = lean_array_uget_borrowed(v_as_4236_, v___x_4242_);
lean_inc(v___x_4243_);
v___x_4244_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4235_, v___x_4243_, v_b_4239_);
if (lean_obj_tag(v___x_4244_) == 0)
{
return v___x_4244_;
}
else
{
lean_object* v_a_4245_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
v_i_4237_ = v___x_4242_;
v_b_4239_ = v_a_4245_;
goto _start;
}
}
else
{
lean_object* v___x_4247_; 
v___x_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4247_, 0, v_b_4239_);
return v___x_4247_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_4235_ = stack[0].m_obj;
lean_object* v_as_4236_ = stack[1].m_obj;
size_t v_i_4237_ = stack[2].m_num;
size_t v_stop_4238_ = stack[3].m_num;
lean_object* v_b_4239_ = stack[4].m_obj;
lean_object* v_res_4248_;
v_res_4248_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4235_, v_as_4236_, v_i_4237_, v_stop_4238_, v_b_4239_);
stack->m_obj
 = v_res_4248_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4249_, lean_object* v_as_4250_, lean_object* v_i_4251_, lean_object* v_stop_4252_, lean_object* v_b_4253_){
_start:
{
size_t v_i_boxed_4254_; size_t v_stop_boxed_4255_; lean_object* v_res_4256_; 
v_i_boxed_4254_ = lean_unbox_usize(v_i_4251_);
lean_dec(v_i_4251_);
v_stop_boxed_4255_ = lean_unbox_usize(v_stop_4252_);
lean_dec(v_stop_4252_);
v_res_4256_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4249_, v_as_4250_, v_i_boxed_4254_, v_stop_boxed_4255_, v_b_4253_);
lean_dec_ref(v_as_4250_);
lean_dec(v_start_4249_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4257_, lean_object* v_x_4258_, lean_object* v_x_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4257_, v_x_4258_, v_x_4259_);
lean_dec(v_start_4257_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4261_, lean_object* v_t_4262_, lean_object* v_init_4263_){
_start:
{
lean_object* v_root_4264_; lean_object* v_tail_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; uint8_t v___x_4268_; 
v_root_4264_ = lean_ctor_get(v_t_4262_, 0);
lean_inc_ref(v_root_4264_);
v_tail_4265_ = lean_ctor_get(v_t_4262_, 1);
lean_inc_ref(v_tail_4265_);
lean_dec_ref(v_t_4262_);
v___x_4266_ = lean_array_get_size(v_tail_4265_);
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = lean_nat_dec_lt(v___x_4267_, v___x_4266_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; 
lean_dec_ref(v_tail_4265_);
v___x_4269_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4261_, v_root_4264_, v_init_4263_);
return v___x_4269_;
}
else
{
size_t v___x_4270_; size_t v___x_4271_; lean_object* v___x_4272_; 
v___x_4270_ = lean_usize_of_nat(v___x_4266_);
v___x_4271_ = ((size_t)0ULL);
v___x_4272_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4261_, v_tail_4265_, v___x_4270_, v___x_4271_, v_init_4263_);
lean_dec_ref(v_tail_4265_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_dec_ref(v_root_4264_);
return v___x_4272_;
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4274_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___x_4272_, 1);
v___x_4274_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4261_, v_root_4264_, v_a_4273_);
return v___x_4274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4275_, lean_object* v_t_4276_, lean_object* v_init_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4275_, v_t_4276_, v_init_4277_);
lean_dec(v_start_4275_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4279_, lean_object* v_lctx_4280_, lean_object* v_init_4281_){
_start:
{
lean_object* v_decls_4282_; lean_object* v___x_4283_; 
v_decls_4282_ = lean_ctor_get(v_lctx_4280_, 1);
lean_inc_ref(v_decls_4282_);
lean_dec_ref(v_lctx_4280_);
v___x_4283_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4279_, v_decls_4282_, v_init_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4284_, lean_object* v_lctx_4285_, lean_object* v_init_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4284_, v_lctx_4285_, v_init_4286_);
lean_dec(v_start_4284_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4290_, lean_object* v_userNames_4291_, lean_object* v_start_4292_){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4293_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4294_, 0, v_userNames_4291_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4292_, v_lctx_4290_, v___x_4294_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
v___x_4297_ = l_Array_reverse___redArg(v_a_4296_);
return v___x_4297_;
}
else
{
lean_object* v_a_4298_; lean_object* v_snd_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_a_4298_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4295_, 1);
v_snd_4299_ = lean_ctor_get(v_a_4298_, 1);
lean_inc(v_snd_4299_);
lean_dec(v_a_4298_);
v___x_4300_ = l_Array_reverse___redArg(v_snd_4299_);
v___x_4301_ = l_Array_reverse___redArg(v___x_4300_);
return v___x_4301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4302_, lean_object* v_userNames_4303_, lean_object* v_start_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4302_, v_userNames_4303_, v_start_4304_);
lean_dec(v_start_4304_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4306_, lean_object* v_lctx_4307_, lean_object* v_userNames_4308_, lean_object* v_start_4309_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4307_, v_userNames_4308_, v_start_4309_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4311_, lean_object* v_lctx_4312_, lean_object* v_userNames_4313_, lean_object* v_start_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4311_, v_lctx_4312_, v_userNames_4313_, v_start_4314_);
lean_dec(v_start_4314_);
return v_res_4315_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4316_, lean_object* v_m_4317_, lean_object* v_a_4318_){
_start:
{
uint8_t v___x_4319_; 
v___x_4319_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4317_, v_a_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_4317_ = stack[1].m_obj;
lean_object* v_a_4318_ = stack[2].m_obj;
uint8_t v_res_4320_;
v_res_4320_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_box(0), v_m_4317_, v_a_4318_);
stack->m_num = v_res_4320_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4321_, lean_object* v_m_4322_, lean_object* v_a_4323_){
_start:
{
uint8_t v_res_4324_; lean_object* v_r_4325_; 
v_res_4324_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4321_, v_m_4322_, v_a_4323_);
lean_dec(v_a_4323_);
lean_dec_ref(v_m_4322_);
v_r_4325_ = lean_box(v_res_4324_);
return v_r_4325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4326_, lean_object* v_m_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4327_, v_a_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4330_, lean_object* v_m_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4330_, v_m_4331_, v_a_4332_);
lean_dec(v_a_4332_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4334_, lean_object* v_start_4335_, lean_object* v_lctx_4336_, lean_object* v_init_4337_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4335_, v_lctx_4336_, v_init_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4339_, lean_object* v_start_4340_, lean_object* v_lctx_4341_, lean_object* v_init_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4339_, v_start_4340_, v_lctx_4341_, v_init_4342_);
lean_dec(v_start_4340_);
return v_res_4343_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4344_, lean_object* v_a_4345_, lean_object* v_x_4346_){
_start:
{
uint8_t v___x_4347_; 
v___x_4347_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4345_, v_x_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4345_ = stack[1].m_obj;
lean_object* v_x_4346_ = stack[2].m_obj;
uint8_t v_res_4348_;
v_res_4348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_box(0), v_a_4345_, v_x_4346_);
stack->m_num = v_res_4348_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4349_, lean_object* v_a_4350_, lean_object* v_x_4351_){
_start:
{
uint8_t v_res_4352_; lean_object* v_r_4353_; 
v_res_4352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4349_, v_a_4350_, v_x_4351_);
lean_dec(v_x_4351_);
lean_dec(v_a_4350_);
v_r_4353_ = lean_box(v_res_4352_);
return v_r_4353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4354_, lean_object* v_a_4355_, lean_object* v_x_4356_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4355_, v_x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4358_, lean_object* v_a_4359_, lean_object* v_x_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4358_, v_a_4359_, v_x_4360_);
lean_dec(v_a_4359_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4362_, lean_object* v_start_4363_, lean_object* v_t_4364_, lean_object* v_init_4365_){
_start:
{
lean_object* v___x_4366_; 
v___x_4366_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4363_, v_t_4364_, v_init_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4367_, lean_object* v_start_4368_, lean_object* v_t_4369_, lean_object* v_init_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4367_, v_start_4368_, v_t_4369_, v_init_4370_);
lean_dec(v_start_4368_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4372_, lean_object* v_start_4373_, lean_object* v_x_4374_, lean_object* v_x_4375_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4373_, v_x_4374_, v_x_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4377_, lean_object* v_start_4378_, lean_object* v_x_4379_, lean_object* v_x_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4377_, v_start_4378_, v_x_4379_, v_x_4380_);
lean_dec(v_start_4378_);
return v_res_4381_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4382_, lean_object* v_start_4383_, lean_object* v_as_4384_, size_t v_i_4385_, size_t v_stop_4386_, lean_object* v_b_4387_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4383_, v_as_4384_, v_i_4385_, v_stop_4386_, v_b_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_4383_ = stack[1].m_obj;
lean_object* v_as_4384_ = stack[2].m_obj;
size_t v_i_4385_ = stack[3].m_num;
size_t v_stop_4386_ = stack[4].m_num;
lean_object* v_b_4387_ = stack[5].m_obj;
lean_object* v_res_4389_;
v_res_4389_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_box(0), v_start_4383_, v_as_4384_, v_i_4385_, v_stop_4386_, v_b_4387_);
stack->m_obj
 = v_res_4389_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4390_, lean_object* v_start_4391_, lean_object* v_as_4392_, lean_object* v_i_4393_, lean_object* v_stop_4394_, lean_object* v_b_4395_){
_start:
{
size_t v_i_boxed_4396_; size_t v_stop_boxed_4397_; lean_object* v_res_4398_; 
v_i_boxed_4396_ = lean_unbox_usize(v_i_4393_);
lean_dec(v_i_4393_);
v_stop_boxed_4397_ = lean_unbox_usize(v_stop_4394_);
lean_dec(v_stop_4394_);
v_res_4398_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4390_, v_start_4391_, v_as_4392_, v_i_boxed_4396_, v_stop_boxed_4397_, v_b_4395_);
lean_dec_ref(v_as_4392_);
lean_dec(v_start_4391_);
return v_res_4398_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4399_, lean_object* v_start_4400_, lean_object* v_as_4401_, size_t v_i_4402_, size_t v_stop_4403_, lean_object* v_b_4404_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4400_, v_as_4401_, v_i_4402_, v_stop_4403_, v_b_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_4400_ = stack[1].m_obj;
lean_object* v_as_4401_ = stack[2].m_obj;
size_t v_i_4402_ = stack[3].m_num;
size_t v_stop_4403_ = stack[4].m_num;
lean_object* v_b_4404_ = stack[5].m_obj;
lean_object* v_res_4406_;
v_res_4406_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_box(0), v_start_4400_, v_as_4401_, v_i_4402_, v_stop_4403_, v_b_4404_);
stack->m_obj
 = v_res_4406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4407_, lean_object* v_start_4408_, lean_object* v_as_4409_, lean_object* v_i_4410_, lean_object* v_stop_4411_, lean_object* v_b_4412_){
_start:
{
size_t v_i_boxed_4413_; size_t v_stop_boxed_4414_; lean_object* v_res_4415_; 
v_i_boxed_4413_ = lean_unbox_usize(v_i_4410_);
lean_dec(v_i_4410_);
v_stop_boxed_4414_ = lean_unbox_usize(v_stop_4411_);
lean_dec(v_stop_4411_);
v_res_4415_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4407_, v_start_4408_, v_as_4409_, v_i_boxed_4413_, v_stop_boxed_4414_, v_b_4412_);
lean_dec_ref(v_as_4409_);
lean_dec(v_start_4408_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4416_, lean_object* v_inst_4417_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = lean_apply_2(v_inst_4416_, lean_box(0), v_inst_4417_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4419_, lean_object* v_n_4420_, lean_object* v_inst_4421_, lean_object* v_inst_4422_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = lean_apply_2(v_inst_4421_, lean_box(0), v_inst_4422_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4424_, lean_object* v_d_x3f_4425_, lean_object* v_b_4426_){
_start:
{
if (lean_obj_tag(v_d_x3f_4425_) == 0)
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4427_, 0, v_b_4426_);
v___x_4428_ = lean_apply_2(v_toPure_4424_, lean_box(0), v___x_4427_);
return v___x_4428_;
}
else
{
lean_object* v_val_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4444_; 
v_val_4429_ = lean_ctor_get(v_d_x3f_4425_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_d_x3f_4425_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4431_ = v_d_x3f_4425_;
v_isShared_4432_ = v_isSharedCheck_4444_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_val_4429_);
lean_dec(v_d_x3f_4425_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4444_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
uint8_t v___x_4433_; 
v___x_4433_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4429_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4434_ = l_Lean_LocalDecl_toExpr(v_val_4429_);
v___x_4435_ = lean_array_push(v_b_4426_, v___x_4434_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4435_);
v___x_4437_ = v___x_4431_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_apply_2(v_toPure_4424_, lean_box(0), v___x_4437_);
return v___x_4438_;
}
}
else
{
lean_object* v___x_4441_; 
lean_dec(v_val_4429_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v_b_4426_);
v___x_4441_ = v___x_4431_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_b_4426_);
v___x_4441_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
lean_object* v___x_4442_; 
v___x_4442_ = lean_apply_2(v_toPure_4424_, lean_box(0), v___x_4441_);
return v___x_4442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4445_, lean_object* v_____s_4446_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = lean_apply_2(v_toPure_4445_, lean_box(0), v_____s_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4448_, lean_object* v_hs_4449_, lean_object* v___f_4450_, lean_object* v_toBind_4451_, lean_object* v___f_4452_, lean_object* v_____do__lift_4453_){
_start:
{
lean_object* v_decls_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v_decls_4454_ = lean_ctor_get(v_____do__lift_4453_, 1);
v___x_4455_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4448_, v_decls_4454_, v_hs_4449_, v___f_4450_);
v___x_4456_ = lean_apply_4(v_toBind_4451_, lean_box(0), lean_box(0), v___x_4455_, v___f_4452_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4457_, lean_object* v_hs_4458_, lean_object* v___f_4459_, lean_object* v_toBind_4460_, lean_object* v___f_4461_, lean_object* v_____do__lift_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4457_, v_hs_4458_, v___f_4459_, v_toBind_4460_, v___f_4461_, v_____do__lift_4462_);
lean_dec_ref(v_____do__lift_4462_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4466_, lean_object* v_inst_4467_){
_start:
{
lean_object* v_toApplicative_4468_; lean_object* v_toBind_4469_; lean_object* v_toPure_4470_; lean_object* v_hs_4471_; lean_object* v___f_4472_; lean_object* v___f_4473_; lean_object* v___f_4474_; lean_object* v___x_4475_; 
v_toApplicative_4468_ = lean_ctor_get(v_inst_4466_, 0);
v_toBind_4469_ = lean_ctor_get(v_inst_4466_, 1);
lean_inc_n(v_toBind_4469_, 2);
v_toPure_4470_ = lean_ctor_get(v_toApplicative_4468_, 1);
v_hs_4471_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4470_, 2);
v___f_4472_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4472_, 0, v_toPure_4470_);
v___f_4473_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4473_, 0, v_toPure_4470_);
v___f_4474_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4474_, 0, v_inst_4466_);
lean_closure_set(v___f_4474_, 1, v_hs_4471_);
lean_closure_set(v___f_4474_, 2, v___f_4472_);
lean_closure_set(v___f_4474_, 3, v_toBind_4469_);
lean_closure_set(v___f_4474_, 4, v___f_4473_);
v___x_4475_ = lean_apply_4(v_toBind_4469_, lean_box(0), lean_box(0), v_inst_4467_, v___f_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4476_, lean_object* v_inst_4477_, lean_object* v_inst_4478_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Lean_getLocalHyps___redArg(v_inst_4477_, v_inst_4478_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4480_, lean_object* v_e_4481_, lean_object* v_d_4482_){
_start:
{
lean_object* v___y_4484_; lean_object* v_fvarId_4516_; 
v_fvarId_4516_ = lean_ctor_get(v_d_4482_, 1);
lean_inc(v_fvarId_4516_);
v___y_4484_ = v_fvarId_4516_;
goto v___jp_4483_;
v___jp_4483_:
{
uint8_t v___x_4485_; 
v___x_4485_ = l_Lean_instBEqFVarId_beq(v___y_4484_, v_fvarId_4480_);
lean_dec(v___y_4484_);
if (v___x_4485_ == 0)
{
if (lean_obj_tag(v_d_4482_) == 0)
{
lean_object* v_index_4486_; lean_object* v_fvarId_4487_; lean_object* v_userName_4488_; lean_object* v_type_4489_; uint8_t v_bi_4490_; uint8_t v_kind_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4499_; 
v_index_4486_ = lean_ctor_get(v_d_4482_, 0);
v_fvarId_4487_ = lean_ctor_get(v_d_4482_, 1);
v_userName_4488_ = lean_ctor_get(v_d_4482_, 2);
v_type_4489_ = lean_ctor_get(v_d_4482_, 3);
v_bi_4490_ = lean_ctor_get_uint8(v_d_4482_, sizeof(void*)*4);
v_kind_4491_ = lean_ctor_get_uint8(v_d_4482_, sizeof(void*)*4 + 1);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_d_4482_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4493_ = v_d_4482_;
v_isShared_4494_ = v_isSharedCheck_4499_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_type_4489_);
lean_inc(v_userName_4488_);
lean_inc(v_fvarId_4487_);
lean_inc(v_index_4486_);
lean_dec(v_d_4482_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4499_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4495_ = l_Lean_Expr_replaceFVarId(v_type_4489_, v_fvarId_4480_, v_e_4481_);
lean_dec_ref(v_type_4489_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 3, v___x_4495_);
v___x_4497_ = v___x_4493_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_index_4486_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_fvarId_4487_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v_userName_4488_);
lean_ctor_set(v_reuseFailAlloc_4498_, 3, v___x_4495_);
lean_ctor_set_uint8(v_reuseFailAlloc_4498_, sizeof(void*)*4, v_bi_4490_);
lean_ctor_set_uint8(v_reuseFailAlloc_4498_, sizeof(void*)*4 + 1, v_kind_4491_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
else
{
lean_object* v_index_4500_; lean_object* v_fvarId_4501_; lean_object* v_userName_4502_; lean_object* v_type_4503_; lean_object* v_value_4504_; uint8_t v_nondep_4505_; uint8_t v_kind_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4515_; 
v_index_4500_ = lean_ctor_get(v_d_4482_, 0);
v_fvarId_4501_ = lean_ctor_get(v_d_4482_, 1);
v_userName_4502_ = lean_ctor_get(v_d_4482_, 2);
v_type_4503_ = lean_ctor_get(v_d_4482_, 3);
v_value_4504_ = lean_ctor_get(v_d_4482_, 4);
v_nondep_4505_ = lean_ctor_get_uint8(v_d_4482_, sizeof(void*)*5);
v_kind_4506_ = lean_ctor_get_uint8(v_d_4482_, sizeof(void*)*5 + 1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_d_4482_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4508_ = v_d_4482_;
v_isShared_4509_ = v_isSharedCheck_4515_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_value_4504_);
lean_inc(v_type_4503_);
lean_inc(v_userName_4502_);
lean_inc(v_fvarId_4501_);
lean_inc(v_index_4500_);
lean_dec(v_d_4482_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4515_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4513_; 
lean_inc(v_fvarId_4480_);
v___x_4510_ = l_Lean_Expr_replaceFVarId(v_type_4503_, v_fvarId_4480_, v_e_4481_);
lean_dec_ref(v_type_4503_);
v___x_4511_ = l_Lean_Expr_replaceFVarId(v_value_4504_, v_fvarId_4480_, v_e_4481_);
lean_dec_ref(v_value_4504_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 4, v___x_4511_);
lean_ctor_set(v___x_4508_, 3, v___x_4510_);
v___x_4513_ = v___x_4508_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_index_4500_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_fvarId_4501_);
lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_userName_4502_);
lean_ctor_set(v_reuseFailAlloc_4514_, 3, v___x_4510_);
lean_ctor_set(v_reuseFailAlloc_4514_, 4, v___x_4511_);
lean_ctor_set_uint8(v_reuseFailAlloc_4514_, sizeof(void*)*5, v_nondep_4505_);
lean_ctor_set_uint8(v_reuseFailAlloc_4514_, sizeof(void*)*5 + 1, v_kind_4506_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
else
{
lean_dec(v_fvarId_4480_);
return v_d_4482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4517_, lean_object* v_e_4518_, lean_object* v_d_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4517_, v_e_4518_, v_d_4519_);
lean_dec_ref(v_e_4518_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4521_, lean_object* v_e_4522_, lean_object* v_x_4523_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4521_, v_e_4522_, v_x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4525_, lean_object* v_e_4526_, lean_object* v_x_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4525_, v_e_4526_, v_x_4527_);
lean_dec_ref(v_e_4526_);
return v_res_4528_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4529_, lean_object* v_e_4530_, size_t v_sz_4531_, size_t v_i_4532_, lean_object* v_bs_4533_){
_start:
{
uint8_t v___x_4534_; 
v___x_4534_ = lean_usize_dec_lt(v_i_4532_, v_sz_4531_);
if (v___x_4534_ == 0)
{
lean_dec(v_fvarId_4529_);
return v_bs_4533_;
}
else
{
lean_object* v_v_4535_; lean_object* v___x_4536_; lean_object* v_bs_x27_4537_; lean_object* v___y_4539_; 
v_v_4535_ = lean_array_uget(v_bs_4533_, v_i_4532_);
v___x_4536_ = lean_unsigned_to_nat(0u);
v_bs_x27_4537_ = lean_array_uset(v_bs_4533_, v_i_4532_, v___x_4536_);
if (lean_obj_tag(v_v_4535_) == 0)
{
v___y_4539_ = v_v_4535_;
goto v___jp_4538_;
}
else
{
lean_object* v_val_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4552_; 
v_val_4544_ = lean_ctor_get(v_v_4535_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v_v_4535_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4546_ = v_v_4535_;
v_isShared_4547_ = v_isSharedCheck_4552_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_val_4544_);
lean_dec(v_v_4535_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4552_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; lean_object* v___x_4550_; 
lean_inc(v_fvarId_4529_);
v___x_4548_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4529_, v_e_4530_, v_val_4544_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4548_);
v___x_4550_ = v___x_4546_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
v___y_4539_ = v___x_4550_;
goto v___jp_4538_;
}
}
}
v___jp_4538_:
{
size_t v___x_4540_; size_t v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = ((size_t)1ULL);
v___x_4541_ = lean_usize_add(v_i_4532_, v___x_4540_);
v___x_4542_ = lean_array_uset(v_bs_x27_4537_, v_i_4532_, v___y_4539_);
v_i_4532_ = v___x_4541_;
v_bs_4533_ = v___x_4542_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_4529_ = stack[0].m_obj;
lean_object* v_e_4530_ = stack[1].m_obj;
size_t v_sz_4531_ = stack[2].m_num;
size_t v_i_4532_ = stack[3].m_num;
lean_object* v_bs_4533_ = stack[4].m_obj;
lean_object* v_res_4553_;
v_res_4553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4529_, v_e_4530_, v_sz_4531_, v_i_4532_, v_bs_4533_);
stack->m_obj
 = v_res_4553_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4554_, lean_object* v_e_4555_, lean_object* v_sz_4556_, lean_object* v_i_4557_, lean_object* v_bs_4558_){
_start:
{
size_t v_sz_boxed_4559_; size_t v_i_boxed_4560_; lean_object* v_res_4561_; 
v_sz_boxed_4559_ = lean_unbox_usize(v_sz_4556_);
lean_dec(v_sz_4556_);
v_i_boxed_4560_ = lean_unbox_usize(v_i_4557_);
lean_dec(v_i_4557_);
v_res_4561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4554_, v_e_4555_, v_sz_boxed_4559_, v_i_boxed_4560_, v_bs_4558_);
lean_dec_ref(v_e_4555_);
return v_res_4561_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4562_, lean_object* v_e_4563_, size_t v_sz_4564_, size_t v_i_4565_, lean_object* v_bs_4566_){
_start:
{
uint8_t v___x_4567_; 
v___x_4567_ = lean_usize_dec_lt(v_i_4565_, v_sz_4564_);
if (v___x_4567_ == 0)
{
lean_dec(v_fvarId_4562_);
return v_bs_4566_;
}
else
{
lean_object* v_v_4568_; lean_object* v___x_4569_; lean_object* v_bs_x27_4570_; lean_object* v___x_4571_; size_t v___x_4572_; size_t v___x_4573_; lean_object* v___x_4574_; 
v_v_4568_ = lean_array_uget(v_bs_4566_, v_i_4565_);
v___x_4569_ = lean_unsigned_to_nat(0u);
v_bs_x27_4570_ = lean_array_uset(v_bs_4566_, v_i_4565_, v___x_4569_);
lean_inc(v_fvarId_4562_);
v___x_4571_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4562_, v_e_4563_, v_v_4568_);
v___x_4572_ = ((size_t)1ULL);
v___x_4573_ = lean_usize_add(v_i_4565_, v___x_4572_);
v___x_4574_ = lean_array_uset(v_bs_x27_4570_, v_i_4565_, v___x_4571_);
v_i_4565_ = v___x_4573_;
v_bs_4566_ = v___x_4574_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_4562_ = stack[0].m_obj;
lean_object* v_e_4563_ = stack[1].m_obj;
size_t v_sz_4564_ = stack[2].m_num;
size_t v_i_4565_ = stack[3].m_num;
lean_object* v_bs_4566_ = stack[4].m_obj;
lean_object* v_res_4576_;
v_res_4576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4562_, v_e_4563_, v_sz_4564_, v_i_4565_, v_bs_4566_);
stack->m_obj
 = v_res_4576_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4577_, lean_object* v_e_4578_, lean_object* v_x_4579_){
_start:
{
if (lean_obj_tag(v_x_4579_) == 0)
{
lean_object* v_cs_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4590_; 
v_cs_4580_ = lean_ctor_get(v_x_4579_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v_x_4579_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4582_ = v_x_4579_;
v_isShared_4583_ = v_isSharedCheck_4590_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_cs_4580_);
lean_dec(v_x_4579_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4590_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
size_t v_sz_4584_; size_t v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; 
v_sz_4584_ = lean_array_size(v_cs_4580_);
v___x_4585_ = ((size_t)0ULL);
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4577_, v_e_4578_, v_sz_4584_, v___x_4585_, v_cs_4580_);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 0, v___x_4586_);
v___x_4588_ = v___x_4582_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4586_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
else
{
lean_object* v_vs_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4601_; 
v_vs_4591_ = lean_ctor_get(v_x_4579_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v_x_4579_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4593_ = v_x_4579_;
v_isShared_4594_ = v_isSharedCheck_4601_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_vs_4591_);
lean_dec(v_x_4579_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4601_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
size_t v_sz_4595_; size_t v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4599_; 
v_sz_4595_ = lean_array_size(v_vs_4591_);
v___x_4596_ = ((size_t)0ULL);
v___x_4597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4577_, v_e_4578_, v_sz_4595_, v___x_4596_, v_vs_4591_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4597_);
v___x_4599_ = v___x_4593_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4597_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4602_, lean_object* v_e_4603_, lean_object* v_x_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4602_, v_e_4603_, v_x_4604_);
lean_dec_ref(v_e_4603_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4606_, lean_object* v_e_4607_, lean_object* v_sz_4608_, lean_object* v_i_4609_, lean_object* v_bs_4610_){
_start:
{
size_t v_sz_boxed_4611_; size_t v_i_boxed_4612_; lean_object* v_res_4613_; 
v_sz_boxed_4611_ = lean_unbox_usize(v_sz_4608_);
lean_dec(v_sz_4608_);
v_i_boxed_4612_ = lean_unbox_usize(v_i_4609_);
lean_dec(v_i_4609_);
v_res_4613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4606_, v_e_4607_, v_sz_boxed_4611_, v_i_boxed_4612_, v_bs_4610_);
lean_dec_ref(v_e_4607_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4614_, lean_object* v_e_4615_, lean_object* v_t_4616_){
_start:
{
lean_object* v_root_4617_; lean_object* v_tail_4618_; lean_object* v_size_4619_; size_t v_shift_4620_; lean_object* v_tailOff_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4632_; 
v_root_4617_ = lean_ctor_get(v_t_4616_, 0);
v_tail_4618_ = lean_ctor_get(v_t_4616_, 1);
v_size_4619_ = lean_ctor_get(v_t_4616_, 2);
v_shift_4620_ = lean_ctor_get_usize(v_t_4616_, 4);
v_tailOff_4621_ = lean_ctor_get(v_t_4616_, 3);
v_isSharedCheck_4632_ = !lean_is_exclusive(v_t_4616_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4623_ = v_t_4616_;
v_isShared_4624_ = v_isSharedCheck_4632_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_tailOff_4621_);
lean_inc(v_size_4619_);
lean_inc(v_tail_4618_);
lean_inc(v_root_4617_);
lean_dec(v_t_4616_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4632_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4625_; size_t v_sz_4626_; size_t v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4630_; 
lean_inc(v_fvarId_4614_);
v___x_4625_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4614_, v_e_4615_, v_root_4617_);
v_sz_4626_ = lean_array_size(v_tail_4618_);
v___x_4627_ = ((size_t)0ULL);
v___x_4628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4614_, v_e_4615_, v_sz_4626_, v___x_4627_, v_tail_4618_);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 1, v___x_4628_);
lean_ctor_set(v___x_4623_, 0, v___x_4625_);
v___x_4630_ = v___x_4623_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4631_, 1, v___x_4628_);
lean_ctor_set(v_reuseFailAlloc_4631_, 2, v_size_4619_);
lean_ctor_set(v_reuseFailAlloc_4631_, 3, v_tailOff_4621_);
lean_ctor_set_usize(v_reuseFailAlloc_4631_, 4, v_shift_4620_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4633_, lean_object* v_e_4634_, lean_object* v_t_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4633_, v_e_4634_, v_t_4635_);
lean_dec_ref(v_e_4634_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4637_, lean_object* v_x_4638_){
_start:
{
lean_object* v___x_4639_; 
v___x_4639_ = lean_apply_1(v_f_4637_, v_x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4640_, lean_object* v_as_4641_, lean_object* v_i_4642_, lean_object* v_acc_4643_){
_start:
{
lean_object* v___x_4644_; uint8_t v___x_4645_; 
v___x_4644_ = lean_array_get_size(v_as_4641_);
v___x_4645_ = lean_nat_dec_eq(v_i_4642_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4646_ = lean_array_fget_borrowed(v_as_4641_, v_i_4642_);
lean_inc(v_f_4640_);
lean_inc(v___x_4646_);
v___x_4647_ = lean_apply_1(v_f_4640_, v___x_4646_);
v___x_4648_ = lean_unsigned_to_nat(1u);
v___x_4649_ = lean_nat_add(v_i_4642_, v___x_4648_);
lean_dec(v_i_4642_);
v___x_4650_ = lean_array_push(v_acc_4643_, v___x_4647_);
v_i_4642_ = v___x_4649_;
v_acc_4643_ = v___x_4650_;
goto _start;
}
else
{
lean_dec(v_i_4642_);
lean_dec(v_f_4640_);
return v_acc_4643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4652_, lean_object* v_as_4653_, lean_object* v_i_4654_, lean_object* v_acc_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4652_, v_as_4653_, v_i_4654_, v_acc_4655_);
lean_dec_ref(v_as_4653_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4657_, lean_object* v_as_4658_){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4659_ = lean_unsigned_to_nat(0u);
v___x_4660_ = lean_array_get_size(v_as_4658_);
v___x_4661_ = lean_mk_empty_array_with_capacity(v___x_4660_);
v___x_4662_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4657_, v_as_4658_, v___x_4659_, v___x_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4663_, lean_object* v_as_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4663_, v_as_4664_);
lean_dec_ref(v_as_4664_);
return v_res_4665_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4666_, size_t v_sz_4667_, size_t v_i_4668_, lean_object* v_bs_4669_){
_start:
{
uint8_t v___x_4670_; 
v___x_4670_ = lean_usize_dec_lt(v_i_4668_, v_sz_4667_);
if (v___x_4670_ == 0)
{
lean_dec(v_f_4666_);
return v_bs_4669_;
}
else
{
lean_object* v_v_4671_; lean_object* v___x_4672_; lean_object* v_bs_x27_4673_; lean_object* v___y_4675_; 
v_v_4671_ = lean_array_uget(v_bs_4669_, v_i_4668_);
v___x_4672_ = lean_unsigned_to_nat(0u);
v_bs_x27_4673_ = lean_array_uset(v_bs_4669_, v_i_4668_, v___x_4672_);
switch(lean_obj_tag(v_v_4671_))
{
case 0:
{
lean_object* v_key_4680_; lean_object* v_val_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4689_; 
v_key_4680_ = lean_ctor_get(v_v_4671_, 0);
v_val_4681_ = lean_ctor_get(v_v_4671_, 1);
v_isSharedCheck_4689_ = !lean_is_exclusive(v_v_4671_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4683_ = v_v_4671_;
v_isShared_4684_ = v_isSharedCheck_4689_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_val_4681_);
lean_inc(v_key_4680_);
lean_dec(v_v_4671_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4689_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4685_; lean_object* v___x_4687_; 
lean_inc(v_f_4666_);
v___x_4685_ = lean_apply_1(v_f_4666_, v_val_4681_);
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 1, v___x_4685_);
v___x_4687_ = v___x_4683_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_key_4680_);
lean_ctor_set(v_reuseFailAlloc_4688_, 1, v___x_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
v___y_4675_ = v___x_4687_;
goto v___jp_4674_;
}
}
}
case 1:
{
lean_object* v_node_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4698_; 
v_node_4690_ = lean_ctor_get(v_v_4671_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_v_4671_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4692_ = v_v_4671_;
v_isShared_4693_ = v_isSharedCheck_4698_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_node_4690_);
lean_dec(v_v_4671_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4698_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4694_; lean_object* v___x_4696_; 
lean_inc(v_f_4666_);
v___x_4694_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4666_, v_node_4690_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 0, v___x_4694_);
v___x_4696_ = v___x_4692_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4694_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
v___y_4675_ = v___x_4696_;
goto v___jp_4674_;
}
}
}
default: 
{
lean_object* v___x_4699_; 
v___x_4699_ = lean_box(2);
v___y_4675_ = v___x_4699_;
goto v___jp_4674_;
}
}
v___jp_4674_:
{
size_t v___x_4676_; size_t v___x_4677_; lean_object* v___x_4678_; 
v___x_4676_ = ((size_t)1ULL);
v___x_4677_ = lean_usize_add(v_i_4668_, v___x_4676_);
v___x_4678_ = lean_array_uset(v_bs_x27_4673_, v_i_4668_, v___y_4675_);
v_i_4668_ = v___x_4677_;
v_bs_4669_ = v___x_4678_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4666_ = stack[0].m_obj;
size_t v_sz_4667_ = stack[1].m_num;
size_t v_i_4668_ = stack[2].m_num;
lean_object* v_bs_4669_ = stack[3].m_obj;
lean_object* v_res_4700_;
v_res_4700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4666_, v_sz_4667_, v_i_4668_, v_bs_4669_);
stack->m_obj
 = v_res_4700_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4701_, lean_object* v_n_4702_){
_start:
{
if (lean_obj_tag(v_n_4702_) == 0)
{
lean_object* v_es_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4713_; 
v_es_4703_ = lean_ctor_get(v_n_4702_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v_n_4702_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4705_ = v_n_4702_;
v_isShared_4706_ = v_isSharedCheck_4713_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_es_4703_);
lean_dec(v_n_4702_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4713_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
size_t v_sz_4707_; size_t v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
v_sz_4707_ = lean_array_size(v_es_4703_);
v___x_4708_ = ((size_t)0ULL);
v___x_4709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4701_, v_sz_4707_, v___x_4708_, v_es_4703_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 0, v___x_4709_);
v___x_4711_ = v___x_4705_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
else
{
lean_object* v_ks_4714_; lean_object* v_vs_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4723_; 
v_ks_4714_ = lean_ctor_get(v_n_4702_, 0);
v_vs_4715_ = lean_ctor_get(v_n_4702_, 1);
v_isSharedCheck_4723_ = !lean_is_exclusive(v_n_4702_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4717_ = v_n_4702_;
v_isShared_4718_ = v_isSharedCheck_4723_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_vs_4715_);
lean_inc(v_ks_4714_);
lean_dec(v_n_4702_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4723_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v_val_4719_; lean_object* v___x_4721_; 
v_val_4719_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4701_, v_vs_4715_);
lean_dec_ref(v_vs_4715_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 1, v_val_4719_);
v___x_4721_ = v___x_4717_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_ks_4714_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v_val_4719_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4724_, lean_object* v_sz_4725_, lean_object* v_i_4726_, lean_object* v_bs_4727_){
_start:
{
size_t v_sz_boxed_4728_; size_t v_i_boxed_4729_; lean_object* v_res_4730_; 
v_sz_boxed_4728_ = lean_unbox_usize(v_sz_4725_);
lean_dec(v_sz_4725_);
v_i_boxed_4729_ = lean_unbox_usize(v_i_4726_);
lean_dec(v_i_4726_);
v_res_4730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4724_, v_sz_boxed_4728_, v_i_boxed_4729_, v_bs_4727_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4731_, lean_object* v_f_4732_){
_start:
{
lean_object* v___f_4733_; lean_object* v___x_4734_; 
v___f_4733_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4733_, 0, v_f_4732_);
v___x_4734_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4733_, v_pm_4731_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4735_, lean_object* v_e_4736_, lean_object* v_lctx_4737_){
_start:
{
lean_object* v_lctx_4738_; lean_object* v_fvarIdToDecl_4739_; lean_object* v_decls_4740_; lean_object* v_auxDeclToFullName_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4751_; 
v_lctx_4738_ = l_Lean_LocalContext_erase(v_lctx_4737_, v_fvarId_4735_);
v_fvarIdToDecl_4739_ = lean_ctor_get(v_lctx_4738_, 0);
v_decls_4740_ = lean_ctor_get(v_lctx_4738_, 1);
v_auxDeclToFullName_4741_ = lean_ctor_get(v_lctx_4738_, 2);
v_isSharedCheck_4751_ = !lean_is_exclusive(v_lctx_4738_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4743_ = v_lctx_4738_;
v_isShared_4744_ = v_isSharedCheck_4751_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_auxDeclToFullName_4741_);
lean_inc(v_decls_4740_);
lean_inc(v_fvarIdToDecl_4739_);
lean_dec(v_lctx_4738_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4751_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___f_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4749_; 
lean_inc_ref(v_e_4736_);
lean_inc(v_fvarId_4735_);
v___f_4745_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4745_, 0, v_fvarId_4735_);
lean_closure_set(v___f_4745_, 1, v_e_4736_);
v___x_4746_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4739_, v___f_4745_);
v___x_4747_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4735_, v_e_4736_, v_decls_4740_);
lean_dec_ref(v_e_4736_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 1, v___x_4747_);
lean_ctor_set(v___x_4743_, 0, v___x_4746_);
v___x_4749_ = v___x_4743_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v___x_4747_);
lean_ctor_set(v_reuseFailAlloc_4750_, 2, v_auxDeclToFullName_4741_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4752_, lean_object* v_00_u03c3_4753_, lean_object* v_pm_4754_, lean_object* v_f_4755_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4754_, v_f_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4757_, lean_object* v_f_4758_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4758_, v_pm_4757_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4760_, lean_object* v_00_u03c3_4761_, lean_object* v_pm_4762_, lean_object* v_f_4763_){
_start:
{
lean_object* v___x_4764_; 
v___x_4764_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4763_, v_pm_4762_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4765_, lean_object* v_00_u03b2_4766_, lean_object* v_00_u03c3_4767_, lean_object* v_f_4768_, lean_object* v_n_4769_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4768_, v_n_4769_);
return v___x_4770_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4771_, lean_object* v_00_u03b2_4772_, lean_object* v_00_u03c3_4773_, lean_object* v_f_4774_, size_t v_sz_4775_, size_t v_i_4776_, lean_object* v_bs_4777_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4774_, v_sz_4775_, v_i_4776_, v_bs_4777_);
return v___x_4778_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4774_ = stack[3].m_obj;
size_t v_sz_4775_ = stack[4].m_num;
size_t v_i_4776_ = stack[5].m_num;
lean_object* v_bs_4777_ = stack[6].m_obj;
lean_object* v_res_4779_;
v_res_4779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_box(0), lean_box(0), lean_box(0), v_f_4774_, v_sz_4775_, v_i_4776_, v_bs_4777_);
stack->m_obj
 = v_res_4779_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4780_, lean_object* v_00_u03b2_4781_, lean_object* v_00_u03c3_4782_, lean_object* v_f_4783_, lean_object* v_sz_4784_, lean_object* v_i_4785_, lean_object* v_bs_4786_){
_start:
{
size_t v_sz_boxed_4787_; size_t v_i_boxed_4788_; lean_object* v_res_4789_; 
v_sz_boxed_4787_ = lean_unbox_usize(v_sz_4784_);
lean_dec(v_sz_4784_);
v_i_boxed_4788_ = lean_unbox_usize(v_i_4785_);
lean_dec(v_i_4785_);
v_res_4789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4780_, v_00_u03b2_4781_, v_00_u03c3_4782_, v_f_4783_, v_sz_boxed_4787_, v_i_boxed_4788_, v_bs_4786_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4790_, lean_object* v_00_u03b2_4791_, lean_object* v_f_4792_, lean_object* v_as_4793_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4792_, v_as_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4795_, lean_object* v_00_u03b2_4796_, lean_object* v_f_4797_, lean_object* v_as_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4795_, v_00_u03b2_4796_, v_f_4797_, v_as_4798_);
lean_dec_ref(v_as_4798_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4800_, lean_object* v_00_u03b2_4801_, lean_object* v_f_4802_, lean_object* v_as_4803_, lean_object* v_i_4804_, lean_object* v_acc_4805_, lean_object* v_hle_4806_){
_start:
{
lean_object* v___x_4807_; 
v___x_4807_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4802_, v_as_4803_, v_i_4804_, v_acc_4805_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4808_, lean_object* v_00_u03b2_4809_, lean_object* v_f_4810_, lean_object* v_as_4811_, lean_object* v_i_4812_, lean_object* v_acc_4813_, lean_object* v_hle_4814_){
_start:
{
lean_object* v_res_4815_; 
v_res_4815_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4808_, v_00_u03b2_4809_, v_f_4810_, v_as_4811_, v_i_4812_, v_acc_4813_, v_hle_4814_);
lean_dec_ref(v_as_4811_);
return v_res_4815_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
