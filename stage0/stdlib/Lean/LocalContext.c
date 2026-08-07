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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_LocalDeclKind_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_23_){
_start:
{
lean_inc(v_default_23_);
return v_default_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_24_);
lean_dec(v_default_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_default_29_){
_start:
{
lean_inc(v_default_29_);
return v_default_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_default_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_LocalDeclKind_default_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_default_33_);
lean_dec(v_default_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_36_){
_start:
{
lean_inc(v_implDetail_36_);
return v_implDetail_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_37_);
lean_dec(v_implDetail_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_implDetail_42_){
_start:
{
lean_inc(v_implDetail_42_);
return v_implDetail_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_implDetail_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_implDetail_46_);
lean_dec(v_implDetail_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_49_){
_start:
{
lean_inc(v_auxDecl_49_);
return v_auxDecl_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_50_);
lean_dec(v_auxDecl_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_auxDecl_55_){
_start:
{
lean_inc(v_auxDecl_55_);
return v_auxDecl_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_auxDecl_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_auxDecl_59_);
lean_dec(v_auxDecl_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_77_, lean_object* v_prec_78_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_87_; lean_object* v___y_94_; 
switch(v_x_77_)
{
case 0:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1024u);
v___x_101_ = lean_nat_dec_le(v___x_100_, v_prec_78_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_80_ = v___x_102_;
goto v___jp_79_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_80_ = v___x_103_;
goto v___jp_79_;
}
}
case 1:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_78_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_87_ = v___x_106_;
goto v___jp_86_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_87_ = v___x_107_;
goto v___jp_86_;
}
}
default: 
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1024u);
v___x_109_ = lean_nat_dec_le(v___x_108_, v_prec_78_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_94_ = v___x_110_;
goto v___jp_93_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_94_ = v___x_111_;
goto v___jp_93_;
}
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_80_);
v___x_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_82_, 0, v___y_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = l_Repr_addAppParen(v___x_84_, v_prec_78_);
return v___x_85_;
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_78_);
return v___x_92_;
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v_prec_78_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_112_, lean_object* v_prec_113_){
_start:
{
uint8_t v_x_177__boxed_114_; lean_object* v_res_115_; 
v_x_177__boxed_114_ = lean_unbox(v_x_112_);
v_res_115_ = l_Lean_instReprLocalDeclKind_repr(v_x_177__boxed_114_, v_prec_113_);
lean_dec(v_prec_113_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_nat_dec_le(v_n_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_dec_le(v_n_118_, v___x_121_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 2;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 1;
return v___x_124_;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_LocalDeclKind_ofNat(v_n_126_);
lean_dec(v_n_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_129_, uint8_t v_y_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_LocalDeclKind_ctorIdx(v_x_129_);
v___x_132_ = l_Lean_LocalDeclKind_ctorIdx(v_y_130_);
v___x_133_ = lean_nat_dec_eq(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
lean_dec(v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_x_13__boxed_136_; uint8_t v_y_14__boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_x_13__boxed_136_ = lean_unbox(v_x_134_);
v_y_14__boxed_137_ = lean_unbox(v_y_135_);
v_res_138_ = l_Lean_instDecidableEqLocalDeclKind(v_x_13__boxed_136_, v_y_14__boxed_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_140_){
_start:
{
switch(v_x_140_)
{
case 0:
{
uint64_t v___x_141_; 
v___x_141_ = 0ULL;
return v___x_141_;
}
case 1:
{
uint64_t v___x_142_; 
v___x_142_ = 1ULL;
return v___x_142_;
}
default: 
{
uint64_t v___x_143_; 
v___x_143_ = 2ULL;
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_144_){
_start:
{
uint8_t v_x_40__boxed_145_; uint64_t v_res_146_; lean_object* v_r_147_; 
v_x_40__boxed_145_ = lean_unbox(v_x_144_);
v_res_146_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_145_);
v_r_147_ = lean_box_uint64(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_unsigned_to_nat(0u);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_unsigned_to_nat(1u);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_LocalDecl_ctorIdx(v_x_153_);
lean_dec_ref(v_x_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_155_, lean_object* v_k_156_){
_start:
{
if (lean_obj_tag(v_t_155_) == 0)
{
lean_object* v_index_157_; lean_object* v_fvarId_158_; lean_object* v_userName_159_; lean_object* v_type_160_; uint8_t v_bi_161_; uint8_t v_kind_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_index_157_ = lean_ctor_get(v_t_155_, 0);
lean_inc(v_index_157_);
v_fvarId_158_ = lean_ctor_get(v_t_155_, 1);
lean_inc(v_fvarId_158_);
v_userName_159_ = lean_ctor_get(v_t_155_, 2);
lean_inc(v_userName_159_);
v_type_160_ = lean_ctor_get(v_t_155_, 3);
lean_inc_ref(v_type_160_);
v_bi_161_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*4);
v_kind_162_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*4 + 1);
lean_dec_ref_known(v_t_155_, 4);
v___x_163_ = lean_box(v_bi_161_);
v___x_164_ = lean_box(v_kind_162_);
v___x_165_ = lean_apply_6(v_k_156_, v_index_157_, v_fvarId_158_, v_userName_159_, v_type_160_, v___x_163_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_index_166_; lean_object* v_fvarId_167_; lean_object* v_userName_168_; lean_object* v_type_169_; lean_object* v_value_170_; uint8_t v_nondep_171_; uint8_t v_kind_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_index_166_ = lean_ctor_get(v_t_155_, 0);
lean_inc(v_index_166_);
v_fvarId_167_ = lean_ctor_get(v_t_155_, 1);
lean_inc(v_fvarId_167_);
v_userName_168_ = lean_ctor_get(v_t_155_, 2);
lean_inc(v_userName_168_);
v_type_169_ = lean_ctor_get(v_t_155_, 3);
lean_inc_ref(v_type_169_);
v_value_170_ = lean_ctor_get(v_t_155_, 4);
lean_inc_ref(v_value_170_);
v_nondep_171_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*5);
v_kind_172_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*5 + 1);
lean_dec_ref_known(v_t_155_, 5);
v___x_173_ = lean_box(v_nondep_171_);
v___x_174_ = lean_box(v_kind_172_);
v___x_175_ = lean_apply_7(v_k_156_, v_index_166_, v_fvarId_167_, v_userName_168_, v_type_169_, v_value_170_, v___x_173_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_176_, lean_object* v_ctorIdx_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_178_, v_k_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_182_, lean_object* v_ctorIdx_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_k_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_LocalDecl_ctorElim(v_motive_182_, v_ctorIdx_183_, v_t_184_, v_h_185_, v_k_186_);
lean_dec(v_ctorIdx_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_188_, lean_object* v_cdecl_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_188_, v_cdecl_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_cdecl_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_192_, v_cdecl_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_196_, lean_object* v_ldecl_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_196_, v_ldecl_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_ldecl_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_200_, v_ldecl_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_box(0);
v___x_208_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_209_ = l_Lean_Expr_const___override(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = 0;
v___x_211_ = 0;
v___x_212_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_213_ = lean_box(0);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_213_);
lean_ctor_set(v___x_215_, 3, v___x_212_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*4, v___x_211_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*4 + 1, v___x_210_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_218_, lean_object* v_fvarId_219_, lean_object* v_userName_220_, lean_object* v_type_221_, uint8_t v_bi_222_){
_start:
{
uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_224_, 0, v_index_218_);
lean_ctor_set(v___x_224_, 1, v_fvarId_219_);
lean_ctor_set(v___x_224_, 2, v_userName_220_);
lean_ctor_set(v___x_224_, 3, v_type_221_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*4, v_bi_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*4 + 1, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_225_, lean_object* v_fvarId_226_, lean_object* v_userName_227_, lean_object* v_type_228_, lean_object* v_bi_229_){
_start:
{
uint8_t v_bi_boxed_230_; lean_object* v_res_231_; 
v_bi_boxed_230_ = lean_unbox(v_bi_229_);
v_res_231_ = lean_mk_local_decl(v_index_225_, v_fvarId_226_, v_userName_227_, v_type_228_, v_bi_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_232_, lean_object* v_fvarId_233_, lean_object* v_userName_234_, lean_object* v_type_235_, lean_object* v_val_236_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; 
v___x_237_ = 0;
v___x_238_ = 0;
v___x_239_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_239_, 0, v_index_232_);
lean_ctor_set(v___x_239_, 1, v_fvarId_233_);
lean_ctor_set(v___x_239_, 2, v_userName_234_);
lean_ctor_set(v___x_239_, 3, v_type_235_);
lean_ctor_set(v___x_239_, 4, v_val_236_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*5, v___x_237_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*5 + 1, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
uint8_t v_bi_241_; 
v_bi_241_ = lean_ctor_get_uint8(v_x_240_, sizeof(void*)*4);
lean_dec_ref_known(v_x_240_, 4);
return v_bi_241_;
}
else
{
uint8_t v___x_242_; 
lean_dec_ref(v_x_240_);
v___x_242_ = 0;
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = lean_local_decl_binder_info(v_x_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_246_, uint8_t v_x_247_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
else
{
uint8_t v_nondep_249_; 
v_nondep_249_ = lean_ctor_get_uint8(v_x_246_, sizeof(void*)*5);
if (v_nondep_249_ == 0)
{
uint8_t v___x_250_; 
v___x_250_ = 1;
return v___x_250_;
}
else
{
return v_x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_x_53__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_x_53__boxed_253_ = lean_unbox(v_x_252_);
v_res_254_ = l_Lean_LocalDecl_isLet(v_x_251_, v_x_53__boxed_253_);
lean_dec_ref(v_x_251_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_256_){
_start:
{
lean_object* v_index_257_; 
v_index_257_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_index_257_);
return v_index_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_LocalDecl_index(v_x_258_);
lean_dec_ref(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v_fvarId_262_; lean_object* v_userName_263_; lean_object* v_type_264_; uint8_t v_bi_265_; uint8_t v_kind_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_fvarId_262_ = lean_ctor_get(v_x_260_, 1);
v_userName_263_ = lean_ctor_get(v_x_260_, 2);
v_type_264_ = lean_ctor_get(v_x_260_, 3);
v_bi_265_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*4);
v_kind_266_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*4 + 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_274_);
v___x_268_ = v_x_260_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_type_264_);
lean_inc(v_userName_263_);
lean_inc(v_fvarId_262_);
lean_dec(v_x_260_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_x_261_);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_fvarId_262_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_userName_263_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_type_264_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*4, v_bi_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*4 + 1, v_kind_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_fvarId_275_; lean_object* v_userName_276_; lean_object* v_type_277_; lean_object* v_value_278_; uint8_t v_nondep_279_; uint8_t v_kind_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_fvarId_275_ = lean_ctor_get(v_x_260_, 1);
v_userName_276_ = lean_ctor_get(v_x_260_, 2);
v_type_277_ = lean_ctor_get(v_x_260_, 3);
v_value_278_ = lean_ctor_get(v_x_260_, 4);
v_nondep_279_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*5);
v_kind_280_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*5 + 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_288_);
v___x_282_ = v_x_260_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_value_278_);
lean_inc(v_type_277_);
lean_inc(v_userName_276_);
lean_inc(v_fvarId_275_);
lean_dec(v_x_260_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_x_261_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_fvarId_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_userName_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_type_277_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_value_278_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*5, v_nondep_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*5 + 1, v_kind_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_289_){
_start:
{
lean_object* v_fvarId_290_; 
v_fvarId_290_ = lean_ctor_get(v_x_289_, 1);
lean_inc(v_fvarId_290_);
return v_fvarId_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_LocalDecl_fvarId(v_x_291_);
lean_dec_ref(v_x_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_293_){
_start:
{
lean_object* v_userName_294_; 
v_userName_294_ = lean_ctor_get(v_x_293_, 2);
lean_inc(v_userName_294_);
return v_userName_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_LocalDecl_userName(v_x_295_);
lean_dec_ref(v_x_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_297_){
_start:
{
lean_object* v_type_298_; 
v_type_298_ = lean_ctor_get(v_x_297_, 3);
lean_inc_ref(v_type_298_);
return v_type_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_LocalDecl_type(v_x_299_);
lean_dec_ref(v_x_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_index_303_; lean_object* v_fvarId_304_; lean_object* v_userName_305_; uint8_t v_bi_306_; uint8_t v_kind_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_index_303_ = lean_ctor_get(v_x_301_, 0);
v_fvarId_304_ = lean_ctor_get(v_x_301_, 1);
v_userName_305_ = lean_ctor_get(v_x_301_, 2);
v_bi_306_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*4);
v_kind_307_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*4 + 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v_x_301_, 3);
lean_dec(v_unused_315_);
v___x_309_ = v_x_301_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_userName_305_);
lean_inc(v_fvarId_304_);
lean_inc(v_index_303_);
lean_dec(v_x_301_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 3, v_x_302_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_index_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_fvarId_304_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_userName_305_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_x_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*4, v_bi_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*4 + 1, v_kind_307_);
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
lean_object* v_index_316_; lean_object* v_fvarId_317_; lean_object* v_userName_318_; lean_object* v_value_319_; uint8_t v_nondep_320_; uint8_t v_kind_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_index_316_ = lean_ctor_get(v_x_301_, 0);
v_fvarId_317_ = lean_ctor_get(v_x_301_, 1);
v_userName_318_ = lean_ctor_get(v_x_301_, 2);
v_value_319_ = lean_ctor_get(v_x_301_, 4);
v_nondep_320_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*5);
v_kind_321_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*5 + 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_x_301_, 3);
lean_dec(v_unused_329_);
v___x_323_ = v_x_301_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_value_319_);
lean_inc(v_userName_318_);
lean_inc(v_fvarId_317_);
lean_inc(v_index_316_);
lean_dec(v_x_301_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 3, v_x_302_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_index_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_fvarId_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_userName_318_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_x_302_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_value_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*5, v_nondep_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*5 + 1, v_kind_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
uint8_t v_bi_331_; 
v_bi_331_ = lean_ctor_get_uint8(v_x_330_, sizeof(void*)*4);
return v_bi_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lean_LocalDecl_binderInfo(v_x_333_);
lean_dec_ref(v_x_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
uint8_t v_kind_337_; 
v_kind_337_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*4 + 1);
return v_kind_337_;
}
else
{
uint8_t v_kind_338_; 
v_kind_338_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*5 + 1);
return v_kind_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Lean_LocalDecl_kind(v_x_339_);
lean_dec_ref(v_x_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_342_){
_start:
{
uint8_t v___y_344_; 
if (lean_obj_tag(v_d_342_) == 0)
{
uint8_t v_kind_347_; 
v_kind_347_ = lean_ctor_get_uint8(v_d_342_, sizeof(void*)*4 + 1);
v___y_344_ = v_kind_347_;
goto v___jp_343_;
}
else
{
uint8_t v_kind_348_; 
v_kind_348_ = lean_ctor_get_uint8(v_d_342_, sizeof(void*)*5 + 1);
v___y_344_ = v_kind_348_;
goto v___jp_343_;
}
v___jp_343_:
{
uint8_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 2;
v___x_346_ = l_Lean_instDecidableEqLocalDeclKind(v___y_344_, v___x_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Lean_LocalDecl_isAuxDecl(v_d_349_);
lean_dec_ref(v_d_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_352_){
_start:
{
uint8_t v___y_354_; 
if (lean_obj_tag(v_d_352_) == 0)
{
uint8_t v_kind_359_; 
v_kind_359_ = lean_ctor_get_uint8(v_d_352_, sizeof(void*)*4 + 1);
v___y_354_ = v_kind_359_;
goto v___jp_353_;
}
else
{
uint8_t v_kind_360_; 
v_kind_360_ = lean_ctor_get_uint8(v_d_352_, sizeof(void*)*5 + 1);
v___y_354_ = v_kind_360_;
goto v___jp_353_;
}
v___jp_353_:
{
uint8_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 0;
v___x_356_ = l_Lean_instDecidableEqLocalDeclKind(v___y_354_, v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
v___x_357_ = 1;
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = 0;
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_LocalDecl_isImplementationDetail(v_d_361_);
lean_dec_ref(v_d_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_364_, uint8_t v_x_365_){
_start:
{
if (lean_obj_tag(v_x_364_) == 1)
{
uint8_t v_nondep_366_; 
v_nondep_366_ = lean_ctor_get_uint8(v_x_364_, sizeof(void*)*5);
if (v_nondep_366_ == 0)
{
lean_object* v_value_367_; lean_object* v___x_368_; 
v_value_367_ = lean_ctor_get(v_x_364_, 4);
lean_inc_ref(v_value_367_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v_value_367_);
return v___x_368_;
}
else
{
if (v_x_365_ == 1)
{
lean_object* v_value_369_; lean_object* v___x_370_; 
v_value_369_ = lean_ctor_get(v_x_364_, 4);
lean_inc_ref(v_value_369_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_value_369_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
}
else
{
lean_object* v___x_372_; 
v___x_372_ = lean_box(0);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
uint8_t v_x_57__boxed_375_; lean_object* v_res_376_; 
v_x_57__boxed_375_ = lean_unbox(v_x_374_);
v_res_376_ = l_Lean_LocalDecl_value_x3f(v_x_373_, v_x_57__boxed_375_);
lean_dec_ref(v_x_373_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Lean_instInhabitedExpr;
v___x_379_ = lean_panic_fn_borrowed(v___x_378_, v_msg_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_383_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_384_ = lean_unsigned_to_nat(54u);
v___x_385_ = lean_unsigned_to_nat(172u);
v___x_386_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_387_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_388_ = l_mkPanicMessageWithDecl(v___x_387_, v___x_386_, v___x_385_, v___x_384_, v___x_383_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_390_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_391_ = lean_unsigned_to_nat(54u);
v___x_392_ = lean_unsigned_to_nat(175u);
v___x_393_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_394_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_395_ = l_mkPanicMessageWithDecl(v___x_394_, v___x_393_, v___x_392_, v___x_391_, v___x_390_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_396_, uint8_t v_x_397_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_399_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_398_);
return v___x_399_;
}
else
{
uint8_t v_nondep_400_; 
v_nondep_400_ = lean_ctor_get_uint8(v_x_396_, sizeof(void*)*5);
if (v_nondep_400_ == 0)
{
lean_object* v_value_401_; 
v_value_401_ = lean_ctor_get(v_x_396_, 4);
lean_inc_ref(v_value_401_);
return v_value_401_;
}
else
{
if (v_x_397_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_403_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_402_);
return v___x_403_;
}
else
{
lean_object* v_value_404_; 
v_value_404_ = lean_ctor_get(v_x_396_, 4);
lean_inc_ref(v_value_404_);
return v_value_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
uint8_t v_x_143__boxed_407_; lean_object* v_res_408_; 
v_x_143__boxed_407_ = lean_unbox(v_x_406_);
v_res_408_ = l_Lean_LocalDecl_value(v_x_405_, v_x_143__boxed_407_);
lean_dec_ref(v_x_405_);
return v_res_408_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_409_, uint8_t v_x_410_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
else
{
uint8_t v_nondep_412_; 
v_nondep_412_ = lean_ctor_get_uint8(v_x_409_, sizeof(void*)*5);
if (v_nondep_412_ == 0)
{
uint8_t v___x_413_; 
v___x_413_ = 1;
return v___x_413_;
}
else
{
return v_x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
uint8_t v_x_72__boxed_416_; uint8_t v_res_417_; lean_object* v_r_418_; 
v_x_72__boxed_416_ = lean_unbox(v_x_415_);
v_res_417_ = l_Lean_LocalDecl_hasValue(v_x_414_, v_x_72__boxed_416_);
lean_dec_ref(v_x_414_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_419_) == 1)
{
lean_object* v_index_421_; lean_object* v_fvarId_422_; lean_object* v_userName_423_; lean_object* v_type_424_; uint8_t v_nondep_425_; uint8_t v_kind_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_index_421_ = lean_ctor_get(v_x_419_, 0);
v_fvarId_422_ = lean_ctor_get(v_x_419_, 1);
v_userName_423_ = lean_ctor_get(v_x_419_, 2);
v_type_424_ = lean_ctor_get(v_x_419_, 3);
v_nondep_425_ = lean_ctor_get_uint8(v_x_419_, sizeof(void*)*5);
v_kind_426_ = lean_ctor_get_uint8(v_x_419_, sizeof(void*)*5 + 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_419_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v_x_419_, 4);
lean_dec(v_unused_434_);
v___x_428_ = v_x_419_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_type_424_);
lean_inc(v_userName_423_);
lean_inc(v_fvarId_422_);
lean_inc(v_index_421_);
lean_dec(v_x_419_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 4, v_x_420_);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_index_421_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_fvarId_422_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_userName_423_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_type_424_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_x_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*5, v_nondep_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*5 + 1, v_kind_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
lean_dec_ref(v_x_420_);
return v_x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_435_, uint8_t v_x_436_){
_start:
{
if (lean_obj_tag(v_x_435_) == 1)
{
lean_object* v_index_437_; lean_object* v_fvarId_438_; lean_object* v_userName_439_; lean_object* v_type_440_; lean_object* v_value_441_; uint8_t v_kind_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_index_437_ = lean_ctor_get(v_x_435_, 0);
v_fvarId_438_ = lean_ctor_get(v_x_435_, 1);
v_userName_439_ = lean_ctor_get(v_x_435_, 2);
v_type_440_ = lean_ctor_get(v_x_435_, 3);
v_value_441_ = lean_ctor_get(v_x_435_, 4);
v_kind_442_ = lean_ctor_get_uint8(v_x_435_, sizeof(void*)*5 + 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_435_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v_x_435_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_value_441_);
lean_inc(v_type_440_);
lean_inc(v_userName_439_);
lean_inc(v_fvarId_438_);
lean_inc(v_index_437_);
lean_dec(v_x_435_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_index_437_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_fvarId_438_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_userName_439_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_type_440_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v_value_441_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*5 + 1, v_kind_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*5, v_x_436_);
return v___x_447_;
}
}
}
else
{
return v_x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
uint8_t v_x_27__boxed_452_; lean_object* v_res_453_; 
v_x_27__boxed_452_ = lean_unbox(v_x_451_);
v_res_453_ = l_Lean_LocalDecl_setNondep(v_x_450_, v_x_27__boxed_452_);
return v_res_453_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 1)
{
uint8_t v_nondep_455_; 
v_nondep_455_ = lean_ctor_get_uint8(v_x_454_, sizeof(void*)*5);
return v_nondep_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_LocalDecl_isNondep(v_x_457_);
lean_dec_ref(v_x_457_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
lean_object* v_index_462_; lean_object* v_fvarId_463_; lean_object* v_type_464_; uint8_t v_bi_465_; uint8_t v_kind_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
v_index_462_ = lean_ctor_get(v_x_460_, 0);
v_fvarId_463_ = lean_ctor_get(v_x_460_, 1);
v_type_464_ = lean_ctor_get(v_x_460_, 3);
v_bi_465_ = lean_ctor_get_uint8(v_x_460_, sizeof(void*)*4);
v_kind_466_ = lean_ctor_get_uint8(v_x_460_, sizeof(void*)*4 + 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_x_460_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v_x_460_, 2);
lean_dec(v_unused_474_);
v___x_468_ = v_x_460_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_type_464_);
lean_inc(v_fvarId_463_);
lean_inc(v_index_462_);
lean_dec(v_x_460_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 2, v_x_461_);
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_index_462_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_fvarId_463_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_x_461_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v_type_464_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, sizeof(void*)*4, v_bi_465_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, sizeof(void*)*4 + 1, v_kind_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
else
{
lean_object* v_index_475_; lean_object* v_fvarId_476_; lean_object* v_type_477_; lean_object* v_value_478_; uint8_t v_nondep_479_; uint8_t v_kind_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_index_475_ = lean_ctor_get(v_x_460_, 0);
v_fvarId_476_ = lean_ctor_get(v_x_460_, 1);
v_type_477_ = lean_ctor_get(v_x_460_, 3);
v_value_478_ = lean_ctor_get(v_x_460_, 4);
v_nondep_479_ = lean_ctor_get_uint8(v_x_460_, sizeof(void*)*5);
v_kind_480_ = lean_ctor_get_uint8(v_x_460_, sizeof(void*)*5 + 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_x_460_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_x_460_, 2);
lean_dec(v_unused_488_);
v___x_482_ = v_x_460_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_value_478_);
lean_inc(v_type_477_);
lean_inc(v_fvarId_476_);
lean_inc(v_index_475_);
lean_dec(v_x_460_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 2, v_x_461_);
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_index_475_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_fvarId_476_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_x_461_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_type_477_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_value_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*5, v_nondep_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*5 + 1, v_kind_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = l_Lean_instInhabitedLocalDecl_default;
v___x_491_ = lean_panic_fn_borrowed(v___x_490_, v_msg_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_494_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_495_ = lean_unsigned_to_nat(38u);
v___x_496_ = lean_unsigned_to_nat(237u);
v___x_497_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_498_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_499_ = l_mkPanicMessageWithDecl(v___x_498_, v___x_497_, v___x_496_, v___x_495_, v___x_494_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_500_, uint8_t v_x_501_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v_index_502_; lean_object* v_fvarId_503_; lean_object* v_userName_504_; lean_object* v_type_505_; uint8_t v_kind_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_index_502_ = lean_ctor_get(v_x_500_, 0);
v_fvarId_503_ = lean_ctor_get(v_x_500_, 1);
v_userName_504_ = lean_ctor_get(v_x_500_, 2);
v_type_505_ = lean_ctor_get(v_x_500_, 3);
v_kind_506_ = lean_ctor_get_uint8(v_x_500_, sizeof(void*)*4 + 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v_x_500_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_type_505_);
lean_inc(v_userName_504_);
lean_inc(v_fvarId_503_);
lean_inc(v_index_502_);
lean_dec(v_x_500_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_index_502_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_fvarId_503_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_userName_504_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_type_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_512_, sizeof(void*)*4 + 1, v_kind_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*4, v_x_501_);
return v___x_511_;
}
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref_known(v_x_500_, 5);
v___x_514_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_515_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
uint8_t v_x_84__boxed_518_; lean_object* v_res_519_; 
v_x_84__boxed_518_ = lean_unbox(v_x_517_);
v_res_519_ = l_Lean_LocalDecl_setBinderInfo(v_x_516_, v_x_84__boxed_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_520_){
_start:
{
lean_object* v_fvarId_521_; lean_object* v___x_522_; 
v_fvarId_521_ = lean_ctor_get(v_decl_520_, 1);
lean_inc(v_fvarId_521_);
lean_dec_ref(v_decl_520_);
v___x_522_ = l_Lean_mkFVar(v_fvarId_521_);
return v___x_522_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_object* v_type_524_; uint8_t v___x_525_; 
v_type_524_ = lean_ctor_get(v_x_523_, 3);
v___x_525_ = l_Lean_Expr_hasExprMVar(v_type_524_);
return v___x_525_;
}
else
{
lean_object* v_type_526_; lean_object* v_value_527_; uint8_t v___x_528_; 
v_type_526_ = lean_ctor_get(v_x_523_, 3);
v_value_527_ = lean_ctor_get(v_x_523_, 4);
v___x_528_ = l_Lean_Expr_hasExprMVar(v_type_526_);
if (v___x_528_ == 0)
{
uint8_t v___x_529_; 
v___x_529_ = l_Lean_Expr_hasExprMVar(v_value_527_);
return v___x_529_;
}
else
{
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Lean_LocalDecl_hasExprMVar(v_x_530_);
lean_dec_ref(v_x_530_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_533_, uint8_t v_x_534_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v_index_535_; lean_object* v_fvarId_536_; lean_object* v_userName_537_; lean_object* v_type_538_; uint8_t v_bi_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_index_535_ = lean_ctor_get(v_x_533_, 0);
v_fvarId_536_ = lean_ctor_get(v_x_533_, 1);
v_userName_537_ = lean_ctor_get(v_x_533_, 2);
v_type_538_ = lean_ctor_get(v_x_533_, 3);
v_bi_539_ = lean_ctor_get_uint8(v_x_533_, sizeof(void*)*4);
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
lean_ctor_set_uint8(v_reuseFailAlloc_545_, sizeof(void*)*4, v_bi_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*4 + 1, v_x_534_);
return v___x_544_;
}
}
}
else
{
lean_object* v_index_547_; lean_object* v_fvarId_548_; lean_object* v_userName_549_; lean_object* v_type_550_; lean_object* v_value_551_; uint8_t v_nondep_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_index_547_ = lean_ctor_get(v_x_533_, 0);
v_fvarId_548_ = lean_ctor_get(v_x_533_, 1);
v_userName_549_ = lean_ctor_get(v_x_533_, 2);
v_type_550_ = lean_ctor_get(v_x_533_, 3);
v_value_551_ = lean_ctor_get(v_x_533_, 4);
v_nondep_552_ = lean_ctor_get_uint8(v_x_533_, sizeof(void*)*5);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_533_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v_x_533_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_value_551_);
lean_inc(v_type_550_);
lean_inc(v_userName_549_);
lean_inc(v_fvarId_548_);
lean_inc(v_index_547_);
lean_dec(v_x_533_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_index_547_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_fvarId_548_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_userName_549_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_type_550_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_value_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_558_, sizeof(void*)*5, v_nondep_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*5 + 1, v_x_534_);
return v___x_557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
uint8_t v_x_31__boxed_562_; lean_object* v_res_563_; 
v_x_31__boxed_562_ = lean_unbox(v_x_561_);
v_res_563_ = l_Lean_LocalDecl_setKind(v_x_560_, v_x_31__boxed_562_);
return v_res_563_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_564_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(32u);
v___x_568_ = lean_mk_empty_array_with_capacity(v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_570_ = ((size_t)5ULL);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_unsigned_to_nat(32u);
v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
v___x_574_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_575_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_573_);
lean_ctor_set(v___x_575_, 2, v___x_571_);
lean_ctor_set(v___x_575_, 3, v___x_571_);
lean_ctor_set_usize(v___x_575_, 4, v___x_570_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_576_ = lean_box(1);
v___x_577_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_578_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_576_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_instInhabitedLocalContext_default;
return v___x_581_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_unsigned_to_nat(32u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
lean_dec_ref(v___x_584_);
v___x_585_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_unsigned_to_nat(32u);
v___x_587_ = lean_mk_empty_array_with_capacity(v___x_586_);
lean_dec_ref(v___x_587_);
v___x_588_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_588_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_591_);
lean_dec_ref(v_x_591_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_594_, lean_object* v_x_595_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_597_, lean_object* v_x_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_597_, v_x_598_);
lean_dec_ref(v_x_598_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* v_lctx_601_){
_start:
{
lean_object* v_fvarIdToDecl_602_; uint8_t v___x_603_; 
v_fvarIdToDecl_602_ = lean_ctor_get(v_lctx_601_, 0);
lean_inc_ref(v_fvarIdToDecl_602_);
lean_dec_ref(v_lctx_601_);
v___x_603_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_602_);
lean_dec_ref(v_fvarIdToDecl_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = lean_local_ctx_is_empty(v_lctx_604_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v_ks_611_; lean_object* v_vs_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_636_; 
v_ks_611_ = lean_ctor_get(v_x_607_, 0);
v_vs_612_ = lean_ctor_get(v_x_607_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_x_607_);
if (v_isSharedCheck_636_ == 0)
{
v___x_614_ = v_x_607_;
v_isShared_615_ = v_isSharedCheck_636_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_vs_612_);
lean_inc(v_ks_611_);
lean_dec(v_x_607_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_636_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_array_get_size(v_ks_611_);
v___x_617_ = lean_nat_dec_lt(v_x_608_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
lean_dec(v_x_608_);
v___x_618_ = lean_array_push(v_ks_611_, v_x_609_);
v___x_619_ = lean_array_push(v_vs_612_, v_x_610_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_619_);
lean_ctor_set(v___x_614_, 0, v___x_618_);
v___x_621_ = v___x_614_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v_k_x27_623_; uint8_t v___x_624_; 
v_k_x27_623_ = lean_array_fget_borrowed(v_ks_611_, v_x_608_);
v___x_624_ = l_Lean_instBEqFVarId_beq(v_x_609_, v_k_x27_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_626_; 
if (v_isShared_615_ == 0)
{
v___x_626_ = v___x_614_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_ks_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_vs_612_);
v___x_626_ = v_reuseFailAlloc_630_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_x_608_, v___x_627_);
lean_dec(v_x_608_);
v_x_607_ = v___x_626_;
v_x_608_ = v___x_628_;
goto _start;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_631_ = lean_array_fset(v_ks_611_, v_x_608_, v_x_609_);
v___x_632_ = lean_array_fset(v_vs_612_, v_x_608_, v_x_610_);
lean_dec(v_x_608_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_632_);
lean_ctor_set(v___x_614_, 0, v___x_631_);
v___x_634_ = v___x_614_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_637_, lean_object* v_k_638_, lean_object* v_v_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_637_, v___x_640_, v_k_638_, v_v_639_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_643_, size_t v_x_644_, size_t v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v_es_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v_j_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_es_648_ = lean_ctor_get(v_x_643_, 0);
v___x_649_ = ((size_t)31ULL);
v___x_650_ = lean_usize_land(v_x_644_, v___x_649_);
v_j_651_ = lean_usize_to_nat(v___x_650_);
v___x_652_ = lean_array_get_size(v_es_648_);
v___x_653_ = lean_nat_dec_lt(v_j_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_dec(v_j_651_);
lean_dec(v_x_647_);
lean_dec(v_x_646_);
return v_x_643_;
}
else
{
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_692_; 
lean_inc_ref(v_es_648_);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v_x_643_, 0);
lean_dec(v_unused_693_);
v___x_655_ = v_x_643_;
v_isShared_656_ = v_isSharedCheck_692_;
goto v_resetjp_654_;
}
else
{
lean_dec(v_x_643_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_692_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_v_657_; lean_object* v___x_658_; lean_object* v_xs_x27_659_; lean_object* v___y_661_; 
v_v_657_ = lean_array_fget(v_es_648_, v_j_651_);
v___x_658_ = lean_box(0);
v_xs_x27_659_ = lean_array_fset(v_es_648_, v_j_651_, v___x_658_);
switch(lean_obj_tag(v_v_657_))
{
case 0:
{
lean_object* v_key_666_; lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_677_; 
v_key_666_ = lean_ctor_get(v_v_657_, 0);
v_val_667_ = lean_ctor_get(v_v_657_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_v_657_);
if (v_isSharedCheck_677_ == 0)
{
v___x_669_ = v_v_657_;
v_isShared_670_ = v_isSharedCheck_677_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_inc(v_key_666_);
lean_dec(v_v_657_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_677_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
uint8_t v___x_671_; 
v___x_671_ = l_Lean_instBEqFVarId_beq(v_x_646_, v_key_666_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_del_object(v___x_669_);
v___x_672_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_666_, v_val_667_, v_x_646_, v_x_647_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___y_661_ = v___x_673_;
goto v___jp_660_;
}
else
{
lean_object* v___x_675_; 
lean_dec(v_val_667_);
lean_dec(v_key_666_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v_x_647_);
lean_ctor_set(v___x_669_, 0, v_x_646_);
v___x_675_ = v___x_669_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_x_646_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_x_647_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
v___y_661_ = v___x_675_;
goto v___jp_660_;
}
}
}
}
case 1:
{
lean_object* v_node_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_690_; 
v_node_678_ = lean_ctor_get(v_v_657_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v_v_657_);
if (v_isSharedCheck_690_ == 0)
{
v___x_680_ = v_v_657_;
v_isShared_681_ = v_isSharedCheck_690_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_node_678_);
lean_dec(v_v_657_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_690_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
size_t v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_682_ = ((size_t)5ULL);
v___x_683_ = lean_usize_shift_right(v_x_644_, v___x_682_);
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_add(v_x_645_, v___x_684_);
v___x_686_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_678_, v___x_683_, v___x_685_, v_x_646_, v_x_647_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_686_);
v___x_688_ = v___x_680_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v___y_661_ = v___x_688_;
goto v___jp_660_;
}
}
}
default: 
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_x_646_);
lean_ctor_set(v___x_691_, 1, v_x_647_);
v___y_661_ = v___x_691_;
goto v___jp_660_;
}
}
v___jp_660_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_array_fset(v_xs_x27_659_, v_j_651_, v___y_661_);
lean_dec(v_j_651_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_662_);
v___x_664_ = v___x_655_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
else
{
lean_object* v_ks_694_; lean_object* v_vs_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_715_; 
v_ks_694_ = lean_ctor_get(v_x_643_, 0);
v_vs_695_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_715_ == 0)
{
v___x_697_ = v_x_643_;
v_isShared_698_ = v_isSharedCheck_715_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_vs_695_);
lean_inc(v_ks_694_);
lean_dec(v_x_643_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_715_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_ks_694_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_vs_695_);
v___x_700_ = v_reuseFailAlloc_714_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v_newNode_701_; uint8_t v___y_703_; size_t v___x_709_; uint8_t v___x_710_; 
v_newNode_701_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_700_, v_x_646_, v_x_647_);
v___x_709_ = ((size_t)7ULL);
v___x_710_ = lean_usize_dec_le(v___x_709_, v_x_645_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_701_);
v___x_712_ = lean_unsigned_to_nat(4u);
v___x_713_ = lean_nat_dec_lt(v___x_711_, v___x_712_);
lean_dec(v___x_711_);
v___y_703_ = v___x_713_;
goto v___jp_702_;
}
else
{
v___y_703_ = v___x_710_;
goto v___jp_702_;
}
v___jp_702_:
{
if (v___y_703_ == 0)
{
lean_object* v_ks_704_; lean_object* v_vs_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_ks_704_ = lean_ctor_get(v_newNode_701_, 0);
lean_inc_ref(v_ks_704_);
v_vs_705_ = lean_ctor_get(v_newNode_701_, 1);
lean_inc_ref(v_vs_705_);
lean_dec_ref(v_newNode_701_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_708_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_645_, v_ks_704_, v_vs_705_, v___x_706_, v___x_707_);
lean_dec_ref(v_vs_705_);
lean_dec_ref(v_ks_704_);
return v___x_708_;
}
else
{
return v_newNode_701_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_716_, lean_object* v_keys_717_, lean_object* v_vals_718_, lean_object* v_i_719_, lean_object* v_entries_720_){
_start:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_array_get_size(v_keys_717_);
v___x_722_ = lean_nat_dec_lt(v_i_719_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec(v_i_719_);
return v_entries_720_;
}
else
{
lean_object* v_k_723_; lean_object* v_v_724_; uint64_t v___x_725_; size_t v_h_726_; size_t v___x_727_; lean_object* v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v_h_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_k_723_ = lean_array_fget_borrowed(v_keys_717_, v_i_719_);
v_v_724_ = lean_array_fget_borrowed(v_vals_718_, v_i_719_);
v___x_725_ = l_Lean_instHashableFVarId_hash(v_k_723_);
v_h_726_ = lean_uint64_to_usize(v___x_725_);
v___x_727_ = ((size_t)5ULL);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_sub(v_depth_716_, v___x_729_);
v___x_731_ = lean_usize_mul(v___x_727_, v___x_730_);
v_h_732_ = lean_usize_shift_right(v_h_726_, v___x_731_);
v___x_733_ = lean_nat_add(v_i_719_, v___x_728_);
lean_dec(v_i_719_);
lean_inc(v_v_724_);
lean_inc(v_k_723_);
v___x_734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_720_, v_h_732_, v_depth_716_, v_k_723_, v_v_724_);
v_i_719_ = v___x_733_;
v_entries_720_ = v___x_734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_736_, lean_object* v_keys_737_, lean_object* v_vals_738_, lean_object* v_i_739_, lean_object* v_entries_740_){
_start:
{
size_t v_depth_boxed_741_; lean_object* v_res_742_; 
v_depth_boxed_741_ = lean_unbox_usize(v_depth_736_);
lean_dec(v_depth_736_);
v_res_742_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_741_, v_keys_737_, v_vals_738_, v_i_739_, v_entries_740_);
lean_dec_ref(v_vals_738_);
lean_dec_ref(v_keys_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
size_t v_x_357__boxed_748_; size_t v_x_358__boxed_749_; lean_object* v_res_750_; 
v_x_357__boxed_748_ = lean_unbox_usize(v_x_744_);
lean_dec(v_x_744_);
v_x_358__boxed_749_ = lean_unbox_usize(v_x_745_);
lean_dec(v_x_745_);
v_res_750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_743_, v_x_357__boxed_748_, v_x_358__boxed_749_, v_x_746_, v_x_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
uint64_t v___x_754_; size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_754_ = l_Lean_instHashableFVarId_hash(v_x_752_);
v___x_755_ = lean_uint64_to_usize(v___x_754_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_751_, v___x_755_, v___x_756_, v_x_752_, v_x_753_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_758_, lean_object* v_fvarId_759_, lean_object* v_userName_760_, lean_object* v_type_761_, uint8_t v_bi_762_, uint8_t v_kind_763_){
_start:
{
lean_object* v_decls_764_; lean_object* v_fvarIdToDecl_765_; lean_object* v_auxDeclToFullName_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_778_; 
v_decls_764_ = lean_ctor_get(v_lctx_758_, 1);
v_fvarIdToDecl_765_ = lean_ctor_get(v_lctx_758_, 0);
v_auxDeclToFullName_766_ = lean_ctor_get(v_lctx_758_, 2);
v_isSharedCheck_778_ = !lean_is_exclusive(v_lctx_758_);
if (v_isSharedCheck_778_ == 0)
{
v___x_768_ = v_lctx_758_;
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_auxDeclToFullName_766_);
lean_inc(v_decls_764_);
lean_inc(v_fvarIdToDecl_765_);
lean_dec(v_lctx_758_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_size_770_; lean_object* v_decl_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v_size_770_ = lean_ctor_get(v_decls_764_, 2);
lean_inc(v_fvarId_759_);
lean_inc(v_size_770_);
v_decl_771_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_771_, 0, v_size_770_);
lean_ctor_set(v_decl_771_, 1, v_fvarId_759_);
lean_ctor_set(v_decl_771_, 2, v_userName_760_);
lean_ctor_set(v_decl_771_, 3, v_type_761_);
lean_ctor_set_uint8(v_decl_771_, sizeof(void*)*4, v_bi_762_);
lean_ctor_set_uint8(v_decl_771_, sizeof(void*)*4 + 1, v_kind_763_);
lean_inc_ref(v_decl_771_);
v___x_772_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_765_, v_fvarId_759_, v_decl_771_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v_decl_771_);
v___x_774_ = l_Lean_PersistentArray_push___redArg(v_decls_764_, v___x_773_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_774_);
lean_ctor_set(v___x_768_, 0, v___x_772_);
v___x_776_ = v___x_768_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_auxDeclToFullName_766_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_779_, lean_object* v_fvarId_780_, lean_object* v_userName_781_, lean_object* v_type_782_, lean_object* v_bi_783_, lean_object* v_kind_784_){
_start:
{
uint8_t v_bi_boxed_785_; uint8_t v_kind_boxed_786_; lean_object* v_res_787_; 
v_bi_boxed_785_ = lean_unbox(v_bi_783_);
v_kind_boxed_786_ = lean_unbox(v_kind_784_);
v_res_787_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_779_, v_fvarId_780_, v_userName_781_, v_type_782_, v_bi_boxed_785_, v_kind_boxed_786_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_789_, v_x_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, size_t v_x_795_, size_t v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_794_, v_x_795_, v_x_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
size_t v_x_561__boxed_806_; size_t v_x_562__boxed_807_; lean_object* v_res_808_; 
v_x_561__boxed_806_ = lean_unbox_usize(v_x_802_);
lean_dec(v_x_802_);
v_x_562__boxed_807_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_res_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_800_, v_x_801_, v_x_561__boxed_806_, v_x_562__boxed_807_, v_x_804_, v_x_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_809_, lean_object* v_n_810_, lean_object* v_k_811_, lean_object* v_v_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_810_, v_k_811_, v_v_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_814_, size_t v_depth_815_, lean_object* v_keys_816_, lean_object* v_vals_817_, lean_object* v_heq_818_, lean_object* v_i_819_, lean_object* v_entries_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_815_, v_keys_816_, v_vals_817_, v_i_819_, v_entries_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_822_, lean_object* v_depth_823_, lean_object* v_keys_824_, lean_object* v_vals_825_, lean_object* v_heq_826_, lean_object* v_i_827_, lean_object* v_entries_828_){
_start:
{
size_t v_depth_boxed_829_; lean_object* v_res_830_; 
v_depth_boxed_829_ = lean_unbox_usize(v_depth_823_);
lean_dec(v_depth_823_);
v_res_830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_822_, v_depth_boxed_829_, v_keys_824_, v_vals_825_, v_heq_826_, v_i_827_, v_entries_828_);
lean_dec_ref(v_vals_825_);
lean_dec_ref(v_keys_824_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_832_, v_x_833_, v_x_834_, v_x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_837_, lean_object* v_fvarId_838_, lean_object* v_userName_839_, lean_object* v_type_840_, uint8_t v_bi_841_){
_start:
{
uint8_t v___x_842_; lean_object* v___x_843_; 
v___x_842_ = 0;
v___x_843_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_837_, v_fvarId_838_, v_userName_839_, v_type_840_, v_bi_841_, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_844_, lean_object* v_fvarId_845_, lean_object* v_userName_846_, lean_object* v_type_847_, lean_object* v_bi_848_){
_start:
{
uint8_t v_bi_boxed_849_; lean_object* v_res_850_; 
v_bi_boxed_849_ = lean_unbox(v_bi_848_);
v_res_850_ = lean_local_ctx_mk_local_decl(v_lctx_844_, v_fvarId_845_, v_userName_846_, v_type_847_, v_bi_boxed_849_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_851_, lean_object* v_fvarId_852_, lean_object* v_userName_853_, lean_object* v_type_854_, lean_object* v_value_855_, uint8_t v_nondep_856_, uint8_t v_kind_857_){
_start:
{
lean_object* v_decls_858_; lean_object* v_fvarIdToDecl_859_; lean_object* v_auxDeclToFullName_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_872_; 
v_decls_858_ = lean_ctor_get(v_lctx_851_, 1);
v_fvarIdToDecl_859_ = lean_ctor_get(v_lctx_851_, 0);
v_auxDeclToFullName_860_ = lean_ctor_get(v_lctx_851_, 2);
v_isSharedCheck_872_ = !lean_is_exclusive(v_lctx_851_);
if (v_isSharedCheck_872_ == 0)
{
v___x_862_ = v_lctx_851_;
v_isShared_863_ = v_isSharedCheck_872_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_auxDeclToFullName_860_);
lean_inc(v_decls_858_);
lean_inc(v_fvarIdToDecl_859_);
lean_dec(v_lctx_851_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_872_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_size_864_; lean_object* v_decl_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v_size_864_ = lean_ctor_get(v_decls_858_, 2);
lean_inc(v_fvarId_852_);
lean_inc(v_size_864_);
v_decl_865_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_865_, 0, v_size_864_);
lean_ctor_set(v_decl_865_, 1, v_fvarId_852_);
lean_ctor_set(v_decl_865_, 2, v_userName_853_);
lean_ctor_set(v_decl_865_, 3, v_type_854_);
lean_ctor_set(v_decl_865_, 4, v_value_855_);
lean_ctor_set_uint8(v_decl_865_, sizeof(void*)*5, v_nondep_856_);
lean_ctor_set_uint8(v_decl_865_, sizeof(void*)*5 + 1, v_kind_857_);
lean_inc_ref(v_decl_865_);
v___x_866_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_859_, v_fvarId_852_, v_decl_865_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v_decl_865_);
v___x_868_ = l_Lean_PersistentArray_push___redArg(v_decls_858_, v___x_867_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v___x_868_);
lean_ctor_set(v___x_862_, 0, v___x_866_);
v___x_870_ = v___x_862_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_auxDeclToFullName_860_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_873_, lean_object* v_fvarId_874_, lean_object* v_userName_875_, lean_object* v_type_876_, lean_object* v_value_877_, lean_object* v_nondep_878_, lean_object* v_kind_879_){
_start:
{
uint8_t v_nondep_boxed_880_; uint8_t v_kind_boxed_881_; lean_object* v_res_882_; 
v_nondep_boxed_880_ = lean_unbox(v_nondep_878_);
v_kind_boxed_881_ = lean_unbox(v_kind_879_);
v_res_882_ = l_Lean_LocalContext_mkLetDecl(v_lctx_873_, v_fvarId_874_, v_userName_875_, v_type_876_, v_value_877_, v_nondep_boxed_880_, v_kind_boxed_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_883_, lean_object* v_fvarId_884_, lean_object* v_userName_885_, lean_object* v_type_886_, lean_object* v_value_887_, uint8_t v_nondep_888_){
_start:
{
uint8_t v___x_889_; lean_object* v___x_890_; 
v___x_889_ = 0;
v___x_890_ = l_Lean_LocalContext_mkLetDecl(v_lctx_883_, v_fvarId_884_, v_userName_885_, v_type_886_, v_value_887_, v_nondep_888_, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_891_, lean_object* v_fvarId_892_, lean_object* v_userName_893_, lean_object* v_type_894_, lean_object* v_value_895_, lean_object* v_nondep_896_){
_start:
{
uint8_t v_nondep_boxed_897_; lean_object* v_res_898_; 
v_nondep_boxed_897_ = lean_unbox(v_nondep_896_);
v_res_898_ = lean_local_ctx_mk_let_decl(v_lctx_891_, v_fvarId_892_, v_userName_893_, v_type_894_, v_value_895_, v_nondep_boxed_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_899_, lean_object* v_fvarId_900_, lean_object* v_userName_901_, lean_object* v_type_902_, lean_object* v_fullName_903_){
_start:
{
lean_object* v_decls_904_; lean_object* v_fvarIdToDecl_905_; lean_object* v_auxDeclToFullName_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_921_; 
v_decls_904_ = lean_ctor_get(v_lctx_899_, 1);
v_fvarIdToDecl_905_ = lean_ctor_get(v_lctx_899_, 0);
v_auxDeclToFullName_906_ = lean_ctor_get(v_lctx_899_, 2);
v_isSharedCheck_921_ = !lean_is_exclusive(v_lctx_899_);
if (v_isSharedCheck_921_ == 0)
{
v___x_908_ = v_lctx_899_;
v_isShared_909_ = v_isSharedCheck_921_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_auxDeclToFullName_906_);
lean_inc(v_decls_904_);
lean_inc(v_fvarIdToDecl_905_);
lean_dec(v_lctx_899_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_921_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_size_910_; uint8_t v___x_911_; uint8_t v___x_912_; lean_object* v_decl_913_; lean_object* v_auxDeclToFullName_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v_size_910_ = lean_ctor_get(v_decls_904_, 2);
v___x_911_ = 0;
v___x_912_ = 2;
lean_inc_n(v_fvarId_900_, 2);
lean_inc(v_size_910_);
v_decl_913_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_913_, 0, v_size_910_);
lean_ctor_set(v_decl_913_, 1, v_fvarId_900_);
lean_ctor_set(v_decl_913_, 2, v_userName_901_);
lean_ctor_set(v_decl_913_, 3, v_type_902_);
lean_ctor_set_uint8(v_decl_913_, sizeof(void*)*4, v___x_911_);
lean_ctor_set_uint8(v_decl_913_, sizeof(void*)*4 + 1, v___x_912_);
v_auxDeclToFullName_914_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_900_, v_fullName_903_, v_auxDeclToFullName_906_);
lean_inc_ref(v_decl_913_);
v___x_915_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_905_, v_fvarId_900_, v_decl_913_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_decl_913_);
v___x_917_ = l_Lean_PersistentArray_push___redArg(v_decls_904_, v___x_916_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 2, v_auxDeclToFullName_914_);
lean_ctor_set(v___x_908_, 1, v___x_917_);
lean_ctor_set(v___x_908_, 0, v___x_915_);
v___x_919_ = v___x_908_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_auxDeclToFullName_914_);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_922_, lean_object* v_newDecl_923_){
_start:
{
lean_object* v_decls_924_; lean_object* v_fvarIdToDecl_925_; lean_object* v_auxDeclToFullName_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_941_; 
v_decls_924_ = lean_ctor_get(v_lctx_922_, 1);
v_fvarIdToDecl_925_ = lean_ctor_get(v_lctx_922_, 0);
v_auxDeclToFullName_926_ = lean_ctor_get(v_lctx_922_, 2);
v_isSharedCheck_941_ = !lean_is_exclusive(v_lctx_922_);
if (v_isSharedCheck_941_ == 0)
{
v___x_928_ = v_lctx_922_;
v_isShared_929_ = v_isSharedCheck_941_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_auxDeclToFullName_926_);
lean_inc(v_decls_924_);
lean_inc(v_fvarIdToDecl_925_);
lean_dec(v_lctx_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_941_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_size_930_; lean_object* v_newDecl_931_; lean_object* v___y_933_; lean_object* v_fvarId_940_; 
v_size_930_ = lean_ctor_get(v_decls_924_, 2);
lean_inc(v_size_930_);
v_newDecl_931_ = l_Lean_LocalDecl_setIndex(v_newDecl_923_, v_size_930_);
v_fvarId_940_ = lean_ctor_get(v_newDecl_931_, 1);
lean_inc(v_fvarId_940_);
v___y_933_ = v_fvarId_940_;
goto v___jp_932_;
v___jp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
lean_inc_ref(v_newDecl_931_);
v___x_934_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_925_, v___y_933_, v_newDecl_931_);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v_newDecl_931_);
v___x_936_ = l_Lean_PersistentArray_push___redArg(v_decls_924_, v___x_935_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_936_);
lean_ctor_set(v___x_928_, 0, v___x_934_);
v___x_938_ = v___x_928_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_auxDeclToFullName_926_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_i_944_, lean_object* v_k_945_){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_array_get_size(v_keys_942_);
v___x_947_ = lean_nat_dec_lt(v_i_944_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_dec(v_i_944_);
v___x_948_ = lean_box(0);
return v___x_948_;
}
else
{
lean_object* v_k_x27_949_; uint8_t v___x_950_; 
v_k_x27_949_ = lean_array_fget_borrowed(v_keys_942_, v_i_944_);
v___x_950_ = l_Lean_instBEqFVarId_beq(v_k_945_, v_k_x27_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(1u);
v___x_952_ = lean_nat_add(v_i_944_, v___x_951_);
lean_dec(v_i_944_);
v_i_944_ = v___x_952_;
goto _start;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_array_fget_borrowed(v_vals_943_, v_i_944_);
lean_dec(v_i_944_);
lean_inc(v___x_954_);
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_956_, lean_object* v_vals_957_, lean_object* v_i_958_, lean_object* v_k_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_956_, v_vals_957_, v_i_958_, v_k_959_);
lean_dec(v_k_959_);
lean_dec_ref(v_vals_957_);
lean_dec_ref(v_keys_956_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_961_, size_t v_x_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_961_) == 0)
{
lean_object* v_es_964_; lean_object* v___x_965_; size_t v___x_966_; size_t v___x_967_; lean_object* v_j_968_; lean_object* v___x_969_; 
v_es_964_ = lean_ctor_get(v_x_961_, 0);
v___x_965_ = lean_box(2);
v___x_966_ = ((size_t)31ULL);
v___x_967_ = lean_usize_land(v_x_962_, v___x_966_);
v_j_968_ = lean_usize_to_nat(v___x_967_);
v___x_969_ = lean_array_get_borrowed(v___x_965_, v_es_964_, v_j_968_);
lean_dec(v_j_968_);
switch(lean_obj_tag(v___x_969_))
{
case 0:
{
lean_object* v_key_970_; lean_object* v_val_971_; uint8_t v___x_972_; 
v_key_970_ = lean_ctor_get(v___x_969_, 0);
v_val_971_ = lean_ctor_get(v___x_969_, 1);
v___x_972_ = l_Lean_instBEqFVarId_beq(v_x_963_, v_key_970_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
v___x_973_ = lean_box(0);
return v___x_973_;
}
else
{
lean_object* v___x_974_; 
lean_inc(v_val_971_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v_val_971_);
return v___x_974_;
}
}
case 1:
{
lean_object* v_node_975_; size_t v___x_976_; size_t v___x_977_; 
v_node_975_ = lean_ctor_get(v___x_969_, 0);
v___x_976_ = ((size_t)5ULL);
v___x_977_ = lean_usize_shift_right(v_x_962_, v___x_976_);
v_x_961_ = v_node_975_;
v_x_962_ = v___x_977_;
goto _start;
}
default: 
{
lean_object* v___x_979_; 
v___x_979_ = lean_box(0);
return v___x_979_;
}
}
}
else
{
lean_object* v_ks_980_; lean_object* v_vs_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_ks_980_ = lean_ctor_get(v_x_961_, 0);
v_vs_981_ = lean_ctor_get(v_x_961_, 1);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_980_, v_vs_981_, v___x_982_, v_x_963_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
size_t v_x_133__boxed_987_; lean_object* v_res_988_; 
v_x_133__boxed_987_ = lean_unbox_usize(v_x_985_);
lean_dec(v_x_985_);
v_res_988_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_984_, v_x_133__boxed_987_, v_x_986_);
lean_dec(v_x_986_);
lean_dec_ref(v_x_984_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
uint64_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_instHashableFVarId_hash(v_x_990_);
v___x_992_ = lean_uint64_to_usize(v___x_991_);
v___x_993_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_989_, v___x_992_, v_x_990_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_994_, v_x_995_);
lean_dec(v_x_995_);
lean_dec_ref(v_x_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_997_, lean_object* v_fvarId_998_){
_start:
{
lean_object* v_fvarIdToDecl_999_; lean_object* v___x_1000_; 
v_fvarIdToDecl_999_ = lean_ctor_get(v_lctx_997_, 0);
lean_inc_ref(v_fvarIdToDecl_999_);
lean_dec_ref(v_lctx_997_);
v___x_1000_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_999_, v_fvarId_998_);
lean_dec(v_fvarId_998_);
lean_dec_ref(v_fvarIdToDecl_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1002_, v_x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1005_, v_x_1006_, v_x_1007_);
lean_dec(v_x_1007_);
lean_dec_ref(v_x_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, size_t v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1010_, v_x_1011_, v_x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
size_t v_x_202__boxed_1018_; lean_object* v_res_1019_; 
v_x_202__boxed_1018_ = lean_unbox_usize(v_x_1016_);
lean_dec(v_x_1016_);
v_res_1019_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1014_, v_x_1015_, v_x_202__boxed_1018_, v_x_1017_);
lean_dec(v_x_1017_);
lean_dec_ref(v_x_1015_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1020_, lean_object* v_keys_1021_, lean_object* v_vals_1022_, lean_object* v_heq_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1021_, v_vals_1022_, v_i_1024_, v_k_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1027_, lean_object* v_keys_1028_, lean_object* v_vals_1029_, lean_object* v_heq_1030_, lean_object* v_i_1031_, lean_object* v_k_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1027_, v_keys_1028_, v_vals_1029_, v_heq_1030_, v_i_1031_, v_k_1032_);
lean_dec(v_k_1032_);
lean_dec_ref(v_vals_1029_);
lean_dec_ref(v_keys_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1034_, lean_object* v_e_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = l_Lean_Expr_fvarId_x21(v_e_1035_);
v___x_1037_ = lean_local_ctx_find(v_lctx_1034_, v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1038_, lean_object* v_e_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1038_, v_e_1039_);
lean_dec_ref(v_e_1039_);
return v_res_1040_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1043_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1044_ = lean_unsigned_to_nat(14u);
v___x_1045_ = lean_unsigned_to_nat(340u);
v___x_1046_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1047_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1048_ = l_mkPanicMessageWithDecl(v___x_1047_, v___x_1046_, v___x_1045_, v___x_1044_, v___x_1043_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1049_, lean_object* v_fvarId_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_local_ctx_find(v_lctx_1049_, v_fvarId_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1053_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1052_);
return v___x_1053_;
}
else
{
lean_object* v_val_1054_; 
v_val_1054_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v___x_1051_, 1);
return v_val_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1055_, lean_object* v_e_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = l_Lean_Expr_fvarId_x21(v_e_1056_);
v___x_1058_ = l_Lean_LocalContext_get_x21(v_lctx_1055_, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1059_, lean_object* v_e_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1059_, v_e_1060_);
lean_dec_ref(v_e_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1062_, lean_object* v_i_1063_, lean_object* v_k_1064_){
_start:
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_array_get_size(v_keys_1062_);
v___x_1066_ = lean_nat_dec_lt(v_i_1063_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec(v_i_1063_);
return v___x_1066_;
}
else
{
lean_object* v_k_x27_1067_; uint8_t v___x_1068_; 
v_k_x27_1067_ = lean_array_fget_borrowed(v_keys_1062_, v_i_1063_);
v___x_1068_ = l_Lean_instBEqFVarId_beq(v_k_1064_, v_k_x27_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_nat_add(v_i_1063_, v___x_1069_);
lean_dec(v_i_1063_);
v_i_1063_ = v___x_1070_;
goto _start;
}
else
{
lean_dec(v_i_1063_);
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1072_, lean_object* v_i_1073_, lean_object* v_k_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1072_, v_i_1073_, v_k_1074_);
lean_dec(v_k_1074_);
lean_dec_ref(v_keys_1072_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1077_, size_t v_x_1078_, lean_object* v_x_1079_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 0)
{
lean_object* v_es_1080_; lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; lean_object* v_j_1084_; lean_object* v___x_1085_; 
v_es_1080_ = lean_ctor_get(v_x_1077_, 0);
v___x_1081_ = lean_box(2);
v___x_1082_ = ((size_t)31ULL);
v___x_1083_ = lean_usize_land(v_x_1078_, v___x_1082_);
v_j_1084_ = lean_usize_to_nat(v___x_1083_);
v___x_1085_ = lean_array_get_borrowed(v___x_1081_, v_es_1080_, v_j_1084_);
lean_dec(v_j_1084_);
switch(lean_obj_tag(v___x_1085_))
{
case 0:
{
lean_object* v_key_1086_; uint8_t v___x_1087_; 
v_key_1086_ = lean_ctor_get(v___x_1085_, 0);
v___x_1087_ = l_Lean_instBEqFVarId_beq(v_x_1079_, v_key_1086_);
return v___x_1087_;
}
case 1:
{
lean_object* v_node_1088_; size_t v___x_1089_; size_t v___x_1090_; 
v_node_1088_ = lean_ctor_get(v___x_1085_, 0);
v___x_1089_ = ((size_t)5ULL);
v___x_1090_ = lean_usize_shift_right(v_x_1078_, v___x_1089_);
v_x_1077_ = v_node_1088_;
v_x_1078_ = v___x_1090_;
goto _start;
}
default: 
{
uint8_t v___x_1092_; 
v___x_1092_ = 0;
return v___x_1092_;
}
}
}
else
{
lean_object* v_ks_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_ks_1093_ = lean_ctor_get(v_x_1077_, 0);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1093_, v___x_1094_, v_x_1079_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v_x_119__boxed_1099_; uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_x_119__boxed_1099_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_res_1100_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1096_, v_x_119__boxed_1099_, v_x_1098_);
lean_dec(v_x_1098_);
lean_dec_ref(v_x_1096_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
uint64_t v___x_1104_; size_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = l_Lean_instHashableFVarId_hash(v_x_1103_);
v___x_1105_ = lean_uint64_to_usize(v___x_1104_);
v___x_1106_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1102_, v___x_1105_, v_x_1103_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1107_, v_x_1108_);
lean_dec(v_x_1108_);
lean_dec_ref(v_x_1107_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1111_, lean_object* v_fvarId_1112_){
_start:
{
lean_object* v_fvarIdToDecl_1113_; uint8_t v___x_1114_; 
v_fvarIdToDecl_1113_ = lean_ctor_get(v_lctx_1111_, 0);
v___x_1114_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1113_, v_fvarId_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1115_, lean_object* v_fvarId_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_Lean_LocalContext_contains(v_lctx_1115_, v_fvarId_1116_);
lean_dec(v_fvarId_1116_);
lean_dec_ref(v_lctx_1115_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
uint8_t v___x_1122_; 
v___x_1122_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1120_, v_x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1123_, v_x_1124_, v_x_1125_);
lean_dec(v_x_1125_);
lean_dec_ref(v_x_1124_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, size_t v_x_1130_, lean_object* v_x_1131_){
_start:
{
uint8_t v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1129_, v_x_1130_, v_x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
size_t v_x_182__boxed_1137_; uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_x_182__boxed_1137_ = lean_unbox_usize(v_x_1135_);
lean_dec(v_x_1135_);
v_res_1138_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1133_, v_x_1134_, v_x_182__boxed_1137_, v_x_1136_);
lean_dec(v_x_1136_);
lean_dec_ref(v_x_1134_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1140_, lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_heq_1143_, lean_object* v_i_1144_, lean_object* v_k_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1141_, v_i_1144_, v_k_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_keys_1148_, lean_object* v_vals_1149_, lean_object* v_heq_1150_, lean_object* v_i_1151_, lean_object* v_k_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1147_, v_keys_1148_, v_vals_1149_, v_heq_1150_, v_i_1151_, v_k_1152_);
lean_dec(v_k_1152_);
lean_dec_ref(v_vals_1149_);
lean_dec_ref(v_keys_1148_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1155_, lean_object* v_e_1156_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = l_Lean_Expr_fvarId_x21(v_e_1156_);
v___x_1158_ = l_Lean_LocalContext_contains(v_lctx_1155_, v___x_1157_);
lean_dec(v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1159_, lean_object* v_e_1160_){
_start:
{
uint8_t v_res_1161_; lean_object* v_r_1162_; 
v_res_1161_ = l_Lean_LocalContext_containsFVar(v_lctx_1159_, v_e_1160_);
lean_dec_ref(v_e_1160_);
lean_dec_ref(v_lctx_1159_);
v_r_1162_ = lean_box(v_res_1161_);
return v_r_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1163_, size_t v_i_1164_, size_t v_stop_1165_, lean_object* v_b_1166_){
_start:
{
lean_object* v___y_1168_; uint8_t v___x_1172_; 
v___x_1172_ = lean_usize_dec_eq(v_i_1164_, v_stop_1165_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_array_uget_borrowed(v_as_1163_, v_i_1164_);
if (lean_obj_tag(v___x_1173_) == 0)
{
v___y_1168_ = v_b_1166_;
goto v___jp_1167_;
}
else
{
lean_object* v_val_1174_; lean_object* v_fvarId_1175_; lean_object* v___x_1176_; 
v_val_1174_ = lean_ctor_get(v___x_1173_, 0);
v_fvarId_1175_ = lean_ctor_get(v_val_1174_, 1);
lean_inc(v_fvarId_1175_);
v___x_1176_ = lean_array_push(v_b_1166_, v_fvarId_1175_);
v___y_1168_ = v___x_1176_;
goto v___jp_1167_;
}
}
else
{
return v_b_1166_;
}
v___jp_1167_:
{
size_t v___x_1169_; size_t v___x_1170_; 
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_add(v_i_1164_, v___x_1169_);
v_i_1164_ = v___x_1170_;
v_b_1166_ = v___y_1168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1177_, lean_object* v_i_1178_, lean_object* v_stop_1179_, lean_object* v_b_1180_){
_start:
{
size_t v_i_boxed_1181_; size_t v_stop_boxed_1182_; lean_object* v_res_1183_; 
v_i_boxed_1181_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_stop_boxed_1182_ = lean_unbox_usize(v_stop_1179_);
lean_dec(v_stop_1179_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1177_, v_i_boxed_1181_, v_stop_boxed_1182_, v_b_1180_);
lean_dec_ref(v_as_1177_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
if (lean_obj_tag(v_x_1184_) == 0)
{
lean_object* v_cs_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_cs_1186_ = lean_ctor_get(v_x_1184_, 0);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_array_get_size(v_cs_1186_);
v___x_1189_ = lean_nat_dec_lt(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
return v_x_1185_;
}
else
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_nat_dec_le(v___x_1188_, v___x_1188_);
if (v___x_1190_ == 0)
{
if (v___x_1189_ == 0)
{
return v_x_1185_;
}
else
{
size_t v___x_1191_; size_t v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = lean_usize_of_nat(v___x_1188_);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1186_, v___x_1191_, v___x_1192_, v_x_1185_);
return v___x_1193_;
}
}
else
{
size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((size_t)0ULL);
v___x_1195_ = lean_usize_of_nat(v___x_1188_);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1186_, v___x_1194_, v___x_1195_, v_x_1185_);
return v___x_1196_;
}
}
}
else
{
lean_object* v_vs_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_vs_1197_ = lean_ctor_get(v_x_1184_, 0);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get_size(v_vs_1197_);
v___x_1200_ = lean_nat_dec_lt(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
return v_x_1185_;
}
else
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_nat_dec_le(v___x_1199_, v___x_1199_);
if (v___x_1201_ == 0)
{
if (v___x_1200_ == 0)
{
return v_x_1185_;
}
else
{
size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = ((size_t)0ULL);
v___x_1203_ = lean_usize_of_nat(v___x_1199_);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1197_, v___x_1202_, v___x_1203_, v_x_1185_);
return v___x_1204_;
}
}
else
{
size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((size_t)0ULL);
v___x_1206_ = lean_usize_of_nat(v___x_1199_);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1197_, v___x_1205_, v___x_1206_, v_x_1185_);
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1208_, size_t v_i_1209_, size_t v_stop_1210_, lean_object* v_b_1211_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_eq(v_i_1209_, v_stop_1210_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; 
v___x_1213_ = lean_array_uget_borrowed(v_as_1208_, v_i_1209_);
v___x_1214_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1213_, v_b_1211_);
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1209_, v___x_1215_);
v_i_1209_ = v___x_1216_;
v_b_1211_ = v___x_1214_;
goto _start;
}
else
{
return v_b_1211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1218_, lean_object* v_i_1219_, lean_object* v_stop_1220_, lean_object* v_b_1221_){
_start:
{
size_t v_i_boxed_1222_; size_t v_stop_boxed_1223_; lean_object* v_res_1224_; 
v_i_boxed_1222_ = lean_unbox_usize(v_i_1219_);
lean_dec(v_i_1219_);
v_stop_boxed_1223_ = lean_unbox_usize(v_stop_1220_);
lean_dec(v_stop_1220_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1218_, v_i_boxed_1222_, v_stop_boxed_1223_, v_b_1221_);
lean_dec_ref(v_as_1218_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1225_, lean_object* v_x_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1225_, v_x_1226_);
lean_dec_ref(v_x_1225_);
return v_res_1227_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1229_, size_t v_x_1230_, size_t v_x_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1229_) == 0)
{
lean_object* v_cs_1233_; lean_object* v___x_1234_; size_t v___x_1235_; lean_object* v_j_1236_; lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_cs_1233_ = lean_ctor_get(v_x_1229_, 0);
v___x_1234_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1235_ = lean_usize_shift_right(v_x_1230_, v_x_1231_);
v_j_1236_ = lean_usize_to_nat(v___x_1235_);
v___x_1237_ = lean_array_get_borrowed(v___x_1234_, v_cs_1233_, v_j_1236_);
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_shift_left(v___x_1238_, v_x_1231_);
v___x_1240_ = lean_usize_sub(v___x_1239_, v___x_1238_);
v___x_1241_ = lean_usize_land(v_x_1230_, v___x_1240_);
v___x_1242_ = ((size_t)5ULL);
v___x_1243_ = lean_usize_sub(v_x_1231_, v___x_1242_);
v___x_1244_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1237_, v___x_1241_, v___x_1243_, v_x_1232_);
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_add(v_j_1236_, v___x_1245_);
lean_dec(v_j_1236_);
v___x_1247_ = lean_array_get_size(v_cs_1233_);
v___x_1248_ = lean_nat_dec_lt(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec(v___x_1246_);
return v___x_1244_;
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_nat_dec_le(v___x_1247_, v___x_1247_);
if (v___x_1249_ == 0)
{
if (v___x_1248_ == 0)
{
lean_dec(v___x_1246_);
return v___x_1244_;
}
else
{
size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_usize_of_nat(v___x_1246_);
lean_dec(v___x_1246_);
v___x_1251_ = lean_usize_of_nat(v___x_1247_);
v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1233_, v___x_1250_, v___x_1251_, v___x_1244_);
return v___x_1252_;
}
}
else
{
size_t v___x_1253_; size_t v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_usize_of_nat(v___x_1246_);
lean_dec(v___x_1246_);
v___x_1254_ = lean_usize_of_nat(v___x_1247_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1233_, v___x_1253_, v___x_1254_, v___x_1244_);
return v___x_1255_;
}
}
}
else
{
lean_object* v_vs_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_vs_1256_ = lean_ctor_get(v_x_1229_, 0);
v___x_1257_ = lean_usize_to_nat(v_x_1230_);
v___x_1258_ = lean_array_get_size(v_vs_1256_);
v___x_1259_ = lean_nat_dec_lt(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec(v___x_1257_);
return v_x_1232_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_nat_dec_le(v___x_1258_, v___x_1258_);
if (v___x_1260_ == 0)
{
if (v___x_1259_ == 0)
{
lean_dec(v___x_1257_);
return v_x_1232_;
}
else
{
size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_usize_of_nat(v___x_1257_);
lean_dec(v___x_1257_);
v___x_1262_ = lean_usize_of_nat(v___x_1258_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1256_, v___x_1261_, v___x_1262_, v_x_1232_);
return v___x_1263_;
}
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_usize_of_nat(v___x_1257_);
lean_dec(v___x_1257_);
v___x_1265_ = lean_usize_of_nat(v___x_1258_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1256_, v___x_1264_, v___x_1265_, v_x_1232_);
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
size_t v_x_1632__boxed_1271_; size_t v_x_1633__boxed_1272_; lean_object* v_res_1273_; 
v_x_1632__boxed_1271_ = lean_unbox_usize(v_x_1268_);
lean_dec(v_x_1268_);
v_x_1633__boxed_1272_ = lean_unbox_usize(v_x_1269_);
lean_dec(v_x_1269_);
v_res_1273_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1267_, v_x_1632__boxed_1271_, v_x_1633__boxed_1272_, v_x_1270_);
lean_dec_ref(v_x_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1274_, lean_object* v_init_1275_, lean_object* v_start_1276_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_nat_dec_eq(v_start_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v_root_1279_; lean_object* v_tail_1280_; size_t v_shift_1281_; lean_object* v_tailOff_1282_; uint8_t v___x_1283_; 
v_root_1279_ = lean_ctor_get(v_t_1274_, 0);
v_tail_1280_ = lean_ctor_get(v_t_1274_, 1);
v_shift_1281_ = lean_ctor_get_usize(v_t_1274_, 4);
v_tailOff_1282_ = lean_ctor_get(v_t_1274_, 3);
v___x_1283_ = lean_nat_dec_le(v_tailOff_1282_, v_start_1276_);
if (v___x_1283_ == 0)
{
size_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1284_ = lean_usize_of_nat(v_start_1276_);
v___x_1285_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1279_, v___x_1284_, v_shift_1281_, v_init_1275_);
v___x_1286_ = lean_array_get_size(v_tail_1280_);
v___x_1287_ = lean_nat_dec_lt(v___x_1277_, v___x_1286_);
if (v___x_1287_ == 0)
{
return v___x_1285_;
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_nat_dec_le(v___x_1286_, v___x_1286_);
if (v___x_1288_ == 0)
{
if (v___x_1287_ == 0)
{
return v___x_1285_;
}
else
{
size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = lean_usize_of_nat(v___x_1286_);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1280_, v___x_1289_, v___x_1290_, v___x_1285_);
return v___x_1291_;
}
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1286_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1280_, v___x_1292_, v___x_1293_, v___x_1285_);
return v___x_1294_;
}
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = lean_nat_sub(v_start_1276_, v_tailOff_1282_);
v___x_1296_ = lean_array_get_size(v_tail_1280_);
v___x_1297_ = lean_nat_dec_lt(v___x_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_dec(v___x_1295_);
return v_init_1275_;
}
else
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_nat_dec_le(v___x_1296_, v___x_1296_);
if (v___x_1298_ == 0)
{
if (v___x_1297_ == 0)
{
lean_dec(v___x_1295_);
return v_init_1275_;
}
else
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_usize_of_nat(v___x_1295_);
lean_dec(v___x_1295_);
v___x_1300_ = lean_usize_of_nat(v___x_1296_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1280_, v___x_1299_, v___x_1300_, v_init_1275_);
return v___x_1301_;
}
}
else
{
size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = lean_usize_of_nat(v___x_1295_);
lean_dec(v___x_1295_);
v___x_1303_ = lean_usize_of_nat(v___x_1296_);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1280_, v___x_1302_, v___x_1303_, v_init_1275_);
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_root_1305_; lean_object* v_tail_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_root_1305_ = lean_ctor_get(v_t_1274_, 0);
v_tail_1306_ = lean_ctor_get(v_t_1274_, 1);
v___x_1307_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1305_, v_init_1275_);
v___x_1308_ = lean_array_get_size(v_tail_1306_);
v___x_1309_ = lean_nat_dec_lt(v___x_1277_, v___x_1308_);
if (v___x_1309_ == 0)
{
return v___x_1307_;
}
else
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_nat_dec_le(v___x_1308_, v___x_1308_);
if (v___x_1310_ == 0)
{
if (v___x_1309_ == 0)
{
return v___x_1307_;
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1308_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1306_, v___x_1311_, v___x_1312_, v___x_1307_);
return v___x_1313_;
}
}
else
{
size_t v___x_1314_; size_t v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = ((size_t)0ULL);
v___x_1315_ = lean_usize_of_nat(v___x_1308_);
v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1306_, v___x_1314_, v___x_1315_, v___x_1307_);
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1317_, lean_object* v_init_1318_, lean_object* v_start_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1317_, v_init_1318_, v_start_1319_);
lean_dec(v_start_1319_);
lean_dec_ref(v_t_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1323_){
_start:
{
lean_object* v_decls_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_decls_1324_ = lean_ctor_get(v_lctx_1323_, 1);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1327_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1324_, v___x_1326_, v___x_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_LocalContext_getFVarIds(v_lctx_1328_);
lean_dec_ref(v_lctx_1328_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_bs_1332_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1333_ == 0)
{
return v_bs_1332_;
}
else
{
lean_object* v_v_1334_; lean_object* v___x_1335_; lean_object* v_bs_x27_1336_; lean_object* v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; lean_object* v___x_1340_; 
v_v_1334_ = lean_array_uget(v_bs_1332_, v_i_1331_);
v___x_1335_ = lean_unsigned_to_nat(0u);
v_bs_x27_1336_ = lean_array_uset(v_bs_1332_, v_i_1331_, v___x_1335_);
v___x_1337_ = l_Lean_mkFVar(v_v_1334_);
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1331_, v___x_1338_);
v___x_1340_ = lean_array_uset(v_bs_x27_1336_, v_i_1331_, v___x_1337_);
v_i_1331_ = v___x_1339_;
v_bs_1332_ = v___x_1340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1342_, lean_object* v_i_1343_, lean_object* v_bs_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1342_);
lean_dec(v_sz_1342_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1345_, v_i_boxed_1346_, v_bs_1344_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1348_){
_start:
{
lean_object* v___x_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = l_Lean_LocalContext_getFVarIds(v_lctx_1348_);
v_sz_1350_ = lean_array_size(v___x_1349_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1350_, v___x_1351_, v___x_1349_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_LocalContext_getFVars(v_lctx_1353_);
lean_dec_ref(v_lctx_1353_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1355_){
_start:
{
lean_object* v_size_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_size_1356_ = lean_ctor_get(v_a_1355_, 2);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_nat_dec_eq(v_size_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = lean_nat_sub(v_size_1356_, v___x_1360_);
v___x_1362_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1359_, v_a_1355_, v___x_1361_);
lean_dec(v___x_1361_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_PersistentArray_pop___redArg(v_a_1355_);
v_a_1355_ = v___x_1363_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1362_, 1);
return v_a_1355_;
}
}
else
{
return v_a_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1365_, lean_object* v_t_1366_){
_start:
{
if (lean_obj_tag(v_t_1366_) == 0)
{
lean_object* v_k_1367_; lean_object* v_v_1368_; lean_object* v_l_1369_; lean_object* v_r_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_2024_; 
v_k_1367_ = lean_ctor_get(v_t_1366_, 1);
v_v_1368_ = lean_ctor_get(v_t_1366_, 2);
v_l_1369_ = lean_ctor_get(v_t_1366_, 3);
v_r_1370_ = lean_ctor_get(v_t_1366_, 4);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_t_1366_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_t_1366_, 0);
lean_dec(v_unused_2025_);
v___x_1372_ = v_t_1366_;
v_isShared_1373_ = v_isSharedCheck_2024_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_r_1370_);
lean_inc(v_l_1369_);
lean_inc(v_v_1368_);
lean_inc(v_k_1367_);
lean_dec(v_t_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_2024_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
uint8_t v___x_1374_; 
v___x_1374_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1365_, v_k_1367_);
switch(v___x_1374_)
{
case 0:
{
lean_object* v_impl_1375_; lean_object* v___x_1376_; 
v_impl_1375_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1365_, v_l_1369_);
v___x_1376_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1375_) == 0)
{
if (lean_obj_tag(v_r_1370_) == 0)
{
lean_object* v_size_1377_; lean_object* v_size_1378_; lean_object* v_k_1379_; lean_object* v_v_1380_; lean_object* v_l_1381_; lean_object* v_r_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_size_1377_ = lean_ctor_get(v_impl_1375_, 0);
lean_inc(v_size_1377_);
v_size_1378_ = lean_ctor_get(v_r_1370_, 0);
v_k_1379_ = lean_ctor_get(v_r_1370_, 1);
v_v_1380_ = lean_ctor_get(v_r_1370_, 2);
v_l_1381_ = lean_ctor_get(v_r_1370_, 3);
lean_inc(v_l_1381_);
v_r_1382_ = lean_ctor_get(v_r_1370_, 4);
v___x_1383_ = lean_unsigned_to_nat(3u);
v___x_1384_ = lean_nat_mul(v___x_1383_, v_size_1377_);
v___x_1385_ = lean_nat_dec_lt(v___x_1384_, v_size_1378_);
lean_dec(v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec(v_l_1381_);
v___x_1386_ = lean_nat_add(v___x_1376_, v_size_1377_);
lean_dec(v_size_1377_);
v___x_1387_ = lean_nat_add(v___x_1386_, v_size_1378_);
lean_dec(v___x_1386_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 3, v_impl_1375_);
lean_ctor_set(v___x_1372_, 0, v___x_1387_);
v___x_1389_ = v___x_1372_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_impl_1375_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_r_1370_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1454_; 
lean_inc(v_r_1382_);
lean_inc(v_v_1380_);
lean_inc(v_k_1379_);
lean_inc(v_size_1378_);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; 
v_unused_1455_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_r_1370_, 2);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_r_1370_, 1);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_r_1370_, 0);
lean_dec(v_unused_1459_);
v___x_1392_ = v_r_1370_;
v_isShared_1393_ = v_isSharedCheck_1454_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v_r_1370_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1454_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_size_1394_; lean_object* v_k_1395_; lean_object* v_v_1396_; lean_object* v_l_1397_; lean_object* v_r_1398_; lean_object* v_size_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_size_1394_ = lean_ctor_get(v_l_1381_, 0);
v_k_1395_ = lean_ctor_get(v_l_1381_, 1);
v_v_1396_ = lean_ctor_get(v_l_1381_, 2);
v_l_1397_ = lean_ctor_get(v_l_1381_, 3);
v_r_1398_ = lean_ctor_get(v_l_1381_, 4);
v_size_1399_ = lean_ctor_get(v_r_1382_, 0);
v___x_1400_ = lean_unsigned_to_nat(2u);
v___x_1401_ = lean_nat_mul(v___x_1400_, v_size_1399_);
v___x_1402_ = lean_nat_dec_lt(v_size_1394_, v___x_1401_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1430_; 
lean_inc(v_r_1398_);
lean_inc(v_l_1397_);
lean_inc(v_v_1396_);
lean_inc(v_k_1395_);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_l_1381_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; 
v_unused_1431_ = lean_ctor_get(v_l_1381_, 4);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_l_1381_, 3);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_l_1381_, 2);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_l_1381_, 1);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_l_1381_, 0);
lean_dec(v_unused_1435_);
v___x_1404_ = v_l_1381_;
v_isShared_1405_ = v_isSharedCheck_1430_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_l_1381_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1430_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1420_; 
v___x_1406_ = lean_nat_add(v___x_1376_, v_size_1377_);
lean_dec(v_size_1377_);
v___x_1407_ = lean_nat_add(v___x_1406_, v_size_1378_);
lean_dec(v_size_1378_);
if (lean_obj_tag(v_l_1397_) == 0)
{
lean_object* v_size_1428_; 
v_size_1428_ = lean_ctor_get(v_l_1397_, 0);
lean_inc(v_size_1428_);
v___y_1420_ = v_size_1428_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___y_1420_ = v___x_1429_;
goto v___jp_1419_;
}
v___jp_1408_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_nat_add(v___y_1409_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec(v___y_1409_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_r_1382_);
lean_ctor_set(v___x_1404_, 3, v_r_1398_);
lean_ctor_set(v___x_1404_, 2, v_v_1380_);
lean_ctor_set(v___x_1404_, 1, v_k_1379_);
lean_ctor_set(v___x_1404_, 0, v___x_1412_);
v___x_1414_ = v___x_1404_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1379_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1380_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_r_1398_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_r_1382_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1414_);
lean_ctor_set(v___x_1392_, 3, v___y_1410_);
lean_ctor_set(v___x_1392_, 2, v_v_1396_);
lean_ctor_set(v___x_1392_, 1, v_k_1395_);
lean_ctor_set(v___x_1392_, 0, v___x_1407_);
v___x_1416_ = v___x_1392_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1395_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1396_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v___y_1410_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_nat_add(v___x_1406_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec(v___x_1406_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v_l_1397_);
lean_ctor_set(v___x_1372_, 3, v_impl_1375_);
lean_ctor_set(v___x_1372_, 0, v___x_1421_);
v___x_1423_ = v___x_1372_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v_impl_1375_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_l_1397_);
v___x_1423_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_nat_add(v___x_1376_, v_size_1399_);
if (lean_obj_tag(v_r_1398_) == 0)
{
lean_object* v_size_1425_; 
v_size_1425_ = lean_ctor_get(v_r_1398_, 0);
lean_inc(v_size_1425_);
v___y_1409_ = v___x_1424_;
v___y_1410_ = v___x_1423_;
v___y_1411_ = v_size_1425_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___y_1409_ = v___x_1424_;
v___y_1410_ = v___x_1423_;
v___y_1411_ = v___x_1426_;
goto v___jp_1408_;
}
}
}
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_del_object(v___x_1372_);
v___x_1436_ = lean_nat_add(v___x_1376_, v_size_1377_);
lean_dec(v_size_1377_);
v___x_1437_ = lean_nat_add(v___x_1436_, v_size_1378_);
lean_dec(v_size_1378_);
v___x_1438_ = lean_nat_add(v___x_1436_, v_size_1394_);
lean_dec(v___x_1436_);
lean_inc_ref(v_impl_1375_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_l_1381_);
lean_ctor_set(v___x_1392_, 3, v_impl_1375_);
lean_ctor_set(v___x_1392_, 2, v_v_1368_);
lean_ctor_set(v___x_1392_, 1, v_k_1367_);
lean_ctor_set(v___x_1392_, 0, v___x_1438_);
v___x_1440_ = v___x_1392_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_impl_1375_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_l_1381_);
v___x_1440_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_isSharedCheck_1447_ = !lean_is_exclusive(v_impl_1375_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1448_ = lean_ctor_get(v_impl_1375_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_impl_1375_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_impl_1375_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_impl_1375_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_impl_1375_, 0);
lean_dec(v_unused_1452_);
v___x_1442_ = v_impl_1375_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_dec(v_impl_1375_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v_r_1382_);
lean_ctor_set(v___x_1442_, 3, v___x_1440_);
lean_ctor_set(v___x_1442_, 2, v_v_1380_);
lean_ctor_set(v___x_1442_, 1, v_k_1379_);
lean_ctor_set(v___x_1442_, 0, v___x_1437_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_k_1379_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_v_1380_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_r_1382_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v_size_1460_ = lean_ctor_get(v_impl_1375_, 0);
lean_inc(v_size_1460_);
v___x_1461_ = lean_nat_add(v___x_1376_, v_size_1460_);
lean_dec(v_size_1460_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 3, v_impl_1375_);
lean_ctor_set(v___x_1372_, 0, v___x_1461_);
v___x_1463_ = v___x_1372_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_impl_1375_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_r_1370_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
else
{
if (lean_obj_tag(v_r_1370_) == 0)
{
lean_object* v_l_1465_; 
v_l_1465_ = lean_ctor_get(v_r_1370_, 3);
lean_inc(v_l_1465_);
if (lean_obj_tag(v_l_1465_) == 0)
{
lean_object* v_r_1466_; 
v_r_1466_ = lean_ctor_get(v_r_1370_, 4);
lean_inc(v_r_1466_);
if (lean_obj_tag(v_r_1466_) == 0)
{
lean_object* v_size_1467_; lean_object* v_k_1468_; lean_object* v_v_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1482_; 
v_size_1467_ = lean_ctor_get(v_r_1370_, 0);
v_k_1468_ = lean_ctor_get(v_r_1370_, 1);
v_v_1469_ = lean_ctor_get(v_r_1370_, 2);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; lean_object* v_unused_1484_; 
v_unused_1483_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1484_);
v___x_1471_ = v_r_1370_;
v_isShared_1472_ = v_isSharedCheck_1482_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_v_1469_);
lean_inc(v_k_1468_);
lean_inc(v_size_1467_);
lean_dec(v_r_1370_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1482_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_size_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v_size_1473_ = lean_ctor_get(v_l_1465_, 0);
v___x_1474_ = lean_nat_add(v___x_1376_, v_size_1467_);
lean_dec(v_size_1467_);
v___x_1475_ = lean_nat_add(v___x_1376_, v_size_1473_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v_l_1465_);
lean_ctor_set(v___x_1471_, 3, v_impl_1375_);
lean_ctor_set(v___x_1471_, 2, v_v_1368_);
lean_ctor_set(v___x_1471_, 1, v_k_1367_);
lean_ctor_set(v___x_1471_, 0, v___x_1475_);
v___x_1477_ = v___x_1471_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_impl_1375_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_l_1465_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v_r_1466_);
lean_ctor_set(v___x_1372_, 3, v___x_1477_);
lean_ctor_set(v___x_1372_, 2, v_v_1469_);
lean_ctor_set(v___x_1372_, 1, v_k_1468_);
lean_ctor_set(v___x_1372_, 0, v___x_1474_);
v___x_1479_ = v___x_1372_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1466_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_k_1485_; lean_object* v_v_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1509_; 
v_k_1485_ = lean_ctor_get(v_r_1370_, 1);
v_v_1486_ = lean_ctor_get(v_r_1370_, 2);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; 
v_unused_1510_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_r_1370_, 0);
lean_dec(v_unused_1512_);
v___x_1488_ = v_r_1370_;
v_isShared_1489_ = v_isSharedCheck_1509_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_v_1486_);
lean_inc(v_k_1485_);
lean_dec(v_r_1370_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1509_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_k_1490_; lean_object* v_v_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1505_; 
v_k_1490_ = lean_ctor_get(v_l_1465_, 1);
v_v_1491_ = lean_ctor_get(v_l_1465_, 2);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_l_1465_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; 
v_unused_1506_ = lean_ctor_get(v_l_1465_, 4);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_l_1465_, 3);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_l_1465_, 0);
lean_dec(v_unused_1508_);
v___x_1493_ = v_l_1465_;
v_isShared_1494_ = v_isSharedCheck_1505_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_v_1491_);
lean_inc(v_k_1490_);
lean_dec(v_l_1465_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1505_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_unsigned_to_nat(3u);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 4, v_r_1466_);
lean_ctor_set(v___x_1493_, 3, v_r_1466_);
lean_ctor_set(v___x_1493_, 2, v_v_1368_);
lean_ctor_set(v___x_1493_, 1, v_k_1367_);
lean_ctor_set(v___x_1493_, 0, v___x_1376_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_r_1466_);
lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_r_1466_);
v___x_1497_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 3, v_r_1466_);
lean_ctor_set(v___x_1488_, 0, v___x_1376_);
v___x_1499_ = v___x_1488_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_k_1485_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_v_1486_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_r_1466_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_r_1466_);
v___x_1499_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___x_1499_);
lean_ctor_set(v___x_1372_, 3, v___x_1497_);
lean_ctor_set(v___x_1372_, 2, v_v_1491_);
lean_ctor_set(v___x_1372_, 1, v_k_1490_);
lean_ctor_set(v___x_1372_, 0, v___x_1495_);
v___x_1501_ = v___x_1372_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1490_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1491_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1513_; 
v_r_1513_ = lean_ctor_get(v_r_1370_, 4);
lean_inc(v_r_1513_);
if (lean_obj_tag(v_r_1513_) == 0)
{
lean_object* v_k_1514_; lean_object* v_v_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1526_; 
v_k_1514_ = lean_ctor_get(v_r_1370_, 1);
v_v_1515_ = lean_ctor_get(v_r_1370_, 2);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; lean_object* v_unused_1528_; lean_object* v_unused_1529_; 
v_unused_1527_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_r_1370_, 0);
lean_dec(v_unused_1529_);
v___x_1517_ = v_r_1370_;
v_isShared_1518_ = v_isSharedCheck_1526_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_v_1515_);
lean_inc(v_k_1514_);
lean_dec(v_r_1370_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1526_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_unsigned_to_nat(3u);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 4, v_l_1465_);
lean_ctor_set(v___x_1517_, 2, v_v_1368_);
lean_ctor_set(v___x_1517_, 1, v_k_1367_);
lean_ctor_set(v___x_1517_, 0, v___x_1376_);
v___x_1521_ = v___x_1517_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_l_1465_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v_r_1513_);
lean_ctor_set(v___x_1372_, 3, v___x_1521_);
lean_ctor_set(v___x_1372_, 2, v_v_1515_);
lean_ctor_set(v___x_1372_, 1, v_k_1514_);
lean_ctor_set(v___x_1372_, 0, v___x_1519_);
v___x_1523_ = v___x_1372_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1514_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1515_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_r_1513_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_size_1530_; lean_object* v_k_1531_; lean_object* v_v_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1543_; 
v_size_1530_ = lean_ctor_get(v_r_1370_, 0);
v_k_1531_ = lean_ctor_get(v_r_1370_, 1);
v_v_1532_ = lean_ctor_get(v_r_1370_, 2);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; lean_object* v_unused_1545_; 
v_unused_1544_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1545_);
v___x_1534_ = v_r_1370_;
v_isShared_1535_ = v_isSharedCheck_1543_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_inc(v_size_1530_);
lean_dec(v_r_1370_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1543_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 3, v_r_1513_);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_size_1530_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_r_1513_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_r_1513_);
v___x_1537_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1538_ = lean_unsigned_to_nat(2u);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___x_1537_);
lean_ctor_set(v___x_1372_, 3, v_r_1513_);
lean_ctor_set(v___x_1372_, 0, v___x_1538_);
v___x_1540_ = v___x_1372_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_r_1513_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v___x_1537_);
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
}
}
else
{
lean_object* v___x_1547_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 3, v_r_1370_);
lean_ctor_set(v___x_1372_, 0, v___x_1376_);
v___x_1547_ = v___x_1372_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_r_1370_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_r_1370_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1372_);
lean_dec(v_v_1368_);
lean_dec(v_k_1367_);
if (lean_obj_tag(v_l_1369_) == 0)
{
if (lean_obj_tag(v_r_1370_) == 0)
{
lean_object* v_size_1549_; lean_object* v_k_1550_; lean_object* v_v_1551_; lean_object* v_l_1552_; lean_object* v_r_1553_; lean_object* v_size_1554_; lean_object* v_k_1555_; lean_object* v_v_1556_; lean_object* v_l_1557_; lean_object* v_r_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_size_1549_ = lean_ctor_get(v_l_1369_, 0);
v_k_1550_ = lean_ctor_get(v_l_1369_, 1);
v_v_1551_ = lean_ctor_get(v_l_1369_, 2);
v_l_1552_ = lean_ctor_get(v_l_1369_, 3);
v_r_1553_ = lean_ctor_get(v_l_1369_, 4);
lean_inc(v_r_1553_);
v_size_1554_ = lean_ctor_get(v_r_1370_, 0);
v_k_1555_ = lean_ctor_get(v_r_1370_, 1);
v_v_1556_ = lean_ctor_get(v_r_1370_, 2);
v_l_1557_ = lean_ctor_get(v_r_1370_, 3);
lean_inc(v_l_1557_);
v_r_1558_ = lean_ctor_get(v_r_1370_, 4);
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_dec_lt(v_size_1549_, v_size_1554_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1696_; 
lean_inc(v_l_1552_);
lean_inc(v_v_1551_);
lean_inc(v_k_1550_);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1697_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_l_1369_, 2);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_l_1369_, 1);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_l_1369_, 0);
lean_dec(v_unused_1701_);
v___x_1562_ = v_l_1369_;
v_isShared_1563_ = v_isSharedCheck_1696_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_l_1369_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1696_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v_tree_1565_; 
v___x_1564_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1550_, v_v_1551_, v_l_1552_, v_r_1553_);
v_tree_1565_ = lean_ctor_get(v___x_1564_, 2);
lean_inc(v_tree_1565_);
if (lean_obj_tag(v_tree_1565_) == 0)
{
lean_object* v_k_1566_; lean_object* v_v_1567_; lean_object* v_size_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v_k_1566_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_k_1566_);
v_v_1567_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_v_1567_);
lean_dec_ref(v___x_1564_);
v_size_1568_ = lean_ctor_get(v_tree_1565_, 0);
v___x_1569_ = lean_unsigned_to_nat(3u);
v___x_1570_ = lean_nat_mul(v___x_1569_, v_size_1568_);
v___x_1571_ = lean_nat_dec_lt(v___x_1570_, v_size_1554_);
lean_dec(v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_dec(v_l_1557_);
v___x_1572_ = lean_nat_add(v___x_1559_, v_size_1568_);
v___x_1573_ = lean_nat_add(v___x_1572_, v_size_1554_);
lean_dec(v___x_1572_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_r_1370_);
lean_ctor_set(v___x_1562_, 3, v_tree_1565_);
lean_ctor_set(v___x_1562_, 2, v_v_1567_);
lean_ctor_set(v___x_1562_, 1, v_k_1566_);
lean_ctor_set(v___x_1562_, 0, v___x_1573_);
v___x_1575_ = v___x_1562_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_tree_1565_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_r_1370_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1631_; 
lean_inc(v_r_1558_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
lean_inc(v_size_1554_);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; lean_object* v_unused_1633_; lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; 
v_unused_1632_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1633_);
v_unused_1634_ = lean_ctor_get(v_r_1370_, 2);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_r_1370_, 1);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_r_1370_, 0);
lean_dec(v_unused_1636_);
v___x_1578_ = v_r_1370_;
v_isShared_1579_ = v_isSharedCheck_1631_;
goto v_resetjp_1577_;
}
else
{
lean_dec(v_r_1370_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1631_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_size_1580_; lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v_l_1583_; lean_object* v_r_1584_; lean_object* v_size_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_size_1580_ = lean_ctor_get(v_l_1557_, 0);
v_k_1581_ = lean_ctor_get(v_l_1557_, 1);
v_v_1582_ = lean_ctor_get(v_l_1557_, 2);
v_l_1583_ = lean_ctor_get(v_l_1557_, 3);
v_r_1584_ = lean_ctor_get(v_l_1557_, 4);
v_size_1585_ = lean_ctor_get(v_r_1558_, 0);
v___x_1586_ = lean_unsigned_to_nat(2u);
v___x_1587_ = lean_nat_mul(v___x_1586_, v_size_1585_);
v___x_1588_ = lean_nat_dec_lt(v_size_1580_, v___x_1587_);
lean_dec(v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1616_; 
lean_inc(v_r_1584_);
lean_inc(v_l_1583_);
lean_inc(v_v_1582_);
lean_inc(v_k_1581_);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_l_1557_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; lean_object* v_unused_1621_; 
v_unused_1617_ = lean_ctor_get(v_l_1557_, 4);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_l_1557_, 3);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_l_1557_, 2);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_l_1557_, 1);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_l_1557_, 0);
lean_dec(v_unused_1621_);
v___x_1590_ = v_l_1557_;
v_isShared_1591_ = v_isSharedCheck_1616_;
goto v_resetjp_1589_;
}
else
{
lean_dec(v_l_1557_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1616_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1606_; 
v___x_1592_ = lean_nat_add(v___x_1559_, v_size_1568_);
v___x_1593_ = lean_nat_add(v___x_1592_, v_size_1554_);
lean_dec(v_size_1554_);
if (lean_obj_tag(v_l_1583_) == 0)
{
lean_object* v_size_1614_; 
v_size_1614_ = lean_ctor_get(v_l_1583_, 0);
lean_inc(v_size_1614_);
v___y_1606_ = v_size_1614_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_unsigned_to_nat(0u);
v___y_1606_ = v___x_1615_;
goto v___jp_1605_;
}
v___jp_1594_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_nat_add(v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec(v___y_1596_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 4, v_r_1558_);
lean_ctor_set(v___x_1590_, 3, v_r_1584_);
lean_ctor_set(v___x_1590_, 2, v_v_1556_);
lean_ctor_set(v___x_1590_, 1, v_k_1555_);
lean_ctor_set(v___x_1590_, 0, v___x_1598_);
v___x_1600_ = v___x_1590_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_r_1584_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_r_1558_);
v___x_1600_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1602_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 4, v___x_1600_);
lean_ctor_set(v___x_1578_, 3, v___y_1595_);
lean_ctor_set(v___x_1578_, 2, v_v_1582_);
lean_ctor_set(v___x_1578_, 1, v_k_1581_);
lean_ctor_set(v___x_1578_, 0, v___x_1593_);
v___x_1602_ = v___x_1578_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1581_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1582_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v___y_1595_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
v___jp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_nat_add(v___x_1592_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec(v___x_1592_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_l_1583_);
lean_ctor_set(v___x_1562_, 3, v_tree_1565_);
lean_ctor_set(v___x_1562_, 2, v_v_1567_);
lean_ctor_set(v___x_1562_, 1, v_k_1566_);
lean_ctor_set(v___x_1562_, 0, v___x_1607_);
v___x_1609_ = v___x_1562_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_tree_1565_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_l_1583_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_nat_add(v___x_1559_, v_size_1585_);
if (lean_obj_tag(v_r_1584_) == 0)
{
lean_object* v_size_1611_; 
v_size_1611_ = lean_ctor_get(v_r_1584_, 0);
lean_inc(v_size_1611_);
v___y_1595_ = v___x_1609_;
v___y_1596_ = v___x_1610_;
v___y_1597_ = v_size_1611_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
v___y_1595_ = v___x_1609_;
v___y_1596_ = v___x_1610_;
v___y_1597_ = v___x_1612_;
goto v___jp_1594_;
}
}
}
}
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1622_ = lean_nat_add(v___x_1559_, v_size_1568_);
v___x_1623_ = lean_nat_add(v___x_1622_, v_size_1554_);
lean_dec(v_size_1554_);
v___x_1624_ = lean_nat_add(v___x_1622_, v_size_1580_);
lean_dec(v___x_1622_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 4, v_l_1557_);
lean_ctor_set(v___x_1578_, 3, v_tree_1565_);
lean_ctor_set(v___x_1578_, 2, v_v_1567_);
lean_ctor_set(v___x_1578_, 1, v_k_1566_);
lean_ctor_set(v___x_1578_, 0, v___x_1624_);
v___x_1626_ = v___x_1578_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_tree_1565_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_l_1557_);
v___x_1626_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1628_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_r_1558_);
lean_ctor_set(v___x_1562_, 3, v___x_1626_);
lean_ctor_set(v___x_1562_, 2, v_v_1556_);
lean_ctor_set(v___x_1562_, 1, v_k_1555_);
lean_ctor_set(v___x_1562_, 0, v___x_1623_);
v___x_1628_ = v___x_1562_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1629_, 4, v_r_1558_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
}
else
{
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1690_; 
lean_inc(v_r_1558_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
lean_inc(v_size_1554_);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; lean_object* v_unused_1695_; 
v_unused_1691_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_r_1370_, 2);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_r_1370_, 1);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_r_1370_, 0);
lean_dec(v_unused_1695_);
v___x_1638_ = v_r_1370_;
v_isShared_1639_ = v_isSharedCheck_1690_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v_r_1370_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1690_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
if (lean_obj_tag(v_l_1557_) == 0)
{
if (lean_obj_tag(v_r_1558_) == 0)
{
lean_object* v_k_1640_; lean_object* v_v_1641_; lean_object* v_size_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v_k_1640_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_k_1640_);
v_v_1641_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_v_1641_);
lean_dec_ref(v___x_1564_);
v_size_1642_ = lean_ctor_get(v_l_1557_, 0);
v___x_1643_ = lean_nat_add(v___x_1559_, v_size_1554_);
lean_dec(v_size_1554_);
v___x_1644_ = lean_nat_add(v___x_1559_, v_size_1642_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 4, v_l_1557_);
lean_ctor_set(v___x_1638_, 3, v_tree_1565_);
lean_ctor_set(v___x_1638_, 2, v_v_1641_);
lean_ctor_set(v___x_1638_, 1, v_k_1640_);
lean_ctor_set(v___x_1638_, 0, v___x_1644_);
v___x_1646_ = v___x_1638_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1640_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1641_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_tree_1565_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_l_1557_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1648_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_r_1558_);
lean_ctor_set(v___x_1562_, 3, v___x_1646_);
lean_ctor_set(v___x_1562_, 2, v_v_1556_);
lean_ctor_set(v___x_1562_, 1, v_k_1555_);
lean_ctor_set(v___x_1562_, 0, v___x_1643_);
v___x_1648_ = v___x_1562_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1649_, 4, v_r_1558_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_k_1651_; lean_object* v_v_1652_; lean_object* v_k_1653_; lean_object* v_v_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_size_1554_);
v_k_1651_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_k_1651_);
v_v_1652_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_v_1652_);
lean_dec_ref(v___x_1564_);
v_k_1653_ = lean_ctor_get(v_l_1557_, 1);
v_v_1654_ = lean_ctor_get(v_l_1557_, 2);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_l_1557_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; 
v_unused_1669_ = lean_ctor_get(v_l_1557_, 4);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_l_1557_, 3);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_l_1557_, 0);
lean_dec(v_unused_1671_);
v___x_1656_ = v_l_1557_;
v_isShared_1657_ = v_isSharedCheck_1668_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_v_1654_);
lean_inc(v_k_1653_);
lean_dec(v_l_1557_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1668_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = lean_unsigned_to_nat(3u);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 4, v_r_1558_);
lean_ctor_set(v___x_1656_, 3, v_r_1558_);
lean_ctor_set(v___x_1656_, 2, v_v_1652_);
lean_ctor_set(v___x_1656_, 1, v_k_1651_);
lean_ctor_set(v___x_1656_, 0, v___x_1559_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1651_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1652_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_r_1558_);
v___x_1660_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 3, v_r_1558_);
lean_ctor_set(v___x_1638_, 0, v___x_1559_);
v___x_1662_ = v___x_1638_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_r_1558_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v___x_1662_);
lean_ctor_set(v___x_1562_, 3, v___x_1660_);
lean_ctor_set(v___x_1562_, 2, v_v_1654_);
lean_ctor_set(v___x_1562_, 1, v_k_1653_);
lean_ctor_set(v___x_1562_, 0, v___x_1658_);
v___x_1664_ = v___x_1562_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1653_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1654_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1558_) == 0)
{
lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
lean_dec(v_size_1554_);
v_k_1672_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_k_1672_);
v_v_1673_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_v_1673_);
lean_dec_ref(v___x_1564_);
v___x_1674_ = lean_unsigned_to_nat(3u);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 4, v_l_1557_);
lean_ctor_set(v___x_1638_, 2, v_v_1673_);
lean_ctor_set(v___x_1638_, 1, v_k_1672_);
lean_ctor_set(v___x_1638_, 0, v___x_1559_);
v___x_1676_ = v___x_1638_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_k_1672_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_v_1673_);
lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_l_1557_);
lean_ctor_set(v_reuseFailAlloc_1680_, 4, v_l_1557_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1678_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_r_1558_);
lean_ctor_set(v___x_1562_, 3, v___x_1676_);
lean_ctor_set(v___x_1562_, 2, v_v_1556_);
lean_ctor_set(v___x_1562_, 1, v_k_1555_);
lean_ctor_set(v___x_1562_, 0, v___x_1674_);
v___x_1678_ = v___x_1562_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1679_, 3, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1679_, 4, v_r_1558_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v_k_1681_; lean_object* v_v_1682_; lean_object* v___x_1684_; 
v_k_1681_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_k_1681_);
v_v_1682_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_v_1682_);
lean_dec_ref(v___x_1564_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 3, v_r_1558_);
v___x_1684_ = v___x_1638_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_size_1554_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_r_1558_);
v___x_1684_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_unsigned_to_nat(2u);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v___x_1684_);
lean_ctor_set(v___x_1562_, 3, v_r_1558_);
lean_ctor_set(v___x_1562_, 2, v_v_1682_);
lean_ctor_set(v___x_1562_, 1, v_k_1681_);
lean_ctor_set(v___x_1562_, 0, v___x_1685_);
v___x_1687_ = v___x_1562_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_k_1681_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_v_1682_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v___x_1684_);
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
}
}
}
}
else
{
lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1854_; 
lean_inc(v_r_1558_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_r_1370_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; 
v_unused_1855_ = lean_ctor_get(v_r_1370_, 4);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_r_1370_, 3);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_r_1370_, 2);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_r_1370_, 1);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_r_1370_, 0);
lean_dec(v_unused_1859_);
v___x_1703_ = v_r_1370_;
v_isShared_1704_ = v_isSharedCheck_1854_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_r_1370_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1854_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v_tree_1706_; 
v___x_1705_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1555_, v_v_1556_, v_l_1557_, v_r_1558_);
v_tree_1706_ = lean_ctor_get(v___x_1705_, 2);
lean_inc(v_tree_1706_);
if (lean_obj_tag(v_tree_1706_) == 0)
{
lean_object* v_k_1707_; lean_object* v_v_1708_; lean_object* v_size_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_k_1707_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1707_);
v_v_1708_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1708_);
lean_dec_ref(v___x_1705_);
v_size_1709_ = lean_ctor_get(v_tree_1706_, 0);
v___x_1710_ = lean_unsigned_to_nat(3u);
v___x_1711_ = lean_nat_mul(v___x_1710_, v_size_1709_);
v___x_1712_ = lean_nat_dec_lt(v___x_1711_, v_size_1549_);
lean_dec(v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec(v_r_1553_);
v___x_1713_ = lean_nat_add(v___x_1559_, v_size_1549_);
v___x_1714_ = lean_nat_add(v___x_1713_, v_size_1709_);
lean_dec(v___x_1713_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_tree_1706_);
lean_ctor_set(v___x_1703_, 3, v_l_1369_);
lean_ctor_set(v___x_1703_, 2, v_v_1708_);
lean_ctor_set(v___x_1703_, 1, v_k_1707_);
lean_ctor_set(v___x_1703_, 0, v___x_1714_);
v___x_1716_ = v___x_1703_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_l_1369_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v_tree_1706_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
else
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1783_; 
lean_inc(v_l_1552_);
lean_inc(v_v_1551_);
lean_inc(v_k_1550_);
lean_inc(v_size_1549_);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; lean_object* v_unused_1785_; lean_object* v_unused_1786_; lean_object* v_unused_1787_; lean_object* v_unused_1788_; 
v_unused_1784_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_1784_);
v_unused_1785_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_1785_);
v_unused_1786_ = lean_ctor_get(v_l_1369_, 2);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v_l_1369_, 1);
lean_dec(v_unused_1787_);
v_unused_1788_ = lean_ctor_get(v_l_1369_, 0);
lean_dec(v_unused_1788_);
v___x_1719_ = v_l_1369_;
v_isShared_1720_ = v_isSharedCheck_1783_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v_l_1369_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1783_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_size_1721_; lean_object* v_size_1722_; lean_object* v_k_1723_; lean_object* v_v_1724_; lean_object* v_l_1725_; lean_object* v_r_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_size_1721_ = lean_ctor_get(v_l_1552_, 0);
v_size_1722_ = lean_ctor_get(v_r_1553_, 0);
v_k_1723_ = lean_ctor_get(v_r_1553_, 1);
v_v_1724_ = lean_ctor_get(v_r_1553_, 2);
v_l_1725_ = lean_ctor_get(v_r_1553_, 3);
v_r_1726_ = lean_ctor_get(v_r_1553_, 4);
v___x_1727_ = lean_unsigned_to_nat(2u);
v___x_1728_ = lean_nat_mul(v___x_1727_, v_size_1721_);
v___x_1729_ = lean_nat_dec_lt(v_size_1722_, v___x_1728_);
lean_dec(v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1767_; 
lean_inc(v_r_1726_);
lean_inc(v_l_1725_);
lean_inc(v_v_1724_);
lean_inc(v_k_1723_);
lean_del_object(v___x_1719_);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_r_1553_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; lean_object* v_unused_1769_; lean_object* v_unused_1770_; lean_object* v_unused_1771_; lean_object* v_unused_1772_; 
v_unused_1768_ = lean_ctor_get(v_r_1553_, 4);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_r_1553_, 3);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_r_1553_, 2);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_r_1553_, 1);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_r_1553_, 0);
lean_dec(v_unused_1772_);
v___x_1731_ = v_r_1553_;
v_isShared_1732_ = v_isSharedCheck_1767_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v_r_1553_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1767_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___x_1755_; lean_object* v___y_1757_; 
v___x_1733_ = lean_nat_add(v___x_1559_, v_size_1549_);
lean_dec(v_size_1549_);
v___x_1734_ = lean_nat_add(v___x_1733_, v_size_1709_);
lean_dec(v___x_1733_);
v___x_1755_ = lean_nat_add(v___x_1559_, v_size_1721_);
if (lean_obj_tag(v_l_1725_) == 0)
{
lean_object* v_size_1765_; 
v_size_1765_ = lean_ctor_get(v_l_1725_, 0);
lean_inc(v_size_1765_);
v___y_1757_ = v_size_1765_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_unsigned_to_nat(0u);
v___y_1757_ = v___x_1766_;
goto v___jp_1756_;
}
v___jp_1735_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_nat_add(v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec(v___y_1737_);
lean_inc_ref(v_tree_1706_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 4, v_tree_1706_);
lean_ctor_set(v___x_1731_, 3, v_r_1726_);
lean_ctor_set(v___x_1731_, 2, v_v_1708_);
lean_ctor_set(v___x_1731_, 1, v_k_1707_);
lean_ctor_set(v___x_1731_, 0, v___x_1739_);
v___x_1741_ = v___x_1731_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_r_1726_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v_tree_1706_);
v___x_1741_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
v_isSharedCheck_1748_ = !lean_is_exclusive(v_tree_1706_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; lean_object* v_unused_1750_; lean_object* v_unused_1751_; lean_object* v_unused_1752_; lean_object* v_unused_1753_; 
v_unused_1749_ = lean_ctor_get(v_tree_1706_, 4);
lean_dec(v_unused_1749_);
v_unused_1750_ = lean_ctor_get(v_tree_1706_, 3);
lean_dec(v_unused_1750_);
v_unused_1751_ = lean_ctor_get(v_tree_1706_, 2);
lean_dec(v_unused_1751_);
v_unused_1752_ = lean_ctor_get(v_tree_1706_, 1);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v_tree_1706_, 0);
lean_dec(v_unused_1753_);
v___x_1743_ = v_tree_1706_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v_tree_1706_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 4, v___x_1741_);
lean_ctor_set(v___x_1743_, 3, v___y_1736_);
lean_ctor_set(v___x_1743_, 2, v_v_1724_);
lean_ctor_set(v___x_1743_, 1, v_k_1723_);
lean_ctor_set(v___x_1743_, 0, v___x_1734_);
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_k_1723_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_v_1724_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v___y_1736_);
lean_ctor_set(v_reuseFailAlloc_1747_, 4, v___x_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
v___jp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = lean_nat_add(v___x_1755_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec(v___x_1755_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_l_1725_);
lean_ctor_set(v___x_1703_, 3, v_l_1552_);
lean_ctor_set(v___x_1703_, 2, v_v_1551_);
lean_ctor_set(v___x_1703_, 1, v_k_1550_);
lean_ctor_set(v___x_1703_, 0, v___x_1758_);
v___x_1760_ = v___x_1703_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_l_1552_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_l_1725_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_nat_add(v___x_1559_, v_size_1709_);
if (lean_obj_tag(v_r_1726_) == 0)
{
lean_object* v_size_1762_; 
v_size_1762_ = lean_ctor_get(v_r_1726_, 0);
lean_inc(v_size_1762_);
v___y_1736_ = v___x_1760_;
v___y_1737_ = v___x_1761_;
v___y_1738_ = v_size_1762_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v___y_1736_ = v___x_1760_;
v___y_1737_ = v___x_1761_;
v___y_1738_ = v___x_1763_;
goto v___jp_1735_;
}
}
}
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1773_ = lean_nat_add(v___x_1559_, v_size_1549_);
lean_dec(v_size_1549_);
v___x_1774_ = lean_nat_add(v___x_1773_, v_size_1709_);
lean_dec(v___x_1773_);
v___x_1775_ = lean_nat_add(v___x_1559_, v_size_1709_);
v___x_1776_ = lean_nat_add(v___x_1775_, v_size_1722_);
lean_dec(v___x_1775_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_tree_1706_);
lean_ctor_set(v___x_1703_, 3, v_r_1553_);
lean_ctor_set(v___x_1703_, 2, v_v_1708_);
lean_ctor_set(v___x_1703_, 1, v_k_1707_);
lean_ctor_set(v___x_1703_, 0, v___x_1776_);
v___x_1778_ = v___x_1703_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_r_1553_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v_tree_1706_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v___x_1778_);
lean_ctor_set(v___x_1719_, 0, v___x_1774_);
v___x_1780_ = v___x_1719_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_l_1552_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1552_) == 0)
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1812_; 
lean_inc_ref(v_l_1552_);
lean_inc(v_v_1551_);
lean_inc(v_k_1550_);
lean_inc(v_size_1549_);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; lean_object* v_unused_1814_; lean_object* v_unused_1815_; lean_object* v_unused_1816_; lean_object* v_unused_1817_; 
v_unused_1813_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_1813_);
v_unused_1814_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_1814_);
v_unused_1815_ = lean_ctor_get(v_l_1369_, 2);
lean_dec(v_unused_1815_);
v_unused_1816_ = lean_ctor_get(v_l_1369_, 1);
lean_dec(v_unused_1816_);
v_unused_1817_ = lean_ctor_get(v_l_1369_, 0);
lean_dec(v_unused_1817_);
v___x_1790_ = v_l_1369_;
v_isShared_1791_ = v_isSharedCheck_1812_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v_l_1369_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1812_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
if (lean_obj_tag(v_r_1553_) == 0)
{
lean_object* v_k_1792_; lean_object* v_v_1793_; lean_object* v_size_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v_k_1792_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1792_);
v_v_1793_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1793_);
lean_dec_ref(v___x_1705_);
v_size_1794_ = lean_ctor_get(v_r_1553_, 0);
v___x_1795_ = lean_nat_add(v___x_1559_, v_size_1549_);
lean_dec(v_size_1549_);
v___x_1796_ = lean_nat_add(v___x_1559_, v_size_1794_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_tree_1706_);
lean_ctor_set(v___x_1703_, 3, v_r_1553_);
lean_ctor_set(v___x_1703_, 2, v_v_1793_);
lean_ctor_set(v___x_1703_, 1, v_k_1792_);
lean_ctor_set(v___x_1703_, 0, v___x_1796_);
v___x_1798_ = v___x_1703_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_k_1792_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_v_1793_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v_r_1553_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v_tree_1706_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1800_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 4, v___x_1798_);
lean_ctor_set(v___x_1790_, 0, v___x_1795_);
v___x_1800_ = v___x_1790_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_l_1552_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
else
{
lean_object* v_k_1803_; lean_object* v_v_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
lean_dec(v_size_1549_);
v_k_1803_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1803_);
v_v_1804_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1804_);
lean_dec_ref(v___x_1705_);
v___x_1805_ = lean_unsigned_to_nat(3u);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_r_1553_);
lean_ctor_set(v___x_1703_, 3, v_r_1553_);
lean_ctor_set(v___x_1703_, 2, v_v_1804_);
lean_ctor_set(v___x_1703_, 1, v_k_1803_);
lean_ctor_set(v___x_1703_, 0, v___x_1559_);
v___x_1807_ = v___x_1703_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_k_1803_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_v_1804_);
lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_r_1553_);
lean_ctor_set(v_reuseFailAlloc_1811_, 4, v_r_1553_);
v___x_1807_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 4, v___x_1807_);
lean_ctor_set(v___x_1790_, 0, v___x_1805_);
v___x_1809_ = v___x_1790_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1810_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1810_, 3, v_l_1552_);
lean_ctor_set(v_reuseFailAlloc_1810_, 4, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1553_) == 0)
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1842_; 
lean_inc(v_l_1552_);
lean_inc(v_v_1551_);
lean_inc(v_k_1550_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; lean_object* v_unused_1844_; lean_object* v_unused_1845_; lean_object* v_unused_1846_; lean_object* v_unused_1847_; 
v_unused_1843_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_1843_);
v_unused_1844_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v_l_1369_, 2);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v_l_1369_, 1);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v_l_1369_, 0);
lean_dec(v_unused_1847_);
v___x_1819_ = v_l_1369_;
v_isShared_1820_ = v_isSharedCheck_1842_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v_l_1369_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1842_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_k_1821_; lean_object* v_v_1822_; lean_object* v_k_1823_; lean_object* v_v_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1838_; 
v_k_1821_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1821_);
v_v_1822_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1822_);
lean_dec_ref(v___x_1705_);
v_k_1823_ = lean_ctor_get(v_r_1553_, 1);
v_v_1824_ = lean_ctor_get(v_r_1553_, 2);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_r_1553_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; lean_object* v_unused_1840_; lean_object* v_unused_1841_; 
v_unused_1839_ = lean_ctor_get(v_r_1553_, 4);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_r_1553_, 3);
lean_dec(v_unused_1840_);
v_unused_1841_ = lean_ctor_get(v_r_1553_, 0);
lean_dec(v_unused_1841_);
v___x_1826_ = v_r_1553_;
v_isShared_1827_ = v_isSharedCheck_1838_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_v_1824_);
lean_inc(v_k_1823_);
lean_dec(v_r_1553_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1838_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_unsigned_to_nat(3u);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 4, v_l_1552_);
lean_ctor_set(v___x_1826_, 3, v_l_1552_);
lean_ctor_set(v___x_1826_, 2, v_v_1551_);
lean_ctor_set(v___x_1826_, 1, v_k_1550_);
lean_ctor_set(v___x_1826_, 0, v___x_1559_);
v___x_1830_ = v___x_1826_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1837_, 3, v_l_1552_);
lean_ctor_set(v_reuseFailAlloc_1837_, 4, v_l_1552_);
v___x_1830_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_l_1552_);
lean_ctor_set(v___x_1703_, 3, v_l_1552_);
lean_ctor_set(v___x_1703_, 2, v_v_1822_);
lean_ctor_set(v___x_1703_, 1, v_k_1821_);
lean_ctor_set(v___x_1703_, 0, v___x_1559_);
v___x_1832_ = v___x_1703_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_k_1821_);
lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_v_1822_);
lean_ctor_set(v_reuseFailAlloc_1836_, 3, v_l_1552_);
lean_ctor_set(v_reuseFailAlloc_1836_, 4, v_l_1552_);
v___x_1832_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v___x_1832_);
lean_ctor_set(v___x_1819_, 3, v___x_1830_);
lean_ctor_set(v___x_1819_, 2, v_v_1824_);
lean_ctor_set(v___x_1819_, 1, v_k_1823_);
lean_ctor_set(v___x_1819_, 0, v___x_1828_);
v___x_1834_ = v___x_1819_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_k_1823_);
lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_v_1824_);
lean_ctor_set(v_reuseFailAlloc_1835_, 3, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1835_, 4, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
else
{
lean_object* v_k_1848_; lean_object* v_v_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v_k_1848_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1848_);
v_v_1849_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1849_);
lean_dec_ref(v___x_1705_);
v___x_1850_ = lean_unsigned_to_nat(2u);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_r_1553_);
lean_ctor_set(v___x_1703_, 3, v_l_1369_);
lean_ctor_set(v___x_1703_, 2, v_v_1849_);
lean_ctor_set(v___x_1703_, 1, v_k_1848_);
lean_ctor_set(v___x_1703_, 0, v___x_1850_);
v___x_1852_ = v___x_1703_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_k_1848_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_v_1849_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_l_1369_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v_r_1553_);
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
return v_l_1369_;
}
}
else
{
return v_r_1370_;
}
}
default: 
{
lean_object* v_impl_1860_; lean_object* v___x_1861_; 
v_impl_1860_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1365_, v_r_1370_);
v___x_1861_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1860_) == 0)
{
if (lean_obj_tag(v_l_1369_) == 0)
{
lean_object* v_size_1862_; lean_object* v_size_1863_; lean_object* v_k_1864_; lean_object* v_v_1865_; lean_object* v_l_1866_; lean_object* v_r_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_size_1862_ = lean_ctor_get(v_impl_1860_, 0);
lean_inc(v_size_1862_);
v_size_1863_ = lean_ctor_get(v_l_1369_, 0);
v_k_1864_ = lean_ctor_get(v_l_1369_, 1);
v_v_1865_ = lean_ctor_get(v_l_1369_, 2);
v_l_1866_ = lean_ctor_get(v_l_1369_, 3);
v_r_1867_ = lean_ctor_get(v_l_1369_, 4);
lean_inc(v_r_1867_);
v___x_1868_ = lean_unsigned_to_nat(3u);
v___x_1869_ = lean_nat_mul(v___x_1868_, v_size_1862_);
v___x_1870_ = lean_nat_dec_lt(v___x_1869_, v_size_1863_);
lean_dec(v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec(v_r_1867_);
v___x_1871_ = lean_nat_add(v___x_1861_, v_size_1863_);
v___x_1872_ = lean_nat_add(v___x_1871_, v_size_1862_);
lean_dec(v_size_1862_);
lean_dec(v___x_1871_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v_impl_1860_);
lean_ctor_set(v___x_1372_, 0, v___x_1872_);
v___x_1874_ = v___x_1372_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_l_1369_);
lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_impl_1860_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
else
{
lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1941_; 
lean_inc(v_l_1866_);
lean_inc(v_v_1865_);
lean_inc(v_k_1864_);
lean_inc(v_size_1863_);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; lean_object* v_unused_1943_; lean_object* v_unused_1944_; lean_object* v_unused_1945_; lean_object* v_unused_1946_; 
v_unused_1942_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_1942_);
v_unused_1943_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_1943_);
v_unused_1944_ = lean_ctor_get(v_l_1369_, 2);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_l_1369_, 1);
lean_dec(v_unused_1945_);
v_unused_1946_ = lean_ctor_get(v_l_1369_, 0);
lean_dec(v_unused_1946_);
v___x_1877_ = v_l_1369_;
v_isShared_1878_ = v_isSharedCheck_1941_;
goto v_resetjp_1876_;
}
else
{
lean_dec(v_l_1369_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1941_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_size_1879_; lean_object* v_size_1880_; lean_object* v_k_1881_; lean_object* v_v_1882_; lean_object* v_l_1883_; lean_object* v_r_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_size_1879_ = lean_ctor_get(v_l_1866_, 0);
v_size_1880_ = lean_ctor_get(v_r_1867_, 0);
v_k_1881_ = lean_ctor_get(v_r_1867_, 1);
v_v_1882_ = lean_ctor_get(v_r_1867_, 2);
v_l_1883_ = lean_ctor_get(v_r_1867_, 3);
v_r_1884_ = lean_ctor_get(v_r_1867_, 4);
v___x_1885_ = lean_unsigned_to_nat(2u);
v___x_1886_ = lean_nat_mul(v___x_1885_, v_size_1879_);
v___x_1887_ = lean_nat_dec_lt(v_size_1880_, v___x_1886_);
lean_dec(v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1916_; 
lean_inc(v_r_1884_);
lean_inc(v_l_1883_);
lean_inc(v_v_1882_);
lean_inc(v_k_1881_);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_r_1867_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; lean_object* v_unused_1918_; lean_object* v_unused_1919_; lean_object* v_unused_1920_; lean_object* v_unused_1921_; 
v_unused_1917_ = lean_ctor_get(v_r_1867_, 4);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_r_1867_, 3);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_r_1867_, 2);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_r_1867_, 1);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_r_1867_, 0);
lean_dec(v_unused_1921_);
v___x_1889_ = v_r_1867_;
v_isShared_1890_ = v_isSharedCheck_1916_;
goto v_resetjp_1888_;
}
else
{
lean_dec(v_r_1867_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1916_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___x_1904_; lean_object* v___y_1906_; 
v___x_1891_ = lean_nat_add(v___x_1861_, v_size_1863_);
lean_dec(v_size_1863_);
v___x_1892_ = lean_nat_add(v___x_1891_, v_size_1862_);
lean_dec(v___x_1891_);
v___x_1904_ = lean_nat_add(v___x_1861_, v_size_1879_);
if (lean_obj_tag(v_l_1883_) == 0)
{
lean_object* v_size_1914_; 
v_size_1914_ = lean_ctor_get(v_l_1883_, 0);
lean_inc(v_size_1914_);
v___y_1906_ = v_size_1914_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___y_1906_ = v___x_1915_;
goto v___jp_1905_;
}
v___jp_1893_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_nat_add(v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec(v___y_1895_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 4, v_impl_1860_);
lean_ctor_set(v___x_1889_, 3, v_r_1884_);
lean_ctor_set(v___x_1889_, 2, v_v_1368_);
lean_ctor_set(v___x_1889_, 1, v_k_1367_);
lean_ctor_set(v___x_1889_, 0, v___x_1897_);
v___x_1899_ = v___x_1889_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_r_1884_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_impl_1860_);
v___x_1899_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1901_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 4, v___x_1899_);
lean_ctor_set(v___x_1877_, 3, v___y_1894_);
lean_ctor_set(v___x_1877_, 2, v_v_1882_);
lean_ctor_set(v___x_1877_, 1, v_k_1881_);
lean_ctor_set(v___x_1877_, 0, v___x_1892_);
v___x_1901_ = v___x_1877_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_k_1881_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_v_1882_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v___y_1894_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
v___jp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_nat_add(v___x_1904_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec(v___x_1904_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v_l_1883_);
lean_ctor_set(v___x_1372_, 3, v_l_1866_);
lean_ctor_set(v___x_1372_, 2, v_v_1865_);
lean_ctor_set(v___x_1372_, 1, v_k_1864_);
lean_ctor_set(v___x_1372_, 0, v___x_1907_);
v___x_1909_ = v___x_1372_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_k_1864_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_v_1865_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_l_1866_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_l_1883_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_nat_add(v___x_1861_, v_size_1862_);
lean_dec(v_size_1862_);
if (lean_obj_tag(v_r_1884_) == 0)
{
lean_object* v_size_1911_; 
v_size_1911_ = lean_ctor_get(v_r_1884_, 0);
lean_inc(v_size_1911_);
v___y_1894_ = v___x_1909_;
v___y_1895_ = v___x_1910_;
v___y_1896_ = v_size_1911_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___y_1894_ = v___x_1909_;
v___y_1895_ = v___x_1910_;
v___y_1896_ = v___x_1912_;
goto v___jp_1893_;
}
}
}
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
lean_del_object(v___x_1372_);
v___x_1922_ = lean_nat_add(v___x_1861_, v_size_1863_);
lean_dec(v_size_1863_);
v___x_1923_ = lean_nat_add(v___x_1922_, v_size_1862_);
lean_dec(v___x_1922_);
v___x_1924_ = lean_nat_add(v___x_1861_, v_size_1862_);
lean_dec(v_size_1862_);
v___x_1925_ = lean_nat_add(v___x_1924_, v_size_1880_);
lean_dec(v___x_1924_);
lean_inc_ref(v_impl_1860_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 4, v_impl_1860_);
lean_ctor_set(v___x_1877_, 3, v_r_1867_);
lean_ctor_set(v___x_1877_, 2, v_v_1368_);
lean_ctor_set(v___x_1877_, 1, v_k_1367_);
lean_ctor_set(v___x_1877_, 0, v___x_1925_);
v___x_1927_ = v___x_1877_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_r_1867_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_impl_1860_);
v___x_1927_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_isSharedCheck_1934_ = !lean_is_exclusive(v_impl_1860_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; lean_object* v_unused_1936_; lean_object* v_unused_1937_; lean_object* v_unused_1938_; lean_object* v_unused_1939_; 
v_unused_1935_ = lean_ctor_get(v_impl_1860_, 4);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_impl_1860_, 3);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_impl_1860_, 2);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_impl_1860_, 1);
lean_dec(v_unused_1938_);
v_unused_1939_ = lean_ctor_get(v_impl_1860_, 0);
lean_dec(v_unused_1939_);
v___x_1929_ = v_impl_1860_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_dec(v_impl_1860_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 4, v___x_1927_);
lean_ctor_set(v___x_1929_, 3, v_l_1866_);
lean_ctor_set(v___x_1929_, 2, v_v_1865_);
lean_ctor_set(v___x_1929_, 1, v_k_1864_);
lean_ctor_set(v___x_1929_, 0, v___x_1923_);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_k_1864_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_v_1865_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_l_1866_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v___x_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v_size_1947_ = lean_ctor_get(v_impl_1860_, 0);
lean_inc(v_size_1947_);
v___x_1948_ = lean_nat_add(v___x_1861_, v_size_1947_);
lean_dec(v_size_1947_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v_impl_1860_);
lean_ctor_set(v___x_1372_, 0, v___x_1948_);
v___x_1950_ = v___x_1372_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_l_1369_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_impl_1860_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
else
{
if (lean_obj_tag(v_l_1369_) == 0)
{
lean_object* v_l_1952_; 
v_l_1952_ = lean_ctor_get(v_l_1369_, 3);
if (lean_obj_tag(v_l_1952_) == 0)
{
lean_object* v_r_1953_; 
lean_inc_ref(v_l_1952_);
v_r_1953_ = lean_ctor_get(v_l_1369_, 4);
lean_inc(v_r_1953_);
if (lean_obj_tag(v_r_1953_) == 0)
{
lean_object* v_size_1954_; lean_object* v_k_1955_; lean_object* v_v_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1969_; 
v_size_1954_ = lean_ctor_get(v_l_1369_, 0);
v_k_1955_ = lean_ctor_get(v_l_1369_, 1);
v_v_1956_ = lean_ctor_get(v_l_1369_, 2);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; lean_object* v_unused_1971_; 
v_unused_1970_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_1971_);
v___x_1958_ = v_l_1369_;
v_isShared_1959_ = v_isSharedCheck_1969_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_v_1956_);
lean_inc(v_k_1955_);
lean_inc(v_size_1954_);
lean_dec(v_l_1369_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1969_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_size_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v_size_1960_ = lean_ctor_get(v_r_1953_, 0);
v___x_1961_ = lean_nat_add(v___x_1861_, v_size_1954_);
lean_dec(v_size_1954_);
v___x_1962_ = lean_nat_add(v___x_1861_, v_size_1960_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v_impl_1860_);
lean_ctor_set(v___x_1958_, 3, v_r_1953_);
lean_ctor_set(v___x_1958_, 2, v_v_1368_);
lean_ctor_set(v___x_1958_, 1, v_k_1367_);
lean_ctor_set(v___x_1958_, 0, v___x_1962_);
v___x_1964_ = v___x_1958_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v_r_1953_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v_impl_1860_);
v___x_1964_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___x_1964_);
lean_ctor_set(v___x_1372_, 3, v_l_1952_);
lean_ctor_set(v___x_1372_, 2, v_v_1956_);
lean_ctor_set(v___x_1372_, 1, v_k_1955_);
lean_ctor_set(v___x_1372_, 0, v___x_1961_);
v___x_1966_ = v___x_1372_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_k_1955_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_v_1956_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_l_1952_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_k_1972_; lean_object* v_v_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1984_; 
v_k_1972_ = lean_ctor_get(v_l_1369_, 1);
v_v_1973_ = lean_ctor_get(v_l_1369_, 2);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; lean_object* v_unused_1986_; lean_object* v_unused_1987_; 
v_unused_1985_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_1986_);
v_unused_1987_ = lean_ctor_get(v_l_1369_, 0);
lean_dec(v_unused_1987_);
v___x_1975_ = v_l_1369_;
v_isShared_1976_ = v_isSharedCheck_1984_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_v_1973_);
lean_inc(v_k_1972_);
lean_dec(v_l_1369_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1984_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_unsigned_to_nat(3u);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 3, v_r_1953_);
lean_ctor_set(v___x_1975_, 2, v_v_1368_);
lean_ctor_set(v___x_1975_, 1, v_k_1367_);
lean_ctor_set(v___x_1975_, 0, v___x_1861_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_r_1953_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v_r_1953_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___x_1979_);
lean_ctor_set(v___x_1372_, 3, v_l_1952_);
lean_ctor_set(v___x_1372_, 2, v_v_1973_);
lean_ctor_set(v___x_1372_, 1, v_k_1972_);
lean_ctor_set(v___x_1372_, 0, v___x_1977_);
v___x_1981_ = v___x_1372_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_k_1972_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_v_1973_);
lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_l_1952_);
lean_ctor_set(v_reuseFailAlloc_1982_, 4, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
else
{
lean_object* v_r_1988_; 
v_r_1988_ = lean_ctor_get(v_l_1369_, 4);
lean_inc(v_r_1988_);
if (lean_obj_tag(v_r_1988_) == 0)
{
lean_object* v_k_1989_; lean_object* v_v_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2013_; 
lean_inc(v_l_1952_);
v_k_1989_ = lean_ctor_get(v_l_1369_, 1);
v_v_1990_ = lean_ctor_get(v_l_1369_, 2);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; lean_object* v_unused_2015_; lean_object* v_unused_2016_; 
v_unused_2014_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_l_1369_, 0);
lean_dec(v_unused_2016_);
v___x_1992_ = v_l_1369_;
v_isShared_1993_ = v_isSharedCheck_2013_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_v_1990_);
lean_inc(v_k_1989_);
lean_dec(v_l_1369_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2013_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_k_1994_; lean_object* v_v_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2009_; 
v_k_1994_ = lean_ctor_get(v_r_1988_, 1);
v_v_1995_ = lean_ctor_get(v_r_1988_, 2);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_r_1988_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; lean_object* v_unused_2011_; lean_object* v_unused_2012_; 
v_unused_2010_ = lean_ctor_get(v_r_1988_, 4);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_r_1988_, 3);
lean_dec(v_unused_2011_);
v_unused_2012_ = lean_ctor_get(v_r_1988_, 0);
lean_dec(v_unused_2012_);
v___x_1997_ = v_r_1988_;
v_isShared_1998_ = v_isSharedCheck_2009_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_v_1995_);
lean_inc(v_k_1994_);
lean_dec(v_r_1988_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2009_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_unsigned_to_nat(3u);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_l_1952_);
lean_ctor_set(v___x_1997_, 3, v_l_1952_);
lean_ctor_set(v___x_1997_, 2, v_v_1990_);
lean_ctor_set(v___x_1997_, 1, v_k_1989_);
lean_ctor_set(v___x_1997_, 0, v___x_1861_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_k_1989_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_v_1990_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_l_1952_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_l_1952_);
v___x_2001_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2003_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v_l_1952_);
lean_ctor_set(v___x_1992_, 2, v_v_1368_);
lean_ctor_set(v___x_1992_, 1, v_k_1367_);
lean_ctor_set(v___x_1992_, 0, v___x_1861_);
v___x_2003_ = v___x_1992_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_l_1952_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_l_1952_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___x_2003_);
lean_ctor_set(v___x_1372_, 3, v___x_2001_);
lean_ctor_set(v___x_1372_, 2, v_v_1995_);
lean_ctor_set(v___x_1372_, 1, v_k_1994_);
lean_ctor_set(v___x_1372_, 0, v___x_1999_);
v___x_2005_ = v___x_1372_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_k_1994_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_v_1995_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v___x_2003_);
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
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = lean_unsigned_to_nat(2u);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v_r_1988_);
lean_ctor_set(v___x_1372_, 0, v___x_2017_);
v___x_2019_ = v___x_1372_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_2020_, 3, v_l_1369_);
lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_r_1988_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v___x_2022_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v_l_1369_);
lean_ctor_set(v___x_1372_, 0, v___x_1861_);
v___x_2022_ = v___x_1372_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_l_1369_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v_l_1369_);
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
}
else
{
return v_t_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2026_, lean_object* v_t_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2026_, v_t_2027_);
lean_dec(v_k_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2029_, lean_object* v_v_2030_, lean_object* v_i_2031_){
_start:
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = lean_array_get_size(v_xs_2029_);
v___x_2033_ = lean_nat_dec_lt(v_i_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_dec(v_i_2031_);
v___x_2034_ = lean_box(0);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_array_fget_borrowed(v_xs_2029_, v_i_2031_);
v___x_2036_ = l_Lean_instBEqFVarId_beq(v___x_2035_, v_v_2030_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_unsigned_to_nat(1u);
v___x_2038_ = lean_nat_add(v_i_2031_, v___x_2037_);
lean_dec(v_i_2031_);
v_i_2031_ = v___x_2038_;
goto _start;
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_i_2031_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2041_, lean_object* v_v_2042_, lean_object* v_i_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2041_, v_v_2042_, v_i_2043_);
lean_dec(v_v_2042_);
lean_dec_ref(v_xs_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2045_, lean_object* v_v_2046_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2045_, v_v_2046_, v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2049_, lean_object* v_v_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2049_, v_v_2050_);
lean_dec(v_v_2050_);
lean_dec_ref(v_xs_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2052_, size_t v_x_2053_, lean_object* v_x_2054_){
_start:
{
if (lean_obj_tag(v_x_2052_) == 0)
{
lean_object* v_es_2055_; lean_object* v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; lean_object* v_j_2059_; lean_object* v_entry_2060_; 
v_es_2055_ = lean_ctor_get(v_x_2052_, 0);
v___x_2056_ = lean_box(2);
v___x_2057_ = ((size_t)31ULL);
v___x_2058_ = lean_usize_land(v_x_2053_, v___x_2057_);
v_j_2059_ = lean_usize_to_nat(v___x_2058_);
v_entry_2060_ = lean_array_get(v___x_2056_, v_es_2055_, v_j_2059_);
switch(lean_obj_tag(v_entry_2060_))
{
case 0:
{
lean_object* v_key_2061_; uint8_t v___x_2062_; 
v_key_2061_ = lean_ctor_get(v_entry_2060_, 0);
lean_inc(v_key_2061_);
lean_dec_ref_known(v_entry_2060_, 2);
v___x_2062_ = l_Lean_instBEqFVarId_beq(v_x_2054_, v_key_2061_);
lean_dec(v_key_2061_);
if (v___x_2062_ == 0)
{
lean_dec(v_j_2059_);
return v_x_2052_;
}
else
{
lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2070_; 
lean_inc_ref(v_es_2055_);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_x_2052_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v_x_2052_, 0);
lean_dec(v_unused_2071_);
v___x_2064_ = v_x_2052_;
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
else
{
lean_dec(v_x_2052_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_array_set(v_es_2055_, v_j_2059_, v___x_2056_);
lean_dec(v_j_2059_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
case 1:
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2106_; 
lean_inc_ref(v_es_2055_);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_x_2052_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; 
v_unused_2107_ = lean_ctor_get(v_x_2052_, 0);
lean_dec(v_unused_2107_);
v___x_2073_ = v_x_2052_;
v_isShared_2074_ = v_isSharedCheck_2106_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v_x_2052_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2106_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_node_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2105_; 
v_node_2075_ = lean_ctor_get(v_entry_2060_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_entry_2060_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2077_ = v_entry_2060_;
v_isShared_2078_ = v_isSharedCheck_2105_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_node_2075_);
lean_dec(v_entry_2060_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2105_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
size_t v___x_2079_; lean_object* v_entries_2080_; size_t v___x_2081_; lean_object* v_newNode_2082_; lean_object* v___x_2083_; 
v___x_2079_ = ((size_t)5ULL);
v_entries_2080_ = lean_array_set(v_es_2055_, v_j_2059_, v___x_2056_);
v___x_2081_ = lean_usize_shift_right(v_x_2053_, v___x_2079_);
v_newNode_2082_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2075_, v___x_2081_, v_x_2054_);
lean_inc_ref(v_newNode_2082_);
v___x_2083_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2082_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2085_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v_newNode_2082_);
v___x_2085_ = v___x_2077_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_newNode_2082_);
v___x_2085_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_array_set(v_entries_2080_, v_j_2059_, v___x_2085_);
lean_dec(v_j_2059_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2086_);
v___x_2088_ = v___x_2073_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
else
{
lean_object* v_val_2091_; lean_object* v_fst_2092_; lean_object* v_snd_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_newNode_2082_);
lean_del_object(v___x_2077_);
v_val_2091_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_val_2091_);
lean_dec_ref_known(v___x_2083_, 1);
v_fst_2092_ = lean_ctor_get(v_val_2091_, 0);
v_snd_2093_ = lean_ctor_get(v_val_2091_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_val_2091_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2095_ = v_val_2091_;
v_isShared_2096_ = v_isSharedCheck_2104_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_snd_2093_);
lean_inc(v_fst_2092_);
lean_dec(v_val_2091_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2104_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_fst_2092_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_snd_2093_);
v___x_2098_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_array_set(v_entries_2080_, v_j_2059_, v___x_2098_);
lean_dec(v_j_2059_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2099_);
v___x_2101_ = v___x_2073_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2059_);
return v_x_2052_;
}
}
}
else
{
lean_object* v_ks_2108_; lean_object* v_vs_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2123_; 
v_ks_2108_ = lean_ctor_get(v_x_2052_, 0);
v_vs_2109_ = lean_ctor_get(v_x_2052_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_x_2052_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2111_ = v_x_2052_;
v_isShared_2112_ = v_isSharedCheck_2123_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_vs_2109_);
lean_inc(v_ks_2108_);
lean_dec(v_x_2052_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2123_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2108_, v_x_2054_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2115_; 
if (v_isShared_2112_ == 0)
{
v___x_2115_ = v___x_2111_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_ks_2108_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_vs_2109_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
else
{
lean_object* v_val_2117_; lean_object* v_keys_x27_2118_; lean_object* v_vals_x27_2119_; lean_object* v___x_2121_; 
v_val_2117_ = lean_ctor_get(v___x_2113_, 0);
lean_inc_n(v_val_2117_, 2);
lean_dec_ref_known(v___x_2113_, 1);
v_keys_x27_2118_ = l_Array_eraseIdx___redArg(v_ks_2108_, v_val_2117_);
v_vals_x27_2119_ = l_Array_eraseIdx___redArg(v_vs_2109_, v_val_2117_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v_vals_x27_2119_);
lean_ctor_set(v___x_2111_, 0, v_keys_x27_2118_);
v___x_2121_ = v___x_2111_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_keys_x27_2118_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_vals_x27_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_){
_start:
{
size_t v_x_2685__boxed_2127_; lean_object* v_res_2128_; 
v_x_2685__boxed_2127_ = lean_unbox_usize(v_x_2125_);
lean_dec(v_x_2125_);
v_res_2128_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2124_, v_x_2685__boxed_2127_, v_x_2126_);
lean_dec(v_x_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2129_, lean_object* v_x_2130_){
_start:
{
uint64_t v___x_2131_; size_t v_h_2132_; lean_object* v___x_2133_; 
v___x_2131_ = l_Lean_instHashableFVarId_hash(v_x_2130_);
v_h_2132_ = lean_uint64_to_usize(v___x_2131_);
v___x_2133_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2129_, v_h_2132_, v_x_2130_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2134_, v_x_2135_);
lean_dec(v_x_2135_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* v_lctx_2137_, lean_object* v_fvarId_2138_){
_start:
{
lean_object* v_fvarIdToDecl_2139_; lean_object* v_decls_2140_; lean_object* v_auxDeclToFullName_2141_; lean_object* v___x_2142_; 
v_fvarIdToDecl_2139_ = lean_ctor_get(v_lctx_2137_, 0);
v_decls_2140_ = lean_ctor_get(v_lctx_2137_, 1);
v_auxDeclToFullName_2141_ = lean_ctor_get(v_lctx_2137_, 2);
v___x_2142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2139_, v_fvarId_2138_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_dec(v_fvarId_2138_);
return v_lctx_2137_;
}
else
{
lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2162_; 
lean_inc(v_auxDeclToFullName_2141_);
lean_inc_ref(v_decls_2140_);
lean_inc_ref(v_fvarIdToDecl_2139_);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_lctx_2137_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2163_ = lean_ctor_get(v_lctx_2137_, 2);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_lctx_2137_, 1);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_lctx_2137_, 0);
lean_dec(v_unused_2165_);
v___x_2144_ = v_lctx_2137_;
v_isShared_2145_ = v_isSharedCheck_2162_;
goto v_resetjp_2143_;
}
else
{
lean_dec(v_lctx_2137_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2162_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v_val_2146_; lean_object* v___x_2147_; lean_object* v___y_2149_; lean_object* v_index_2161_; 
v_val_2146_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2146_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2147_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2139_, v_fvarId_2138_);
v_index_2161_ = lean_ctor_get(v_val_2146_, 0);
lean_inc(v_index_2161_);
v___y_2149_ = v_index_2161_;
goto v___jp_2148_;
v___jp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = l_Lean_PersistentArray_set___redArg(v_decls_2140_, v___y_2149_, v___x_2150_);
lean_dec(v___y_2149_);
v___x_2152_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2151_);
v___x_2153_ = l_Lean_LocalDecl_isAuxDecl(v_val_2146_);
lean_dec(v_val_2146_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2155_; 
lean_dec(v_fvarId_2138_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v___x_2152_);
lean_ctor_set(v___x_2144_, 0, v___x_2147_);
v___x_2155_ = v___x_2144_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_auxDeclToFullName_2141_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2138_, v_auxDeclToFullName_2141_);
lean_dec(v_fvarId_2138_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 2, v___x_2157_);
lean_ctor_set(v___x_2144_, 1, v___x_2152_);
lean_ctor_set(v___x_2144_, 0, v___x_2147_);
v___x_2159_ = v___x_2144_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2167_, v_x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2170_, v_x_2171_, v_x_2172_);
lean_dec(v_x_2172_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2174_, lean_object* v_k_2175_, lean_object* v_t_2176_, lean_object* v_h_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2175_, v_t_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2179_, lean_object* v_k_2180_, lean_object* v_t_2181_, lean_object* v_h_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2179_, v_k_2180_, v_t_2181_, v_h_2182_);
lean_dec(v_k_2180_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2184_, lean_object* v_x_2185_, size_t v_x_2186_, lean_object* v_x_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2185_, v_x_2186_, v_x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_){
_start:
{
size_t v_x_2907__boxed_2193_; lean_object* v_res_2194_; 
v_x_2907__boxed_2193_ = lean_unbox_usize(v_x_2191_);
lean_dec(v_x_2191_);
v_res_2194_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2189_, v_x_2190_, v_x_2907__boxed_2193_, v_x_2192_);
lean_dec(v_x_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2195_){
_start:
{
lean_object* v_decls_2196_; lean_object* v_fvarIdToDecl_2197_; lean_object* v_auxDeclToFullName_2198_; lean_object* v_size_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v_decls_2196_ = lean_ctor_get(v_lctx_2195_, 1);
v_fvarIdToDecl_2197_ = lean_ctor_get(v_lctx_2195_, 0);
v_auxDeclToFullName_2198_ = lean_ctor_get(v_lctx_2195_, 2);
v_size_2199_ = lean_ctor_get(v_decls_2196_, 2);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = lean_nat_dec_eq(v_size_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = lean_box(0);
v___x_2203_ = lean_unsigned_to_nat(1u);
v___x_2204_ = lean_nat_sub(v_size_2199_, v___x_2203_);
v___x_2205_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2202_, v_decls_2196_, v___x_2204_);
lean_dec(v___x_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
return v_lctx_2195_;
}
else
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2224_; 
lean_inc(v_auxDeclToFullName_2198_);
lean_inc_ref(v_fvarIdToDecl_2197_);
lean_inc_ref(v_decls_2196_);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_lctx_2195_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; 
v_unused_2225_ = lean_ctor_get(v_lctx_2195_, 2);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_lctx_2195_, 1);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_lctx_2195_, 0);
lean_dec(v_unused_2227_);
v___x_2207_ = v_lctx_2195_;
v_isShared_2208_ = v_isSharedCheck_2224_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v_lctx_2195_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2224_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_val_2209_; lean_object* v___y_2211_; lean_object* v_fvarId_2223_; 
v_val_2209_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v___x_2205_, 1);
v_fvarId_2223_ = lean_ctor_get(v_val_2209_, 1);
lean_inc(v_fvarId_2223_);
v___y_2211_ = v_fvarId_2223_;
goto v___jp_2210_;
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2212_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2197_, v___y_2211_);
v___x_2213_ = l_Lean_PersistentArray_pop___redArg(v_decls_2196_);
v___x_2214_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2213_);
v___x_2215_ = l_Lean_LocalDecl_isAuxDecl(v_val_2209_);
lean_dec(v_val_2209_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2217_; 
lean_dec(v___y_2211_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v___x_2214_);
lean_ctor_set(v___x_2207_, 0, v___x_2212_);
v___x_2217_ = v___x_2207_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_auxDeclToFullName_2198_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2211_, v_auxDeclToFullName_2198_);
lean_dec(v___y_2211_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 2, v___x_2219_);
lean_ctor_set(v___x_2207_, 1, v___x_2214_);
lean_ctor_set(v___x_2207_, 0, v___x_2212_);
v___x_2221_ = v___x_2207_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
}
else
{
return v_lctx_2195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2228_, lean_object* v_as_2229_, lean_object* v_i_2230_){
_start:
{
lean_object* v_zero_2231_; uint8_t v_isZero_2232_; 
v_zero_2231_ = lean_unsigned_to_nat(0u);
v_isZero_2232_ = lean_nat_dec_eq(v_i_2230_, v_zero_2231_);
if (v_isZero_2232_ == 1)
{
lean_object* v___x_2233_; 
lean_dec(v_i_2230_);
v___x_2233_ = lean_box(0);
return v___x_2233_;
}
else
{
lean_object* v_one_2234_; lean_object* v_n_2235_; lean_object* v___y_2237_; lean_object* v___x_2239_; lean_object* v___y_2241_; 
v_one_2234_ = lean_unsigned_to_nat(1u);
v_n_2235_ = lean_nat_sub(v_i_2230_, v_one_2234_);
lean_dec(v_i_2230_);
v___x_2239_ = lean_array_fget_borrowed(v_as_2229_, v_n_2235_);
if (lean_obj_tag(v___x_2239_) == 0)
{
v___y_2237_ = v___x_2239_;
goto v___jp_2236_;
}
else
{
lean_object* v_val_2244_; lean_object* v_userName_2245_; 
v_val_2244_ = lean_ctor_get(v___x_2239_, 0);
v_userName_2245_ = lean_ctor_get(v_val_2244_, 2);
v___y_2241_ = v_userName_2245_;
goto v___jp_2240_;
}
v___jp_2236_:
{
if (lean_obj_tag(v___y_2237_) == 0)
{
v_i_2230_ = v_n_2235_;
goto _start;
}
else
{
lean_dec(v_n_2235_);
lean_inc_ref(v___y_2237_);
return v___y_2237_;
}
}
v___jp_2240_:
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_name_eq(v___y_2241_, v_userName_2228_);
if (v___x_2242_ == 0)
{
v_i_2230_ = v_n_2235_;
goto _start;
}
else
{
v___y_2237_ = v___x_2239_;
goto v___jp_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2246_, lean_object* v_as_2247_, lean_object* v_i_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2246_, v_as_2247_, v_i_2248_);
lean_dec_ref(v_as_2247_);
lean_dec(v_userName_2246_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2250_, lean_object* v_as_2251_, lean_object* v_i_2252_){
_start:
{
lean_object* v_zero_2253_; uint8_t v_isZero_2254_; 
v_zero_2253_ = lean_unsigned_to_nat(0u);
v_isZero_2254_ = lean_nat_dec_eq(v_i_2252_, v_zero_2253_);
if (v_isZero_2254_ == 1)
{
lean_object* v___x_2255_; 
lean_dec(v_i_2252_);
v___x_2255_ = lean_box(0);
return v___x_2255_;
}
else
{
lean_object* v_one_2256_; lean_object* v_n_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_one_2256_ = lean_unsigned_to_nat(1u);
v_n_2257_ = lean_nat_sub(v_i_2252_, v_one_2256_);
lean_dec(v_i_2252_);
v___x_2258_ = lean_array_fget_borrowed(v_as_2251_, v_n_2257_);
v___x_2259_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2250_, v___x_2258_);
if (lean_obj_tag(v___x_2259_) == 0)
{
v_i_2252_ = v_n_2257_;
goto _start;
}
else
{
lean_dec(v_n_2257_);
return v___x_2259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2261_, lean_object* v_x_2262_){
_start:
{
if (lean_obj_tag(v_x_2262_) == 0)
{
lean_object* v_cs_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_cs_2263_ = lean_ctor_get(v_x_2262_, 0);
v___x_2264_ = lean_array_get_size(v_cs_2263_);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2261_, v_cs_2263_, v___x_2264_);
return v___x_2265_;
}
else
{
lean_object* v_vs_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_vs_2266_ = lean_ctor_get(v_x_2262_, 0);
v___x_2267_ = lean_array_get_size(v_vs_2266_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2261_, v_vs_2266_, v___x_2267_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2269_, lean_object* v_x_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2269_, v_x_2270_);
lean_dec_ref(v_x_2270_);
lean_dec(v_userName_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2272_, lean_object* v_as_2273_, lean_object* v_i_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2272_, v_as_2273_, v_i_2274_);
lean_dec_ref(v_as_2273_);
lean_dec(v_userName_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2276_, lean_object* v_t_2277_){
_start:
{
lean_object* v_root_2278_; lean_object* v_tail_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v_root_2278_ = lean_ctor_get(v_t_2277_, 0);
v_tail_2279_ = lean_ctor_get(v_t_2277_, 1);
v___x_2280_ = lean_array_get_size(v_tail_2279_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2276_, v_tail_2279_, v___x_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2276_, v_root_2278_);
return v___x_2282_;
}
else
{
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2283_, lean_object* v_t_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2283_, v_t_2284_);
lean_dec_ref(v_t_2284_);
lean_dec(v_userName_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2286_, lean_object* v_userName_2287_){
_start:
{
lean_object* v_decls_2288_; lean_object* v___x_2289_; 
v_decls_2288_ = lean_ctor_get(v_lctx_2286_, 1);
v___x_2289_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2287_, v_decls_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2290_, lean_object* v_userName_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2290_, v_userName_2291_);
lean_dec(v_userName_2291_);
lean_dec_ref(v_lctx_2290_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2293_, lean_object* v_as_2294_, lean_object* v_i_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2293_, v_as_2294_, v_i_2295_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2298_, lean_object* v_as_2299_, lean_object* v_i_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2298_, v_as_2299_, v_i_2300_, v_a_2301_);
lean_dec_ref(v_as_2299_);
lean_dec(v_userName_2298_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2303_, lean_object* v_as_2304_, lean_object* v_i_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2303_, v_as_2304_, v_i_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2308_, lean_object* v_as_2309_, lean_object* v_i_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2308_, v_as_2309_, v_i_2310_, v_a_2311_);
lean_dec_ref(v_as_2309_);
lean_dec(v_userName_2308_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2316_, lean_object* v_userName_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2316_, v_userName_2317_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2319_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2320_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2321_ = lean_unsigned_to_nat(403u);
v___x_2322_ = lean_unsigned_to_nat(17u);
v___x_2323_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2324_ = 1;
v___x_2325_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2317_, v___x_2324_);
v___x_2326_ = lean_string_append(v___x_2323_, v___x_2325_);
lean_dec_ref(v___x_2325_);
v___x_2327_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2328_ = lean_string_append(v___x_2326_, v___x_2327_);
v___x_2329_ = l_mkPanicMessageWithDecl(v___x_2319_, v___x_2320_, v___x_2321_, v___x_2322_, v___x_2328_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2329_);
return v___x_2330_;
}
else
{
lean_object* v_val_2331_; 
lean_dec(v_userName_2317_);
v_val_2331_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_val_2331_);
lean_dec_ref_known(v___x_2318_, 1);
return v_val_2331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2332_, lean_object* v_userName_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2332_, v_userName_2333_);
lean_dec_ref(v_lctx_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2335_, lean_object* v_userName_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2335_, v_userName_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
uint8_t v___x_2338_; 
v___x_2338_ = 0;
return v___x_2338_;
}
else
{
uint8_t v___x_2339_; 
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = 1;
return v___x_2339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2340_, lean_object* v_userName_2341_){
_start:
{
uint8_t v_res_2342_; lean_object* v_r_2343_; 
v_res_2342_ = l_Lean_LocalContext_usesUserName(v_lctx_2340_, v_userName_2341_);
lean_dec(v_userName_2341_);
lean_dec_ref(v_lctx_2340_);
v_r_2343_ = lean_box(v_res_2342_);
return v_r_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2344_, lean_object* v_suggestion_2345_, lean_object* v_i_2346_){
_start:
{
lean_object* v_curr_2347_; uint8_t v___x_2348_; 
lean_inc(v_i_2346_);
lean_inc(v_suggestion_2345_);
v_curr_2347_ = lean_name_append_index_after(v_suggestion_2345_, v_i_2346_);
v___x_2348_ = l_Lean_LocalContext_usesUserName(v_lctx_2344_, v_curr_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec(v_suggestion_2345_);
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_add(v_i_2346_, v___x_2349_);
lean_dec(v_i_2346_);
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_curr_2347_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
return v___x_2351_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v_curr_2347_);
v___x_2352_ = lean_unsigned_to_nat(1u);
v___x_2353_ = lean_nat_add(v_i_2346_, v___x_2352_);
lean_dec(v_i_2346_);
v_i_2346_ = v___x_2353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2355_, lean_object* v_suggestion_2356_, lean_object* v_i_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2355_, v_suggestion_2356_, v_i_2357_);
lean_dec_ref(v_lctx_2355_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2359_, lean_object* v_suggestion_2360_){
_start:
{
lean_object* v_suggestion_2361_; uint8_t v___x_2362_; 
v_suggestion_2361_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2360_);
v___x_2362_ = l_Lean_LocalContext_usesUserName(v_lctx_2359_, v_suggestion_2361_);
if (v___x_2362_ == 0)
{
return v_suggestion_2361_;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v_fst_2365_; 
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2359_, v_suggestion_2361_, v___x_2363_);
v_fst_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_fst_2365_);
lean_dec_ref(v___x_2364_);
return v_fst_2365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2366_, lean_object* v_suggestion_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_LocalContext_getUnusedName(v_lctx_2366_, v_suggestion_2367_);
lean_dec(v_suggestion_2367_);
lean_dec_ref(v_lctx_2366_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2369_){
_start:
{
lean_object* v_decls_2370_; lean_object* v_size_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_decls_2370_ = lean_ctor_get(v_lctx_2369_, 1);
v_size_2371_ = lean_ctor_get(v_decls_2370_, 2);
v___x_2372_ = lean_box(0);
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_sub(v_size_2371_, v___x_2373_);
v___x_2375_ = lean_nat_dec_lt(v___x_2374_, v_size_2371_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_dec(v___x_2374_);
v___x_2376_ = l_outOfBounds___redArg(v___x_2372_);
return v___x_2376_;
}
else
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2372_, v_decls_2370_, v___x_2374_);
lean_dec(v___x_2374_);
return v___x_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_LocalContext_lastDecl(v_lctx_2378_);
lean_dec_ref(v_lctx_2378_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2380_, lean_object* v_fvarId_2381_, lean_object* v_userName_2382_){
_start:
{
lean_object* v_fvarIdToDecl_2383_; lean_object* v_decls_2384_; lean_object* v_auxDeclToFullName_2385_; lean_object* v_decl_2386_; lean_object* v_decl_2387_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2395_; lean_object* v_fvarId_2398_; 
v_fvarIdToDecl_2383_ = lean_ctor_get(v_lctx_2380_, 0);
lean_inc_ref(v_fvarIdToDecl_2383_);
v_decls_2384_ = lean_ctor_get(v_lctx_2380_, 1);
lean_inc_ref(v_decls_2384_);
v_auxDeclToFullName_2385_ = lean_ctor_get(v_lctx_2380_, 2);
lean_inc(v_auxDeclToFullName_2385_);
v_decl_2386_ = l_Lean_LocalContext_get_x21(v_lctx_2380_, v_fvarId_2381_);
v_decl_2387_ = l_Lean_LocalDecl_setUserName(v_decl_2386_, v_userName_2382_);
v_fvarId_2398_ = lean_ctor_get(v_decl_2387_, 1);
lean_inc(v_fvarId_2398_);
v___y_2395_ = v_fvarId_2398_;
goto v___jp_2394_;
v___jp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2391_, 0, v_decl_2387_);
v___x_2392_ = l_Lean_PersistentArray_set___redArg(v_decls_2384_, v___y_2390_, v___x_2391_);
lean_dec(v___y_2390_);
v___x_2393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2393_, 0, v___y_2389_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_ctor_set(v___x_2393_, 2, v_auxDeclToFullName_2385_);
return v___x_2393_;
}
v___jp_2394_:
{
lean_object* v___x_2396_; lean_object* v_index_2397_; 
lean_inc_ref(v_decl_2387_);
v___x_2396_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2383_, v___y_2395_, v_decl_2387_);
v_index_2397_ = lean_ctor_get(v_decl_2387_, 0);
lean_inc(v_index_2397_);
v___y_2389_ = v___x_2396_;
v___y_2390_ = v_index_2397_;
goto v___jp_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2399_, lean_object* v_fromName_2400_, lean_object* v_toName_2401_){
_start:
{
lean_object* v_fvarIdToDecl_2402_; lean_object* v_decls_2403_; lean_object* v_auxDeclToFullName_2404_; lean_object* v___x_2405_; 
v_fvarIdToDecl_2402_ = lean_ctor_get(v_lctx_2399_, 0);
v_decls_2403_ = lean_ctor_get(v_lctx_2399_, 1);
v_auxDeclToFullName_2404_ = lean_ctor_get(v_lctx_2399_, 2);
v___x_2405_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2399_, v_fromName_2400_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_dec(v_toName_2401_);
return v_lctx_2399_;
}
else
{
lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2430_; 
lean_inc(v_auxDeclToFullName_2404_);
lean_inc_ref(v_decls_2403_);
lean_inc_ref(v_fvarIdToDecl_2402_);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_lctx_2399_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; lean_object* v_unused_2432_; lean_object* v_unused_2433_; 
v_unused_2431_ = lean_ctor_get(v_lctx_2399_, 2);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_lctx_2399_, 1);
lean_dec(v_unused_2432_);
v_unused_2433_ = lean_ctor_get(v_lctx_2399_, 0);
lean_dec(v_unused_2433_);
v___x_2407_ = v_lctx_2399_;
v_isShared_2408_ = v_isSharedCheck_2430_;
goto v_resetjp_2406_;
}
else
{
lean_dec(v_lctx_2399_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2430_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v_val_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2429_; 
v_val_2409_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2411_ = v___x_2405_;
v_isShared_2412_ = v_isSharedCheck_2429_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_val_2409_);
lean_dec(v___x_2405_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2429_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_decl_2413_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2425_; lean_object* v_fvarId_2428_; 
v_decl_2413_ = l_Lean_LocalDecl_setUserName(v_val_2409_, v_toName_2401_);
v_fvarId_2428_ = lean_ctor_get(v_decl_2413_, 1);
lean_inc(v_fvarId_2428_);
v___y_2425_ = v_fvarId_2428_;
goto v___jp_2424_;
v___jp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v_decl_2413_);
v___x_2418_ = v___x_2411_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_decl_2413_);
v___x_2418_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = l_Lean_PersistentArray_set___redArg(v_decls_2403_, v___y_2416_, v___x_2418_);
lean_dec(v___y_2416_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 1, v___x_2419_);
lean_ctor_set(v___x_2407_, 0, v___y_2415_);
v___x_2421_ = v___x_2407_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___y_2415_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_auxDeclToFullName_2404_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
v___jp_2424_:
{
lean_object* v___x_2426_; lean_object* v_index_2427_; 
lean_inc_ref(v_decl_2413_);
v___x_2426_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2402_, v___y_2425_, v_decl_2413_);
v_index_2427_ = lean_ctor_get(v_decl_2413_, 0);
lean_inc(v_index_2427_);
v___y_2415_ = v___x_2426_;
v___y_2416_ = v_index_2427_;
goto v___jp_2414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2434_, lean_object* v_fromName_2435_, lean_object* v_toName_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_LocalContext_renameUserName(v_lctx_2434_, v_fromName_2435_, v_toName_2436_);
lean_dec(v_fromName_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2440_, lean_object* v_fvarId_2441_, lean_object* v_f_2442_){
_start:
{
lean_object* v_fvarIdToDecl_2443_; lean_object* v_decls_2444_; lean_object* v_auxDeclToFullName_2445_; lean_object* v___x_2446_; 
v_fvarIdToDecl_2443_ = lean_ctor_get(v_lctx_2440_, 0);
v_decls_2444_ = lean_ctor_get(v_lctx_2440_, 1);
v_auxDeclToFullName_2445_ = lean_ctor_get(v_lctx_2440_, 2);
lean_inc_ref(v_lctx_2440_);
v___x_2446_ = lean_local_ctx_find(v_lctx_2440_, v_fvarId_2441_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_dec_ref(v_f_2442_);
return v_lctx_2440_;
}
else
{
lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2473_; 
lean_inc(v_auxDeclToFullName_2445_);
lean_inc_ref(v_decls_2444_);
lean_inc_ref(v_fvarIdToDecl_2443_);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_lctx_2440_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; lean_object* v_unused_2475_; lean_object* v_unused_2476_; 
v_unused_2474_ = lean_ctor_get(v_lctx_2440_, 2);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_lctx_2440_, 1);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_lctx_2440_, 0);
lean_dec(v_unused_2476_);
v___x_2448_ = v_lctx_2440_;
v_isShared_2449_ = v_isSharedCheck_2473_;
goto v_resetjp_2447_;
}
else
{
lean_dec(v_lctx_2440_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2473_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v_val_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2472_; 
v_val_2450_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2452_ = v___x_2446_;
v_isShared_2453_ = v_isSharedCheck_2472_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_val_2450_);
lean_dec(v___x_2446_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2472_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v_decl_2456_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2468_; lean_object* v_fvarId_2471_; 
v___x_2454_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2455_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2456_ = lean_apply_1(v_f_2442_, v_val_2450_);
v_fvarId_2471_ = lean_ctor_get(v_decl_2456_, 1);
lean_inc(v_fvarId_2471_);
v___y_2468_ = v_fvarId_2471_;
goto v___jp_2467_;
v___jp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v_decl_2456_);
v___x_2461_ = v___x_2452_;
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
v___x_2462_ = l_Lean_PersistentArray_set___redArg(v_decls_2444_, v___y_2459_, v___x_2461_);
lean_dec(v___y_2459_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 1, v___x_2462_);
lean_ctor_set(v___x_2448_, 0, v___y_2458_);
v___x_2464_ = v___x_2448_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___y_2458_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_auxDeclToFullName_2445_);
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
v___x_2469_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2454_, v___x_2455_, v_fvarIdToDecl_2443_, v___y_2468_, v_decl_2456_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2477_, lean_object* v_as_2478_, size_t v_i_2479_, size_t v_stop_2480_, lean_object* v_b_2481_){
_start:
{
lean_object* v___y_2483_; uint8_t v___x_2487_; 
v___x_2487_ = lean_usize_dec_eq(v_i_2479_, v_stop_2480_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_array_uget(v_as_2478_, v_i_2479_);
if (lean_obj_tag(v___x_2488_) == 0)
{
v___y_2483_ = v_b_2481_;
goto v___jp_2482_;
}
else
{
lean_object* v_val_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2516_; 
v_val_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2516_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_val_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2516_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_fvarIdToDecl_2493_; lean_object* v_decls_2494_; lean_object* v_auxDeclToFullName_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2515_; 
v_fvarIdToDecl_2493_ = lean_ctor_get(v_b_2481_, 0);
v_decls_2494_ = lean_ctor_get(v_b_2481_, 1);
v_auxDeclToFullName_2495_ = lean_ctor_get(v_b_2481_, 2);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_b_2481_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2497_ = v_b_2481_;
v_isShared_2498_ = v_isSharedCheck_2515_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_auxDeclToFullName_2495_);
lean_inc(v_decls_2494_);
lean_inc(v_fvarIdToDecl_2493_);
lean_dec(v_b_2481_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2515_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v_decl_2499_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2511_; lean_object* v_fvarId_2514_; 
lean_inc_ref(v_f_2477_);
v_decl_2499_ = lean_apply_1(v_f_2477_, v_val_2489_);
v_fvarId_2514_ = lean_ctor_get(v_decl_2499_, 1);
lean_inc(v_fvarId_2514_);
v___y_2511_ = v_fvarId_2514_;
goto v___jp_2510_;
v___jp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v_decl_2499_);
v___x_2504_ = v___x_2491_;
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
v___x_2505_ = l_Lean_PersistentArray_set___redArg(v_decls_2494_, v___y_2502_, v___x_2504_);
lean_dec(v___y_2502_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v___x_2505_);
lean_ctor_set(v___x_2497_, 0, v___y_2501_);
v___x_2507_ = v___x_2497_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___y_2501_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_auxDeclToFullName_2495_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
v___y_2483_ = v___x_2507_;
goto v___jp_2482_;
}
}
}
v___jp_2510_:
{
lean_object* v___x_2512_; lean_object* v_index_2513_; 
lean_inc_ref(v_decl_2499_);
v___x_2512_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2493_, v___y_2511_, v_decl_2499_);
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
else
{
lean_dec_ref(v_f_2477_);
return v_b_2481_;
}
v___jp_2482_:
{
size_t v___x_2484_; size_t v___x_2485_; 
v___x_2484_ = ((size_t)1ULL);
v___x_2485_ = lean_usize_add(v_i_2479_, v___x_2484_);
v_i_2479_ = v___x_2485_;
v_b_2481_ = v___y_2483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2517_, lean_object* v_as_2518_, lean_object* v_i_2519_, lean_object* v_stop_2520_, lean_object* v_b_2521_){
_start:
{
size_t v_i_boxed_2522_; size_t v_stop_boxed_2523_; lean_object* v_res_2524_; 
v_i_boxed_2522_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_stop_boxed_2523_ = lean_unbox_usize(v_stop_2520_);
lean_dec(v_stop_2520_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2517_, v_as_2518_, v_i_boxed_2522_, v_stop_boxed_2523_, v_b_2521_);
lean_dec_ref(v_as_2518_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2525_, lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2526_) == 0)
{
lean_object* v_cs_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_cs_2528_ = lean_ctor_get(v_x_2526_, 0);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_array_get_size(v_cs_2528_);
v___x_2531_ = lean_nat_dec_lt(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_dec_ref(v_f_2525_);
return v_x_2527_;
}
else
{
uint8_t v___x_2532_; 
v___x_2532_ = lean_nat_dec_le(v___x_2530_, v___x_2530_);
if (v___x_2532_ == 0)
{
if (v___x_2531_ == 0)
{
lean_dec_ref(v_f_2525_);
return v_x_2527_;
}
else
{
size_t v___x_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = ((size_t)0ULL);
v___x_2534_ = lean_usize_of_nat(v___x_2530_);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2525_, v_cs_2528_, v___x_2533_, v___x_2534_, v_x_2527_);
return v___x_2535_;
}
}
else
{
size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = ((size_t)0ULL);
v___x_2537_ = lean_usize_of_nat(v___x_2530_);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2525_, v_cs_2528_, v___x_2536_, v___x_2537_, v_x_2527_);
return v___x_2538_;
}
}
}
else
{
lean_object* v_vs_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_vs_2539_ = lean_ctor_get(v_x_2526_, 0);
v___x_2540_ = lean_unsigned_to_nat(0u);
v___x_2541_ = lean_array_get_size(v_vs_2539_);
v___x_2542_ = lean_nat_dec_lt(v___x_2540_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec_ref(v_f_2525_);
return v_x_2527_;
}
else
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_nat_dec_le(v___x_2541_, v___x_2541_);
if (v___x_2543_ == 0)
{
if (v___x_2542_ == 0)
{
lean_dec_ref(v_f_2525_);
return v_x_2527_;
}
else
{
size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = lean_usize_of_nat(v___x_2541_);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2525_, v_vs_2539_, v___x_2544_, v___x_2545_, v_x_2527_);
return v___x_2546_;
}
}
else
{
size_t v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = lean_usize_of_nat(v___x_2541_);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2525_, v_vs_2539_, v___x_2547_, v___x_2548_, v_x_2527_);
return v___x_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2550_, lean_object* v_as_2551_, size_t v_i_2552_, size_t v_stop_2553_, lean_object* v_b_2554_){
_start:
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_usize_dec_eq(v_i_2552_, v_stop_2553_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; size_t v___x_2558_; size_t v___x_2559_; 
v___x_2556_ = lean_array_uget_borrowed(v_as_2551_, v_i_2552_);
lean_inc_ref(v_f_2550_);
v___x_2557_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2550_, v___x_2556_, v_b_2554_);
v___x_2558_ = ((size_t)1ULL);
v___x_2559_ = lean_usize_add(v_i_2552_, v___x_2558_);
v_i_2552_ = v___x_2559_;
v_b_2554_ = v___x_2557_;
goto _start;
}
else
{
lean_dec_ref(v_f_2550_);
return v_b_2554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2561_, lean_object* v_as_2562_, lean_object* v_i_2563_, lean_object* v_stop_2564_, lean_object* v_b_2565_){
_start:
{
size_t v_i_boxed_2566_; size_t v_stop_boxed_2567_; lean_object* v_res_2568_; 
v_i_boxed_2566_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_stop_boxed_2567_ = lean_unbox_usize(v_stop_2564_);
lean_dec(v_stop_2564_);
v_res_2568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2561_, v_as_2562_, v_i_boxed_2566_, v_stop_boxed_2567_, v_b_2565_);
lean_dec_ref(v_as_2562_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2569_, v_x_2570_, v_x_2571_);
lean_dec_ref(v_x_2570_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2573_, lean_object* v_x_2574_, size_t v_x_2575_, size_t v_x_2576_, lean_object* v_x_2577_){
_start:
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v_cs_2578_; lean_object* v___x_2579_; size_t v___x_2580_; lean_object* v_j_2581_; lean_object* v___x_2582_; size_t v___x_2583_; size_t v___x_2584_; size_t v___x_2585_; size_t v___x_2586_; size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_cs_2578_ = lean_ctor_get(v_x_2574_, 0);
v___x_2579_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2580_ = lean_usize_shift_right(v_x_2575_, v_x_2576_);
v_j_2581_ = lean_usize_to_nat(v___x_2580_);
v___x_2582_ = lean_array_get_borrowed(v___x_2579_, v_cs_2578_, v_j_2581_);
v___x_2583_ = ((size_t)1ULL);
v___x_2584_ = lean_usize_shift_left(v___x_2583_, v_x_2576_);
v___x_2585_ = lean_usize_sub(v___x_2584_, v___x_2583_);
v___x_2586_ = lean_usize_land(v_x_2575_, v___x_2585_);
v___x_2587_ = ((size_t)5ULL);
v___x_2588_ = lean_usize_sub(v_x_2576_, v___x_2587_);
lean_inc_ref(v_f_2573_);
v___x_2589_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2573_, v___x_2582_, v___x_2586_, v___x_2588_, v_x_2577_);
v___x_2590_ = lean_unsigned_to_nat(1u);
v___x_2591_ = lean_nat_add(v_j_2581_, v___x_2590_);
lean_dec(v_j_2581_);
v___x_2592_ = lean_array_get_size(v_cs_2578_);
v___x_2593_ = lean_nat_dec_lt(v___x_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_dec(v___x_2591_);
lean_dec_ref(v_f_2573_);
return v___x_2589_;
}
else
{
uint8_t v___x_2594_; 
v___x_2594_ = lean_nat_dec_le(v___x_2592_, v___x_2592_);
if (v___x_2594_ == 0)
{
if (v___x_2593_ == 0)
{
lean_dec(v___x_2591_);
lean_dec_ref(v_f_2573_);
return v___x_2589_;
}
else
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_usize_of_nat(v___x_2591_);
lean_dec(v___x_2591_);
v___x_2596_ = lean_usize_of_nat(v___x_2592_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2573_, v_cs_2578_, v___x_2595_, v___x_2596_, v___x_2589_);
return v___x_2597_;
}
}
else
{
size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_usize_of_nat(v___x_2591_);
lean_dec(v___x_2591_);
v___x_2599_ = lean_usize_of_nat(v___x_2592_);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2573_, v_cs_2578_, v___x_2598_, v___x_2599_, v___x_2589_);
return v___x_2600_;
}
}
}
else
{
lean_object* v_vs_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v_vs_2601_ = lean_ctor_get(v_x_2574_, 0);
v___x_2602_ = lean_usize_to_nat(v_x_2575_);
v___x_2603_ = lean_array_get_size(v_vs_2601_);
v___x_2604_ = lean_nat_dec_lt(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_dec(v___x_2602_);
lean_dec_ref(v_f_2573_);
return v_x_2577_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_nat_dec_le(v___x_2603_, v___x_2603_);
if (v___x_2605_ == 0)
{
if (v___x_2604_ == 0)
{
lean_dec(v___x_2602_);
lean_dec_ref(v_f_2573_);
return v_x_2577_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = lean_usize_of_nat(v___x_2602_);
lean_dec(v___x_2602_);
v___x_2607_ = lean_usize_of_nat(v___x_2603_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2573_, v_vs_2601_, v___x_2606_, v___x_2607_, v_x_2577_);
return v___x_2608_;
}
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_usize_of_nat(v___x_2602_);
lean_dec(v___x_2602_);
v___x_2610_ = lean_usize_of_nat(v___x_2603_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2573_, v_vs_2601_, v___x_2609_, v___x_2610_, v_x_2577_);
return v___x_2611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
size_t v_x_1859__boxed_2617_; size_t v_x_1860__boxed_2618_; lean_object* v_res_2619_; 
v_x_1859__boxed_2617_ = lean_unbox_usize(v_x_2614_);
lean_dec(v_x_2614_);
v_x_1860__boxed_2618_ = lean_unbox_usize(v_x_2615_);
lean_dec(v_x_2615_);
v_res_2619_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2612_, v_x_2613_, v_x_1859__boxed_2617_, v_x_1860__boxed_2618_, v_x_2616_);
lean_dec_ref(v_x_2613_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2620_, lean_object* v_t_2621_, lean_object* v_init_2622_, lean_object* v_start_2623_){
_start:
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = lean_unsigned_to_nat(0u);
v___x_2625_ = lean_nat_dec_eq(v_start_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v_root_2626_; lean_object* v_tail_2627_; size_t v_shift_2628_; lean_object* v_tailOff_2629_; uint8_t v___x_2630_; 
v_root_2626_ = lean_ctor_get(v_t_2621_, 0);
v_tail_2627_ = lean_ctor_get(v_t_2621_, 1);
v_shift_2628_ = lean_ctor_get_usize(v_t_2621_, 4);
v_tailOff_2629_ = lean_ctor_get(v_t_2621_, 3);
v___x_2630_ = lean_nat_dec_le(v_tailOff_2629_, v_start_2623_);
if (v___x_2630_ == 0)
{
size_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2631_ = lean_usize_of_nat(v_start_2623_);
lean_inc_ref(v_f_2620_);
v___x_2632_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2620_, v_root_2626_, v___x_2631_, v_shift_2628_, v_init_2622_);
v___x_2633_ = lean_array_get_size(v_tail_2627_);
v___x_2634_ = lean_nat_dec_lt(v___x_2624_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_dec_ref(v_f_2620_);
return v___x_2632_;
}
else
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_nat_dec_le(v___x_2633_, v___x_2633_);
if (v___x_2635_ == 0)
{
if (v___x_2634_ == 0)
{
lean_dec_ref(v_f_2620_);
return v___x_2632_;
}
else
{
size_t v___x_2636_; size_t v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = ((size_t)0ULL);
v___x_2637_ = lean_usize_of_nat(v___x_2633_);
v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2620_, v_tail_2627_, v___x_2636_, v___x_2637_, v___x_2632_);
return v___x_2638_;
}
}
else
{
size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = ((size_t)0ULL);
v___x_2640_ = lean_usize_of_nat(v___x_2633_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2620_, v_tail_2627_, v___x_2639_, v___x_2640_, v___x_2632_);
return v___x_2641_;
}
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2642_ = lean_nat_sub(v_start_2623_, v_tailOff_2629_);
v___x_2643_ = lean_array_get_size(v_tail_2627_);
v___x_2644_ = lean_nat_dec_lt(v___x_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_dec(v___x_2642_);
lean_dec_ref(v_f_2620_);
return v_init_2622_;
}
else
{
uint8_t v___x_2645_; 
v___x_2645_ = lean_nat_dec_le(v___x_2643_, v___x_2643_);
if (v___x_2645_ == 0)
{
if (v___x_2644_ == 0)
{
lean_dec(v___x_2642_);
lean_dec_ref(v_f_2620_);
return v_init_2622_;
}
else
{
size_t v___x_2646_; size_t v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = lean_usize_of_nat(v___x_2642_);
lean_dec(v___x_2642_);
v___x_2647_ = lean_usize_of_nat(v___x_2643_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2620_, v_tail_2627_, v___x_2646_, v___x_2647_, v_init_2622_);
return v___x_2648_;
}
}
else
{
size_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = lean_usize_of_nat(v___x_2642_);
lean_dec(v___x_2642_);
v___x_2650_ = lean_usize_of_nat(v___x_2643_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2620_, v_tail_2627_, v___x_2649_, v___x_2650_, v_init_2622_);
return v___x_2651_;
}
}
}
}
else
{
lean_object* v_root_2652_; lean_object* v_tail_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v_root_2652_ = lean_ctor_get(v_t_2621_, 0);
v_tail_2653_ = lean_ctor_get(v_t_2621_, 1);
lean_inc_ref(v_f_2620_);
v___x_2654_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2620_, v_root_2652_, v_init_2622_);
v___x_2655_ = lean_array_get_size(v_tail_2653_);
v___x_2656_ = lean_nat_dec_lt(v___x_2624_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_dec_ref(v_f_2620_);
return v___x_2654_;
}
else
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_nat_dec_le(v___x_2655_, v___x_2655_);
if (v___x_2657_ == 0)
{
if (v___x_2656_ == 0)
{
lean_dec_ref(v_f_2620_);
return v___x_2654_;
}
else
{
size_t v___x_2658_; size_t v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = lean_usize_of_nat(v___x_2655_);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2620_, v_tail_2653_, v___x_2658_, v___x_2659_, v___x_2654_);
return v___x_2660_;
}
}
else
{
size_t v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = lean_usize_of_nat(v___x_2655_);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2620_, v_tail_2653_, v___x_2661_, v___x_2662_, v___x_2654_);
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2664_, lean_object* v_t_2665_, lean_object* v_init_2666_, lean_object* v_start_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2664_, v_t_2665_, v_init_2666_, v_start_2667_);
lean_dec(v_start_2667_);
lean_dec_ref(v_t_2665_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2669_, lean_object* v_f_2670_){
_start:
{
lean_object* v_decls_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_decls_2671_ = lean_ctor_get(v_lctx_2669_, 1);
lean_inc_ref(v_decls_2671_);
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2670_, v_decls_2671_, v_lctx_2669_, v___x_2672_);
lean_dec_ref(v_decls_2671_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2674_, lean_object* v_fvarId_2675_, uint8_t v_kind_2676_){
_start:
{
lean_object* v_fvarIdToDecl_2677_; lean_object* v_decls_2678_; lean_object* v_auxDeclToFullName_2679_; lean_object* v___x_2680_; 
v_fvarIdToDecl_2677_ = lean_ctor_get(v_lctx_2674_, 0);
v_decls_2678_ = lean_ctor_get(v_lctx_2674_, 1);
v_auxDeclToFullName_2679_ = lean_ctor_get(v_lctx_2674_, 2);
lean_inc_ref(v_lctx_2674_);
v___x_2680_ = lean_local_ctx_find(v_lctx_2674_, v_fvarId_2675_);
if (lean_obj_tag(v___x_2680_) == 0)
{
return v_lctx_2674_;
}
else
{
lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2705_; 
lean_inc(v_auxDeclToFullName_2679_);
lean_inc_ref(v_decls_2678_);
lean_inc_ref(v_fvarIdToDecl_2677_);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_lctx_2674_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; lean_object* v_unused_2707_; lean_object* v_unused_2708_; 
v_unused_2706_ = lean_ctor_get(v_lctx_2674_, 2);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_lctx_2674_, 1);
lean_dec(v_unused_2707_);
v_unused_2708_ = lean_ctor_get(v_lctx_2674_, 0);
lean_dec(v_unused_2708_);
v___x_2682_ = v_lctx_2674_;
v_isShared_2683_ = v_isSharedCheck_2705_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v_lctx_2674_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2705_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v_val_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2704_; 
v_val_2684_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2686_ = v___x_2680_;
v_isShared_2687_ = v_isSharedCheck_2704_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_val_2684_);
lean_dec(v___x_2680_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2704_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_decl_2688_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2700_; lean_object* v_fvarId_2703_; 
v_decl_2688_ = l_Lean_LocalDecl_setKind(v_val_2684_, v_kind_2676_);
v_fvarId_2703_ = lean_ctor_get(v_decl_2688_, 1);
lean_inc(v_fvarId_2703_);
v___y_2700_ = v_fvarId_2703_;
goto v___jp_2699_;
v___jp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v_decl_2688_);
v___x_2693_ = v___x_2686_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_decl_2688_);
v___x_2693_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2694_ = l_Lean_PersistentArray_set___redArg(v_decls_2678_, v___y_2691_, v___x_2693_);
lean_dec(v___y_2691_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 1, v___x_2694_);
lean_ctor_set(v___x_2682_, 0, v___y_2690_);
v___x_2696_ = v___x_2682_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___y_2690_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_auxDeclToFullName_2679_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v_index_2702_; 
lean_inc_ref(v_decl_2688_);
v___x_2701_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2677_, v___y_2700_, v_decl_2688_);
v_index_2702_ = lean_ctor_get(v_decl_2688_, 0);
lean_inc(v_index_2702_);
v___y_2690_ = v___x_2701_;
v___y_2691_ = v_index_2702_;
goto v___jp_2689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2709_, lean_object* v_fvarId_2710_, lean_object* v_kind_2711_){
_start:
{
uint8_t v_kind_boxed_2712_; lean_object* v_res_2713_; 
v_kind_boxed_2712_ = lean_unbox(v_kind_2711_);
v_res_2713_ = l_Lean_LocalContext_setKind(v_lctx_2709_, v_fvarId_2710_, v_kind_boxed_2712_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2714_, lean_object* v_fvarId_2715_, uint8_t v_bi_2716_){
_start:
{
lean_object* v_fvarIdToDecl_2717_; lean_object* v_decls_2718_; lean_object* v_auxDeclToFullName_2719_; lean_object* v___x_2720_; 
v_fvarIdToDecl_2717_ = lean_ctor_get(v_lctx_2714_, 0);
v_decls_2718_ = lean_ctor_get(v_lctx_2714_, 1);
v_auxDeclToFullName_2719_ = lean_ctor_get(v_lctx_2714_, 2);
lean_inc_ref(v_lctx_2714_);
v___x_2720_ = lean_local_ctx_find(v_lctx_2714_, v_fvarId_2715_);
if (lean_obj_tag(v___x_2720_) == 0)
{
return v_lctx_2714_;
}
else
{
lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2745_; 
lean_inc(v_auxDeclToFullName_2719_);
lean_inc_ref(v_decls_2718_);
lean_inc_ref(v_fvarIdToDecl_2717_);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_lctx_2714_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; 
v_unused_2746_ = lean_ctor_get(v_lctx_2714_, 2);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_lctx_2714_, 1);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_lctx_2714_, 0);
lean_dec(v_unused_2748_);
v___x_2722_ = v_lctx_2714_;
v_isShared_2723_ = v_isSharedCheck_2745_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v_lctx_2714_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2745_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_val_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2744_; 
v_val_2724_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2726_ = v___x_2720_;
v_isShared_2727_ = v_isSharedCheck_2744_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_val_2724_);
lean_dec(v___x_2720_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2744_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v_decl_2728_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2740_; lean_object* v_fvarId_2743_; 
v_decl_2728_ = l_Lean_LocalDecl_setBinderInfo(v_val_2724_, v_bi_2716_);
v_fvarId_2743_ = lean_ctor_get(v_decl_2728_, 1);
lean_inc(v_fvarId_2743_);
v___y_2740_ = v_fvarId_2743_;
goto v___jp_2739_;
v___jp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v_decl_2728_);
v___x_2733_ = v___x_2726_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_decl_2728_);
v___x_2733_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = l_Lean_PersistentArray_set___redArg(v_decls_2718_, v___y_2731_, v___x_2733_);
lean_dec(v___y_2731_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 1, v___x_2734_);
lean_ctor_set(v___x_2722_, 0, v___y_2730_);
v___x_2736_ = v___x_2722_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___y_2730_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2737_, 2, v_auxDeclToFullName_2719_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
v___jp_2739_:
{
lean_object* v___x_2741_; lean_object* v_index_2742_; 
lean_inc_ref(v_decl_2728_);
v___x_2741_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2717_, v___y_2740_, v_decl_2728_);
v_index_2742_ = lean_ctor_get(v_decl_2728_, 0);
lean_inc(v_index_2742_);
v___y_2730_ = v___x_2741_;
v___y_2731_ = v_index_2742_;
goto v___jp_2729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2749_, lean_object* v_fvarId_2750_, lean_object* v_bi_2751_){
_start:
{
uint8_t v_bi_boxed_2752_; lean_object* v_res_2753_; 
v_bi_boxed_2752_ = lean_unbox(v_bi_2751_);
v_res_2753_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2749_, v_fvarId_2750_, v_bi_boxed_2752_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2754_, lean_object* v_fvarId_2755_, lean_object* v_type_2756_){
_start:
{
lean_object* v_fvarIdToDecl_2757_; lean_object* v_decls_2758_; lean_object* v_auxDeclToFullName_2759_; lean_object* v___x_2760_; 
v_fvarIdToDecl_2757_ = lean_ctor_get(v_lctx_2754_, 0);
v_decls_2758_ = lean_ctor_get(v_lctx_2754_, 1);
v_auxDeclToFullName_2759_ = lean_ctor_get(v_lctx_2754_, 2);
lean_inc_ref(v_lctx_2754_);
v___x_2760_ = lean_local_ctx_find(v_lctx_2754_, v_fvarId_2755_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_dec_ref(v_type_2756_);
return v_lctx_2754_;
}
else
{
lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2785_; 
lean_inc(v_auxDeclToFullName_2759_);
lean_inc_ref(v_decls_2758_);
lean_inc_ref(v_fvarIdToDecl_2757_);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_lctx_2754_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; lean_object* v_unused_2787_; lean_object* v_unused_2788_; 
v_unused_2786_ = lean_ctor_get(v_lctx_2754_, 2);
lean_dec(v_unused_2786_);
v_unused_2787_ = lean_ctor_get(v_lctx_2754_, 1);
lean_dec(v_unused_2787_);
v_unused_2788_ = lean_ctor_get(v_lctx_2754_, 0);
lean_dec(v_unused_2788_);
v___x_2762_ = v_lctx_2754_;
v_isShared_2763_ = v_isSharedCheck_2785_;
goto v_resetjp_2761_;
}
else
{
lean_dec(v_lctx_2754_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2785_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v_val_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2784_; 
v_val_2764_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2766_ = v___x_2760_;
v_isShared_2767_ = v_isSharedCheck_2784_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_val_2764_);
lean_dec(v___x_2760_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2784_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_decl_2768_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2780_; lean_object* v_fvarId_2783_; 
v_decl_2768_ = l_Lean_LocalDecl_setType(v_val_2764_, v_type_2756_);
v_fvarId_2783_ = lean_ctor_get(v_decl_2768_, 1);
lean_inc(v_fvarId_2783_);
v___y_2780_ = v_fvarId_2783_;
goto v___jp_2779_;
v___jp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v_decl_2768_);
v___x_2773_ = v___x_2766_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_decl_2768_);
v___x_2773_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = l_Lean_PersistentArray_set___redArg(v_decls_2758_, v___y_2771_, v___x_2773_);
lean_dec(v___y_2771_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 1, v___x_2774_);
lean_ctor_set(v___x_2762_, 0, v___y_2770_);
v___x_2776_ = v___x_2762_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___y_2770_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v_auxDeclToFullName_2759_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
v___jp_2779_:
{
lean_object* v___x_2781_; lean_object* v_index_2782_; 
lean_inc_ref(v_decl_2768_);
v___x_2781_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2757_, v___y_2780_, v_decl_2768_);
v_index_2782_ = lean_ctor_get(v_decl_2768_, 0);
lean_inc(v_index_2782_);
v___y_2770_ = v___x_2781_;
v___y_2771_ = v_index_2782_;
goto v___jp_2769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2789_){
_start:
{
lean_object* v_decls_2790_; lean_object* v_size_2791_; 
v_decls_2790_ = lean_ctor_get(v_lctx_2789_, 1);
lean_inc_ref(v_decls_2790_);
lean_dec_ref(v_lctx_2789_);
v_size_2791_ = lean_ctor_get(v_decls_2790_, 2);
lean_inc(v_size_2791_);
lean_dec_ref(v_decls_2790_);
return v_size_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2792_, lean_object* v_i_2793_){
_start:
{
lean_object* v_decls_2794_; lean_object* v_size_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_decls_2794_ = lean_ctor_get(v_lctx_2792_, 1);
v_size_2795_ = lean_ctor_get(v_decls_2794_, 2);
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_nat_dec_lt(v_i_2793_, v_size_2795_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; 
v___x_2798_ = l_outOfBounds___redArg(v___x_2796_);
return v___x_2798_;
}
else
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2796_, v_decls_2794_, v_i_2793_);
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2800_, lean_object* v_i_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2800_, v_i_2801_);
lean_dec(v_i_2801_);
lean_dec_ref(v_lctx_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2803_, lean_object* v_f_2804_, lean_object* v_b_2805_, lean_object* v_decl_2806_){
_start:
{
if (lean_obj_tag(v_decl_2806_) == 0)
{
lean_object* v___x_2807_; 
lean_dec(v_f_2804_);
v___x_2807_ = lean_apply_2(v_toPure_2803_, lean_box(0), v_b_2805_);
return v___x_2807_;
}
else
{
lean_object* v_val_2808_; lean_object* v___x_2809_; 
lean_dec(v_toPure_2803_);
v_val_2808_ = lean_ctor_get(v_decl_2806_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v_decl_2806_, 1);
v___x_2809_ = lean_apply_2(v_f_2804_, v_b_2805_, v_val_2808_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2810_, lean_object* v_lctx_2811_, lean_object* v_f_2812_, lean_object* v_init_2813_, lean_object* v_start_2814_){
_start:
{
lean_object* v_toApplicative_2815_; lean_object* v_decls_2816_; lean_object* v_toPure_2817_; lean_object* v___f_2818_; lean_object* v___x_2819_; 
v_toApplicative_2815_ = lean_ctor_get(v_inst_2810_, 0);
v_decls_2816_ = lean_ctor_get(v_lctx_2811_, 1);
lean_inc_ref(v_decls_2816_);
lean_dec_ref(v_lctx_2811_);
v_toPure_2817_ = lean_ctor_get(v_toApplicative_2815_, 1);
lean_inc(v_toPure_2817_);
v___f_2818_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2818_, 0, v_toPure_2817_);
lean_closure_set(v___f_2818_, 1, v_f_2812_);
v___x_2819_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2810_, v_decls_2816_, v___f_2818_, v_init_2813_, v_start_2814_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2820_, lean_object* v_lctx_2821_, lean_object* v_f_2822_, lean_object* v_init_2823_, lean_object* v_start_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2820_, v_lctx_2821_, v_f_2822_, v_init_2823_, v_start_2824_);
lean_dec(v_start_2824_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2826_, lean_object* v_00_u03b2_2827_, lean_object* v_inst_2828_, lean_object* v_lctx_2829_, lean_object* v_f_2830_, lean_object* v_init_2831_, lean_object* v_start_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2828_, v_lctx_2829_, v_f_2830_, v_init_2831_, v_start_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2834_, lean_object* v_00_u03b2_2835_, lean_object* v_inst_2836_, lean_object* v_lctx_2837_, lean_object* v_f_2838_, lean_object* v_init_2839_, lean_object* v_start_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_LocalContext_foldlM(v_m_2834_, v_00_u03b2_2835_, v_inst_2836_, v_lctx_2837_, v_f_2838_, v_init_2839_, v_start_2840_);
lean_dec(v_start_2840_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2842_, lean_object* v_f_2843_, lean_object* v_decl_2844_, lean_object* v_b_2845_){
_start:
{
if (lean_obj_tag(v_decl_2844_) == 0)
{
lean_object* v___x_2846_; 
lean_dec(v_f_2843_);
v___x_2846_ = lean_apply_2(v_toPure_2842_, lean_box(0), v_b_2845_);
return v___x_2846_;
}
else
{
lean_object* v_val_2847_; lean_object* v___x_2848_; 
lean_dec(v_toPure_2842_);
v_val_2847_ = lean_ctor_get(v_decl_2844_, 0);
lean_inc(v_val_2847_);
lean_dec_ref_known(v_decl_2844_, 1);
v___x_2848_ = lean_apply_2(v_f_2843_, v_val_2847_, v_b_2845_);
return v___x_2848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2849_, lean_object* v_lctx_2850_, lean_object* v_f_2851_, lean_object* v_init_2852_){
_start:
{
lean_object* v_toApplicative_2853_; lean_object* v_decls_2854_; lean_object* v_toPure_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; 
v_toApplicative_2853_ = lean_ctor_get(v_inst_2849_, 0);
v_decls_2854_ = lean_ctor_get(v_lctx_2850_, 1);
lean_inc_ref(v_decls_2854_);
lean_dec_ref(v_lctx_2850_);
v_toPure_2855_ = lean_ctor_get(v_toApplicative_2853_, 1);
lean_inc(v_toPure_2855_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2856_, 0, v_toPure_2855_);
lean_closure_set(v___f_2856_, 1, v_f_2851_);
v___x_2857_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2849_, v_decls_2854_, v___f_2856_, v_init_2852_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2858_, lean_object* v_00_u03b2_2859_, lean_object* v_inst_2860_, lean_object* v_lctx_2861_, lean_object* v_f_2862_, lean_object* v_init_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2860_, v_lctx_2861_, v_f_2862_, v_init_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2865_, lean_object* v_f_2866_, lean_object* v_decl_2867_){
_start:
{
if (lean_obj_tag(v_decl_2867_) == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec(v_f_2866_);
v___x_2868_ = lean_box(0);
v___x_2869_ = lean_apply_2(v_toPure_2865_, lean_box(0), v___x_2868_);
return v___x_2869_;
}
else
{
lean_object* v_val_2870_; lean_object* v___x_2871_; 
lean_dec(v_toPure_2865_);
v_val_2870_ = lean_ctor_get(v_decl_2867_, 0);
lean_inc(v_val_2870_);
lean_dec_ref_known(v_decl_2867_, 1);
v___x_2871_ = lean_apply_1(v_f_2866_, v_val_2870_);
return v___x_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2872_, lean_object* v_lctx_2873_, lean_object* v_f_2874_, lean_object* v_start_2875_){
_start:
{
lean_object* v_toApplicative_2876_; lean_object* v_decls_2877_; lean_object* v_toPure_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; 
v_toApplicative_2876_ = lean_ctor_get(v_inst_2872_, 0);
v_decls_2877_ = lean_ctor_get(v_lctx_2873_, 1);
lean_inc_ref(v_decls_2877_);
lean_dec_ref(v_lctx_2873_);
v_toPure_2878_ = lean_ctor_get(v_toApplicative_2876_, 1);
lean_inc(v_toPure_2878_);
v___f_2879_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2879_, 0, v_toPure_2878_);
lean_closure_set(v___f_2879_, 1, v_f_2874_);
v___x_2880_ = l_Lean_PersistentArray_forM___redArg(v_inst_2872_, v_decls_2877_, v___f_2879_, v_start_2875_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2881_, lean_object* v_lctx_2882_, lean_object* v_f_2883_, lean_object* v_start_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_LocalContext_forM___redArg(v_inst_2881_, v_lctx_2882_, v_f_2883_, v_start_2884_);
lean_dec(v_start_2884_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2886_, lean_object* v_inst_2887_, lean_object* v_lctx_2888_, lean_object* v_f_2889_, lean_object* v_start_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_LocalContext_forM___redArg(v_inst_2887_, v_lctx_2888_, v_f_2889_, v_start_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2892_, lean_object* v_inst_2893_, lean_object* v_lctx_2894_, lean_object* v_f_2895_, lean_object* v_start_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_LocalContext_forM(v_m_2892_, v_inst_2893_, v_lctx_2894_, v_f_2895_, v_start_2896_);
lean_dec(v_start_2896_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2898_, lean_object* v_f_2899_, lean_object* v_decl_2900_){
_start:
{
if (lean_obj_tag(v_decl_2900_) == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec(v_f_2899_);
v___x_2901_ = lean_box(0);
v___x_2902_ = lean_apply_2(v_toPure_2898_, lean_box(0), v___x_2901_);
return v___x_2902_;
}
else
{
lean_object* v_val_2903_; lean_object* v___x_2904_; 
lean_dec(v_toPure_2898_);
v_val_2903_ = lean_ctor_get(v_decl_2900_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v_decl_2900_, 1);
v___x_2904_ = lean_apply_1(v_f_2899_, v_val_2903_);
return v___x_2904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2905_, lean_object* v_lctx_2906_, lean_object* v_f_2907_){
_start:
{
lean_object* v_toApplicative_2908_; lean_object* v_decls_2909_; lean_object* v_toPure_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; 
v_toApplicative_2908_ = lean_ctor_get(v_inst_2905_, 0);
v_decls_2909_ = lean_ctor_get(v_lctx_2906_, 1);
lean_inc_ref(v_decls_2909_);
lean_dec_ref(v_lctx_2906_);
v_toPure_2910_ = lean_ctor_get(v_toApplicative_2908_, 1);
lean_inc(v_toPure_2910_);
v___f_2911_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2911_, 0, v_toPure_2910_);
lean_closure_set(v___f_2911_, 1, v_f_2907_);
v___x_2912_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2905_, v_decls_2909_, v___f_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2913_, lean_object* v_00_u03b2_2914_, lean_object* v_inst_2915_, lean_object* v_lctx_2916_, lean_object* v_f_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2915_, v_lctx_2916_, v_f_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2919_, lean_object* v_lctx_2920_, lean_object* v_f_2921_){
_start:
{
lean_object* v_toApplicative_2922_; lean_object* v_decls_2923_; lean_object* v_toPure_2924_; lean_object* v___f_2925_; lean_object* v___x_2926_; 
v_toApplicative_2922_ = lean_ctor_get(v_inst_2919_, 0);
v_decls_2923_ = lean_ctor_get(v_lctx_2920_, 1);
lean_inc_ref(v_decls_2923_);
lean_dec_ref(v_lctx_2920_);
v_toPure_2924_ = lean_ctor_get(v_toApplicative_2922_, 1);
lean_inc(v_toPure_2924_);
v___f_2925_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2925_, 0, v_toPure_2924_);
lean_closure_set(v___f_2925_, 1, v_f_2921_);
v___x_2926_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2919_, v_decls_2923_, v___f_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2927_, lean_object* v_00_u03b2_2928_, lean_object* v_inst_2929_, lean_object* v_lctx_2930_, lean_object* v_f_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2929_, v_lctx_2930_, v_f_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2933_, lean_object* v_f_2934_, lean_object* v_d_x3f_2935_, lean_object* v_b_2936_){
_start:
{
if (lean_obj_tag(v_d_x3f_2935_) == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_dec(v_f_2934_);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_b_2936_);
v___x_2938_ = lean_apply_2(v_toPure_2933_, lean_box(0), v___x_2937_);
return v___x_2938_;
}
else
{
lean_object* v_val_2939_; lean_object* v___x_2940_; 
lean_dec(v_toPure_2933_);
v_val_2939_ = lean_ctor_get(v_d_x3f_2935_, 0);
lean_inc(v_val_2939_);
lean_dec_ref_known(v_d_x3f_2935_, 1);
v___x_2940_ = lean_apply_2(v_f_2934_, v_val_2939_, v_b_2936_);
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2941_, lean_object* v_inst_2942_, lean_object* v_00_u03b2_2943_, lean_object* v_lctx_2944_, lean_object* v_init_2945_, lean_object* v_f_2946_){
_start:
{
lean_object* v_decls_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; 
v_decls_2947_ = lean_ctor_get(v_lctx_2944_, 1);
v___f_2948_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2948_, 0, v_toPure_2941_);
lean_closure_set(v___f_2948_, 1, v_f_2946_);
v___x_2949_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2942_, v_decls_2947_, v_init_2945_, v___f_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2950_, lean_object* v_inst_2951_, lean_object* v_00_u03b2_2952_, lean_object* v_lctx_2953_, lean_object* v_init_2954_, lean_object* v_f_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2950_, v_inst_2951_, v_00_u03b2_2952_, v_lctx_2953_, v_init_2954_, v_f_2955_);
lean_dec_ref(v_lctx_2953_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2957_){
_start:
{
lean_object* v_toApplicative_2958_; lean_object* v_toPure_2959_; lean_object* v___f_2960_; 
v_toApplicative_2958_ = lean_ctor_get(v_inst_2957_, 0);
v_toPure_2959_ = lean_ctor_get(v_toApplicative_2958_, 1);
lean_inc(v_toPure_2959_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2960_, 0, v_toPure_2959_);
lean_closure_set(v___f_2960_, 1, v_inst_2957_);
return v___f_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2961_, lean_object* v_inst_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2964_, lean_object* v_x1_2965_, lean_object* v_x2_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_apply_2(v_f_2964_, v_x1_2965_, v_x2_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2987_, lean_object* v_f_2988_, lean_object* v_init_2989_, lean_object* v_start_2990_){
_start:
{
lean_object* v___f_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___f_2991_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2991_, 0, v_f_2988_);
v___x_2992_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2993_ = l_Lean_LocalContext_foldlM___redArg(v___x_2992_, v_lctx_2987_, v___f_2991_, v_init_2989_, v_start_2990_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2994_, lean_object* v_f_2995_, lean_object* v_init_2996_, lean_object* v_start_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2994_, v_f_2995_, v_init_2996_, v_start_2997_);
lean_dec(v_start_2997_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2999_, lean_object* v_lctx_3000_, lean_object* v_f_3001_, lean_object* v_init_3002_, lean_object* v_start_3003_){
_start:
{
lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3004_, 0, v_f_3001_);
v___x_3005_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3006_ = l_Lean_LocalContext_foldlM___redArg(v___x_3005_, v_lctx_3000_, v___f_3004_, v_init_3002_, v_start_3003_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_3007_, lean_object* v_lctx_3008_, lean_object* v_f_3009_, lean_object* v_init_3010_, lean_object* v_start_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_LocalContext_foldl(v_00_u03b2_3007_, v_lctx_3008_, v_f_3009_, v_init_3010_, v_start_3011_);
lean_dec(v_start_3011_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_3013_, lean_object* v_x1_3014_, lean_object* v_x2_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_apply_2(v_f_3013_, v_x1_3014_, v_x2_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_3017_, lean_object* v_f_3018_, lean_object* v_init_3019_){
_start:
{
lean_object* v___f_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3020_, 0, v_f_3018_);
v___x_3021_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3022_ = l_Lean_LocalContext_foldrM___redArg(v___x_3021_, v_lctx_3017_, v___f_3020_, v_init_3019_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_3023_, lean_object* v_lctx_3024_, lean_object* v_f_3025_, lean_object* v_init_3026_){
_start:
{
lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___f_3027_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3027_, 0, v_f_3025_);
v___x_3028_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3029_ = l_Lean_LocalContext_foldrM___redArg(v___x_3028_, v_lctx_3024_, v___f_3027_, v_init_3026_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_3030_, size_t v_i_3031_, size_t v_stop_3032_, lean_object* v_b_3033_){
_start:
{
lean_object* v___y_3035_; uint8_t v___x_3039_; 
v___x_3039_ = lean_usize_dec_eq(v_i_3031_, v_stop_3032_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_array_uget_borrowed(v_as_3030_, v_i_3031_);
if (lean_obj_tag(v___x_3040_) == 0)
{
v___y_3035_ = v_b_3033_;
goto v___jp_3034_;
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_unsigned_to_nat(1u);
v___x_3042_ = lean_nat_add(v_b_3033_, v___x_3041_);
lean_dec(v_b_3033_);
v___y_3035_ = v___x_3042_;
goto v___jp_3034_;
}
}
else
{
return v_b_3033_;
}
v___jp_3034_:
{
size_t v___x_3036_; size_t v___x_3037_; 
v___x_3036_ = ((size_t)1ULL);
v___x_3037_ = lean_usize_add(v_i_3031_, v___x_3036_);
v_i_3031_ = v___x_3037_;
v_b_3033_ = v___y_3035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3043_, lean_object* v_i_3044_, lean_object* v_stop_3045_, lean_object* v_b_3046_){
_start:
{
size_t v_i_boxed_3047_; size_t v_stop_boxed_3048_; lean_object* v_res_3049_; 
v_i_boxed_3047_ = lean_unbox_usize(v_i_3044_);
lean_dec(v_i_3044_);
v_stop_boxed_3048_ = lean_unbox_usize(v_stop_3045_);
lean_dec(v_stop_3045_);
v_res_3049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3043_, v_i_boxed_3047_, v_stop_boxed_3048_, v_b_3046_);
lean_dec_ref(v_as_3043_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3050_, lean_object* v_x_3051_){
_start:
{
if (lean_obj_tag(v_x_3050_) == 0)
{
lean_object* v_cs_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v_cs_3052_ = lean_ctor_get(v_x_3050_, 0);
v___x_3053_ = lean_unsigned_to_nat(0u);
v___x_3054_ = lean_array_get_size(v_cs_3052_);
v___x_3055_ = lean_nat_dec_lt(v___x_3053_, v___x_3054_);
if (v___x_3055_ == 0)
{
return v_x_3051_;
}
else
{
uint8_t v___x_3056_; 
v___x_3056_ = lean_nat_dec_le(v___x_3054_, v___x_3054_);
if (v___x_3056_ == 0)
{
if (v___x_3055_ == 0)
{
return v_x_3051_;
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = lean_usize_of_nat(v___x_3054_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3052_, v___x_3057_, v___x_3058_, v_x_3051_);
return v___x_3059_;
}
}
else
{
size_t v___x_3060_; size_t v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = ((size_t)0ULL);
v___x_3061_ = lean_usize_of_nat(v___x_3054_);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3052_, v___x_3060_, v___x_3061_, v_x_3051_);
return v___x_3062_;
}
}
}
else
{
lean_object* v_vs_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v_vs_3063_ = lean_ctor_get(v_x_3050_, 0);
v___x_3064_ = lean_unsigned_to_nat(0u);
v___x_3065_ = lean_array_get_size(v_vs_3063_);
v___x_3066_ = lean_nat_dec_lt(v___x_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
return v_x_3051_;
}
else
{
uint8_t v___x_3067_; 
v___x_3067_ = lean_nat_dec_le(v___x_3065_, v___x_3065_);
if (v___x_3067_ == 0)
{
if (v___x_3066_ == 0)
{
return v_x_3051_;
}
else
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = lean_usize_of_nat(v___x_3065_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3063_, v___x_3068_, v___x_3069_, v_x_3051_);
return v___x_3070_;
}
}
else
{
size_t v___x_3071_; size_t v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = lean_usize_of_nat(v___x_3065_);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3063_, v___x_3071_, v___x_3072_, v_x_3051_);
return v___x_3073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3074_, size_t v_i_3075_, size_t v_stop_3076_, lean_object* v_b_3077_){
_start:
{
uint8_t v___x_3078_; 
v___x_3078_ = lean_usize_dec_eq(v_i_3075_, v_stop_3076_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; size_t v___x_3081_; size_t v___x_3082_; 
v___x_3079_ = lean_array_uget_borrowed(v_as_3074_, v_i_3075_);
v___x_3080_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3079_, v_b_3077_);
v___x_3081_ = ((size_t)1ULL);
v___x_3082_ = lean_usize_add(v_i_3075_, v___x_3081_);
v_i_3075_ = v___x_3082_;
v_b_3077_ = v___x_3080_;
goto _start;
}
else
{
return v_b_3077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3084_, lean_object* v_i_3085_, lean_object* v_stop_3086_, lean_object* v_b_3087_){
_start:
{
size_t v_i_boxed_3088_; size_t v_stop_boxed_3089_; lean_object* v_res_3090_; 
v_i_boxed_3088_ = lean_unbox_usize(v_i_3085_);
lean_dec(v_i_3085_);
v_stop_boxed_3089_ = lean_unbox_usize(v_stop_3086_);
lean_dec(v_stop_3086_);
v_res_3090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3084_, v_i_boxed_3088_, v_stop_boxed_3089_, v_b_3087_);
lean_dec_ref(v_as_3084_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3091_, v_x_3092_);
lean_dec_ref(v_x_3091_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3094_, size_t v_x_3095_, size_t v_x_3096_, lean_object* v_x_3097_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
lean_object* v_cs_3098_; lean_object* v___x_3099_; size_t v___x_3100_; lean_object* v_j_3101_; lean_object* v___x_3102_; size_t v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; size_t v___x_3106_; size_t v___x_3107_; size_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v_cs_3098_ = lean_ctor_get(v_x_3094_, 0);
v___x_3099_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3100_ = lean_usize_shift_right(v_x_3095_, v_x_3096_);
v_j_3101_ = lean_usize_to_nat(v___x_3100_);
v___x_3102_ = lean_array_get_borrowed(v___x_3099_, v_cs_3098_, v_j_3101_);
v___x_3103_ = ((size_t)1ULL);
v___x_3104_ = lean_usize_shift_left(v___x_3103_, v_x_3096_);
v___x_3105_ = lean_usize_sub(v___x_3104_, v___x_3103_);
v___x_3106_ = lean_usize_land(v_x_3095_, v___x_3105_);
v___x_3107_ = ((size_t)5ULL);
v___x_3108_ = lean_usize_sub(v_x_3096_, v___x_3107_);
v___x_3109_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3102_, v___x_3106_, v___x_3108_, v_x_3097_);
v___x_3110_ = lean_unsigned_to_nat(1u);
v___x_3111_ = lean_nat_add(v_j_3101_, v___x_3110_);
lean_dec(v_j_3101_);
v___x_3112_ = lean_array_get_size(v_cs_3098_);
v___x_3113_ = lean_nat_dec_lt(v___x_3111_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_dec(v___x_3111_);
return v___x_3109_;
}
else
{
uint8_t v___x_3114_; 
v___x_3114_ = lean_nat_dec_le(v___x_3112_, v___x_3112_);
if (v___x_3114_ == 0)
{
if (v___x_3113_ == 0)
{
lean_dec(v___x_3111_);
return v___x_3109_;
}
else
{
size_t v___x_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_usize_of_nat(v___x_3111_);
lean_dec(v___x_3111_);
v___x_3116_ = lean_usize_of_nat(v___x_3112_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3098_, v___x_3115_, v___x_3116_, v___x_3109_);
return v___x_3117_;
}
}
else
{
size_t v___x_3118_; size_t v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_usize_of_nat(v___x_3111_);
lean_dec(v___x_3111_);
v___x_3119_ = lean_usize_of_nat(v___x_3112_);
v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3098_, v___x_3118_, v___x_3119_, v___x_3109_);
return v___x_3120_;
}
}
}
else
{
lean_object* v_vs_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v_vs_3121_ = lean_ctor_get(v_x_3094_, 0);
v___x_3122_ = lean_usize_to_nat(v_x_3095_);
v___x_3123_ = lean_array_get_size(v_vs_3121_);
v___x_3124_ = lean_nat_dec_lt(v___x_3122_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_dec(v___x_3122_);
return v_x_3097_;
}
else
{
uint8_t v___x_3125_; 
v___x_3125_ = lean_nat_dec_le(v___x_3123_, v___x_3123_);
if (v___x_3125_ == 0)
{
if (v___x_3124_ == 0)
{
lean_dec(v___x_3122_);
return v_x_3097_;
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = lean_usize_of_nat(v___x_3122_);
lean_dec(v___x_3122_);
v___x_3127_ = lean_usize_of_nat(v___x_3123_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3121_, v___x_3126_, v___x_3127_, v_x_3097_);
return v___x_3128_;
}
}
else
{
size_t v___x_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = lean_usize_of_nat(v___x_3122_);
lean_dec(v___x_3122_);
v___x_3130_ = lean_usize_of_nat(v___x_3123_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3121_, v___x_3129_, v___x_3130_, v_x_3097_);
return v___x_3131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3132_, lean_object* v_x_3133_, lean_object* v_x_3134_, lean_object* v_x_3135_){
_start:
{
size_t v_x_1557__boxed_3136_; size_t v_x_1558__boxed_3137_; lean_object* v_res_3138_; 
v_x_1557__boxed_3136_ = lean_unbox_usize(v_x_3133_);
lean_dec(v_x_3133_);
v_x_1558__boxed_3137_ = lean_unbox_usize(v_x_3134_);
lean_dec(v_x_3134_);
v_res_3138_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3132_, v_x_1557__boxed_3136_, v_x_1558__boxed_3137_, v_x_3135_);
lean_dec_ref(v_x_3132_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3139_, lean_object* v_init_3140_, lean_object* v_start_3141_){
_start:
{
lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_nat_dec_eq(v_start_3141_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v_root_3144_; lean_object* v_tail_3145_; size_t v_shift_3146_; lean_object* v_tailOff_3147_; uint8_t v___x_3148_; 
v_root_3144_ = lean_ctor_get(v_t_3139_, 0);
v_tail_3145_ = lean_ctor_get(v_t_3139_, 1);
v_shift_3146_ = lean_ctor_get_usize(v_t_3139_, 4);
v_tailOff_3147_ = lean_ctor_get(v_t_3139_, 3);
v___x_3148_ = lean_nat_dec_le(v_tailOff_3147_, v_start_3141_);
if (v___x_3148_ == 0)
{
size_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3149_ = lean_usize_of_nat(v_start_3141_);
v___x_3150_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3144_, v___x_3149_, v_shift_3146_, v_init_3140_);
v___x_3151_ = lean_array_get_size(v_tail_3145_);
v___x_3152_ = lean_nat_dec_lt(v___x_3142_, v___x_3151_);
if (v___x_3152_ == 0)
{
return v___x_3150_;
}
else
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_nat_dec_le(v___x_3151_, v___x_3151_);
if (v___x_3153_ == 0)
{
if (v___x_3152_ == 0)
{
return v___x_3150_;
}
else
{
size_t v___x_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((size_t)0ULL);
v___x_3155_ = lean_usize_of_nat(v___x_3151_);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3145_, v___x_3154_, v___x_3155_, v___x_3150_);
return v___x_3156_;
}
}
else
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = ((size_t)0ULL);
v___x_3158_ = lean_usize_of_nat(v___x_3151_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3145_, v___x_3157_, v___x_3158_, v___x_3150_);
return v___x_3159_;
}
}
}
else
{
lean_object* v___x_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3160_ = lean_nat_sub(v_start_3141_, v_tailOff_3147_);
v___x_3161_ = lean_array_get_size(v_tail_3145_);
v___x_3162_ = lean_nat_dec_lt(v___x_3160_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_dec(v___x_3160_);
return v_init_3140_;
}
else
{
uint8_t v___x_3163_; 
v___x_3163_ = lean_nat_dec_le(v___x_3161_, v___x_3161_);
if (v___x_3163_ == 0)
{
if (v___x_3162_ == 0)
{
lean_dec(v___x_3160_);
return v_init_3140_;
}
else
{
size_t v___x_3164_; size_t v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_usize_of_nat(v___x_3160_);
lean_dec(v___x_3160_);
v___x_3165_ = lean_usize_of_nat(v___x_3161_);
v___x_3166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3145_, v___x_3164_, v___x_3165_, v_init_3140_);
return v___x_3166_;
}
}
else
{
size_t v___x_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_usize_of_nat(v___x_3160_);
lean_dec(v___x_3160_);
v___x_3168_ = lean_usize_of_nat(v___x_3161_);
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3145_, v___x_3167_, v___x_3168_, v_init_3140_);
return v___x_3169_;
}
}
}
}
else
{
lean_object* v_root_3170_; lean_object* v_tail_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_root_3170_ = lean_ctor_get(v_t_3139_, 0);
v_tail_3171_ = lean_ctor_get(v_t_3139_, 1);
v___x_3172_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3170_, v_init_3140_);
v___x_3173_ = lean_array_get_size(v_tail_3171_);
v___x_3174_ = lean_nat_dec_lt(v___x_3142_, v___x_3173_);
if (v___x_3174_ == 0)
{
return v___x_3172_;
}
else
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_nat_dec_le(v___x_3173_, v___x_3173_);
if (v___x_3175_ == 0)
{
if (v___x_3174_ == 0)
{
return v___x_3172_;
}
else
{
size_t v___x_3176_; size_t v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = ((size_t)0ULL);
v___x_3177_ = lean_usize_of_nat(v___x_3173_);
v___x_3178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3171_, v___x_3176_, v___x_3177_, v___x_3172_);
return v___x_3178_;
}
}
else
{
size_t v___x_3179_; size_t v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = ((size_t)0ULL);
v___x_3180_ = lean_usize_of_nat(v___x_3173_);
v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3171_, v___x_3179_, v___x_3180_, v___x_3172_);
return v___x_3181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3182_, lean_object* v_init_3183_, lean_object* v_start_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3182_, v_init_3183_, v_start_3184_);
lean_dec(v_start_3184_);
lean_dec_ref(v_t_3182_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3186_, lean_object* v_init_3187_, lean_object* v_start_3188_){
_start:
{
lean_object* v_decls_3189_; lean_object* v___x_3190_; 
v_decls_3189_ = lean_ctor_get(v_lctx_3186_, 1);
v___x_3190_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3189_, v_init_3187_, v_start_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3191_, lean_object* v_init_3192_, lean_object* v_start_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3191_, v_init_3192_, v_start_3193_);
lean_dec(v_start_3193_);
lean_dec_ref(v_lctx_3191_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3195_){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3195_, v___x_3196_, v___x_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_LocalContext_size(v_lctx_3198_);
lean_dec_ref(v_lctx_3198_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3200_, lean_object* v_x_3201_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_apply_1(v_f_3200_, v_x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3203_, lean_object* v_f_3204_){
_start:
{
lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___f_3205_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3205_, 0, v_f_3204_);
v___x_3206_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3207_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3206_, v_lctx_3203_, v___f_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3208_, lean_object* v_lctx_3209_, lean_object* v_f_3210_){
_start:
{
lean_object* v___f_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3211_, 0, v_f_3210_);
v___x_3212_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3213_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3212_, v_lctx_3209_, v___f_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3214_, lean_object* v_f_3215_){
_start:
{
lean_object* v___f_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___f_3216_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3216_, 0, v_f_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3218_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3217_, v_lctx_3214_, v___f_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3219_, lean_object* v_lctx_3220_, lean_object* v_f_3221_){
_start:
{
lean_object* v___f_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___f_3222_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3222_, 0, v_f_3221_);
v___x_3223_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3224_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3223_, v_lctx_3220_, v___f_3222_);
return v___x_3224_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3225_, lean_object* v_as_3226_, size_t v_i_3227_, size_t v_stop_3228_){
_start:
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_usize_dec_eq(v_i_3227_, v_stop_3228_);
if (v___x_3229_ == 0)
{
uint8_t v___x_3230_; uint8_t v___y_3232_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v_fvarId_3238_; uint8_t v___x_3239_; 
v___x_3230_ = 1;
v___x_3236_ = lean_array_uget_borrowed(v_as_3226_, v_i_3227_);
v___x_3237_ = l_Lean_Expr_fvarId_x21(v___x_3236_);
v_fvarId_3238_ = lean_ctor_get(v_val_3225_, 1);
v___x_3239_ = l_Lean_instBEqFVarId_beq(v___x_3237_, v_fvarId_3238_);
lean_dec(v___x_3237_);
v___y_3232_ = v___x_3239_;
goto v___jp_3231_;
v___jp_3231_:
{
if (v___y_3232_ == 0)
{
size_t v___x_3233_; size_t v___x_3234_; 
v___x_3233_ = ((size_t)1ULL);
v___x_3234_ = lean_usize_add(v_i_3227_, v___x_3233_);
v_i_3227_ = v___x_3234_;
goto _start;
}
else
{
return v___x_3230_;
}
}
}
else
{
uint8_t v___x_3240_; 
v___x_3240_ = 0;
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3241_, lean_object* v_as_3242_, lean_object* v_i_3243_, lean_object* v_stop_3244_){
_start:
{
size_t v_i_boxed_3245_; size_t v_stop_boxed_3246_; uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_i_boxed_3245_ = lean_unbox_usize(v_i_3243_);
lean_dec(v_i_3243_);
v_stop_boxed_3246_ = lean_unbox_usize(v_stop_3244_);
lean_dec(v_stop_3244_);
v_res_3247_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3241_, v_as_3242_, v_i_boxed_3245_, v_stop_boxed_3246_);
lean_dec_ref(v_as_3242_);
lean_dec_ref(v_val_3241_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3249_, lean_object* v_a_u2082_3250_, lean_object* v_exceptFVars_3251_, lean_object* v_i_3252_, lean_object* v_j_3253_){
_start:
{
lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v_size_3269_; uint8_t v___x_3270_; 
v_size_3269_ = lean_ctor_get(v_a_u2081_3249_, 2);
v___x_3270_ = lean_nat_dec_lt(v_i_3252_, v_size_3269_);
if (v___x_3270_ == 0)
{
uint8_t v___x_3271_; 
lean_dec(v_j_3253_);
lean_dec(v_i_3252_);
v___x_3271_ = 1;
return v___x_3271_;
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = lean_box(0);
v___x_3273_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3272_, v_a_u2081_3249_, v_i_3252_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = lean_unsigned_to_nat(1u);
v___x_3275_ = lean_nat_add(v_i_3252_, v___x_3274_);
lean_dec(v_i_3252_);
v_i_3252_ = v___x_3275_;
goto _start;
}
else
{
lean_object* v_val_3277_; uint8_t v___y_3279_; lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v_val_3277_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_val_3277_);
lean_dec_ref_known(v___x_3273_, 1);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_array_get_size(v_exceptFVars_3251_);
v___x_3290_ = lean_nat_dec_lt(v___x_3288_, v___x_3289_);
if (v___x_3290_ == 0)
{
v___y_3279_ = v___x_3290_;
goto v___jp_3278_;
}
else
{
if (v___x_3290_ == 0)
{
v___y_3279_ = v___x_3290_;
goto v___jp_3278_;
}
else
{
size_t v___x_3291_; size_t v___x_3292_; uint8_t v___x_3293_; 
v___x_3291_ = ((size_t)0ULL);
v___x_3292_ = lean_usize_of_nat(v___x_3289_);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3277_, v_exceptFVars_3251_, v___x_3291_, v___x_3292_);
if (v___x_3293_ == 0)
{
v___y_3279_ = v___x_3293_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec(v_val_3277_);
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = lean_nat_add(v_i_3252_, v___x_3294_);
lean_dec(v_i_3252_);
v_i_3252_ = v___x_3295_;
goto _start;
}
}
}
v___jp_3278_:
{
lean_object* v_size_3280_; uint8_t v___x_3281_; 
v_size_3280_ = lean_ctor_get(v_a_u2082_3250_, 2);
v___x_3281_ = lean_nat_dec_lt(v_j_3253_, v_size_3280_);
if (v___x_3281_ == 0)
{
lean_dec(v_val_3277_);
lean_dec(v_j_3253_);
lean_dec(v_i_3252_);
return v___y_3279_;
}
else
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3272_, v_a_u2082_3250_, v_j_3253_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec(v_val_3277_);
v___x_3283_ = lean_unsigned_to_nat(1u);
v___x_3284_ = lean_nat_add(v_j_3253_, v___x_3283_);
lean_dec(v_j_3253_);
v_j_3253_ = v___x_3284_;
goto _start;
}
else
{
lean_object* v_val_3286_; lean_object* v_fvarId_3287_; 
v_val_3286_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_val_3286_);
lean_dec_ref_known(v___x_3282_, 1);
v_fvarId_3287_ = lean_ctor_get(v_val_3277_, 1);
lean_inc(v_fvarId_3287_);
lean_dec(v_val_3277_);
v___y_3266_ = v_val_3286_;
v___y_3267_ = v_fvarId_3287_;
goto v___jp_3265_;
}
}
}
}
}
v___jp_3254_:
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Lean_instBEqFVarId_beq(v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_unsigned_to_nat(1u);
v___x_3259_ = lean_nat_add(v_j_3253_, v___x_3258_);
lean_dec(v_j_3253_);
v_j_3253_ = v___x_3259_;
goto _start;
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = lean_unsigned_to_nat(1u);
v___x_3262_ = lean_nat_add(v_i_3252_, v___x_3261_);
lean_dec(v_i_3252_);
v___x_3263_ = lean_nat_add(v_j_3253_, v___x_3261_);
lean_dec(v_j_3253_);
v_i_3252_ = v___x_3262_;
v_j_3253_ = v___x_3263_;
goto _start;
}
}
v___jp_3265_:
{
lean_object* v_fvarId_3268_; 
v_fvarId_3268_ = lean_ctor_get(v___y_3266_, 1);
lean_inc(v_fvarId_3268_);
lean_dec_ref(v___y_3266_);
v___y_3255_ = v___y_3267_;
v___y_3256_ = v_fvarId_3268_;
goto v___jp_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3297_, lean_object* v_a_u2082_3298_, lean_object* v_exceptFVars_3299_, lean_object* v_i_3300_, lean_object* v_j_3301_){
_start:
{
uint8_t v_res_3302_; lean_object* v_r_3303_; 
v_res_3302_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3297_, v_a_u2082_3298_, v_exceptFVars_3299_, v_i_3300_, v_j_3301_);
lean_dec_ref(v_exceptFVars_3299_);
lean_dec_ref(v_a_u2082_3298_);
lean_dec_ref(v_a_u2081_3297_);
v_r_3303_ = lean_box(v_res_3302_);
return v_r_3303_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3304_, lean_object* v_lctx_u2082_3305_, lean_object* v_exceptFVars_3306_){
_start:
{
lean_object* v_decls_3307_; lean_object* v_decls_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v_decls_3307_ = lean_ctor_get(v_lctx_u2081_3304_, 1);
v_decls_3308_ = lean_ctor_get(v_lctx_u2082_3305_, 1);
v___x_3309_ = lean_unsigned_to_nat(0u);
v___x_3310_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3307_, v_decls_3308_, v_exceptFVars_3306_, v___x_3309_, v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3311_, lean_object* v_lctx_u2082_3312_, lean_object* v_exceptFVars_3313_){
_start:
{
uint8_t v_res_3314_; lean_object* v_r_3315_; 
v_res_3314_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3311_, v_lctx_u2082_3312_, v_exceptFVars_3313_);
lean_dec_ref(v_exceptFVars_3313_);
lean_dec_ref(v_lctx_u2082_3312_);
lean_dec_ref(v_lctx_u2081_3311_);
v_r_3315_ = lean_box(v_res_3314_);
return v_r_3315_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3317_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3318_ = lean_unsigned_to_nat(14u);
v___x_3319_ = lean_unsigned_to_nat(576u);
v___x_3320_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3321_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3322_ = l_mkPanicMessageWithDecl(v___x_3321_, v___x_3320_, v___x_3319_, v___x_3318_, v___x_3317_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3323_, lean_object* v_lctx_3324_, lean_object* v___x_3325_, uint8_t v_isLambda_3326_, uint8_t v_usedLetOnly_3327_, uint8_t v_generalizeNondepLet_3328_, lean_object* v_i_3329_, lean_object* v_x_3330_, lean_object* v_b_3331_){
_start:
{
lean_object* v_n_3333_; lean_object* v_ty_3334_; uint8_t v_bi_3335_; lean_object* v_x_3339_; lean_object* v___x_3340_; 
v_x_3339_ = lean_array_fget_borrowed(v_xs_3323_, v_i_3329_);
v___x_3340_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3324_, v_x_3339_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
lean_dec_ref(v_b_3331_);
v___x_3341_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3342_ = l_panic___redArg(v___x_3325_, v___x_3341_);
return v___x_3342_;
}
else
{
lean_object* v_val_3343_; 
v_val_3343_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3340_, 1);
if (lean_obj_tag(v_val_3343_) == 0)
{
lean_object* v_userName_3344_; lean_object* v_type_3345_; uint8_t v_bi_3346_; 
v_userName_3344_ = lean_ctor_get(v_val_3343_, 2);
lean_inc(v_userName_3344_);
v_type_3345_ = lean_ctor_get(v_val_3343_, 3);
lean_inc_ref(v_type_3345_);
v_bi_3346_ = lean_ctor_get_uint8(v_val_3343_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3343_, 4);
v_n_3333_ = v_userName_3344_;
v_ty_3334_ = v_type_3345_;
v_bi_3335_ = v_bi_3346_;
goto v___jp_3332_;
}
else
{
lean_object* v_userName_3347_; lean_object* v_type_3348_; lean_object* v_value_3349_; uint8_t v_nondep_3350_; uint8_t v___y_3356_; 
v_userName_3347_ = lean_ctor_get(v_val_3343_, 2);
lean_inc(v_userName_3347_);
v_type_3348_ = lean_ctor_get(v_val_3343_, 3);
lean_inc_ref(v_type_3348_);
v_value_3349_ = lean_ctor_get(v_val_3343_, 4);
lean_inc_ref(v_value_3349_);
v_nondep_3350_ = lean_ctor_get_uint8(v_val_3343_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3343_, 5);
if (v_nondep_3350_ == 0)
{
v___y_3356_ = v_nondep_3350_;
goto v___jp_3355_;
}
else
{
if (v_generalizeNondepLet_3328_ == 0)
{
v___y_3356_ = v_generalizeNondepLet_3328_;
goto v___jp_3355_;
}
else
{
uint8_t v___x_3361_; 
lean_dec_ref(v_value_3349_);
v___x_3361_ = 0;
v_n_3333_ = v_userName_3347_;
v_ty_3334_ = v_type_3348_;
v_bi_3335_ = v___x_3361_;
goto v___jp_3332_;
}
}
v___jp_3351_:
{
lean_object* v_ty_3352_; lean_object* v_val_3353_; lean_object* v___x_3354_; 
v_ty_3352_ = lean_expr_abstract_range(v_type_3348_, v_i_3329_, v_xs_3323_);
lean_dec_ref(v_type_3348_);
v_val_3353_ = lean_expr_abstract_range(v_value_3349_, v_i_3329_, v_xs_3323_);
lean_dec_ref(v_value_3349_);
v___x_3354_ = l_Lean_Expr_letE___override(v_userName_3347_, v_ty_3352_, v_val_3353_, v_b_3331_, v_nondep_3350_);
return v___x_3354_;
}
v___jp_3355_:
{
if (v_usedLetOnly_3327_ == 0)
{
goto v___jp_3351_;
}
else
{
if (v___y_3356_ == 0)
{
lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = lean_unsigned_to_nat(0u);
v___x_3358_ = lean_expr_has_loose_bvar(v_b_3331_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec_ref(v_value_3349_);
lean_dec_ref(v_type_3348_);
lean_dec(v_userName_3347_);
v___x_3359_ = lean_unsigned_to_nat(1u);
v___x_3360_ = lean_expr_lower_loose_bvars(v_b_3331_, v___x_3359_, v___x_3359_);
lean_dec_ref(v_b_3331_);
return v___x_3360_;
}
else
{
goto v___jp_3351_;
}
}
else
{
goto v___jp_3351_;
}
}
}
}
}
v___jp_3332_:
{
lean_object* v_ty_3336_; 
v_ty_3336_ = lean_expr_abstract_range(v_ty_3334_, v_i_3329_, v_xs_3323_);
lean_dec_ref(v_ty_3334_);
if (v_isLambda_3326_ == 0)
{
lean_object* v___x_3337_; 
v___x_3337_ = l_Lean_mkForall(v_n_3333_, v_bi_3335_, v_ty_3336_, v_b_3331_);
return v___x_3337_;
}
else
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_mkLambda(v_n_3333_, v_bi_3335_, v_ty_3336_, v_b_3331_);
return v___x_3338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3362_, lean_object* v_lctx_3363_, lean_object* v___x_3364_, lean_object* v_isLambda_3365_, lean_object* v_usedLetOnly_3366_, lean_object* v_generalizeNondepLet_3367_, lean_object* v_i_3368_, lean_object* v_x_3369_, lean_object* v_b_3370_){
_start:
{
uint8_t v_isLambda_boxed_3371_; uint8_t v_usedLetOnly_boxed_3372_; uint8_t v_generalizeNondepLet_boxed_3373_; lean_object* v_res_3374_; 
v_isLambda_boxed_3371_ = lean_unbox(v_isLambda_3365_);
v_usedLetOnly_boxed_3372_ = lean_unbox(v_usedLetOnly_3366_);
v_generalizeNondepLet_boxed_3373_ = lean_unbox(v_generalizeNondepLet_3367_);
v_res_3374_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3362_, v_lctx_3363_, v___x_3364_, v_isLambda_boxed_3371_, v_usedLetOnly_boxed_3372_, v_generalizeNondepLet_boxed_3373_, v_i_3368_, v_x_3369_, v_b_3370_);
lean_dec(v_i_3368_);
lean_dec_ref(v___x_3364_);
lean_dec_ref(v_xs_3362_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3375_, lean_object* v_lctx_3376_, lean_object* v_xs_3377_, lean_object* v_b_3378_, uint8_t v_usedLetOnly_3379_, uint8_t v_generalizeNondepLet_3380_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___f_3385_; lean_object* v_b_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3381_ = l_Lean_instInhabitedExpr;
v___x_3382_ = lean_box(v_isLambda_3375_);
v___x_3383_ = lean_box(v_usedLetOnly_3379_);
v___x_3384_ = lean_box(v_generalizeNondepLet_3380_);
lean_inc_ref(v_xs_3377_);
v___f_3385_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3385_, 0, v_xs_3377_);
lean_closure_set(v___f_3385_, 1, v_lctx_3376_);
lean_closure_set(v___f_3385_, 2, v___x_3381_);
lean_closure_set(v___f_3385_, 3, v___x_3382_);
lean_closure_set(v___f_3385_, 4, v___x_3383_);
lean_closure_set(v___f_3385_, 5, v___x_3384_);
v_b_3386_ = lean_expr_abstract(v_b_3378_, v_xs_3377_);
v___x_3387_ = lean_array_get_size(v_xs_3377_);
lean_dec_ref(v_xs_3377_);
v___x_3388_ = l_Nat_foldRev___redArg(v___x_3387_, v___f_3385_, v_b_3386_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3389_, lean_object* v_lctx_3390_, lean_object* v_xs_3391_, lean_object* v_b_3392_, lean_object* v_usedLetOnly_3393_, lean_object* v_generalizeNondepLet_3394_){
_start:
{
uint8_t v_isLambda_boxed_3395_; uint8_t v_usedLetOnly_boxed_3396_; uint8_t v_generalizeNondepLet_boxed_3397_; lean_object* v_res_3398_; 
v_isLambda_boxed_3395_ = lean_unbox(v_isLambda_3389_);
v_usedLetOnly_boxed_3396_ = lean_unbox(v_usedLetOnly_3393_);
v_generalizeNondepLet_boxed_3397_ = lean_unbox(v_generalizeNondepLet_3394_);
v_res_3398_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3395_, v_lctx_3390_, v_xs_3391_, v_b_3392_, v_usedLetOnly_boxed_3396_, v_generalizeNondepLet_boxed_3397_);
lean_dec_ref(v_b_3392_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3399_, lean_object* v_lctx_3400_, uint8_t v_usedLetOnly_3401_, uint8_t v_generalizeNondepLet_3402_, lean_object* v_x_3403_, lean_object* v_x_3404_){
_start:
{
lean_object* v_zero_3405_; uint8_t v_isZero_3406_; 
v_zero_3405_ = lean_unsigned_to_nat(0u);
v_isZero_3406_ = lean_nat_dec_eq(v_x_3403_, v_zero_3405_);
if (v_isZero_3406_ == 1)
{
lean_dec(v_x_3403_);
lean_dec_ref(v_lctx_3400_);
return v_x_3404_;
}
else
{
lean_object* v_one_3407_; lean_object* v_n_3408_; lean_object* v_n_3410_; lean_object* v_ty_3411_; uint8_t v_bi_3412_; lean_object* v_x_3416_; lean_object* v___x_3417_; 
v_one_3407_ = lean_unsigned_to_nat(1u);
v_n_3408_ = lean_nat_sub(v_x_3403_, v_one_3407_);
lean_dec(v_x_3403_);
v_x_3416_ = lean_array_fget_borrowed(v_xs_3399_, v_n_3408_);
lean_inc_ref(v_lctx_3400_);
v___x_3417_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3400_, v_x_3416_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec_ref(v_x_3404_);
v___x_3418_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3419_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3418_);
v_x_3403_ = v_n_3408_;
v_x_3404_ = v___x_3419_;
goto _start;
}
else
{
lean_object* v_val_3421_; 
v_val_3421_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_val_3421_);
lean_dec_ref_known(v___x_3417_, 1);
if (lean_obj_tag(v_val_3421_) == 0)
{
lean_object* v_userName_3422_; lean_object* v_type_3423_; uint8_t v_bi_3424_; 
v_userName_3422_ = lean_ctor_get(v_val_3421_, 2);
lean_inc(v_userName_3422_);
v_type_3423_ = lean_ctor_get(v_val_3421_, 3);
lean_inc_ref(v_type_3423_);
v_bi_3424_ = lean_ctor_get_uint8(v_val_3421_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3421_, 4);
v_n_3410_ = v_userName_3422_;
v_ty_3411_ = v_type_3423_;
v_bi_3412_ = v_bi_3424_;
goto v___jp_3409_;
}
else
{
lean_object* v_userName_3425_; lean_object* v_type_3426_; lean_object* v_value_3427_; uint8_t v_nondep_3428_; uint8_t v___y_3435_; 
v_userName_3425_ = lean_ctor_get(v_val_3421_, 2);
lean_inc(v_userName_3425_);
v_type_3426_ = lean_ctor_get(v_val_3421_, 3);
lean_inc_ref(v_type_3426_);
v_value_3427_ = lean_ctor_get(v_val_3421_, 4);
lean_inc_ref(v_value_3427_);
v_nondep_3428_ = lean_ctor_get_uint8(v_val_3421_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3421_, 5);
if (v_nondep_3428_ == 0)
{
v___y_3435_ = v_nondep_3428_;
goto v___jp_3434_;
}
else
{
if (v_generalizeNondepLet_3402_ == 0)
{
v___y_3435_ = v_generalizeNondepLet_3402_;
goto v___jp_3434_;
}
else
{
uint8_t v___x_3439_; 
lean_dec_ref(v_value_3427_);
v___x_3439_ = 0;
v_n_3410_ = v_userName_3425_;
v_ty_3411_ = v_type_3426_;
v_bi_3412_ = v___x_3439_;
goto v___jp_3409_;
}
}
v___jp_3429_:
{
lean_object* v_ty_3430_; lean_object* v_val_3431_; lean_object* v___x_3432_; 
v_ty_3430_ = lean_expr_abstract_range(v_type_3426_, v_n_3408_, v_xs_3399_);
lean_dec_ref(v_type_3426_);
v_val_3431_ = lean_expr_abstract_range(v_value_3427_, v_n_3408_, v_xs_3399_);
lean_dec_ref(v_value_3427_);
v___x_3432_ = l_Lean_Expr_letE___override(v_userName_3425_, v_ty_3430_, v_val_3431_, v_x_3404_, v_nondep_3428_);
v_x_3403_ = v_n_3408_;
v_x_3404_ = v___x_3432_;
goto _start;
}
v___jp_3434_:
{
if (v_usedLetOnly_3401_ == 0)
{
goto v___jp_3429_;
}
else
{
if (v___y_3435_ == 0)
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_expr_has_loose_bvar(v_x_3404_, v_zero_3405_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; 
lean_dec_ref(v_value_3427_);
lean_dec_ref(v_type_3426_);
lean_dec(v_userName_3425_);
v___x_3437_ = lean_expr_lower_loose_bvars(v_x_3404_, v_one_3407_, v_one_3407_);
lean_dec_ref(v_x_3404_);
v_x_3403_ = v_n_3408_;
v_x_3404_ = v___x_3437_;
goto _start;
}
else
{
goto v___jp_3429_;
}
}
else
{
goto v___jp_3429_;
}
}
}
}
}
v___jp_3409_:
{
lean_object* v_ty_3413_; lean_object* v___x_3414_; 
v_ty_3413_ = lean_expr_abstract_range(v_ty_3411_, v_n_3408_, v_xs_3399_);
lean_dec_ref(v_ty_3411_);
v___x_3414_ = l_Lean_mkLambda(v_n_3410_, v_bi_3412_, v_ty_3413_, v_x_3404_);
v_x_3403_ = v_n_3408_;
v_x_3404_ = v___x_3414_;
goto _start;
}
}
}
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
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3449_, lean_object* v_lctx_3450_, uint8_t v_usedLetOnly_3451_, uint8_t v_generalizeNondepLet_3452_, lean_object* v_x_3453_, lean_object* v_x_3454_){
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
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3490_, lean_object* v_lctx_3491_, lean_object* v_usedLetOnly_3492_, lean_object* v_generalizeNondepLet_3493_, lean_object* v_x_3494_, lean_object* v_x_3495_){
_start:
{
uint8_t v_usedLetOnly_boxed_3496_; uint8_t v_generalizeNondepLet_boxed_3497_; lean_object* v_res_3498_; 
v_usedLetOnly_boxed_3496_ = lean_unbox(v_usedLetOnly_3492_);
v_generalizeNondepLet_boxed_3497_ = lean_unbox(v_generalizeNondepLet_3493_);
v_res_3498_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3490_, v_lctx_3491_, v_usedLetOnly_boxed_3496_, v_generalizeNondepLet_boxed_3497_, v_x_3494_, v_x_3495_);
lean_dec(v_x_3494_);
lean_dec_ref(v_xs_3490_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3499_, lean_object* v_xs_3500_, lean_object* v_b_3501_, uint8_t v_usedLetOnly_3502_, uint8_t v_generalizeNondepLet_3503_){
_start:
{
lean_object* v_b_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_b_3504_ = lean_expr_abstract(v_b_3501_, v_xs_3500_);
v___x_3505_ = lean_array_get_size(v_xs_3500_);
v___x_3506_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3500_, v_lctx_3499_, v_usedLetOnly_3502_, v_generalizeNondepLet_3503_, v___x_3505_, v_b_3504_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3507_, lean_object* v_xs_3508_, lean_object* v_b_3509_, lean_object* v_usedLetOnly_3510_, lean_object* v_generalizeNondepLet_3511_){
_start:
{
uint8_t v_usedLetOnly_boxed_3512_; uint8_t v_generalizeNondepLet_boxed_3513_; lean_object* v_res_3514_; 
v_usedLetOnly_boxed_3512_ = lean_unbox(v_usedLetOnly_3510_);
v_generalizeNondepLet_boxed_3513_ = lean_unbox(v_generalizeNondepLet_3511_);
v_res_3514_ = l_Lean_LocalContext_mkLambda(v_lctx_3507_, v_xs_3508_, v_b_3509_, v_usedLetOnly_boxed_3512_, v_generalizeNondepLet_boxed_3513_);
lean_dec_ref(v_b_3509_);
lean_dec_ref(v_xs_3508_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3515_, lean_object* v_lctx_3516_, uint8_t v_usedLetOnly_3517_, uint8_t v_generalizeNondepLet_3518_, lean_object* v_x_3519_, lean_object* v_x_3520_){
_start:
{
lean_object* v_zero_3521_; uint8_t v_isZero_3522_; 
v_zero_3521_ = lean_unsigned_to_nat(0u);
v_isZero_3522_ = lean_nat_dec_eq(v_x_3519_, v_zero_3521_);
if (v_isZero_3522_ == 1)
{
lean_dec(v_x_3519_);
lean_dec_ref(v_lctx_3516_);
return v_x_3520_;
}
else
{
lean_object* v_one_3523_; lean_object* v_n_3524_; lean_object* v_n_3526_; lean_object* v_ty_3527_; uint8_t v_bi_3528_; lean_object* v_x_3532_; lean_object* v___x_3533_; 
v_one_3523_ = lean_unsigned_to_nat(1u);
v_n_3524_ = lean_nat_sub(v_x_3519_, v_one_3523_);
lean_dec(v_x_3519_);
v_x_3532_ = lean_array_fget_borrowed(v_xs_3515_, v_n_3524_);
lean_inc_ref(v_lctx_3516_);
v___x_3533_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3516_, v_x_3532_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec_ref(v_x_3520_);
v___x_3534_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3535_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3534_);
v_x_3519_ = v_n_3524_;
v_x_3520_ = v___x_3535_;
goto _start;
}
else
{
lean_object* v_val_3537_; 
v_val_3537_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_val_3537_);
lean_dec_ref_known(v___x_3533_, 1);
if (lean_obj_tag(v_val_3537_) == 0)
{
lean_object* v_userName_3538_; lean_object* v_type_3539_; uint8_t v_bi_3540_; 
v_userName_3538_ = lean_ctor_get(v_val_3537_, 2);
lean_inc(v_userName_3538_);
v_type_3539_ = lean_ctor_get(v_val_3537_, 3);
lean_inc_ref(v_type_3539_);
v_bi_3540_ = lean_ctor_get_uint8(v_val_3537_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3537_, 4);
v_n_3526_ = v_userName_3538_;
v_ty_3527_ = v_type_3539_;
v_bi_3528_ = v_bi_3540_;
goto v___jp_3525_;
}
else
{
lean_object* v_userName_3541_; lean_object* v_type_3542_; lean_object* v_value_3543_; uint8_t v_nondep_3544_; uint8_t v___y_3551_; 
v_userName_3541_ = lean_ctor_get(v_val_3537_, 2);
lean_inc(v_userName_3541_);
v_type_3542_ = lean_ctor_get(v_val_3537_, 3);
lean_inc_ref(v_type_3542_);
v_value_3543_ = lean_ctor_get(v_val_3537_, 4);
lean_inc_ref(v_value_3543_);
v_nondep_3544_ = lean_ctor_get_uint8(v_val_3537_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3537_, 5);
if (v_nondep_3544_ == 0)
{
v___y_3551_ = v_nondep_3544_;
goto v___jp_3550_;
}
else
{
if (v_generalizeNondepLet_3518_ == 0)
{
v___y_3551_ = v_generalizeNondepLet_3518_;
goto v___jp_3550_;
}
else
{
uint8_t v___x_3555_; 
lean_dec_ref(v_value_3543_);
v___x_3555_ = 0;
v_n_3526_ = v_userName_3541_;
v_ty_3527_ = v_type_3542_;
v_bi_3528_ = v___x_3555_;
goto v___jp_3525_;
}
}
v___jp_3545_:
{
lean_object* v_ty_3546_; lean_object* v_val_3547_; lean_object* v___x_3548_; 
v_ty_3546_ = lean_expr_abstract_range(v_type_3542_, v_n_3524_, v_xs_3515_);
lean_dec_ref(v_type_3542_);
v_val_3547_ = lean_expr_abstract_range(v_value_3543_, v_n_3524_, v_xs_3515_);
lean_dec_ref(v_value_3543_);
v___x_3548_ = l_Lean_Expr_letE___override(v_userName_3541_, v_ty_3546_, v_val_3547_, v_x_3520_, v_nondep_3544_);
v_x_3519_ = v_n_3524_;
v_x_3520_ = v___x_3548_;
goto _start;
}
v___jp_3550_:
{
if (v_usedLetOnly_3517_ == 0)
{
goto v___jp_3545_;
}
else
{
if (v___y_3551_ == 0)
{
uint8_t v___x_3552_; 
v___x_3552_ = lean_expr_has_loose_bvar(v_x_3520_, v_zero_3521_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; 
lean_dec_ref(v_value_3543_);
lean_dec_ref(v_type_3542_);
lean_dec(v_userName_3541_);
v___x_3553_ = lean_expr_lower_loose_bvars(v_x_3520_, v_one_3523_, v_one_3523_);
lean_dec_ref(v_x_3520_);
v_x_3519_ = v_n_3524_;
v_x_3520_ = v___x_3553_;
goto _start;
}
else
{
goto v___jp_3545_;
}
}
else
{
goto v___jp_3545_;
}
}
}
}
}
v___jp_3525_:
{
lean_object* v_ty_3529_; lean_object* v___x_3530_; 
v_ty_3529_ = lean_expr_abstract_range(v_ty_3527_, v_n_3524_, v_xs_3515_);
lean_dec_ref(v_ty_3527_);
v___x_3530_ = l_Lean_mkForall(v_n_3526_, v_bi_3528_, v_ty_3529_, v_x_3520_);
v_x_3519_ = v_n_3524_;
v_x_3520_ = v___x_3530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3556_, lean_object* v_lctx_3557_, lean_object* v_usedLetOnly_3558_, lean_object* v_generalizeNondepLet_3559_, lean_object* v_x_3560_, lean_object* v_x_3561_){
_start:
{
uint8_t v_usedLetOnly_boxed_3562_; uint8_t v_generalizeNondepLet_boxed_3563_; lean_object* v_res_3564_; 
v_usedLetOnly_boxed_3562_ = lean_unbox(v_usedLetOnly_3558_);
v_generalizeNondepLet_boxed_3563_ = lean_unbox(v_generalizeNondepLet_3559_);
v_res_3564_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3556_, v_lctx_3557_, v_usedLetOnly_boxed_3562_, v_generalizeNondepLet_boxed_3563_, v_x_3560_, v_x_3561_);
lean_dec_ref(v_xs_3556_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3565_, lean_object* v_lctx_3566_, uint8_t v_usedLetOnly_3567_, uint8_t v_generalizeNondepLet_3568_, lean_object* v_x_3569_, lean_object* v_x_3570_){
_start:
{
lean_object* v_zero_3571_; uint8_t v_isZero_3572_; 
v_zero_3571_ = lean_unsigned_to_nat(0u);
v_isZero_3572_ = lean_nat_dec_eq(v_x_3569_, v_zero_3571_);
if (v_isZero_3572_ == 1)
{
lean_dec_ref(v_lctx_3566_);
return v_x_3570_;
}
else
{
lean_object* v_one_3573_; lean_object* v_n_3574_; lean_object* v_n_3576_; lean_object* v_ty_3577_; uint8_t v_bi_3578_; lean_object* v_x_3582_; lean_object* v___x_3583_; 
v_one_3573_ = lean_unsigned_to_nat(1u);
v_n_3574_ = lean_nat_sub(v_x_3569_, v_one_3573_);
v_x_3582_ = lean_array_fget_borrowed(v_xs_3565_, v_n_3574_);
lean_inc_ref(v_lctx_3566_);
v___x_3583_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3566_, v_x_3582_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec_ref(v_x_3570_);
v___x_3584_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3585_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3584_);
v___x_3586_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3565_, v_lctx_3566_, v_usedLetOnly_3567_, v_generalizeNondepLet_3568_, v_n_3574_, v___x_3585_);
return v___x_3586_;
}
else
{
lean_object* v_val_3587_; 
v_val_3587_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_val_3587_);
lean_dec_ref_known(v___x_3583_, 1);
if (lean_obj_tag(v_val_3587_) == 0)
{
lean_object* v_userName_3588_; lean_object* v_type_3589_; uint8_t v_bi_3590_; 
v_userName_3588_ = lean_ctor_get(v_val_3587_, 2);
lean_inc(v_userName_3588_);
v_type_3589_ = lean_ctor_get(v_val_3587_, 3);
lean_inc_ref(v_type_3589_);
v_bi_3590_ = lean_ctor_get_uint8(v_val_3587_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3587_, 4);
v_n_3576_ = v_userName_3588_;
v_ty_3577_ = v_type_3589_;
v_bi_3578_ = v_bi_3590_;
goto v___jp_3575_;
}
else
{
lean_object* v_userName_3591_; lean_object* v_type_3592_; lean_object* v_value_3593_; uint8_t v_nondep_3594_; uint8_t v___y_3601_; 
v_userName_3591_ = lean_ctor_get(v_val_3587_, 2);
lean_inc(v_userName_3591_);
v_type_3592_ = lean_ctor_get(v_val_3587_, 3);
lean_inc_ref(v_type_3592_);
v_value_3593_ = lean_ctor_get(v_val_3587_, 4);
lean_inc_ref(v_value_3593_);
v_nondep_3594_ = lean_ctor_get_uint8(v_val_3587_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3587_, 5);
if (v_nondep_3594_ == 0)
{
v___y_3601_ = v_nondep_3594_;
goto v___jp_3600_;
}
else
{
if (v_generalizeNondepLet_3568_ == 0)
{
v___y_3601_ = v_generalizeNondepLet_3568_;
goto v___jp_3600_;
}
else
{
uint8_t v___x_3605_; 
lean_dec_ref(v_value_3593_);
v___x_3605_ = 0;
v_n_3576_ = v_userName_3591_;
v_ty_3577_ = v_type_3592_;
v_bi_3578_ = v___x_3605_;
goto v___jp_3575_;
}
}
v___jp_3595_:
{
lean_object* v_ty_3596_; lean_object* v_val_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_ty_3596_ = lean_expr_abstract_range(v_type_3592_, v_n_3574_, v_xs_3565_);
lean_dec_ref(v_type_3592_);
v_val_3597_ = lean_expr_abstract_range(v_value_3593_, v_n_3574_, v_xs_3565_);
lean_dec_ref(v_value_3593_);
v___x_3598_ = l_Lean_Expr_letE___override(v_userName_3591_, v_ty_3596_, v_val_3597_, v_x_3570_, v_nondep_3594_);
v___x_3599_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3565_, v_lctx_3566_, v_usedLetOnly_3567_, v_generalizeNondepLet_3568_, v_n_3574_, v___x_3598_);
return v___x_3599_;
}
v___jp_3600_:
{
if (v_usedLetOnly_3567_ == 0)
{
goto v___jp_3595_;
}
else
{
if (v___y_3601_ == 0)
{
uint8_t v___x_3602_; 
v___x_3602_ = lean_expr_has_loose_bvar(v_x_3570_, v_zero_3571_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
lean_dec_ref(v_value_3593_);
lean_dec_ref(v_type_3592_);
lean_dec(v_userName_3591_);
v___x_3603_ = lean_expr_lower_loose_bvars(v_x_3570_, v_one_3573_, v_one_3573_);
lean_dec_ref(v_x_3570_);
v___x_3604_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3565_, v_lctx_3566_, v_usedLetOnly_3567_, v_generalizeNondepLet_3568_, v_n_3574_, v___x_3603_);
return v___x_3604_;
}
else
{
goto v___jp_3595_;
}
}
else
{
goto v___jp_3595_;
}
}
}
}
}
v___jp_3575_:
{
lean_object* v_ty_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_ty_3579_ = lean_expr_abstract_range(v_ty_3577_, v_n_3574_, v_xs_3565_);
lean_dec_ref(v_ty_3577_);
v___x_3580_ = l_Lean_mkForall(v_n_3576_, v_bi_3578_, v_ty_3579_, v_x_3570_);
v___x_3581_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3565_, v_lctx_3566_, v_usedLetOnly_3567_, v_generalizeNondepLet_3568_, v_n_3574_, v___x_3580_);
return v___x_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3606_, lean_object* v_lctx_3607_, lean_object* v_usedLetOnly_3608_, lean_object* v_generalizeNondepLet_3609_, lean_object* v_x_3610_, lean_object* v_x_3611_){
_start:
{
uint8_t v_usedLetOnly_boxed_3612_; uint8_t v_generalizeNondepLet_boxed_3613_; lean_object* v_res_3614_; 
v_usedLetOnly_boxed_3612_ = lean_unbox(v_usedLetOnly_3608_);
v_generalizeNondepLet_boxed_3613_ = lean_unbox(v_generalizeNondepLet_3609_);
v_res_3614_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3606_, v_lctx_3607_, v_usedLetOnly_boxed_3612_, v_generalizeNondepLet_boxed_3613_, v_x_3610_, v_x_3611_);
lean_dec(v_x_3610_);
lean_dec_ref(v_xs_3606_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3615_, lean_object* v_xs_3616_, lean_object* v_b_3617_, uint8_t v_usedLetOnly_3618_, uint8_t v_generalizeNondepLet_3619_){
_start:
{
lean_object* v_b_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_b_3620_ = lean_expr_abstract(v_b_3617_, v_xs_3616_);
v___x_3621_ = lean_array_get_size(v_xs_3616_);
v___x_3622_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3616_, v_lctx_3615_, v_usedLetOnly_3618_, v_generalizeNondepLet_3619_, v___x_3621_, v_b_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3623_, lean_object* v_xs_3624_, lean_object* v_b_3625_, lean_object* v_usedLetOnly_3626_, lean_object* v_generalizeNondepLet_3627_){
_start:
{
uint8_t v_usedLetOnly_boxed_3628_; uint8_t v_generalizeNondepLet_boxed_3629_; lean_object* v_res_3630_; 
v_usedLetOnly_boxed_3628_ = lean_unbox(v_usedLetOnly_3626_);
v_generalizeNondepLet_boxed_3629_ = lean_unbox(v_generalizeNondepLet_3627_);
v_res_3630_ = l_Lean_LocalContext_mkForall(v_lctx_3623_, v_xs_3624_, v_b_3625_, v_usedLetOnly_boxed_3628_, v_generalizeNondepLet_boxed_3629_);
lean_dec_ref(v_b_3625_);
lean_dec_ref(v_xs_3624_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3631_, lean_object* v_p_3632_, lean_object* v_d_3633_){
_start:
{
if (lean_obj_tag(v_d_3633_) == 0)
{
uint8_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec(v_p_3632_);
v___x_3634_ = 0;
v___x_3635_ = lean_box(v___x_3634_);
v___x_3636_ = lean_apply_2(v_toPure_3631_, lean_box(0), v___x_3635_);
return v___x_3636_;
}
else
{
lean_object* v_val_3637_; lean_object* v___x_3638_; 
lean_dec(v_toPure_3631_);
v_val_3637_ = lean_ctor_get(v_d_3633_, 0);
lean_inc(v_val_3637_);
lean_dec_ref_known(v_d_3633_, 1);
v___x_3638_ = lean_apply_1(v_p_3632_, v_val_3637_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3639_, lean_object* v_lctx_3640_, lean_object* v_p_3641_){
_start:
{
lean_object* v_toApplicative_3642_; lean_object* v_decls_3643_; lean_object* v_toPure_3644_; lean_object* v___f_3645_; lean_object* v___x_3646_; 
v_toApplicative_3642_ = lean_ctor_get(v_inst_3639_, 0);
v_decls_3643_ = lean_ctor_get(v_lctx_3640_, 1);
lean_inc_ref(v_decls_3643_);
lean_dec_ref(v_lctx_3640_);
v_toPure_3644_ = lean_ctor_get(v_toApplicative_3642_, 1);
lean_inc(v_toPure_3644_);
v___f_3645_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3645_, 0, v_toPure_3644_);
lean_closure_set(v___f_3645_, 1, v_p_3641_);
v___x_3646_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3639_, v_decls_3643_, v___f_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3647_, lean_object* v_inst_3648_, lean_object* v_lctx_3649_, lean_object* v_p_3650_){
_start:
{
lean_object* v_toApplicative_3651_; lean_object* v_decls_3652_; lean_object* v_toPure_3653_; lean_object* v___f_3654_; lean_object* v___x_3655_; 
v_toApplicative_3651_ = lean_ctor_get(v_inst_3648_, 0);
v_decls_3652_ = lean_ctor_get(v_lctx_3649_, 1);
lean_inc_ref(v_decls_3652_);
lean_dec_ref(v_lctx_3649_);
v_toPure_3653_ = lean_ctor_get(v_toApplicative_3651_, 1);
lean_inc(v_toPure_3653_);
v___f_3654_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3654_, 0, v_toPure_3653_);
lean_closure_set(v___f_3654_, 1, v_p_3650_);
v___x_3655_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3648_, v_decls_3652_, v___f_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3656_, uint8_t v_b_3657_){
_start:
{
if (v_b_3657_ == 0)
{
uint8_t v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = 1;
v___x_3659_ = lean_box(v___x_3658_);
v___x_3660_ = lean_apply_2(v_toPure_3656_, lean_box(0), v___x_3659_);
return v___x_3660_;
}
else
{
uint8_t v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = 0;
v___x_3662_ = lean_box(v___x_3661_);
v___x_3663_ = lean_apply_2(v_toPure_3656_, lean_box(0), v___x_3662_);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3664_, lean_object* v_b_3665_){
_start:
{
uint8_t v_b_boxed_3666_; lean_object* v_res_3667_; 
v_b_boxed_3666_ = lean_unbox(v_b_3665_);
v_res_3667_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3664_, v_b_boxed_3666_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3668_, lean_object* v_toBind_3669_, lean_object* v___f_3670_, lean_object* v_p_3671_, lean_object* v_v_3672_){
_start:
{
if (lean_obj_tag(v_v_3672_) == 0)
{
uint8_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_dec(v_p_3671_);
v___x_3673_ = 1;
v___x_3674_ = lean_box(v___x_3673_);
v___x_3675_ = lean_apply_2(v_toPure_3668_, lean_box(0), v___x_3674_);
v___x_3676_ = lean_apply_4(v_toBind_3669_, lean_box(0), lean_box(0), v___x_3675_, v___f_3670_);
return v___x_3676_;
}
else
{
lean_object* v_val_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_dec(v_toPure_3668_);
v_val_3677_ = lean_ctor_get(v_v_3672_, 0);
lean_inc(v_val_3677_);
lean_dec_ref_known(v_v_3672_, 1);
v___x_3678_ = lean_apply_1(v_p_3671_, v_val_3677_);
v___x_3679_ = lean_apply_4(v_toBind_3669_, lean_box(0), lean_box(0), v___x_3678_, v___f_3670_);
return v___x_3679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3680_, lean_object* v_lctx_3681_, lean_object* v_p_3682_){
_start:
{
lean_object* v_toApplicative_3683_; lean_object* v_decls_3684_; lean_object* v_toBind_3685_; lean_object* v_toPure_3686_; lean_object* v___f_3687_; lean_object* v___f_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v_toApplicative_3683_ = lean_ctor_get(v_inst_3680_, 0);
v_decls_3684_ = lean_ctor_get(v_lctx_3681_, 1);
lean_inc_ref(v_decls_3684_);
lean_dec_ref(v_lctx_3681_);
v_toBind_3685_ = lean_ctor_get(v_inst_3680_, 1);
lean_inc_n(v_toBind_3685_, 2);
v_toPure_3686_ = lean_ctor_get(v_toApplicative_3683_, 1);
lean_inc_n(v_toPure_3686_, 2);
v___f_3687_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3687_, 0, v_toPure_3686_);
lean_inc_ref(v___f_3687_);
v___f_3688_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3688_, 0, v_toPure_3686_);
lean_closure_set(v___f_3688_, 1, v_toBind_3685_);
lean_closure_set(v___f_3688_, 2, v___f_3687_);
lean_closure_set(v___f_3688_, 3, v_p_3682_);
v___x_3689_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3680_, v_decls_3684_, v___f_3688_);
v___x_3690_ = lean_apply_4(v_toBind_3685_, lean_box(0), lean_box(0), v___x_3689_, v___f_3687_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3691_, lean_object* v_inst_3692_, lean_object* v_lctx_3693_, lean_object* v_p_3694_){
_start:
{
lean_object* v_toApplicative_3695_; lean_object* v_decls_3696_; lean_object* v_toBind_3697_; lean_object* v_toPure_3698_; lean_object* v___f_3699_; lean_object* v___f_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v_toApplicative_3695_ = lean_ctor_get(v_inst_3692_, 0);
v_decls_3696_ = lean_ctor_get(v_lctx_3693_, 1);
lean_inc_ref(v_decls_3696_);
lean_dec_ref(v_lctx_3693_);
v_toBind_3697_ = lean_ctor_get(v_inst_3692_, 1);
lean_inc_n(v_toBind_3697_, 2);
v_toPure_3698_ = lean_ctor_get(v_toApplicative_3695_, 1);
lean_inc_n(v_toPure_3698_, 2);
v___f_3699_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3699_, 0, v_toPure_3698_);
lean_inc_ref(v___f_3699_);
v___f_3700_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3700_, 0, v_toPure_3698_);
lean_closure_set(v___f_3700_, 1, v_toBind_3697_);
lean_closure_set(v___f_3700_, 2, v___f_3699_);
lean_closure_set(v___f_3700_, 3, v_p_3694_);
v___x_3701_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3692_, v_decls_3696_, v___f_3700_);
v___x_3702_ = lean_apply_4(v_toBind_3697_, lean_box(0), lean_box(0), v___x_3701_, v___f_3699_);
return v___x_3702_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3703_, lean_object* v_d_3704_){
_start:
{
if (lean_obj_tag(v_d_3704_) == 0)
{
uint8_t v___x_3705_; 
lean_dec_ref(v_p_3703_);
v___x_3705_ = 0;
return v___x_3705_;
}
else
{
lean_object* v_val_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v_val_3706_ = lean_ctor_get(v_d_3704_, 0);
lean_inc(v_val_3706_);
lean_dec_ref_known(v_d_3704_, 1);
v___x_3707_ = lean_apply_1(v_p_3703_, v_val_3706_);
v___x_3708_ = lean_unbox(v___x_3707_);
return v___x_3708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3709_, lean_object* v_d_3710_){
_start:
{
uint8_t v_res_3711_; lean_object* v_r_3712_; 
v_res_3711_ = l_Lean_LocalContext_any___lam__0(v_p_3709_, v_d_3710_);
v_r_3712_ = lean_box(v_res_3711_);
return v_r_3712_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3713_, lean_object* v_p_3714_){
_start:
{
lean_object* v___x_3715_; lean_object* v_decls_3716_; lean_object* v___f_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3715_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3716_ = lean_ctor_get(v_lctx_3713_, 1);
lean_inc_ref(v_decls_3716_);
lean_dec_ref(v_lctx_3713_);
v___f_3717_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3717_, 0, v_p_3714_);
v___x_3718_ = l_Lean_PersistentArray_anyM___redArg(v___x_3715_, v_decls_3716_, v___f_3717_);
v___x_3719_ = lean_unbox(v___x_3718_);
lean_dec(v___x_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3720_, lean_object* v_p_3721_){
_start:
{
uint8_t v_res_3722_; lean_object* v_r_3723_; 
v_res_3722_ = l_Lean_LocalContext_any(v_lctx_3720_, v_p_3721_);
v_r_3723_ = lean_box(v_res_3722_);
return v_r_3723_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3724_, lean_object* v_v_3725_){
_start:
{
if (lean_obj_tag(v_v_3725_) == 0)
{
uint8_t v___x_3726_; 
lean_dec_ref(v_p_3724_);
v___x_3726_ = 0;
return v___x_3726_;
}
else
{
lean_object* v_val_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v_val_3727_ = lean_ctor_get(v_v_3725_, 0);
lean_inc(v_val_3727_);
lean_dec_ref_known(v_v_3725_, 1);
v___x_3728_ = lean_apply_1(v_p_3724_, v_val_3727_);
v___x_3729_ = lean_unbox(v___x_3728_);
if (v___x_3729_ == 0)
{
uint8_t v___x_3730_; 
v___x_3730_ = 1;
return v___x_3730_;
}
else
{
uint8_t v___x_3731_; 
v___x_3731_ = 0;
return v___x_3731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3732_, lean_object* v_v_3733_){
_start:
{
uint8_t v_res_3734_; lean_object* v_r_3735_; 
v_res_3734_ = l_Lean_LocalContext_all___lam__0(v_p_3732_, v_v_3733_);
v_r_3735_ = lean_box(v_res_3734_);
return v_r_3735_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3736_, lean_object* v_p_3737_){
_start:
{
lean_object* v___x_3738_; lean_object* v_decls_3739_; lean_object* v___f_3740_; lean_object* v___x_3741_; uint8_t v___x_3742_; 
v___x_3738_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3739_ = lean_ctor_get(v_lctx_3736_, 1);
lean_inc_ref(v_decls_3739_);
lean_dec_ref(v_lctx_3736_);
v___f_3740_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3740_, 0, v_p_3737_);
v___x_3741_ = l_Lean_PersistentArray_anyM___redArg(v___x_3738_, v_decls_3739_, v___f_3740_);
v___x_3742_ = lean_unbox(v___x_3741_);
lean_dec(v___x_3741_);
if (v___x_3742_ == 0)
{
uint8_t v___x_3743_; 
v___x_3743_ = 1;
return v___x_3743_;
}
else
{
uint8_t v___x_3744_; 
v___x_3744_ = 0;
return v___x_3744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3745_, lean_object* v_p_3746_){
_start:
{
uint8_t v_res_3747_; lean_object* v_r_3748_; 
v_res_3747_ = l_Lean_LocalContext_all(v_lctx_3745_, v_p_3746_);
v_r_3748_ = lean_box(v_res_3747_);
return v_r_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3749_, lean_object* v_a_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_zero_3753_; uint8_t v_isZero_3754_; 
v_zero_3753_ = lean_unsigned_to_nat(0u);
v_isZero_3754_ = lean_nat_dec_eq(v_i_3749_, v_zero_3753_);
if (v_isZero_3754_ == 1)
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
lean_dec(v_i_3749_);
v___x_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3755_, 0, v_a_3750_);
lean_ctor_set(v___x_3755_, 1, v___y_3751_);
v___x_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
lean_ctor_set(v___x_3756_, 1, v___y_3752_);
return v___x_3756_;
}
else
{
lean_object* v_decls_3757_; lean_object* v_size_3758_; lean_object* v_one_3759_; lean_object* v_n_3760_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3777_; lean_object* v___y_3778_; uint8_t v___y_3779_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3789_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v_decls_3757_ = lean_ctor_get(v_a_3750_, 1);
v_size_3758_ = lean_ctor_get(v_decls_3757_, 2);
v_one_3759_ = lean_unsigned_to_nat(1u);
v_n_3760_ = lean_nat_sub(v_i_3749_, v_one_3759_);
lean_dec(v_i_3749_);
v___x_3793_ = lean_box(0);
v___x_3794_ = lean_nat_dec_lt(v_n_3760_, v_size_3758_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; 
v___x_3795_ = l_outOfBounds___redArg(v___x_3793_);
v___y_3789_ = v___x_3795_;
goto v___jp_3788_;
}
else
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3793_, v_decls_3757_, v_n_3760_);
v___y_3789_ = v___x_3796_;
goto v___jp_3788_;
}
v___jp_3761_:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_LocalContext_setUserName(v_a_3750_, v___y_3765_, v___y_3764_);
v_i_3749_ = v_n_3760_;
v_a_3750_ = v___x_3766_;
v___y_3751_ = v___y_3762_;
v___y_3752_ = v___y_3763_;
goto _start;
}
v___jp_3768_:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v_fst_3773_; lean_object* v_snd_3774_; lean_object* v_fvarId_3775_; 
lean_inc(v___y_3770_);
v___x_3771_ = l_Lean_NameSet_insert(v___y_3751_, v___y_3770_);
v___x_3772_ = l_Lean_sanitizeName(v___y_3770_, v___y_3752_);
v_fst_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_fst_3773_);
v_snd_3774_ = lean_ctor_get(v___x_3772_, 1);
lean_inc(v_snd_3774_);
lean_dec_ref(v___x_3772_);
v_fvarId_3775_ = lean_ctor_get(v___y_3769_, 1);
lean_inc(v_fvarId_3775_);
lean_dec_ref(v___y_3769_);
v___y_3762_ = v___x_3771_;
v___y_3763_ = v_snd_3774_;
v___y_3764_ = v_fst_3773_;
v___y_3765_ = v_fvarId_3775_;
goto v___jp_3761_;
}
v___jp_3776_:
{
if (v___y_3779_ == 0)
{
lean_object* v___x_3780_; 
lean_dec_ref(v___y_3777_);
v___x_3780_ = l_Lean_NameSet_insert(v___y_3751_, v___y_3778_);
v_i_3749_ = v_n_3760_;
v___y_3751_ = v___x_3780_;
goto _start;
}
else
{
v___y_3769_ = v___y_3777_;
v___y_3770_ = v___y_3778_;
goto v___jp_3768_;
}
}
v___jp_3782_:
{
uint8_t v___x_3785_; 
v___x_3785_ = l_Lean_Name_hasMacroScopes(v___y_3784_);
if (v___x_3785_ == 0)
{
lean_object* v_userName_3786_; uint8_t v___x_3787_; 
v_userName_3786_ = lean_ctor_get(v___y_3783_, 2);
v___x_3787_ = l_Lean_NameSet_contains(v___y_3751_, v_userName_3786_);
v___y_3777_ = v___y_3783_;
v___y_3778_ = v___y_3784_;
v___y_3779_ = v___x_3787_;
goto v___jp_3776_;
}
else
{
v___y_3769_ = v___y_3783_;
v___y_3770_ = v___y_3784_;
goto v___jp_3768_;
}
}
v___jp_3788_:
{
if (lean_obj_tag(v___y_3789_) == 0)
{
v_i_3749_ = v_n_3760_;
goto _start;
}
else
{
lean_object* v_val_3791_; lean_object* v_userName_3792_; 
v_val_3791_ = lean_ctor_get(v___y_3789_, 0);
lean_inc(v_val_3791_);
lean_dec_ref_known(v___y_3789_, 1);
v_userName_3792_ = lean_ctor_get(v_val_3791_, 2);
lean_inc(v_userName_3792_);
v___y_3783_ = v_val_3791_;
v___y_3784_ = v_userName_3792_;
goto v___jp_3782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3797_, lean_object* v_a_3798_){
_start:
{
lean_object* v_options_3799_; uint8_t v___x_3800_; 
v_options_3799_ = lean_ctor_get(v_a_3798_, 0);
v___x_3800_ = l_Lean_getSanitizeNames(v_options_3799_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v_lctx_3797_);
lean_ctor_set(v___x_3801_, 1, v_a_3798_);
return v___x_3801_;
}
else
{
lean_object* v_decls_3802_; lean_object* v_size_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v_fst_3806_; lean_object* v_snd_3807_; lean_object* v_fst_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_decls_3802_ = lean_ctor_get(v_lctx_3797_, 1);
v_size_3803_ = lean_ctor_get(v_decls_3802_, 2);
lean_inc(v_size_3803_);
v___x_3804_ = l_Lean_NameSet_empty;
v___x_3805_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3803_, v_lctx_3797_, v___x_3804_, v_a_3798_);
v_fst_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_fst_3806_);
v_snd_3807_ = lean_ctor_get(v___x_3805_, 1);
lean_inc(v_snd_3807_);
lean_dec_ref(v___x_3805_);
v_fst_3808_ = lean_ctor_get(v_fst_3806_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_fst_3806_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; 
v_unused_3816_ = lean_ctor_get(v_fst_3806_, 1);
lean_dec(v_unused_3816_);
v___x_3810_ = v_fst_3806_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_fst_3808_);
lean_dec(v_fst_3806_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 1, v_snd_3807_);
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_fst_3808_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_snd_3807_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3817_, lean_object* v_i_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3818_, v_a_3820_, v___y_3821_, v___y_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3824_, lean_object* v_i_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3824_, v_i_3825_, v_a_3826_, v_a_3827_, v___y_3828_, v___y_3829_);
lean_dec(v_n_3824_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3831_, lean_object* v_fvarId_3832_){
_start:
{
lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___x_3845_; 
lean_inc_ref(v_lctx_3831_);
v___x_3845_ = lean_local_ctx_find(v_lctx_3831_, v_fvarId_3832_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v___x_3846_; 
lean_dec_ref(v_lctx_3831_);
v___x_3846_ = lean_box(0);
return v___x_3846_;
}
else
{
lean_object* v_val_3847_; lean_object* v___y_3849_; lean_object* v_userName_3854_; 
v_val_3847_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_val_3847_);
lean_dec_ref_known(v___x_3845_, 1);
v_userName_3854_ = lean_ctor_get(v_val_3847_, 2);
lean_inc(v_userName_3854_);
v___y_3849_ = v_userName_3854_;
goto v___jp_3848_;
v___jp_3848_:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3831_, v___y_3849_);
lean_dec_ref(v_lctx_3831_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v___x_3851_; 
lean_dec(v___y_3849_);
lean_dec(v_val_3847_);
v___x_3851_ = lean_box(0);
return v___x_3851_;
}
else
{
lean_object* v_val_3852_; lean_object* v_fvarId_3853_; 
v_val_3852_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_val_3852_);
lean_dec_ref_known(v___x_3850_, 1);
v_fvarId_3853_ = lean_ctor_get(v_val_3847_, 1);
lean_inc(v_fvarId_3853_);
lean_dec(v_val_3847_);
v___y_3841_ = v___y_3849_;
v___y_3842_ = v_val_3852_;
v___y_3843_ = v_fvarId_3853_;
goto v___jp_3840_;
}
}
}
v___jp_3833_:
{
uint8_t v___x_3837_; 
v___x_3837_ = l_Lean_instBEqFVarId_beq(v___y_3834_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec(v___y_3834_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; 
lean_dec(v___y_3835_);
v___x_3838_ = lean_box(0);
return v___x_3838_;
}
else
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3839_, 0, v___y_3835_);
return v___x_3839_;
}
}
v___jp_3840_:
{
lean_object* v_fvarId_3844_; 
v_fvarId_3844_ = lean_ctor_get(v___y_3842_, 1);
lean_inc(v_fvarId_3844_);
lean_dec_ref(v___y_3842_);
v___y_3834_ = v___y_3843_;
v___y_3835_ = v___y_3841_;
v___y_3836_ = v_fvarId_3844_;
goto v___jp_3833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3855_, size_t v_i_3856_, lean_object* v_bs_3857_){
_start:
{
uint8_t v___x_3858_; 
v___x_3858_ = lean_usize_dec_lt(v_i_3856_, v_sz_3855_);
if (v___x_3858_ == 0)
{
return v_bs_3857_;
}
else
{
lean_object* v_v_3859_; lean_object* v_snd_3860_; lean_object* v___x_3861_; lean_object* v_bs_x27_3862_; size_t v___x_3863_; size_t v___x_3864_; lean_object* v___x_3865_; 
v_v_3859_ = lean_array_uget_borrowed(v_bs_3857_, v_i_3856_);
v_snd_3860_ = lean_ctor_get(v_v_3859_, 1);
lean_inc(v_snd_3860_);
v___x_3861_ = lean_unsigned_to_nat(0u);
v_bs_x27_3862_ = lean_array_uset(v_bs_3857_, v_i_3856_, v___x_3861_);
v___x_3863_ = ((size_t)1ULL);
v___x_3864_ = lean_usize_add(v_i_3856_, v___x_3863_);
v___x_3865_ = lean_array_uset(v_bs_x27_3862_, v_i_3856_, v_snd_3860_);
v_i_3856_ = v___x_3864_;
v_bs_3857_ = v___x_3865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3867_, lean_object* v_i_3868_, lean_object* v_bs_3869_){
_start:
{
size_t v_sz_boxed_3870_; size_t v_i_boxed_3871_; lean_object* v_res_3872_; 
v_sz_boxed_3870_ = lean_unbox_usize(v_sz_3867_);
lean_dec(v_sz_3867_);
v_i_boxed_3871_ = lean_unbox_usize(v_i_3868_);
lean_dec(v_i_3868_);
v_res_3872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3870_, v_i_boxed_3871_, v_bs_3869_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3873_, size_t v_sz_3874_, size_t v_i_3875_, lean_object* v_bs_3876_){
_start:
{
uint8_t v___x_3877_; 
v___x_3877_ = lean_usize_dec_lt(v_i_3875_, v_sz_3874_);
if (v___x_3877_ == 0)
{
return v_bs_3876_;
}
else
{
lean_object* v_fvarIdToDecl_3878_; lean_object* v_v_3879_; lean_object* v___x_3880_; lean_object* v_bs_x27_3881_; lean_object* v___y_3883_; lean_object* v___x_3888_; 
v_fvarIdToDecl_3878_ = lean_ctor_get(v_lctx_3873_, 0);
v_v_3879_ = lean_array_uget(v_bs_3876_, v_i_3875_);
v___x_3880_ = lean_unsigned_to_nat(0u);
v_bs_x27_3881_ = lean_array_uset(v_bs_3876_, v_i_3875_, v___x_3880_);
v___x_3888_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3878_, v_v_3879_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3880_);
lean_ctor_set(v___x_3889_, 1, v_v_3879_);
v___y_3883_ = v___x_3889_;
goto v___jp_3882_;
}
else
{
lean_object* v_val_3890_; lean_object* v_index_3891_; lean_object* v___x_3892_; 
v_val_3890_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_val_3890_);
lean_dec_ref_known(v___x_3888_, 1);
v_index_3891_ = lean_ctor_get(v_val_3890_, 0);
lean_inc(v_index_3891_);
lean_dec(v_val_3890_);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v_index_3891_);
lean_ctor_set(v___x_3892_, 1, v_v_3879_);
v___y_3883_ = v___x_3892_;
goto v___jp_3882_;
}
v___jp_3882_:
{
size_t v___x_3884_; size_t v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = ((size_t)1ULL);
v___x_3885_ = lean_usize_add(v_i_3875_, v___x_3884_);
v___x_3886_ = lean_array_uset(v_bs_x27_3881_, v_i_3875_, v___y_3883_);
v_i_3875_ = v___x_3885_;
v_bs_3876_ = v___x_3886_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3893_, lean_object* v_sz_3894_, lean_object* v_i_3895_, lean_object* v_bs_3896_){
_start:
{
size_t v_sz_boxed_3897_; size_t v_i_boxed_3898_; lean_object* v_res_3899_; 
v_sz_boxed_3897_ = lean_unbox_usize(v_sz_3894_);
lean_dec(v_sz_3894_);
v_i_boxed_3898_ = lean_unbox_usize(v_i_3895_);
lean_dec(v_i_3895_);
v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3893_, v_sz_boxed_3897_, v_i_boxed_3898_, v_bs_3896_);
lean_dec_ref(v_lctx_3893_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3900_, lean_object* v_pivot_3901_, lean_object* v_as_3902_, lean_object* v_i_3903_, lean_object* v_k_3904_){
_start:
{
uint8_t v___x_3905_; 
v___x_3905_ = lean_nat_dec_lt(v_k_3904_, v_hi_3900_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
lean_dec(v_k_3904_);
v___x_3906_ = lean_array_fswap(v_as_3902_, v_i_3903_, v_hi_3900_);
v___x_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3907_, 0, v_i_3903_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
return v___x_3907_;
}
else
{
lean_object* v___x_3908_; lean_object* v_fst_3909_; lean_object* v_fst_3910_; uint8_t v___x_3911_; 
v___x_3908_ = lean_array_fget_borrowed(v_as_3902_, v_k_3904_);
v_fst_3909_ = lean_ctor_get(v___x_3908_, 0);
v_fst_3910_ = lean_ctor_get(v_pivot_3901_, 0);
v___x_3911_ = lean_nat_dec_lt(v_fst_3909_, v_fst_3910_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = lean_unsigned_to_nat(1u);
v___x_3913_ = lean_nat_add(v_k_3904_, v___x_3912_);
lean_dec(v_k_3904_);
v_k_3904_ = v___x_3913_;
goto _start;
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3915_ = lean_array_fswap(v_as_3902_, v_i_3903_, v_k_3904_);
v___x_3916_ = lean_unsigned_to_nat(1u);
v___x_3917_ = lean_nat_add(v_i_3903_, v___x_3916_);
lean_dec(v_i_3903_);
v___x_3918_ = lean_nat_add(v_k_3904_, v___x_3916_);
lean_dec(v_k_3904_);
v_as_3902_ = v___x_3915_;
v_i_3903_ = v___x_3917_;
v_k_3904_ = v___x_3918_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3920_, lean_object* v_pivot_3921_, lean_object* v_as_3922_, lean_object* v_i_3923_, lean_object* v_k_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3920_, v_pivot_3921_, v_as_3922_, v_i_3923_, v_k_3924_);
lean_dec_ref(v_pivot_3921_);
lean_dec(v_hi_3920_);
return v_res_3925_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3926_, lean_object* v_i_3927_){
_start:
{
lean_object* v_fst_3928_; lean_object* v_fst_3929_; uint8_t v___x_3930_; 
v_fst_3928_ = lean_ctor_get(v_h_3926_, 0);
v_fst_3929_ = lean_ctor_get(v_i_3927_, 0);
v___x_3930_ = lean_nat_dec_lt(v_fst_3928_, v_fst_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3931_, lean_object* v_i_3932_){
_start:
{
uint8_t v_res_3933_; lean_object* v_r_3934_; 
v_res_3933_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3931_, v_i_3932_);
lean_dec_ref(v_i_3932_);
lean_dec_ref(v_h_3931_);
v_r_3934_ = lean_box(v_res_3933_);
return v_r_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3935_, lean_object* v_as_3936_, lean_object* v_lo_3937_, lean_object* v_hi_3938_){
_start:
{
lean_object* v___y_3940_; uint8_t v___x_3950_; 
v___x_3950_ = lean_nat_dec_lt(v_lo_3937_, v_hi_3938_);
if (v___x_3950_ == 0)
{
lean_dec(v_lo_3937_);
return v_as_3936_;
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v_mid_3953_; lean_object* v___y_3955_; lean_object* v___y_3961_; lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3951_ = lean_nat_add(v_lo_3937_, v_hi_3938_);
v___x_3952_ = lean_unsigned_to_nat(1u);
v_mid_3953_ = lean_nat_shiftr(v___x_3951_, v___x_3952_);
lean_dec(v___x_3951_);
v___x_3966_ = lean_array_fget_borrowed(v_as_3936_, v_mid_3953_);
v___x_3967_ = lean_array_fget_borrowed(v_as_3936_, v_lo_3937_);
v___x_3968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3966_, v___x_3967_);
if (v___x_3968_ == 0)
{
v___y_3961_ = v_as_3936_;
goto v___jp_3960_;
}
else
{
lean_object* v___x_3969_; 
v___x_3969_ = lean_array_fswap(v_as_3936_, v_lo_3937_, v_mid_3953_);
v___y_3961_ = v___x_3969_;
goto v___jp_3960_;
}
v___jp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v___x_3956_ = lean_array_fget_borrowed(v___y_3955_, v_mid_3953_);
v___x_3957_ = lean_array_fget_borrowed(v___y_3955_, v_hi_3938_);
v___x_3958_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_dec(v_mid_3953_);
v___y_3940_ = v___y_3955_;
goto v___jp_3939_;
}
else
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_array_fswap(v___y_3955_, v_mid_3953_, v_hi_3938_);
lean_dec(v_mid_3953_);
v___y_3940_ = v___x_3959_;
goto v___jp_3939_;
}
}
v___jp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v___x_3962_ = lean_array_fget_borrowed(v___y_3961_, v_hi_3938_);
v___x_3963_ = lean_array_fget_borrowed(v___y_3961_, v_lo_3937_);
v___x_3964_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3962_, v___x_3963_);
if (v___x_3964_ == 0)
{
v___y_3955_ = v___y_3961_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_array_fswap(v___y_3961_, v_lo_3937_, v_hi_3938_);
v___y_3955_ = v___x_3965_;
goto v___jp_3954_;
}
}
}
v___jp_3939_:
{
lean_object* v_pivot_3941_; lean_object* v___x_3942_; lean_object* v_fst_3943_; lean_object* v_snd_3944_; uint8_t v___x_3945_; 
v_pivot_3941_ = lean_array_fget(v___y_3940_, v_hi_3938_);
lean_inc_n(v_lo_3937_, 2);
v___x_3942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3938_, v_pivot_3941_, v___y_3940_, v_lo_3937_, v_lo_3937_);
lean_dec(v_pivot_3941_);
v_fst_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_fst_3943_);
v_snd_3944_ = lean_ctor_get(v___x_3942_, 1);
lean_inc(v_snd_3944_);
lean_dec_ref(v___x_3942_);
v___x_3945_ = lean_nat_dec_le(v_hi_3938_, v_fst_3943_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3946_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3935_, v_snd_3944_, v_lo_3937_, v_fst_3943_);
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = lean_nat_add(v_fst_3943_, v___x_3947_);
lean_dec(v_fst_3943_);
v_as_3936_ = v___x_3946_;
v_lo_3937_ = v___x_3948_;
goto _start;
}
else
{
lean_dec(v_fst_3943_);
lean_dec(v_lo_3937_);
return v_snd_3944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3970_, lean_object* v_as_3971_, lean_object* v_lo_3972_, lean_object* v_hi_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3970_, v_as_3971_, v_lo_3972_, v_hi_3973_);
lean_dec(v_hi_3973_);
lean_dec(v_n_3970_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3975_, lean_object* v_hyps_3976_){
_start:
{
lean_object* v___y_3978_; size_t v_sz_3982_; size_t v___x_3983_; lean_object* v_hyps_3984_; lean_object* v___x_3985_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___x_3990_; uint8_t v___x_3991_; 
v_sz_3982_ = lean_array_size(v_hyps_3976_);
v___x_3983_ = ((size_t)0ULL);
v_hyps_3984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3975_, v_sz_3982_, v___x_3983_, v_hyps_3976_);
v___x_3985_ = lean_array_get_size(v_hyps_3984_);
v___x_3990_ = lean_unsigned_to_nat(0u);
v___x_3991_ = lean_nat_dec_eq(v___x_3985_, v___x_3990_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___y_3995_; uint8_t v___x_3997_; 
v___x_3992_ = lean_unsigned_to_nat(1u);
v___x_3993_ = lean_nat_sub(v___x_3985_, v___x_3992_);
v___x_3997_ = lean_nat_dec_le(v___x_3990_, v___x_3993_);
if (v___x_3997_ == 0)
{
lean_inc(v___x_3993_);
v___y_3995_ = v___x_3993_;
goto v___jp_3994_;
}
else
{
v___y_3995_ = v___x_3990_;
goto v___jp_3994_;
}
v___jp_3994_:
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_nat_dec_le(v___y_3995_, v___x_3993_);
if (v___x_3996_ == 0)
{
lean_dec(v___x_3993_);
lean_inc(v___y_3995_);
v___y_3987_ = v___y_3995_;
v___y_3988_ = v___y_3995_;
goto v___jp_3986_;
}
else
{
v___y_3987_ = v___y_3995_;
v___y_3988_ = v___x_3993_;
goto v___jp_3986_;
}
}
}
else
{
v___y_3978_ = v_hyps_3984_;
goto v___jp_3977_;
}
v___jp_3977_:
{
size_t v_sz_3979_; size_t v___x_3980_; lean_object* v___x_3981_; 
v_sz_3979_ = lean_array_size(v___y_3978_);
v___x_3980_ = ((size_t)0ULL);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3979_, v___x_3980_, v___y_3978_);
return v___x_3981_;
}
v___jp_3986_:
{
lean_object* v___x_3989_; 
v___x_3989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3985_, v_hyps_3984_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
v___y_3978_ = v___x_3989_;
goto v___jp_3977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_3998_, lean_object* v_hyps_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_3998_, v_hyps_3999_);
lean_dec_ref(v_lctx_3998_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_4001_, lean_object* v_as_4002_, lean_object* v_lo_4003_, lean_object* v_hi_4004_, lean_object* v_w_4005_, lean_object* v_hlo_4006_, lean_object* v_hhi_4007_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_4001_, v_as_4002_, v_lo_4003_, v_hi_4004_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_4009_, lean_object* v_as_4010_, lean_object* v_lo_4011_, lean_object* v_hi_4012_, lean_object* v_w_4013_, lean_object* v_hlo_4014_, lean_object* v_hhi_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_4009_, v_as_4010_, v_lo_4011_, v_hi_4012_, v_w_4013_, v_hlo_4014_, v_hhi_4015_);
lean_dec(v_hi_4012_);
lean_dec(v_n_4009_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_4017_, lean_object* v_lo_4018_, lean_object* v_hi_4019_, lean_object* v_hhi_4020_, lean_object* v_pivot_4021_, lean_object* v_as_4022_, lean_object* v_i_4023_, lean_object* v_k_4024_, lean_object* v_ilo_4025_, lean_object* v_ik_4026_, lean_object* v_w_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_4019_, v_pivot_4021_, v_as_4022_, v_i_4023_, v_k_4024_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_4029_, lean_object* v_lo_4030_, lean_object* v_hi_4031_, lean_object* v_hhi_4032_, lean_object* v_pivot_4033_, lean_object* v_as_4034_, lean_object* v_i_4035_, lean_object* v_k_4036_, lean_object* v_ilo_4037_, lean_object* v_ik_4038_, lean_object* v_w_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_4029_, v_lo_4030_, v_hi_4031_, v_hhi_4032_, v_pivot_4033_, v_as_4034_, v_i_4035_, v_k_4036_, v_ilo_4037_, v_ik_4038_, v_w_4039_);
lean_dec_ref(v_pivot_4033_);
lean_dec(v_hi_4031_);
lean_dec(v_lo_4030_);
lean_dec(v_n_4029_);
return v_res_4040_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_4041_, lean_object* v_x_4042_){
_start:
{
if (lean_obj_tag(v_x_4042_) == 0)
{
uint8_t v___x_4043_; 
v___x_4043_ = 0;
return v___x_4043_;
}
else
{
lean_object* v_key_4044_; lean_object* v_tail_4045_; uint8_t v___x_4046_; 
v_key_4044_ = lean_ctor_get(v_x_4042_, 0);
v_tail_4045_ = lean_ctor_get(v_x_4042_, 2);
v___x_4046_ = lean_name_eq(v_key_4044_, v_a_4041_);
if (v___x_4046_ == 0)
{
v_x_4042_ = v_tail_4045_;
goto _start;
}
else
{
return v___x_4046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_4048_, lean_object* v_x_4049_){
_start:
{
uint8_t v_res_4050_; lean_object* v_r_4051_; 
v_res_4050_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4048_, v_x_4049_);
lean_dec(v_x_4049_);
lean_dec(v_a_4048_);
v_r_4051_ = lean_box(v_res_4050_);
return v_r_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_4052_, lean_object* v_x_4053_){
_start:
{
if (lean_obj_tag(v_x_4053_) == 0)
{
return v_x_4053_;
}
else
{
lean_object* v_key_4054_; lean_object* v_value_4055_; lean_object* v_tail_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4065_; 
v_key_4054_ = lean_ctor_get(v_x_4053_, 0);
v_value_4055_ = lean_ctor_get(v_x_4053_, 1);
v_tail_4056_ = lean_ctor_get(v_x_4053_, 2);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_x_4053_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4058_ = v_x_4053_;
v_isShared_4059_ = v_isSharedCheck_4065_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_tail_4056_);
lean_inc(v_value_4055_);
lean_inc(v_key_4054_);
lean_dec(v_x_4053_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4065_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
uint8_t v___x_4060_; 
v___x_4060_ = lean_name_eq(v_key_4054_, v_a_4052_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4061_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4052_, v_tail_4056_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 2, v___x_4061_);
v___x_4063_ = v___x_4058_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_key_4054_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_value_4055_);
lean_ctor_set(v_reuseFailAlloc_4064_, 2, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
else
{
lean_del_object(v___x_4058_);
lean_dec(v_value_4055_);
lean_dec(v_key_4054_);
return v_tail_4056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_4066_, lean_object* v_x_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4066_, v_x_4067_);
lean_dec(v_a_4066_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_size_4071_; lean_object* v_buckets_4072_; lean_object* v___x_4073_; uint64_t v___y_4075_; 
v_size_4071_ = lean_ctor_get(v_m_4069_, 0);
v_buckets_4072_ = lean_ctor_get(v_m_4069_, 1);
v___x_4073_ = lean_array_get_size(v_buckets_4072_);
if (lean_obj_tag(v_a_4070_) == 0)
{
uint64_t v___x_4104_; 
v___x_4104_ = 1723ULL;
v___y_4075_ = v___x_4104_;
goto v___jp_4074_;
}
else
{
uint64_t v_hash_4105_; 
v_hash_4105_ = lean_ctor_get_uint64(v_a_4070_, sizeof(void*)*2);
v___y_4075_ = v_hash_4105_;
goto v___jp_4074_;
}
v___jp_4074_:
{
uint64_t v___x_4076_; uint64_t v___x_4077_; uint64_t v_fold_4078_; uint64_t v___x_4079_; uint64_t v___x_4080_; uint64_t v___x_4081_; size_t v___x_4082_; size_t v___x_4083_; size_t v___x_4084_; size_t v___x_4085_; size_t v___x_4086_; lean_object* v_bkt_4087_; uint8_t v___x_4088_; 
v___x_4076_ = 32ULL;
v___x_4077_ = lean_uint64_shift_right(v___y_4075_, v___x_4076_);
v_fold_4078_ = lean_uint64_xor(v___y_4075_, v___x_4077_);
v___x_4079_ = 16ULL;
v___x_4080_ = lean_uint64_shift_right(v_fold_4078_, v___x_4079_);
v___x_4081_ = lean_uint64_xor(v_fold_4078_, v___x_4080_);
v___x_4082_ = lean_uint64_to_usize(v___x_4081_);
v___x_4083_ = lean_usize_of_nat(v___x_4073_);
v___x_4084_ = ((size_t)1ULL);
v___x_4085_ = lean_usize_sub(v___x_4083_, v___x_4084_);
v___x_4086_ = lean_usize_land(v___x_4082_, v___x_4085_);
v_bkt_4087_ = lean_array_uget_borrowed(v_buckets_4072_, v___x_4086_);
v___x_4088_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4070_, v_bkt_4087_);
if (v___x_4088_ == 0)
{
return v_m_4069_;
}
else
{
lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4101_; 
lean_inc(v_bkt_4087_);
lean_inc_ref(v_buckets_4072_);
lean_inc(v_size_4071_);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_m_4069_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; lean_object* v_unused_4103_; 
v_unused_4102_ = lean_ctor_get(v_m_4069_, 1);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_m_4069_, 0);
lean_dec(v_unused_4103_);
v___x_4090_ = v_m_4069_;
v_isShared_4091_ = v_isSharedCheck_4101_;
goto v_resetjp_4089_;
}
else
{
lean_dec(v_m_4069_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4101_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4092_; lean_object* v_buckets_x27_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4099_; 
v___x_4092_ = lean_box(0);
v_buckets_x27_4093_ = lean_array_uset(v_buckets_4072_, v___x_4086_, v___x_4092_);
v___x_4094_ = lean_unsigned_to_nat(1u);
v___x_4095_ = lean_nat_sub(v_size_4071_, v___x_4094_);
lean_dec(v_size_4071_);
v___x_4096_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4070_, v_bkt_4087_);
v___x_4097_ = lean_array_uset(v_buckets_x27_4093_, v___x_4086_, v___x_4096_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 1, v___x_4097_);
lean_ctor_set(v___x_4090_, 0, v___x_4095_);
v___x_4099_ = v___x_4090_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4095_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v___x_4097_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4106_, v_a_4107_);
lean_dec(v_a_4107_);
return v_res_4108_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4109_, lean_object* v_a_4110_){
_start:
{
lean_object* v_buckets_4111_; lean_object* v___x_4112_; uint64_t v___y_4114_; 
v_buckets_4111_ = lean_ctor_get(v_m_4109_, 1);
v___x_4112_ = lean_array_get_size(v_buckets_4111_);
if (lean_obj_tag(v_a_4110_) == 0)
{
uint64_t v___x_4128_; 
v___x_4128_ = 1723ULL;
v___y_4114_ = v___x_4128_;
goto v___jp_4113_;
}
else
{
uint64_t v_hash_4129_; 
v_hash_4129_ = lean_ctor_get_uint64(v_a_4110_, sizeof(void*)*2);
v___y_4114_ = v_hash_4129_;
goto v___jp_4113_;
}
v___jp_4113_:
{
uint64_t v___x_4115_; uint64_t v___x_4116_; uint64_t v_fold_4117_; uint64_t v___x_4118_; uint64_t v___x_4119_; uint64_t v___x_4120_; size_t v___x_4121_; size_t v___x_4122_; size_t v___x_4123_; size_t v___x_4124_; size_t v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; 
v___x_4115_ = 32ULL;
v___x_4116_ = lean_uint64_shift_right(v___y_4114_, v___x_4115_);
v_fold_4117_ = lean_uint64_xor(v___y_4114_, v___x_4116_);
v___x_4118_ = 16ULL;
v___x_4119_ = lean_uint64_shift_right(v_fold_4117_, v___x_4118_);
v___x_4120_ = lean_uint64_xor(v_fold_4117_, v___x_4119_);
v___x_4121_ = lean_uint64_to_usize(v___x_4120_);
v___x_4122_ = lean_usize_of_nat(v___x_4112_);
v___x_4123_ = ((size_t)1ULL);
v___x_4124_ = lean_usize_sub(v___x_4122_, v___x_4123_);
v___x_4125_ = lean_usize_land(v___x_4121_, v___x_4124_);
v___x_4126_ = lean_array_uget_borrowed(v_buckets_4111_, v___x_4125_);
v___x_4127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4110_, v___x_4126_);
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4130_, lean_object* v_a_4131_){
_start:
{
uint8_t v_res_4132_; lean_object* v_r_4133_; 
v_res_4132_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4130_, v_a_4131_);
lean_dec(v_a_4131_);
lean_dec_ref(v_m_4130_);
v_r_4133_ = lean_box(v_res_4132_);
return v_r_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4134_, lean_object* v_as_4135_, size_t v_i_4136_, size_t v_stop_4137_, lean_object* v_b_4138_){
_start:
{
uint8_t v___x_4139_; 
v___x_4139_ = lean_usize_dec_eq(v_i_4136_, v_stop_4137_);
if (v___x_4139_ == 0)
{
size_t v___x_4140_; size_t v___x_4141_; lean_object* v___x_4142_; 
v___x_4140_ = ((size_t)1ULL);
v___x_4141_ = lean_usize_sub(v_i_4136_, v___x_4140_);
v___x_4142_ = lean_array_uget(v_as_4135_, v___x_4141_);
if (lean_obj_tag(v___x_4142_) == 0)
{
v_i_4136_ = v___x_4141_;
goto _start;
}
else
{
lean_object* v_val_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4178_; 
v_val_4144_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4146_ = v___x_4142_;
v_isShared_4147_ = v_isSharedCheck_4178_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_val_4144_);
lean_dec(v___x_4142_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4178_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v_fst_4148_; lean_object* v_snd_4149_; lean_object* v___y_4151_; lean_object* v___y_4167_; lean_object* v_size_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; 
v_fst_4148_ = lean_ctor_get(v_b_4138_, 0);
v_snd_4149_ = lean_ctor_get(v_b_4138_, 1);
v_size_4173_ = lean_ctor_get(v_fst_4148_, 0);
v___x_4174_ = lean_unsigned_to_nat(0u);
v___x_4175_ = lean_nat_dec_eq(v_size_4173_, v___x_4174_);
if (v___x_4175_ == 0)
{
lean_object* v_index_4176_; 
v_index_4176_ = lean_ctor_get(v_val_4144_, 0);
lean_inc(v_index_4176_);
v___y_4167_ = v_index_4176_;
goto v___jp_4166_;
}
else
{
lean_object* v___x_4177_; 
lean_inc(v_snd_4149_);
lean_del_object(v___x_4146_);
lean_dec(v_val_4144_);
lean_dec_ref(v_b_4138_);
v___x_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4177_, 0, v_snd_4149_);
return v___x_4177_;
}
v___jp_4150_:
{
uint8_t v___x_4152_; 
v___x_4152_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4148_, v___y_4151_);
if (v___x_4152_ == 0)
{
lean_dec(v___y_4151_);
lean_dec(v_val_4144_);
v_i_4136_ = v___x_4141_;
goto _start;
}
else
{
lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4163_; 
lean_inc(v_snd_4149_);
lean_inc(v_fst_4148_);
v_isSharedCheck_4163_ = !lean_is_exclusive(v_b_4138_);
if (v_isSharedCheck_4163_ == 0)
{
lean_object* v_unused_4164_; lean_object* v_unused_4165_; 
v_unused_4164_ = lean_ctor_get(v_b_4138_, 1);
lean_dec(v_unused_4164_);
v_unused_4165_ = lean_ctor_get(v_b_4138_, 0);
lean_dec(v_unused_4165_);
v___x_4155_ = v_b_4138_;
v_isShared_4156_ = v_isSharedCheck_4163_;
goto v_resetjp_4154_;
}
else
{
lean_dec(v_b_4138_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4163_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4160_; 
v___x_4157_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4148_, v___y_4151_);
lean_dec(v___y_4151_);
v___x_4158_ = lean_array_push(v_snd_4149_, v_val_4144_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 1, v___x_4158_);
lean_ctor_set(v___x_4155_, 0, v___x_4157_);
v___x_4160_ = v___x_4155_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4162_, 1, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
v_i_4136_ = v___x_4141_;
v_b_4138_ = v___x_4160_;
goto _start;
}
}
}
}
v___jp_4166_:
{
uint8_t v___x_4168_; 
v___x_4168_ = lean_nat_dec_lt(v___y_4167_, v_start_4134_);
lean_dec(v___y_4167_);
if (v___x_4168_ == 0)
{
lean_object* v_userName_4169_; 
lean_del_object(v___x_4146_);
v_userName_4169_ = lean_ctor_get(v_val_4144_, 2);
lean_inc(v_userName_4169_);
v___y_4151_ = v_userName_4169_;
goto v___jp_4150_;
}
else
{
lean_object* v___x_4171_; 
lean_inc(v_snd_4149_);
lean_dec(v_val_4144_);
lean_dec_ref(v_b_4138_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 0);
lean_ctor_set(v___x_4146_, 0, v_snd_4149_);
v___x_4171_ = v___x_4146_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_snd_4149_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
else
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_b_4138_);
return v___x_4179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4180_, lean_object* v_as_4181_, lean_object* v_i_4182_, lean_object* v_stop_4183_, lean_object* v_b_4184_){
_start:
{
size_t v_i_boxed_4185_; size_t v_stop_boxed_4186_; lean_object* v_res_4187_; 
v_i_boxed_4185_ = lean_unbox_usize(v_i_4182_);
lean_dec(v_i_4182_);
v_stop_boxed_4186_ = lean_unbox_usize(v_stop_4183_);
lean_dec(v_stop_4183_);
v_res_4187_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4180_, v_as_4181_, v_i_boxed_4185_, v_stop_boxed_4186_, v_b_4184_);
lean_dec_ref(v_as_4181_);
lean_dec(v_start_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4188_, lean_object* v_x_4189_, lean_object* v_x_4190_){
_start:
{
if (lean_obj_tag(v_x_4189_) == 0)
{
lean_object* v_cs_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4204_; 
v_cs_4191_ = lean_ctor_get(v_x_4189_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_x_4189_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4193_ = v_x_4189_;
v_isShared_4194_ = v_isSharedCheck_4204_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_cs_4191_);
lean_dec(v_x_4189_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4204_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
v___x_4195_ = lean_array_get_size(v_cs_4191_);
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = lean_nat_dec_lt(v___x_4196_, v___x_4195_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4199_; 
lean_dec_ref(v_cs_4191_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 1);
lean_ctor_set(v___x_4193_, 0, v_x_4190_);
v___x_4199_ = v___x_4193_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_x_4190_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
else
{
size_t v___x_4201_; size_t v___x_4202_; lean_object* v___x_4203_; 
lean_del_object(v___x_4193_);
v___x_4201_ = lean_usize_of_nat(v___x_4195_);
v___x_4202_ = ((size_t)0ULL);
v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4188_, v_cs_4191_, v___x_4201_, v___x_4202_, v_x_4190_);
lean_dec_ref(v_cs_4191_);
return v___x_4203_;
}
}
}
else
{
lean_object* v_vs_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4218_; 
v_vs_4205_ = lean_ctor_get(v_x_4189_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_x_4189_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4207_ = v_x_4189_;
v_isShared_4208_ = v_isSharedCheck_4218_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_vs_4205_);
lean_dec(v_x_4189_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4218_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; 
v___x_4209_ = lean_array_get_size(v_vs_4205_);
v___x_4210_ = lean_unsigned_to_nat(0u);
v___x_4211_ = lean_nat_dec_lt(v___x_4210_, v___x_4209_);
if (v___x_4211_ == 0)
{
lean_object* v___x_4213_; 
lean_dec_ref(v_vs_4205_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v_x_4190_);
v___x_4213_ = v___x_4207_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_x_4190_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
else
{
size_t v___x_4215_; size_t v___x_4216_; lean_object* v___x_4217_; 
lean_del_object(v___x_4207_);
v___x_4215_ = lean_usize_of_nat(v___x_4209_);
v___x_4216_ = ((size_t)0ULL);
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4188_, v_vs_4205_, v___x_4215_, v___x_4216_, v_x_4190_);
lean_dec_ref(v_vs_4205_);
return v___x_4217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4219_, lean_object* v_as_4220_, size_t v_i_4221_, size_t v_stop_4222_, lean_object* v_b_4223_){
_start:
{
uint8_t v___x_4224_; 
v___x_4224_ = lean_usize_dec_eq(v_i_4221_, v_stop_4222_);
if (v___x_4224_ == 0)
{
size_t v___x_4225_; size_t v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4225_ = ((size_t)1ULL);
v___x_4226_ = lean_usize_sub(v_i_4221_, v___x_4225_);
v___x_4227_ = lean_array_uget_borrowed(v_as_4220_, v___x_4226_);
lean_inc(v___x_4227_);
v___x_4228_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4219_, v___x_4227_, v_b_4223_);
if (lean_obj_tag(v___x_4228_) == 0)
{
return v___x_4228_;
}
else
{
lean_object* v_a_4229_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4228_, 1);
v_i_4221_ = v___x_4226_;
v_b_4223_ = v_a_4229_;
goto _start;
}
}
else
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4231_, 0, v_b_4223_);
return v___x_4231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4232_, lean_object* v_as_4233_, lean_object* v_i_4234_, lean_object* v_stop_4235_, lean_object* v_b_4236_){
_start:
{
size_t v_i_boxed_4237_; size_t v_stop_boxed_4238_; lean_object* v_res_4239_; 
v_i_boxed_4237_ = lean_unbox_usize(v_i_4234_);
lean_dec(v_i_4234_);
v_stop_boxed_4238_ = lean_unbox_usize(v_stop_4235_);
lean_dec(v_stop_4235_);
v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4232_, v_as_4233_, v_i_boxed_4237_, v_stop_boxed_4238_, v_b_4236_);
lean_dec_ref(v_as_4233_);
lean_dec(v_start_4232_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4240_, lean_object* v_x_4241_, lean_object* v_x_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4240_, v_x_4241_, v_x_4242_);
lean_dec(v_start_4240_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4244_, lean_object* v_t_4245_, lean_object* v_init_4246_){
_start:
{
lean_object* v_root_4247_; lean_object* v_tail_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; 
v_root_4247_ = lean_ctor_get(v_t_4245_, 0);
lean_inc_ref(v_root_4247_);
v_tail_4248_ = lean_ctor_get(v_t_4245_, 1);
lean_inc_ref(v_tail_4248_);
lean_dec_ref(v_t_4245_);
v___x_4249_ = lean_array_get_size(v_tail_4248_);
v___x_4250_ = lean_unsigned_to_nat(0u);
v___x_4251_ = lean_nat_dec_lt(v___x_4250_, v___x_4249_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; 
lean_dec_ref(v_tail_4248_);
v___x_4252_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4244_, v_root_4247_, v_init_4246_);
return v___x_4252_;
}
else
{
size_t v___x_4253_; size_t v___x_4254_; lean_object* v___x_4255_; 
v___x_4253_ = lean_usize_of_nat(v___x_4249_);
v___x_4254_ = ((size_t)0ULL);
v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4244_, v_tail_4248_, v___x_4253_, v___x_4254_, v_init_4246_);
lean_dec_ref(v_tail_4248_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_dec_ref(v_root_4247_);
return v___x_4255_;
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4257_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___x_4257_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4244_, v_root_4247_, v_a_4256_);
return v___x_4257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4258_, lean_object* v_t_4259_, lean_object* v_init_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4258_, v_t_4259_, v_init_4260_);
lean_dec(v_start_4258_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4262_, lean_object* v_lctx_4263_, lean_object* v_init_4264_){
_start:
{
lean_object* v_decls_4265_; lean_object* v___x_4266_; 
v_decls_4265_ = lean_ctor_get(v_lctx_4263_, 1);
lean_inc_ref(v_decls_4265_);
lean_dec_ref(v_lctx_4263_);
v___x_4266_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4262_, v_decls_4265_, v_init_4264_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4267_, lean_object* v_lctx_4268_, lean_object* v_init_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4267_, v_lctx_4268_, v_init_4269_);
lean_dec(v_start_4267_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4273_, lean_object* v_userNames_4274_, lean_object* v_start_4275_){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v_userNames_4274_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4275_, v_lctx_4273_, v___x_4277_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4280_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4279_);
lean_dec_ref_known(v___x_4278_, 1);
v___x_4280_ = l_Array_reverse___redArg(v_a_4279_);
return v___x_4280_;
}
else
{
lean_object* v_a_4281_; lean_object* v_snd_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v_a_4281_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v___x_4278_, 1);
v_snd_4282_ = lean_ctor_get(v_a_4281_, 1);
lean_inc(v_snd_4282_);
lean_dec(v_a_4281_);
v___x_4283_ = l_Array_reverse___redArg(v_snd_4282_);
v___x_4284_ = l_Array_reverse___redArg(v___x_4283_);
return v___x_4284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4285_, lean_object* v_userNames_4286_, lean_object* v_start_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4285_, v_userNames_4286_, v_start_4287_);
lean_dec(v_start_4287_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4289_, lean_object* v_lctx_4290_, lean_object* v_userNames_4291_, lean_object* v_start_4292_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4290_, v_userNames_4291_, v_start_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4294_, lean_object* v_lctx_4295_, lean_object* v_userNames_4296_, lean_object* v_start_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4294_, v_lctx_4295_, v_userNames_4296_, v_start_4297_);
lean_dec(v_start_4297_);
return v_res_4298_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4299_, lean_object* v_m_4300_, lean_object* v_a_4301_){
_start:
{
uint8_t v___x_4302_; 
v___x_4302_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4300_, v_a_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4303_, lean_object* v_m_4304_, lean_object* v_a_4305_){
_start:
{
uint8_t v_res_4306_; lean_object* v_r_4307_; 
v_res_4306_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4303_, v_m_4304_, v_a_4305_);
lean_dec(v_a_4305_);
lean_dec_ref(v_m_4304_);
v_r_4307_ = lean_box(v_res_4306_);
return v_r_4307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4308_, lean_object* v_m_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4309_, v_a_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4312_, lean_object* v_m_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4312_, v_m_4313_, v_a_4314_);
lean_dec(v_a_4314_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4316_, lean_object* v_start_4317_, lean_object* v_lctx_4318_, lean_object* v_init_4319_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4317_, v_lctx_4318_, v_init_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4321_, lean_object* v_start_4322_, lean_object* v_lctx_4323_, lean_object* v_init_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4321_, v_start_4322_, v_lctx_4323_, v_init_4324_);
lean_dec(v_start_4322_);
return v_res_4325_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4326_, lean_object* v_a_4327_, lean_object* v_x_4328_){
_start:
{
uint8_t v___x_4329_; 
v___x_4329_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4327_, v_x_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4330_, lean_object* v_a_4331_, lean_object* v_x_4332_){
_start:
{
uint8_t v_res_4333_; lean_object* v_r_4334_; 
v_res_4333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4330_, v_a_4331_, v_x_4332_);
lean_dec(v_x_4332_);
lean_dec(v_a_4331_);
v_r_4334_ = lean_box(v_res_4333_);
return v_r_4334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4335_, lean_object* v_a_4336_, lean_object* v_x_4337_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4336_, v_x_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4339_, lean_object* v_a_4340_, lean_object* v_x_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4339_, v_a_4340_, v_x_4341_);
lean_dec(v_a_4340_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4343_, lean_object* v_start_4344_, lean_object* v_t_4345_, lean_object* v_init_4346_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4344_, v_t_4345_, v_init_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4348_, lean_object* v_start_4349_, lean_object* v_t_4350_, lean_object* v_init_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4348_, v_start_4349_, v_t_4350_, v_init_4351_);
lean_dec(v_start_4349_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4353_, lean_object* v_start_4354_, lean_object* v_x_4355_, lean_object* v_x_4356_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4354_, v_x_4355_, v_x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4358_, lean_object* v_start_4359_, lean_object* v_x_4360_, lean_object* v_x_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4358_, v_start_4359_, v_x_4360_, v_x_4361_);
lean_dec(v_start_4359_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4363_, lean_object* v_start_4364_, lean_object* v_as_4365_, size_t v_i_4366_, size_t v_stop_4367_, lean_object* v_b_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4364_, v_as_4365_, v_i_4366_, v_stop_4367_, v_b_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4370_, lean_object* v_start_4371_, lean_object* v_as_4372_, lean_object* v_i_4373_, lean_object* v_stop_4374_, lean_object* v_b_4375_){
_start:
{
size_t v_i_boxed_4376_; size_t v_stop_boxed_4377_; lean_object* v_res_4378_; 
v_i_boxed_4376_ = lean_unbox_usize(v_i_4373_);
lean_dec(v_i_4373_);
v_stop_boxed_4377_ = lean_unbox_usize(v_stop_4374_);
lean_dec(v_stop_4374_);
v_res_4378_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4370_, v_start_4371_, v_as_4372_, v_i_boxed_4376_, v_stop_boxed_4377_, v_b_4375_);
lean_dec_ref(v_as_4372_);
lean_dec(v_start_4371_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4379_, lean_object* v_start_4380_, lean_object* v_as_4381_, size_t v_i_4382_, size_t v_stop_4383_, lean_object* v_b_4384_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4380_, v_as_4381_, v_i_4382_, v_stop_4383_, v_b_4384_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4386_, lean_object* v_start_4387_, lean_object* v_as_4388_, lean_object* v_i_4389_, lean_object* v_stop_4390_, lean_object* v_b_4391_){
_start:
{
size_t v_i_boxed_4392_; size_t v_stop_boxed_4393_; lean_object* v_res_4394_; 
v_i_boxed_4392_ = lean_unbox_usize(v_i_4389_);
lean_dec(v_i_4389_);
v_stop_boxed_4393_ = lean_unbox_usize(v_stop_4390_);
lean_dec(v_stop_4390_);
v_res_4394_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4386_, v_start_4387_, v_as_4388_, v_i_boxed_4392_, v_stop_boxed_4393_, v_b_4391_);
lean_dec_ref(v_as_4388_);
lean_dec(v_start_4387_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4395_, lean_object* v_inst_4396_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_apply_2(v_inst_4395_, lean_box(0), v_inst_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4398_, lean_object* v_n_4399_, lean_object* v_inst_4400_, lean_object* v_inst_4401_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_apply_2(v_inst_4400_, lean_box(0), v_inst_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4403_, lean_object* v_d_x3f_4404_, lean_object* v_b_4405_){
_start:
{
if (lean_obj_tag(v_d_x3f_4404_) == 0)
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4406_, 0, v_b_4405_);
v___x_4407_ = lean_apply_2(v_toPure_4403_, lean_box(0), v___x_4406_);
return v___x_4407_;
}
else
{
lean_object* v_val_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4423_; 
v_val_4408_ = lean_ctor_get(v_d_x3f_4404_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v_d_x3f_4404_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4410_ = v_d_x3f_4404_;
v_isShared_4411_ = v_isSharedCheck_4423_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_val_4408_);
lean_dec(v_d_x3f_4404_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4423_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
uint8_t v___x_4412_; 
v___x_4412_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4408_);
if (v___x_4412_ == 0)
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
v___x_4413_ = l_Lean_LocalDecl_toExpr(v_val_4408_);
v___x_4414_ = lean_array_push(v_b_4405_, v___x_4413_);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v___x_4414_);
v___x_4416_ = v___x_4410_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_apply_2(v_toPure_4403_, lean_box(0), v___x_4416_);
return v___x_4417_;
}
}
else
{
lean_object* v___x_4420_; 
lean_dec(v_val_4408_);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v_b_4405_);
v___x_4420_ = v___x_4410_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_b_4405_);
v___x_4420_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; 
v___x_4421_ = lean_apply_2(v_toPure_4403_, lean_box(0), v___x_4420_);
return v___x_4421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4424_, lean_object* v_____s_4425_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = lean_apply_2(v_toPure_4424_, lean_box(0), v_____s_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4427_, lean_object* v_hs_4428_, lean_object* v___f_4429_, lean_object* v_toBind_4430_, lean_object* v___f_4431_, lean_object* v_____do__lift_4432_){
_start:
{
lean_object* v_decls_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_decls_4433_ = lean_ctor_get(v_____do__lift_4432_, 1);
v___x_4434_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4427_, v_decls_4433_, v_hs_4428_, v___f_4429_);
v___x_4435_ = lean_apply_4(v_toBind_4430_, lean_box(0), lean_box(0), v___x_4434_, v___f_4431_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4436_, lean_object* v_hs_4437_, lean_object* v___f_4438_, lean_object* v_toBind_4439_, lean_object* v___f_4440_, lean_object* v_____do__lift_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4436_, v_hs_4437_, v___f_4438_, v_toBind_4439_, v___f_4440_, v_____do__lift_4441_);
lean_dec_ref(v_____do__lift_4441_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4445_, lean_object* v_inst_4446_){
_start:
{
lean_object* v_toApplicative_4447_; lean_object* v_toBind_4448_; lean_object* v_toPure_4449_; lean_object* v_hs_4450_; lean_object* v___f_4451_; lean_object* v___f_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; 
v_toApplicative_4447_ = lean_ctor_get(v_inst_4445_, 0);
v_toBind_4448_ = lean_ctor_get(v_inst_4445_, 1);
lean_inc_n(v_toBind_4448_, 2);
v_toPure_4449_ = lean_ctor_get(v_toApplicative_4447_, 1);
v_hs_4450_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4449_, 2);
v___f_4451_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4451_, 0, v_toPure_4449_);
v___f_4452_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4452_, 0, v_toPure_4449_);
v___f_4453_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4453_, 0, v_inst_4445_);
lean_closure_set(v___f_4453_, 1, v_hs_4450_);
lean_closure_set(v___f_4453_, 2, v___f_4451_);
lean_closure_set(v___f_4453_, 3, v_toBind_4448_);
lean_closure_set(v___f_4453_, 4, v___f_4452_);
v___x_4454_ = lean_apply_4(v_toBind_4448_, lean_box(0), lean_box(0), v_inst_4446_, v___f_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4455_, lean_object* v_inst_4456_, lean_object* v_inst_4457_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Lean_getLocalHyps___redArg(v_inst_4456_, v_inst_4457_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4459_, lean_object* v_e_4460_, lean_object* v_d_4461_){
_start:
{
lean_object* v___y_4463_; lean_object* v_fvarId_4495_; 
v_fvarId_4495_ = lean_ctor_get(v_d_4461_, 1);
lean_inc(v_fvarId_4495_);
v___y_4463_ = v_fvarId_4495_;
goto v___jp_4462_;
v___jp_4462_:
{
uint8_t v___x_4464_; 
v___x_4464_ = l_Lean_instBEqFVarId_beq(v___y_4463_, v_fvarId_4459_);
lean_dec(v___y_4463_);
if (v___x_4464_ == 0)
{
if (lean_obj_tag(v_d_4461_) == 0)
{
lean_object* v_index_4465_; lean_object* v_fvarId_4466_; lean_object* v_userName_4467_; lean_object* v_type_4468_; uint8_t v_bi_4469_; uint8_t v_kind_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4478_; 
v_index_4465_ = lean_ctor_get(v_d_4461_, 0);
v_fvarId_4466_ = lean_ctor_get(v_d_4461_, 1);
v_userName_4467_ = lean_ctor_get(v_d_4461_, 2);
v_type_4468_ = lean_ctor_get(v_d_4461_, 3);
v_bi_4469_ = lean_ctor_get_uint8(v_d_4461_, sizeof(void*)*4);
v_kind_4470_ = lean_ctor_get_uint8(v_d_4461_, sizeof(void*)*4 + 1);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_d_4461_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4472_ = v_d_4461_;
v_isShared_4473_ = v_isSharedCheck_4478_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_type_4468_);
lean_inc(v_userName_4467_);
lean_inc(v_fvarId_4466_);
lean_inc(v_index_4465_);
lean_dec(v_d_4461_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4478_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4474_ = l_Lean_Expr_replaceFVarId(v_type_4468_, v_fvarId_4459_, v_e_4460_);
lean_dec_ref(v_type_4468_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 3, v___x_4474_);
v___x_4476_ = v___x_4472_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_index_4465_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_fvarId_4466_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_userName_4467_);
lean_ctor_set(v_reuseFailAlloc_4477_, 3, v___x_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*4, v_bi_4469_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*4 + 1, v_kind_4470_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
else
{
lean_object* v_index_4479_; lean_object* v_fvarId_4480_; lean_object* v_userName_4481_; lean_object* v_type_4482_; lean_object* v_value_4483_; uint8_t v_nondep_4484_; uint8_t v_kind_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4494_; 
v_index_4479_ = lean_ctor_get(v_d_4461_, 0);
v_fvarId_4480_ = lean_ctor_get(v_d_4461_, 1);
v_userName_4481_ = lean_ctor_get(v_d_4461_, 2);
v_type_4482_ = lean_ctor_get(v_d_4461_, 3);
v_value_4483_ = lean_ctor_get(v_d_4461_, 4);
v_nondep_4484_ = lean_ctor_get_uint8(v_d_4461_, sizeof(void*)*5);
v_kind_4485_ = lean_ctor_get_uint8(v_d_4461_, sizeof(void*)*5 + 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_d_4461_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4487_ = v_d_4461_;
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_value_4483_);
lean_inc(v_type_4482_);
lean_inc(v_userName_4481_);
lean_inc(v_fvarId_4480_);
lean_inc(v_index_4479_);
lean_dec(v_d_4461_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
lean_inc(v_fvarId_4459_);
v___x_4489_ = l_Lean_Expr_replaceFVarId(v_type_4482_, v_fvarId_4459_, v_e_4460_);
lean_dec_ref(v_type_4482_);
v___x_4490_ = l_Lean_Expr_replaceFVarId(v_value_4483_, v_fvarId_4459_, v_e_4460_);
lean_dec_ref(v_value_4483_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 4, v___x_4490_);
lean_ctor_set(v___x_4487_, 3, v___x_4489_);
v___x_4492_ = v___x_4487_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_index_4479_);
lean_ctor_set(v_reuseFailAlloc_4493_, 1, v_fvarId_4480_);
lean_ctor_set(v_reuseFailAlloc_4493_, 2, v_userName_4481_);
lean_ctor_set(v_reuseFailAlloc_4493_, 3, v___x_4489_);
lean_ctor_set(v_reuseFailAlloc_4493_, 4, v___x_4490_);
lean_ctor_set_uint8(v_reuseFailAlloc_4493_, sizeof(void*)*5, v_nondep_4484_);
lean_ctor_set_uint8(v_reuseFailAlloc_4493_, sizeof(void*)*5 + 1, v_kind_4485_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
else
{
lean_dec(v_fvarId_4459_);
return v_d_4461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4496_, lean_object* v_e_4497_, lean_object* v_d_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4496_, v_e_4497_, v_d_4498_);
lean_dec_ref(v_e_4497_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4500_, lean_object* v_e_4501_, lean_object* v_x_4502_){
_start:
{
lean_object* v___x_4503_; 
v___x_4503_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4500_, v_e_4501_, v_x_4502_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4504_, lean_object* v_e_4505_, lean_object* v_x_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4504_, v_e_4505_, v_x_4506_);
lean_dec_ref(v_e_4505_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4508_, lean_object* v_e_4509_, size_t v_sz_4510_, size_t v_i_4511_, lean_object* v_bs_4512_){
_start:
{
uint8_t v___x_4513_; 
v___x_4513_ = lean_usize_dec_lt(v_i_4511_, v_sz_4510_);
if (v___x_4513_ == 0)
{
lean_dec(v_fvarId_4508_);
return v_bs_4512_;
}
else
{
lean_object* v_v_4514_; lean_object* v___x_4515_; lean_object* v_bs_x27_4516_; lean_object* v___y_4518_; 
v_v_4514_ = lean_array_uget(v_bs_4512_, v_i_4511_);
v___x_4515_ = lean_unsigned_to_nat(0u);
v_bs_x27_4516_ = lean_array_uset(v_bs_4512_, v_i_4511_, v___x_4515_);
if (lean_obj_tag(v_v_4514_) == 0)
{
v___y_4518_ = v_v_4514_;
goto v___jp_4517_;
}
else
{
lean_object* v_val_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4531_; 
v_val_4523_ = lean_ctor_get(v_v_4514_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v_v_4514_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4525_ = v_v_4514_;
v_isShared_4526_ = v_isSharedCheck_4531_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_val_4523_);
lean_dec(v_v_4514_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4531_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4527_; lean_object* v___x_4529_; 
lean_inc(v_fvarId_4508_);
v___x_4527_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4508_, v_e_4509_, v_val_4523_);
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 0, v___x_4527_);
v___x_4529_ = v___x_4525_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4527_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
v___y_4518_ = v___x_4529_;
goto v___jp_4517_;
}
}
}
v___jp_4517_:
{
size_t v___x_4519_; size_t v___x_4520_; lean_object* v___x_4521_; 
v___x_4519_ = ((size_t)1ULL);
v___x_4520_ = lean_usize_add(v_i_4511_, v___x_4519_);
v___x_4521_ = lean_array_uset(v_bs_x27_4516_, v_i_4511_, v___y_4518_);
v_i_4511_ = v___x_4520_;
v_bs_4512_ = v___x_4521_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4532_, lean_object* v_e_4533_, lean_object* v_sz_4534_, lean_object* v_i_4535_, lean_object* v_bs_4536_){
_start:
{
size_t v_sz_boxed_4537_; size_t v_i_boxed_4538_; lean_object* v_res_4539_; 
v_sz_boxed_4537_ = lean_unbox_usize(v_sz_4534_);
lean_dec(v_sz_4534_);
v_i_boxed_4538_ = lean_unbox_usize(v_i_4535_);
lean_dec(v_i_4535_);
v_res_4539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4532_, v_e_4533_, v_sz_boxed_4537_, v_i_boxed_4538_, v_bs_4536_);
lean_dec_ref(v_e_4533_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4540_, lean_object* v_e_4541_, size_t v_sz_4542_, size_t v_i_4543_, lean_object* v_bs_4544_){
_start:
{
uint8_t v___x_4545_; 
v___x_4545_ = lean_usize_dec_lt(v_i_4543_, v_sz_4542_);
if (v___x_4545_ == 0)
{
lean_dec(v_fvarId_4540_);
return v_bs_4544_;
}
else
{
lean_object* v_v_4546_; lean_object* v___x_4547_; lean_object* v_bs_x27_4548_; lean_object* v___x_4549_; size_t v___x_4550_; size_t v___x_4551_; lean_object* v___x_4552_; 
v_v_4546_ = lean_array_uget(v_bs_4544_, v_i_4543_);
v___x_4547_ = lean_unsigned_to_nat(0u);
v_bs_x27_4548_ = lean_array_uset(v_bs_4544_, v_i_4543_, v___x_4547_);
lean_inc(v_fvarId_4540_);
v___x_4549_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4540_, v_e_4541_, v_v_4546_);
v___x_4550_ = ((size_t)1ULL);
v___x_4551_ = lean_usize_add(v_i_4543_, v___x_4550_);
v___x_4552_ = lean_array_uset(v_bs_x27_4548_, v_i_4543_, v___x_4549_);
v_i_4543_ = v___x_4551_;
v_bs_4544_ = v___x_4552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4554_, lean_object* v_e_4555_, lean_object* v_x_4556_){
_start:
{
if (lean_obj_tag(v_x_4556_) == 0)
{
lean_object* v_cs_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4567_; 
v_cs_4557_ = lean_ctor_get(v_x_4556_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v_x_4556_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4559_ = v_x_4556_;
v_isShared_4560_ = v_isSharedCheck_4567_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_cs_4557_);
lean_dec(v_x_4556_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4567_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
size_t v_sz_4561_; size_t v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4565_; 
v_sz_4561_ = lean_array_size(v_cs_4557_);
v___x_4562_ = ((size_t)0ULL);
v___x_4563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4554_, v_e_4555_, v_sz_4561_, v___x_4562_, v_cs_4557_);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 0, v___x_4563_);
v___x_4565_ = v___x_4559_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4563_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
else
{
lean_object* v_vs_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4578_; 
v_vs_4568_ = lean_ctor_get(v_x_4556_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v_x_4556_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4570_ = v_x_4556_;
v_isShared_4571_ = v_isSharedCheck_4578_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_vs_4568_);
lean_dec(v_x_4556_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4578_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
size_t v_sz_4572_; size_t v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4576_; 
v_sz_4572_ = lean_array_size(v_vs_4568_);
v___x_4573_ = ((size_t)0ULL);
v___x_4574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4554_, v_e_4555_, v_sz_4572_, v___x_4573_, v_vs_4568_);
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 0, v___x_4574_);
v___x_4576_ = v___x_4570_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4574_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4579_, lean_object* v_e_4580_, lean_object* v_x_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4579_, v_e_4580_, v_x_4581_);
lean_dec_ref(v_e_4580_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4583_, lean_object* v_e_4584_, lean_object* v_sz_4585_, lean_object* v_i_4586_, lean_object* v_bs_4587_){
_start:
{
size_t v_sz_boxed_4588_; size_t v_i_boxed_4589_; lean_object* v_res_4590_; 
v_sz_boxed_4588_ = lean_unbox_usize(v_sz_4585_);
lean_dec(v_sz_4585_);
v_i_boxed_4589_ = lean_unbox_usize(v_i_4586_);
lean_dec(v_i_4586_);
v_res_4590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4583_, v_e_4584_, v_sz_boxed_4588_, v_i_boxed_4589_, v_bs_4587_);
lean_dec_ref(v_e_4584_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4591_, lean_object* v_e_4592_, lean_object* v_t_4593_){
_start:
{
lean_object* v_root_4594_; lean_object* v_tail_4595_; lean_object* v_size_4596_; size_t v_shift_4597_; lean_object* v_tailOff_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4609_; 
v_root_4594_ = lean_ctor_get(v_t_4593_, 0);
v_tail_4595_ = lean_ctor_get(v_t_4593_, 1);
v_size_4596_ = lean_ctor_get(v_t_4593_, 2);
v_shift_4597_ = lean_ctor_get_usize(v_t_4593_, 4);
v_tailOff_4598_ = lean_ctor_get(v_t_4593_, 3);
v_isSharedCheck_4609_ = !lean_is_exclusive(v_t_4593_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4600_ = v_t_4593_;
v_isShared_4601_ = v_isSharedCheck_4609_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_tailOff_4598_);
lean_inc(v_size_4596_);
lean_inc(v_tail_4595_);
lean_inc(v_root_4594_);
lean_dec(v_t_4593_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4609_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4602_; size_t v_sz_4603_; size_t v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4607_; 
lean_inc(v_fvarId_4591_);
v___x_4602_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4591_, v_e_4592_, v_root_4594_);
v_sz_4603_ = lean_array_size(v_tail_4595_);
v___x_4604_ = ((size_t)0ULL);
v___x_4605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4591_, v_e_4592_, v_sz_4603_, v___x_4604_, v_tail_4595_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 1, v___x_4605_);
lean_ctor_set(v___x_4600_, 0, v___x_4602_);
v___x_4607_ = v___x_4600_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4602_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4608_, 2, v_size_4596_);
lean_ctor_set(v_reuseFailAlloc_4608_, 3, v_tailOff_4598_);
lean_ctor_set_usize(v_reuseFailAlloc_4608_, 4, v_shift_4597_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4610_, lean_object* v_e_4611_, lean_object* v_t_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4610_, v_e_4611_, v_t_4612_);
lean_dec_ref(v_e_4611_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4614_, lean_object* v_x_4615_){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = lean_apply_1(v_f_4614_, v_x_4615_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4617_, lean_object* v_as_4618_, lean_object* v_i_4619_, lean_object* v_acc_4620_){
_start:
{
lean_object* v___x_4621_; uint8_t v___x_4622_; 
v___x_4621_ = lean_array_get_size(v_as_4618_);
v___x_4622_ = lean_nat_dec_eq(v_i_4619_, v___x_4621_);
if (v___x_4622_ == 0)
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4623_ = lean_array_fget_borrowed(v_as_4618_, v_i_4619_);
lean_inc(v_f_4617_);
lean_inc(v___x_4623_);
v___x_4624_ = lean_apply_1(v_f_4617_, v___x_4623_);
v___x_4625_ = lean_unsigned_to_nat(1u);
v___x_4626_ = lean_nat_add(v_i_4619_, v___x_4625_);
lean_dec(v_i_4619_);
v___x_4627_ = lean_array_push(v_acc_4620_, v___x_4624_);
v_i_4619_ = v___x_4626_;
v_acc_4620_ = v___x_4627_;
goto _start;
}
else
{
lean_dec(v_i_4619_);
lean_dec(v_f_4617_);
return v_acc_4620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4629_, lean_object* v_as_4630_, lean_object* v_i_4631_, lean_object* v_acc_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4629_, v_as_4630_, v_i_4631_, v_acc_4632_);
lean_dec_ref(v_as_4630_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4634_, lean_object* v_as_4635_){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4636_ = lean_unsigned_to_nat(0u);
v___x_4637_ = lean_array_get_size(v_as_4635_);
v___x_4638_ = lean_mk_empty_array_with_capacity(v___x_4637_);
v___x_4639_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4634_, v_as_4635_, v___x_4636_, v___x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4640_, lean_object* v_as_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4640_, v_as_4641_);
lean_dec_ref(v_as_4641_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4643_, size_t v_sz_4644_, size_t v_i_4645_, lean_object* v_bs_4646_){
_start:
{
uint8_t v___x_4647_; 
v___x_4647_ = lean_usize_dec_lt(v_i_4645_, v_sz_4644_);
if (v___x_4647_ == 0)
{
lean_dec(v_f_4643_);
return v_bs_4646_;
}
else
{
lean_object* v_v_4648_; lean_object* v___x_4649_; lean_object* v_bs_x27_4650_; lean_object* v___y_4652_; 
v_v_4648_ = lean_array_uget(v_bs_4646_, v_i_4645_);
v___x_4649_ = lean_unsigned_to_nat(0u);
v_bs_x27_4650_ = lean_array_uset(v_bs_4646_, v_i_4645_, v___x_4649_);
switch(lean_obj_tag(v_v_4648_))
{
case 0:
{
lean_object* v_key_4657_; lean_object* v_val_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4666_; 
v_key_4657_ = lean_ctor_get(v_v_4648_, 0);
v_val_4658_ = lean_ctor_get(v_v_4648_, 1);
v_isSharedCheck_4666_ = !lean_is_exclusive(v_v_4648_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4660_ = v_v_4648_;
v_isShared_4661_ = v_isSharedCheck_4666_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_val_4658_);
lean_inc(v_key_4657_);
lean_dec(v_v_4648_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4666_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4662_; lean_object* v___x_4664_; 
lean_inc(v_f_4643_);
v___x_4662_ = lean_apply_1(v_f_4643_, v_val_4658_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 1, v___x_4662_);
v___x_4664_ = v___x_4660_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_key_4657_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
v___y_4652_ = v___x_4664_;
goto v___jp_4651_;
}
}
}
case 1:
{
lean_object* v_node_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4675_; 
v_node_4667_ = lean_ctor_get(v_v_4648_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v_v_4648_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4669_ = v_v_4648_;
v_isShared_4670_ = v_isSharedCheck_4675_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_node_4667_);
lean_dec(v_v_4648_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4675_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4671_; lean_object* v___x_4673_; 
lean_inc(v_f_4643_);
v___x_4671_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4643_, v_node_4667_);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 0, v___x_4671_);
v___x_4673_ = v___x_4669_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4671_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
v___y_4652_ = v___x_4673_;
goto v___jp_4651_;
}
}
}
default: 
{
lean_object* v___x_4676_; 
v___x_4676_ = lean_box(2);
v___y_4652_ = v___x_4676_;
goto v___jp_4651_;
}
}
v___jp_4651_:
{
size_t v___x_4653_; size_t v___x_4654_; lean_object* v___x_4655_; 
v___x_4653_ = ((size_t)1ULL);
v___x_4654_ = lean_usize_add(v_i_4645_, v___x_4653_);
v___x_4655_ = lean_array_uset(v_bs_x27_4650_, v_i_4645_, v___y_4652_);
v_i_4645_ = v___x_4654_;
v_bs_4646_ = v___x_4655_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4677_, lean_object* v_n_4678_){
_start:
{
if (lean_obj_tag(v_n_4678_) == 0)
{
lean_object* v_es_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4689_; 
v_es_4679_ = lean_ctor_get(v_n_4678_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v_n_4678_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4681_ = v_n_4678_;
v_isShared_4682_ = v_isSharedCheck_4689_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_es_4679_);
lean_dec(v_n_4678_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4689_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
size_t v_sz_4683_; size_t v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4687_; 
v_sz_4683_ = lean_array_size(v_es_4679_);
v___x_4684_ = ((size_t)0ULL);
v___x_4685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4677_, v_sz_4683_, v___x_4684_, v_es_4679_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 0, v___x_4685_);
v___x_4687_ = v___x_4681_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
else
{
lean_object* v_ks_4690_; lean_object* v_vs_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4699_; 
v_ks_4690_ = lean_ctor_get(v_n_4678_, 0);
v_vs_4691_ = lean_ctor_get(v_n_4678_, 1);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_n_4678_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4693_ = v_n_4678_;
v_isShared_4694_ = v_isSharedCheck_4699_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_vs_4691_);
lean_inc(v_ks_4690_);
lean_dec(v_n_4678_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4699_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v_val_4695_; lean_object* v___x_4697_; 
v_val_4695_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4677_, v_vs_4691_);
lean_dec_ref(v_vs_4691_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 1, v_val_4695_);
v___x_4697_ = v___x_4693_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_ks_4690_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v_val_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4700_, lean_object* v_sz_4701_, lean_object* v_i_4702_, lean_object* v_bs_4703_){
_start:
{
size_t v_sz_boxed_4704_; size_t v_i_boxed_4705_; lean_object* v_res_4706_; 
v_sz_boxed_4704_ = lean_unbox_usize(v_sz_4701_);
lean_dec(v_sz_4701_);
v_i_boxed_4705_ = lean_unbox_usize(v_i_4702_);
lean_dec(v_i_4702_);
v_res_4706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4700_, v_sz_boxed_4704_, v_i_boxed_4705_, v_bs_4703_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4707_, lean_object* v_f_4708_){
_start:
{
lean_object* v___f_4709_; lean_object* v___x_4710_; 
v___f_4709_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4709_, 0, v_f_4708_);
v___x_4710_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4709_, v_pm_4707_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4711_, lean_object* v_e_4712_, lean_object* v_lctx_4713_){
_start:
{
lean_object* v_lctx_4714_; lean_object* v_fvarIdToDecl_4715_; lean_object* v_decls_4716_; lean_object* v_auxDeclToFullName_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4727_; 
lean_inc(v_fvarId_4711_);
v_lctx_4714_ = lean_local_ctx_erase(v_lctx_4713_, v_fvarId_4711_);
v_fvarIdToDecl_4715_ = lean_ctor_get(v_lctx_4714_, 0);
v_decls_4716_ = lean_ctor_get(v_lctx_4714_, 1);
v_auxDeclToFullName_4717_ = lean_ctor_get(v_lctx_4714_, 2);
v_isSharedCheck_4727_ = !lean_is_exclusive(v_lctx_4714_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4719_ = v_lctx_4714_;
v_isShared_4720_ = v_isSharedCheck_4727_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_auxDeclToFullName_4717_);
lean_inc(v_decls_4716_);
lean_inc(v_fvarIdToDecl_4715_);
lean_dec(v_lctx_4714_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4727_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___f_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4725_; 
lean_inc_ref(v_e_4712_);
lean_inc(v_fvarId_4711_);
v___f_4721_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4721_, 0, v_fvarId_4711_);
lean_closure_set(v___f_4721_, 1, v_e_4712_);
v___x_4722_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4715_, v___f_4721_);
v___x_4723_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4711_, v_e_4712_, v_decls_4716_);
lean_dec_ref(v_e_4712_);
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 1, v___x_4723_);
lean_ctor_set(v___x_4719_, 0, v___x_4722_);
v___x_4725_ = v___x_4719_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_auxDeclToFullName_4717_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4728_, lean_object* v_00_u03c3_4729_, lean_object* v_pm_4730_, lean_object* v_f_4731_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4730_, v_f_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4733_, lean_object* v_f_4734_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4734_, v_pm_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4736_, lean_object* v_00_u03c3_4737_, lean_object* v_pm_4738_, lean_object* v_f_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4739_, v_pm_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4741_, lean_object* v_00_u03b2_4742_, lean_object* v_00_u03c3_4743_, lean_object* v_f_4744_, lean_object* v_n_4745_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4744_, v_n_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4747_, lean_object* v_00_u03b2_4748_, lean_object* v_00_u03c3_4749_, lean_object* v_f_4750_, size_t v_sz_4751_, size_t v_i_4752_, lean_object* v_bs_4753_){
_start:
{
lean_object* v___x_4754_; 
v___x_4754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4750_, v_sz_4751_, v_i_4752_, v_bs_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4755_, lean_object* v_00_u03b2_4756_, lean_object* v_00_u03c3_4757_, lean_object* v_f_4758_, lean_object* v_sz_4759_, lean_object* v_i_4760_, lean_object* v_bs_4761_){
_start:
{
size_t v_sz_boxed_4762_; size_t v_i_boxed_4763_; lean_object* v_res_4764_; 
v_sz_boxed_4762_ = lean_unbox_usize(v_sz_4759_);
lean_dec(v_sz_4759_);
v_i_boxed_4763_ = lean_unbox_usize(v_i_4760_);
lean_dec(v_i_4760_);
v_res_4764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4755_, v_00_u03b2_4756_, v_00_u03c3_4757_, v_f_4758_, v_sz_boxed_4762_, v_i_boxed_4763_, v_bs_4761_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4765_, lean_object* v_00_u03b2_4766_, lean_object* v_f_4767_, lean_object* v_as_4768_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4767_, v_as_4768_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4770_, lean_object* v_00_u03b2_4771_, lean_object* v_f_4772_, lean_object* v_as_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4770_, v_00_u03b2_4771_, v_f_4772_, v_as_4773_);
lean_dec_ref(v_as_4773_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4775_, lean_object* v_00_u03b2_4776_, lean_object* v_f_4777_, lean_object* v_as_4778_, lean_object* v_i_4779_, lean_object* v_acc_4780_, lean_object* v_hle_4781_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4777_, v_as_4778_, v_i_4779_, v_acc_4780_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4783_, lean_object* v_00_u03b2_4784_, lean_object* v_f_4785_, lean_object* v_as_4786_, lean_object* v_i_4787_, lean_object* v_acc_4788_, lean_object* v_hle_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4783_, v_00_u03b2_4784_, v_f_4785_, v_as_4786_, v_i_4787_, v_acc_4788_, v_hle_4789_);
lean_dec_ref(v_as_4786_);
return v_res_4790_;
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
