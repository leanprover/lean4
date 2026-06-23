// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Lambda
// Imports: public import Lean.Meta.Sym.Simp.SimpM
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sound"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "f'"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 166, 137, 10, 240, 99, 97, 180)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "g"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 12, 229, 162, 1, 36, 3, 29)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_simpLambda___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simp___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_simpLambda___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpLambda___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = l_Lean_Expr_bvar___override(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = l_Lean_Expr_bvar___override(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(lean_object* v___x_11_, lean_object* v_a_12_, lean_object* v___x_13_, lean_object* v_xs_14_, lean_object* v___x_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v_00_u03b2_20_, uint8_t v___x_21_, uint8_t v___x_22_, uint8_t v___x_23_, lean_object* v___x_24_, lean_object* v_f_25_, lean_object* v_g_26_, lean_object* v_h_27_, lean_object* v___x_28_, lean_object* v_f_x27_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_35_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0));
lean_inc_ref(v___x_11_);
v___x_36_ = l_Lean_Name_mkStr2(v___x_11_, v___x_35_);
lean_inc(v_a_12_);
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v_a_12_);
lean_ctor_set(v___x_37_, 1, v___x_13_);
v___x_38_ = l_Lean_mkConst(v___x_36_, v___x_37_);
v___x_39_ = 0;
v___x_40_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1, &l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1);
v___x_41_ = l_Lean_mkAppN(v___x_40_, v_xs_14_);
lean_inc_ref(v___x_41_);
lean_inc_ref_n(v_a_16_, 4);
lean_inc(v___x_15_);
v___x_42_ = l_Lean_mkLambda(v___x_15_, v___x_39_, v_a_16_, v___x_41_);
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2);
lean_inc_ref_n(v_a_17_, 2);
v___x_45_ = l_Lean_mkAppB(v_a_17_, v___x_44_, v___x_40_);
v___x_46_ = l_Lean_mkLambda(v___x_18_, v___x_39_, v___x_45_, v___x_41_);
v___x_47_ = l_Lean_mkLambda(v___x_19_, v___x_39_, v_a_16_, v___x_46_);
v___x_48_ = l_Lean_mkLambda(v___x_15_, v___x_39_, v_a_16_, v___x_47_);
lean_inc_ref(v_f_x27_29_);
v___x_49_ = l_Lean_mkApp6(v___x_38_, v_a_16_, v_a_17_, v_00_u03b2_20_, v___x_42_, v___x_48_, v_f_x27_29_);
v___x_50_ = lean_mk_empty_array_with_capacity(v___x_43_);
v___x_51_ = lean_array_push(v___x_50_, v_f_x27_29_);
v___x_52_ = l_Array_append___redArg(v___x_51_, v_xs_14_);
v___x_53_ = l_Lean_Meta_mkLambdaFVars(v___x_52_, v___x_49_, v___x_21_, v___x_22_, v___x_21_, v___x_22_, v___x_23_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec_ref(v___x_52_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_53_, 1);
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3));
lean_inc_ref(v___x_11_);
v___x_56_ = l_Lean_Name_mkStr2(v___x_11_, v___x_55_);
lean_inc_n(v___x_24_, 2);
v___x_57_ = l_Lean_mkConst(v___x_56_, v___x_24_);
lean_inc_ref(v_h_27_);
lean_inc_ref_n(v_g_26_, 2);
lean_inc_ref_n(v_f_25_, 2);
lean_inc_ref_n(v_a_17_, 2);
lean_inc_ref_n(v_a_16_, 3);
v___x_58_ = l_Lean_mkApp5(v___x_57_, v_a_16_, v_a_17_, v_f_25_, v_g_26_, v_h_27_);
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4));
v___x_60_ = l_Lean_Name_mkStr2(v___x_11_, v___x_59_);
v___x_61_ = l_Lean_mkConst(v___x_60_, v___x_24_);
lean_inc_ref(v___x_61_);
v___x_62_ = l_Lean_mkApp3(v___x_61_, v_a_16_, v_a_17_, v_f_25_);
v___x_63_ = l_Lean_mkApp3(v___x_61_, v_a_16_, v_a_17_, v_g_26_);
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6));
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v_a_12_);
lean_ctor_set(v___x_65_, 1, v___x_24_);
v___x_66_ = l_Lean_mkConst(v___x_64_, v___x_65_);
v___x_67_ = l_Lean_mkApp6(v___x_66_, v___x_28_, v_a_16_, v___x_62_, v___x_63_, v_a_54_, v___x_58_);
v___x_68_ = lean_unsigned_to_nat(3u);
v___x_69_ = lean_mk_empty_array_with_capacity(v___x_68_);
v___x_70_ = lean_array_push(v___x_69_, v_f_25_);
v___x_71_ = lean_array_push(v___x_70_, v_g_26_);
v___x_72_ = lean_array_push(v___x_71_, v_h_27_);
v___x_73_ = l_Lean_Meta_mkLambdaFVars(v___x_72_, v___x_67_, v___x_21_, v___x_22_, v___x_21_, v___x_22_, v___x_23_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec_ref(v___x_72_);
return v___x_73_;
}
else
{
lean_dec_ref(v___x_28_);
lean_dec_ref(v_h_27_);
lean_dec_ref(v_g_26_);
lean_dec_ref(v_f_25_);
lean_dec(v___x_24_);
lean_dec_ref(v_a_17_);
lean_dec_ref(v_a_16_);
lean_dec(v_a_12_);
lean_dec_ref(v___x_11_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed(lean_object** _args){
lean_object* v___x_74_ = _args[0];
lean_object* v_a_75_ = _args[1];
lean_object* v___x_76_ = _args[2];
lean_object* v_xs_77_ = _args[3];
lean_object* v___x_78_ = _args[4];
lean_object* v_a_79_ = _args[5];
lean_object* v_a_80_ = _args[6];
lean_object* v___x_81_ = _args[7];
lean_object* v___x_82_ = _args[8];
lean_object* v_00_u03b2_83_ = _args[9];
lean_object* v___x_84_ = _args[10];
lean_object* v___x_85_ = _args[11];
lean_object* v___x_86_ = _args[12];
lean_object* v___x_87_ = _args[13];
lean_object* v_f_88_ = _args[14];
lean_object* v_g_89_ = _args[15];
lean_object* v_h_90_ = _args[16];
lean_object* v___x_91_ = _args[17];
lean_object* v_f_x27_92_ = _args[18];
lean_object* v___y_93_ = _args[19];
lean_object* v___y_94_ = _args[20];
lean_object* v___y_95_ = _args[21];
lean_object* v___y_96_ = _args[22];
lean_object* v___y_97_ = _args[23];
_start:
{
uint8_t v___x_1958__boxed_98_; uint8_t v___x_1959__boxed_99_; uint8_t v___x_1960__boxed_100_; lean_object* v_res_101_; 
v___x_1958__boxed_98_ = lean_unbox(v___x_84_);
v___x_1959__boxed_99_ = lean_unbox(v___x_85_);
v___x_1960__boxed_100_ = lean_unbox(v___x_86_);
v_res_101_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(v___x_74_, v_a_75_, v___x_76_, v_xs_77_, v___x_78_, v_a_79_, v_a_80_, v___x_81_, v___x_82_, v_00_u03b2_83_, v___x_1958__boxed_98_, v___x_1959__boxed_99_, v___x_1960__boxed_100_, v___x_87_, v_f_88_, v_g_89_, v_h_90_, v___x_91_, v_f_x27_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_xs_77_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(lean_object* v_k_102_, lean_object* v_b_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
lean_inc(v___y_105_);
lean_inc_ref(v___y_104_);
v___x_109_ = lean_apply_6(v_k_102_, v_b_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_110_, lean_object* v_b_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(v_k_110_, v_b_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(lean_object* v_name_118_, uint8_t v_bi_119_, lean_object* v_type_120_, lean_object* v_k_121_, uint8_t v_kind_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; 
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_128_, 0, v_k_121_);
v___x_129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_118_, v_bi_119_, v_type_120_, v___f_128_, v_kind_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_129_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_129_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___boxed(lean_object* v_name_146_, lean_object* v_bi_147_, lean_object* v_type_148_, lean_object* v_k_149_, lean_object* v_kind_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
uint8_t v_bi_boxed_156_; uint8_t v_kind_boxed_157_; lean_object* v_res_158_; 
v_bi_boxed_156_ = lean_unbox(v_bi_147_);
v_kind_boxed_157_ = lean_unbox(v_kind_150_);
v_res_158_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_146_, v_bi_boxed_156_, v_type_148_, v_k_149_, v_kind_boxed_157_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(lean_object* v_name_159_, lean_object* v_type_160_, lean_object* v_k_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; 
v___x_167_ = 0;
v___x_168_ = 0;
v___x_169_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_159_, v___x_167_, v_type_160_, v_k_161_, v___x_168_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg___boxed(lean_object* v_name_170_, lean_object* v_type_171_, lean_object* v_k_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_170_, v_type_171_, v_k_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(lean_object* v_xs_185_, lean_object* v___x_186_, uint8_t v___x_187_, uint8_t v___x_188_, uint8_t v___x_189_, lean_object* v_f_190_, lean_object* v_g_191_, lean_object* v_a_192_, lean_object* v___x_193_, lean_object* v_a_194_, lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v___x_197_, lean_object* v___x_198_, lean_object* v_00_u03b2_199_, lean_object* v_h_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_mkForallFVars(v_xs_185_, v___x_186_, v___x_187_, v___x_188_, v___x_188_, v___x_189_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = lean_unsigned_to_nat(2u);
v___x_209_ = lean_mk_empty_array_with_capacity(v___x_208_);
lean_inc_ref(v_f_190_);
v___x_210_ = lean_array_push(v___x_209_, v_f_190_);
lean_inc_ref(v_g_191_);
v___x_211_ = lean_array_push(v___x_210_, v_g_191_);
v___x_212_ = l_Lean_Meta_mkLambdaFVars(v___x_211_, v_a_207_, v___x_187_, v___x_188_, v___x_187_, v___x_188_, v___x_189_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec_ref(v___x_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc_n(v_a_213_, 2);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0));
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1));
lean_inc(v_a_192_);
v___x_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_216_, 0, v_a_192_);
lean_ctor_set(v___x_216_, 1, v___x_193_);
lean_inc_ref(v___x_216_);
v___x_217_ = l_Lean_mkConst(v___x_215_, v___x_216_);
lean_inc_ref(v_a_194_);
v___x_218_ = l_Lean_mkAppB(v___x_217_, v_a_194_, v_a_213_);
v___x_219_ = lean_box(v___x_187_);
v___x_220_ = lean_box(v___x_188_);
v___x_221_ = lean_box(v___x_189_);
lean_inc_ref(v___x_218_);
v___f_222_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed), 24, 18);
lean_closure_set(v___f_222_, 0, v___x_214_);
lean_closure_set(v___f_222_, 1, v_a_192_);
lean_closure_set(v___f_222_, 2, v___x_195_);
lean_closure_set(v___f_222_, 3, v_xs_185_);
lean_closure_set(v___f_222_, 4, v___x_196_);
lean_closure_set(v___f_222_, 5, v_a_194_);
lean_closure_set(v___f_222_, 6, v_a_213_);
lean_closure_set(v___f_222_, 7, v___x_197_);
lean_closure_set(v___f_222_, 8, v___x_198_);
lean_closure_set(v___f_222_, 9, v_00_u03b2_199_);
lean_closure_set(v___f_222_, 10, v___x_219_);
lean_closure_set(v___f_222_, 11, v___x_220_);
lean_closure_set(v___f_222_, 12, v___x_221_);
lean_closure_set(v___f_222_, 13, v___x_216_);
lean_closure_set(v___f_222_, 14, v_f_190_);
lean_closure_set(v___f_222_, 15, v_g_191_);
lean_closure_set(v___f_222_, 16, v_h_200_);
lean_closure_set(v___f_222_, 17, v___x_218_);
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3));
v___x_224_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_223_, v___x_218_, v___f_222_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
return v___x_224_;
}
else
{
lean_dec_ref(v_h_200_);
lean_dec_ref(v_00_u03b2_199_);
lean_dec(v___x_198_);
lean_dec(v___x_197_);
lean_dec(v___x_196_);
lean_dec(v___x_195_);
lean_dec_ref(v_a_194_);
lean_dec(v___x_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_g_191_);
lean_dec_ref(v_f_190_);
lean_dec_ref(v_xs_185_);
return v___x_212_;
}
}
else
{
lean_dec_ref(v_h_200_);
lean_dec_ref(v_00_u03b2_199_);
lean_dec(v___x_198_);
lean_dec(v___x_197_);
lean_dec(v___x_196_);
lean_dec(v___x_195_);
lean_dec_ref(v_a_194_);
lean_dec(v___x_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_g_191_);
lean_dec_ref(v_f_190_);
lean_dec_ref(v_xs_185_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed(lean_object** _args){
lean_object* v_xs_225_ = _args[0];
lean_object* v___x_226_ = _args[1];
lean_object* v___x_227_ = _args[2];
lean_object* v___x_228_ = _args[3];
lean_object* v___x_229_ = _args[4];
lean_object* v_f_230_ = _args[5];
lean_object* v_g_231_ = _args[6];
lean_object* v_a_232_ = _args[7];
lean_object* v___x_233_ = _args[8];
lean_object* v_a_234_ = _args[9];
lean_object* v___x_235_ = _args[10];
lean_object* v___x_236_ = _args[11];
lean_object* v___x_237_ = _args[12];
lean_object* v___x_238_ = _args[13];
lean_object* v_00_u03b2_239_ = _args[14];
lean_object* v_h_240_ = _args[15];
lean_object* v___y_241_ = _args[16];
lean_object* v___y_242_ = _args[17];
lean_object* v___y_243_ = _args[18];
lean_object* v___y_244_ = _args[19];
lean_object* v___y_245_ = _args[20];
_start:
{
uint8_t v___x_2195__boxed_246_; uint8_t v___x_2196__boxed_247_; uint8_t v___x_2197__boxed_248_; lean_object* v_res_249_; 
v___x_2195__boxed_246_ = lean_unbox(v___x_227_);
v___x_2196__boxed_247_ = lean_unbox(v___x_228_);
v___x_2197__boxed_248_ = lean_unbox(v___x_229_);
v_res_249_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(v_xs_225_, v___x_226_, v___x_2195__boxed_246_, v___x_2196__boxed_247_, v___x_2197__boxed_248_, v_f_230_, v_g_231_, v_a_232_, v___x_233_, v_a_234_, v___x_235_, v___x_236_, v___x_237_, v___x_238_, v_00_u03b2_239_, v_h_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(lean_object* v_a_256_, lean_object* v_f_257_, lean_object* v_xs_258_, lean_object* v_00_u03b2_259_, uint8_t v___x_260_, uint8_t v___x_261_, uint8_t v___x_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v_g_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1));
v___x_274_ = lean_box(0);
v___x_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_275_, 0, v_a_256_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
lean_inc_ref(v___x_275_);
v___x_276_ = l_Lean_mkConst(v___x_273_, v___x_275_);
lean_inc_ref(v_f_257_);
v___x_277_ = l_Lean_mkAppN(v_f_257_, v_xs_258_);
lean_inc_ref(v_g_267_);
v___x_278_ = l_Lean_mkAppN(v_g_267_, v_xs_258_);
lean_inc_ref(v_00_u03b2_259_);
v___x_279_ = l_Lean_mkApp3(v___x_276_, v_00_u03b2_259_, v___x_277_, v___x_278_);
lean_inc_ref(v___x_279_);
v___x_280_ = l_Lean_Meta_mkForallFVars(v_xs_258_, v___x_279_, v___x_260_, v___x_261_, v___x_261_, v___x_262_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___x_287_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3));
v___x_283_ = lean_box(v___x_260_);
v___x_284_ = lean_box(v___x_261_);
v___x_285_ = lean_box(v___x_262_);
v___f_286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed), 21, 15);
lean_closure_set(v___f_286_, 0, v_xs_258_);
lean_closure_set(v___f_286_, 1, v___x_279_);
lean_closure_set(v___f_286_, 2, v___x_283_);
lean_closure_set(v___f_286_, 3, v___x_284_);
lean_closure_set(v___f_286_, 4, v___x_285_);
lean_closure_set(v___f_286_, 5, v_f_257_);
lean_closure_set(v___f_286_, 6, v_g_267_);
lean_closure_set(v___f_286_, 7, v_a_263_);
lean_closure_set(v___f_286_, 8, v___x_274_);
lean_closure_set(v___f_286_, 9, v_a_264_);
lean_closure_set(v___f_286_, 10, v___x_275_);
lean_closure_set(v___f_286_, 11, v___x_265_);
lean_closure_set(v___f_286_, 12, v___x_282_);
lean_closure_set(v___f_286_, 13, v___x_266_);
lean_closure_set(v___f_286_, 14, v_00_u03b2_259_);
v___x_287_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_282_, v_a_281_, v___f_286_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
return v___x_287_;
}
else
{
lean_dec_ref(v___x_279_);
lean_dec_ref_known(v___x_275_, 2);
lean_dec_ref(v_g_267_);
lean_dec(v___x_266_);
lean_dec(v___x_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_00_u03b2_259_);
lean_dec_ref(v_xs_258_);
lean_dec_ref(v_f_257_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed(lean_object** _args){
lean_object* v_a_288_ = _args[0];
lean_object* v_f_289_ = _args[1];
lean_object* v_xs_290_ = _args[2];
lean_object* v_00_u03b2_291_ = _args[3];
lean_object* v___x_292_ = _args[4];
lean_object* v___x_293_ = _args[5];
lean_object* v___x_294_ = _args[6];
lean_object* v_a_295_ = _args[7];
lean_object* v_a_296_ = _args[8];
lean_object* v___x_297_ = _args[9];
lean_object* v___x_298_ = _args[10];
lean_object* v_g_299_ = _args[11];
lean_object* v___y_300_ = _args[12];
lean_object* v___y_301_ = _args[13];
lean_object* v___y_302_ = _args[14];
lean_object* v___y_303_ = _args[15];
lean_object* v___y_304_ = _args[16];
_start:
{
uint8_t v___x_2301__boxed_305_; uint8_t v___x_2302__boxed_306_; uint8_t v___x_2303__boxed_307_; lean_object* v_res_308_; 
v___x_2301__boxed_305_ = lean_unbox(v___x_292_);
v___x_2302__boxed_306_ = lean_unbox(v___x_293_);
v___x_2303__boxed_307_ = lean_unbox(v___x_294_);
v_res_308_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(v_a_288_, v_f_289_, v_xs_290_, v_00_u03b2_291_, v___x_2301__boxed_305_, v___x_2302__boxed_306_, v___x_2303__boxed_307_, v_a_295_, v_a_296_, v___x_297_, v___x_298_, v_g_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(lean_object* v_a_312_, lean_object* v_xs_313_, lean_object* v_00_u03b2_314_, uint8_t v___x_315_, uint8_t v___x_316_, uint8_t v___x_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v___x_320_, lean_object* v_f_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___f_331_; lean_object* v___x_332_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1));
v___x_328_ = lean_box(v___x_315_);
v___x_329_ = lean_box(v___x_316_);
v___x_330_ = lean_box(v___x_317_);
lean_inc_ref(v_a_319_);
v___f_331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed), 17, 11);
lean_closure_set(v___f_331_, 0, v_a_312_);
lean_closure_set(v___f_331_, 1, v_f_321_);
lean_closure_set(v___f_331_, 2, v_xs_313_);
lean_closure_set(v___f_331_, 3, v_00_u03b2_314_);
lean_closure_set(v___f_331_, 4, v___x_328_);
lean_closure_set(v___f_331_, 5, v___x_329_);
lean_closure_set(v___f_331_, 6, v___x_330_);
lean_closure_set(v___f_331_, 7, v_a_318_);
lean_closure_set(v___f_331_, 8, v_a_319_);
lean_closure_set(v___f_331_, 9, v___x_320_);
lean_closure_set(v___f_331_, 10, v___x_327_);
v___x_332_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_327_, v_a_319_, v___f_331_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed(lean_object* v_a_333_, lean_object* v_xs_334_, lean_object* v_00_u03b2_335_, lean_object* v___x_336_, lean_object* v___x_337_, lean_object* v___x_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v___x_341_, lean_object* v_f_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
uint8_t v___x_2383__boxed_348_; uint8_t v___x_2384__boxed_349_; uint8_t v___x_2385__boxed_350_; lean_object* v_res_351_; 
v___x_2383__boxed_348_ = lean_unbox(v___x_336_);
v___x_2384__boxed_349_ = lean_unbox(v___x_337_);
v___x_2385__boxed_350_ = lean_unbox(v___x_338_);
v_res_351_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(v_a_333_, v_xs_334_, v_00_u03b2_335_, v___x_2383__boxed_348_, v___x_2384__boxed_349_, v___x_2385__boxed_350_, v_a_339_, v_a_340_, v___x_341_, v_f_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(lean_object* v_xs_355_, lean_object* v_00_u03b2_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
uint8_t v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; 
v___x_362_ = 0;
v___x_363_ = 1;
v___x_364_ = 1;
lean_inc_ref(v_00_u03b2_356_);
v___x_365_ = l_Lean_Meta_mkForallFVars(v_xs_355_, v_00_u03b2_356_, v___x_362_, v___x_363_, v___x_363_, v___x_364_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_367_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
lean_inc_ref(v_00_u03b2_356_);
v___x_367_ = l_Lean_Meta_getLevel(v_00_u03b2_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
lean_inc(v_a_366_);
v___x_369_ = l_Lean_Meta_getLevel(v_a_366_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___f_375_; lean_object* v___x_376_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1));
v___x_372_ = lean_box(v___x_362_);
v___x_373_ = lean_box(v___x_363_);
v___x_374_ = lean_box(v___x_364_);
lean_inc(v_a_366_);
v___f_375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed), 15, 9);
lean_closure_set(v___f_375_, 0, v_a_368_);
lean_closure_set(v___f_375_, 1, v_xs_355_);
lean_closure_set(v___f_375_, 2, v_00_u03b2_356_);
lean_closure_set(v___f_375_, 3, v___x_372_);
lean_closure_set(v___f_375_, 4, v___x_373_);
lean_closure_set(v___f_375_, 5, v___x_374_);
lean_closure_set(v___f_375_, 6, v_a_370_);
lean_closure_set(v___f_375_, 7, v_a_366_);
lean_closure_set(v___f_375_, 8, v___x_371_);
v___x_376_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_371_, v_a_366_, v___f_375_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_376_;
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_a_368_);
lean_dec(v_a_366_);
lean_dec_ref(v_00_u03b2_356_);
lean_dec_ref(v_xs_355_);
v_a_377_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_369_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_369_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_366_);
lean_dec_ref(v_00_u03b2_356_);
lean_dec_ref(v_xs_355_);
v_a_385_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_367_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_367_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03b2_356_);
lean_dec_ref(v_xs_355_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___boxed(lean_object* v_xs_393_, lean_object* v_00_u03b2_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(v_xs_393_, v_00_u03b2_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(lean_object* v_00_u03b1_401_, lean_object* v_name_402_, uint8_t v_bi_403_, lean_object* v_type_404_, lean_object* v_k_405_, uint8_t v_kind_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_402_, v_bi_403_, v_type_404_, v_k_405_, v_kind_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___boxed(lean_object* v_00_u03b1_413_, lean_object* v_name_414_, lean_object* v_bi_415_, lean_object* v_type_416_, lean_object* v_k_417_, lean_object* v_kind_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v_bi_boxed_424_; uint8_t v_kind_boxed_425_; lean_object* v_res_426_; 
v_bi_boxed_424_ = lean_unbox(v_bi_415_);
v_kind_boxed_425_ = lean_unbox(v_kind_418_);
v_res_426_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(v_00_u03b1_413_, v_name_414_, v_bi_boxed_424_, v_type_416_, v_k_417_, v_kind_boxed_425_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(lean_object* v_00_u03b1_427_, lean_object* v_name_428_, lean_object* v_type_429_, lean_object* v_k_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_428_, v_type_429_, v_k_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___boxed(lean_object* v_00_u03b1_437_, lean_object* v_name_438_, lean_object* v_type_439_, lean_object* v_k_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(v_00_u03b1_437_, v_name_438_, v_type_439_, v_k_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_447_, lean_object* v_vals_448_, lean_object* v_i_449_, lean_object* v_k_450_){
_start:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_array_get_size(v_keys_447_);
v___x_452_ = lean_nat_dec_lt(v_i_449_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v_i_449_);
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v_k_x27_454_; uint8_t v___x_455_; 
v_k_x27_454_ = lean_array_fget_borrowed(v_keys_447_, v_i_449_);
v___x_455_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_450_, v_k_x27_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_add(v_i_449_, v___x_456_);
lean_dec(v_i_449_);
v_i_449_ = v___x_457_;
goto _start;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_array_fget_borrowed(v_vals_448_, v_i_449_);
lean_dec(v_i_449_);
lean_inc(v___x_459_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_461_, lean_object* v_vals_462_, lean_object* v_i_463_, lean_object* v_k_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_461_, v_vals_462_, v_i_463_, v_k_464_);
lean_dec_ref(v_k_464_);
lean_dec_ref(v_vals_462_);
lean_dec_ref(v_keys_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(lean_object* v_x_466_, size_t v_x_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v_es_469_; lean_object* v___x_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v_j_473_; lean_object* v___x_474_; 
v_es_469_ = lean_ctor_get(v_x_466_, 0);
v___x_470_ = lean_box(2);
v___x_471_ = ((size_t)31ULL);
v___x_472_ = lean_usize_land(v_x_467_, v___x_471_);
v_j_473_ = lean_usize_to_nat(v___x_472_);
v___x_474_ = lean_array_get_borrowed(v___x_470_, v_es_469_, v_j_473_);
lean_dec(v_j_473_);
switch(lean_obj_tag(v___x_474_))
{
case 0:
{
lean_object* v_key_475_; lean_object* v_val_476_; uint8_t v___x_477_; 
v_key_475_ = lean_ctor_get(v___x_474_, 0);
v_val_476_ = lean_ctor_get(v___x_474_, 1);
v___x_477_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_468_, v_key_475_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
lean_inc(v_val_476_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_val_476_);
return v___x_479_;
}
}
case 1:
{
lean_object* v_node_480_; size_t v___x_481_; size_t v___x_482_; 
v_node_480_ = lean_ctor_get(v___x_474_, 0);
v___x_481_ = ((size_t)5ULL);
v___x_482_ = lean_usize_shift_right(v_x_467_, v___x_481_);
v_x_466_ = v_node_480_;
v_x_467_ = v___x_482_;
goto _start;
}
default: 
{
lean_object* v___x_484_; 
v___x_484_ = lean_box(0);
return v___x_484_;
}
}
}
else
{
lean_object* v_ks_485_; lean_object* v_vs_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_ks_485_ = lean_ctor_get(v_x_466_, 0);
v_vs_486_ = lean_ctor_get(v_x_466_, 1);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_ks_485_, v_vs_486_, v___x_487_, v_x_468_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___boxed(lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
size_t v_x_6870__boxed_492_; lean_object* v_res_493_; 
v_x_6870__boxed_492_ = lean_unbox_usize(v_x_490_);
lean_dec(v_x_490_);
v_res_493_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_489_, v_x_6870__boxed_492_, v_x_491_);
lean_dec_ref(v_x_491_);
lean_dec_ref(v_x_489_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
uint64_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_495_);
v___x_497_ = lean_uint64_to_usize(v___x_496_);
v___x_498_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_494_, v___x_497_, v_x_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg___boxed(lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_499_, v_x_500_);
lean_dec_ref(v_x_500_);
lean_dec_ref(v_x_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
lean_object* v_ks_506_; lean_object* v_vs_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_531_; 
v_ks_506_ = lean_ctor_get(v_x_502_, 0);
v_vs_507_ = lean_ctor_get(v_x_502_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_531_ == 0)
{
v___x_509_ = v_x_502_;
v_isShared_510_ = v_isSharedCheck_531_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_vs_507_);
lean_inc(v_ks_506_);
lean_dec(v_x_502_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_531_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_array_get_size(v_ks_506_);
v___x_512_ = lean_nat_dec_lt(v_x_503_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_dec(v_x_503_);
v___x_513_ = lean_array_push(v_ks_506_, v_x_504_);
v___x_514_ = lean_array_push(v_vs_507_, v_x_505_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_514_);
lean_ctor_set(v___x_509_, 0, v___x_513_);
v___x_516_ = v___x_509_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
else
{
lean_object* v_k_x27_518_; uint8_t v___x_519_; 
v_k_x27_518_ = lean_array_fget_borrowed(v_ks_506_, v_x_503_);
v___x_519_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_504_, v_k_x27_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_521_; 
if (v_isShared_510_ == 0)
{
v___x_521_ = v___x_509_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_ks_506_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_vs_507_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_x_503_, v___x_522_);
lean_dec(v_x_503_);
v_x_502_ = v___x_521_;
v_x_503_ = v___x_523_;
goto _start;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_526_ = lean_array_fset(v_ks_506_, v_x_503_, v_x_504_);
v___x_527_ = lean_array_fset(v_vs_507_, v_x_503_, v_x_505_);
lean_dec(v_x_503_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_527_);
lean_ctor_set(v___x_509_, 0, v___x_526_);
v___x_529_ = v___x_509_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(lean_object* v_n_532_, lean_object* v_k_533_, lean_object* v_v_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_n_532_, v___x_535_, v_k_533_, v_v_534_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(lean_object* v_x_538_, size_t v_x_539_, size_t v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v_es_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v_j_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_es_543_ = lean_ctor_get(v_x_538_, 0);
v___x_544_ = ((size_t)31ULL);
v___x_545_ = lean_usize_land(v_x_539_, v___x_544_);
v_j_546_ = lean_usize_to_nat(v___x_545_);
v___x_547_ = lean_array_get_size(v_es_543_);
v___x_548_ = lean_nat_dec_lt(v_j_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec(v_j_546_);
lean_dec(v_x_542_);
lean_dec_ref(v_x_541_);
return v_x_538_;
}
else
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_587_; 
lean_inc_ref(v_es_543_);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_x_538_, 0);
lean_dec(v_unused_588_);
v___x_550_ = v_x_538_;
v_isShared_551_ = v_isSharedCheck_587_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_x_538_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_587_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_v_552_; lean_object* v___x_553_; lean_object* v_xs_x27_554_; lean_object* v___y_556_; 
v_v_552_ = lean_array_fget(v_es_543_, v_j_546_);
v___x_553_ = lean_box(0);
v_xs_x27_554_ = lean_array_fset(v_es_543_, v_j_546_, v___x_553_);
switch(lean_obj_tag(v_v_552_))
{
case 0:
{
lean_object* v_key_561_; lean_object* v_val_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_572_; 
v_key_561_ = lean_ctor_get(v_v_552_, 0);
v_val_562_ = lean_ctor_get(v_v_552_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_v_552_);
if (v_isSharedCheck_572_ == 0)
{
v___x_564_ = v_v_552_;
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_val_562_);
lean_inc(v_key_561_);
lean_dec(v_v_552_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___x_566_; 
v___x_566_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_541_, v_key_561_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_del_object(v___x_564_);
v___x_567_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_561_, v_val_562_, v_x_541_, v_x_542_);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
v___y_556_ = v___x_568_;
goto v___jp_555_;
}
else
{
lean_object* v___x_570_; 
lean_dec(v_val_562_);
lean_dec(v_key_561_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v_x_542_);
lean_ctor_set(v___x_564_, 0, v_x_541_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_x_541_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_x_542_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v___y_556_ = v___x_570_;
goto v___jp_555_;
}
}
}
}
case 1:
{
lean_object* v_node_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_585_; 
v_node_573_ = lean_ctor_get(v_v_552_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_v_552_);
if (v_isSharedCheck_585_ == 0)
{
v___x_575_ = v_v_552_;
v_isShared_576_ = v_isSharedCheck_585_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_node_573_);
lean_dec(v_v_552_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_585_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_577_ = ((size_t)5ULL);
v___x_578_ = lean_usize_shift_right(v_x_539_, v___x_577_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_x_540_, v___x_579_);
v___x_581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_node_573_, v___x_578_, v___x_580_, v_x_541_, v_x_542_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_581_);
v___x_583_ = v___x_575_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v___y_556_ = v___x_583_;
goto v___jp_555_;
}
}
}
default: 
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_x_541_);
lean_ctor_set(v___x_586_, 1, v_x_542_);
v___y_556_ = v___x_586_;
goto v___jp_555_;
}
}
v___jp_555_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_array_fset(v_xs_x27_554_, v_j_546_, v___y_556_);
lean_dec(v_j_546_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_557_);
v___x_559_ = v___x_550_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
else
{
lean_object* v_ks_589_; lean_object* v_vs_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_610_; 
v_ks_589_ = lean_ctor_get(v_x_538_, 0);
v_vs_590_ = lean_ctor_get(v_x_538_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_610_ == 0)
{
v___x_592_ = v_x_538_;
v_isShared_593_ = v_isSharedCheck_610_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_vs_590_);
lean_inc(v_ks_589_);
lean_dec(v_x_538_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_610_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_ks_589_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_vs_590_);
v___x_595_ = v_reuseFailAlloc_609_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v_newNode_596_; uint8_t v___y_598_; size_t v___x_604_; uint8_t v___x_605_; 
v_newNode_596_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v___x_595_, v_x_541_, v_x_542_);
v___x_604_ = ((size_t)7ULL);
v___x_605_ = lean_usize_dec_le(v___x_604_, v_x_540_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_596_);
v___x_607_ = lean_unsigned_to_nat(4u);
v___x_608_ = lean_nat_dec_lt(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___y_598_ = v___x_608_;
goto v___jp_597_;
}
else
{
v___y_598_ = v___x_605_;
goto v___jp_597_;
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_object* v_ks_599_; lean_object* v_vs_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_ks_599_ = lean_ctor_get(v_newNode_596_, 0);
lean_inc_ref(v_ks_599_);
v_vs_600_ = lean_ctor_get(v_newNode_596_, 1);
lean_inc_ref(v_vs_600_);
lean_dec_ref(v_newNode_596_);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0);
v___x_603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_x_540_, v_ks_599_, v_vs_600_, v___x_601_, v___x_602_);
lean_dec_ref(v_vs_600_);
lean_dec_ref(v_ks_599_);
return v___x_603_;
}
else
{
return v_newNode_596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(size_t v_depth_611_, lean_object* v_keys_612_, lean_object* v_vals_613_, lean_object* v_i_614_, lean_object* v_entries_615_){
_start:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_array_get_size(v_keys_612_);
v___x_617_ = lean_nat_dec_lt(v_i_614_, v___x_616_);
if (v___x_617_ == 0)
{
lean_dec(v_i_614_);
return v_entries_615_;
}
else
{
lean_object* v_k_618_; lean_object* v_v_619_; uint64_t v___x_620_; size_t v_h_621_; size_t v___x_622_; lean_object* v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; size_t v_h_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_k_618_ = lean_array_fget_borrowed(v_keys_612_, v_i_614_);
v_v_619_ = lean_array_fget_borrowed(v_vals_613_, v_i_614_);
v___x_620_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_618_);
v_h_621_ = lean_uint64_to_usize(v___x_620_);
v___x_622_ = ((size_t)5ULL);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_sub(v_depth_611_, v___x_624_);
v___x_626_ = lean_usize_mul(v___x_622_, v___x_625_);
v_h_627_ = lean_usize_shift_right(v_h_621_, v___x_626_);
v___x_628_ = lean_nat_add(v_i_614_, v___x_623_);
lean_dec(v_i_614_);
lean_inc(v_v_619_);
lean_inc(v_k_618_);
v___x_629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_entries_615_, v_h_627_, v_depth_611_, v_k_618_, v_v_619_);
v_i_614_ = v___x_628_;
v_entries_615_ = v___x_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_631_, lean_object* v_keys_632_, lean_object* v_vals_633_, lean_object* v_i_634_, lean_object* v_entries_635_){
_start:
{
size_t v_depth_boxed_636_; lean_object* v_res_637_; 
v_depth_boxed_636_ = lean_unbox_usize(v_depth_631_);
lean_dec(v_depth_631_);
v_res_637_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_boxed_636_, v_keys_632_, v_vals_633_, v_i_634_, v_entries_635_);
lean_dec_ref(v_vals_633_);
lean_dec_ref(v_keys_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___boxed(lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
size_t v_x_7005__boxed_643_; size_t v_x_7006__boxed_644_; lean_object* v_res_645_; 
v_x_7005__boxed_643_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_x_7006__boxed_644_ = lean_unbox_usize(v_x_640_);
lean_dec(v_x_640_);
v_res_645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_638_, v_x_7005__boxed_643_, v_x_7006__boxed_644_, v_x_641_, v_x_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
uint64_t v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v___x_649_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_647_);
v___x_650_ = lean_uint64_to_usize(v___x_649_);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_646_, v___x_650_, v___x_651_, v_x_647_, v_x_648_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(lean_object* v_e_653_, lean_object* v_xs_654_, lean_object* v_b_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; 
lean_inc(v_a_660_);
lean_inc_ref(v_a_659_);
lean_inc(v_a_658_);
lean_inc_ref(v_a_657_);
v___x_662_ = lean_infer_type(v_e_653_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_699_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_699_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_699_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_699_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v_funext_668_; lean_object* v___x_669_; 
v___x_667_ = lean_st_ref_get(v_a_656_);
v_funext_668_ = lean_ctor_get(v___x_667_, 3);
lean_inc_ref(v_funext_668_);
lean_dec(v___x_667_);
v___x_669_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_funext_668_, v_a_663_);
lean_dec_ref(v_funext_668_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_672_; 
lean_dec(v_a_663_);
lean_dec_ref(v_b_655_);
lean_dec_ref(v_xs_654_);
v_val_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v___x_669_, 1);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v_val_670_);
v___x_672_ = v___x_665_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_val_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_object* v___x_674_; 
lean_dec(v___x_669_);
lean_del_object(v___x_665_);
lean_inc(v_a_660_);
lean_inc_ref(v_a_659_);
lean_inc(v_a_658_);
lean_inc_ref(v_a_657_);
v___x_674_ = lean_infer_type(v_b_655_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(v_xs_654_, v_a_675_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_698_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_698_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_698_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_698_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v_numSteps_682_; lean_object* v_persistentCache_683_; lean_object* v_transientCache_684_; lean_object* v_funext_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_697_; 
v___x_681_ = lean_st_ref_take(v_a_656_);
v_numSteps_682_ = lean_ctor_get(v___x_681_, 0);
v_persistentCache_683_ = lean_ctor_get(v___x_681_, 1);
v_transientCache_684_ = lean_ctor_get(v___x_681_, 2);
v_funext_685_ = lean_ctor_get(v___x_681_, 3);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_697_ == 0)
{
v___x_687_ = v___x_681_;
v_isShared_688_ = v_isSharedCheck_697_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_funext_685_);
lean_inc(v_transientCache_684_);
lean_inc(v_persistentCache_683_);
lean_inc(v_numSteps_682_);
lean_dec(v___x_681_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_697_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
lean_inc(v_a_677_);
v___x_689_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_funext_685_, v_a_663_, v_a_677_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 3, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_numSteps_682_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_persistentCache_683_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_transientCache_684_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v___x_689_);
v___x_691_ = v_reuseFailAlloc_696_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = lean_st_ref_set(v_a_656_, v___x_691_);
if (v_isShared_680_ == 0)
{
v___x_694_ = v___x_679_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_677_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_dec(v_a_663_);
return v___x_676_;
}
}
else
{
lean_dec(v_a_663_);
lean_dec_ref(v_xs_654_);
return v___x_674_;
}
}
}
}
else
{
lean_dec_ref(v_b_655_);
lean_dec_ref(v_xs_654_);
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg___boxed(lean_object* v_e_700_, lean_object* v_xs_701_, lean_object* v_b_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_700_, v_xs_701_, v_b_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(lean_object* v_e_710_, lean_object* v_xs_711_, lean_object* v_b_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_710_, v_xs_711_, v_b_712_, v_a_715_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___boxed(lean_object* v_e_724_, lean_object* v_xs_725_, lean_object* v_b_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(v_e_724_, v_xs_725_, v_b_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(lean_object* v_00_u03b2_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___boxed(lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(v_00_u03b2_742_, v_x_743_, v_x_744_);
lean_dec_ref(v_x_744_);
lean_dec_ref(v_x_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1(lean_object* v_00_u03b2_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_x_747_, v_x_748_, v_x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(lean_object* v_00_u03b2_751_, lean_object* v_x_752_, size_t v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_752_, v_x_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___boxed(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
size_t v_x_7268__boxed_760_; lean_object* v_res_761_; 
v_x_7268__boxed_760_ = lean_unbox_usize(v_x_758_);
lean_dec(v_x_758_);
v_res_761_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(v_00_u03b2_756_, v_x_757_, v_x_7268__boxed_760_, v_x_759_);
lean_dec_ref(v_x_759_);
lean_dec_ref(v_x_757_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(lean_object* v_00_u03b2_762_, lean_object* v_x_763_, size_t v_x_764_, size_t v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_763_, v_x_764_, v_x_765_, v_x_766_, v_x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___boxed(lean_object* v_00_u03b2_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
size_t v_x_7279__boxed_775_; size_t v_x_7280__boxed_776_; lean_object* v_res_777_; 
v_x_7279__boxed_775_ = lean_unbox_usize(v_x_771_);
lean_dec(v_x_771_);
v_x_7280__boxed_776_ = lean_unbox_usize(v_x_772_);
lean_dec(v_x_772_);
v_res_777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(v_00_u03b2_769_, v_x_770_, v_x_7279__boxed_775_, v_x_7280__boxed_776_, v_x_773_, v_x_774_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_778_, lean_object* v_keys_779_, lean_object* v_vals_780_, lean_object* v_heq_781_, lean_object* v_i_782_, lean_object* v_k_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_779_, v_vals_780_, v_i_782_, v_k_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_785_, lean_object* v_keys_786_, lean_object* v_vals_787_, lean_object* v_heq_788_, lean_object* v_i_789_, lean_object* v_k_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(v_00_u03b2_785_, v_keys_786_, v_vals_787_, v_heq_788_, v_i_789_, v_k_790_);
lean_dec_ref(v_k_790_);
lean_dec_ref(v_vals_787_);
lean_dec_ref(v_keys_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_792_, lean_object* v_n_793_, lean_object* v_k_794_, lean_object* v_v_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v_n_793_, v_k_794_, v_v_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_797_, size_t v_depth_798_, lean_object* v_keys_799_, lean_object* v_vals_800_, lean_object* v_heq_801_, lean_object* v_i_802_, lean_object* v_entries_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_798_, v_keys_799_, v_vals_800_, v_i_802_, v_entries_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_805_, lean_object* v_depth_806_, lean_object* v_keys_807_, lean_object* v_vals_808_, lean_object* v_heq_809_, lean_object* v_i_810_, lean_object* v_entries_811_){
_start:
{
size_t v_depth_boxed_812_; lean_object* v_res_813_; 
v_depth_boxed_812_ = lean_unbox_usize(v_depth_806_);
lean_dec(v_depth_806_);
v_res_813_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(v_00_u03b2_805_, v_depth_boxed_812_, v_keys_807_, v_vals_808_, v_heq_809_, v_i_810_, v_entries_811_);
lean_dec_ref(v_vals_808_);
lean_dec_ref(v_keys_807_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_x_815_, v_x_816_, v_x_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(lean_object* v_simpBody_820_, lean_object* v_e_821_, lean_object* v_xs_822_, lean_object* v_b_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; 
lean_inc(v_a_832_);
lean_inc_ref(v_a_831_);
lean_inc(v_a_830_);
lean_inc_ref(v_a_829_);
lean_inc(v_a_828_);
lean_inc_ref(v_a_827_);
lean_inc(v_a_826_);
lean_inc_ref(v_a_825_);
lean_inc(v_a_824_);
lean_inc_ref(v_b_823_);
v___x_834_ = lean_apply_11(v_simpBody_820_, v_b_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, lean_box(0));
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_905_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_905_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_905_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_905_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
if (lean_obj_tag(v_a_835_) == 0)
{
uint8_t v_contextDependent_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
lean_dec_ref(v_b_823_);
lean_dec_ref(v_xs_822_);
lean_dec_ref(v_e_821_);
v_contextDependent_839_ = lean_ctor_get_uint8(v_a_835_, 1);
lean_dec_ref_known(v_a_835_, 0);
v___x_840_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_839_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_840_);
v___x_842_ = v___x_837_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
else
{
lean_object* v_e_x27_844_; lean_object* v_proof_845_; uint8_t v_contextDependent_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_837_);
v_e_x27_844_ = lean_ctor_get(v_a_835_, 0);
v_proof_845_ = lean_ctor_get(v_a_835_, 1);
v_contextDependent_846_ = lean_ctor_get_uint8(v_a_835_, sizeof(void*)*2 + 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_a_835_);
if (v_isSharedCheck_904_ == 0)
{
v___x_848_ = v_a_835_;
v_isShared_849_ = v_isSharedCheck_904_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_proof_845_);
lean_inc(v_e_x27_844_);
lean_dec(v_a_835_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_904_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
uint8_t v___x_850_; uint8_t v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; 
v___x_850_ = 0;
v___x_851_ = 1;
v___x_852_ = 1;
v___x_853_ = l_Lean_Meta_mkLambdaFVars(v_xs_822_, v_proof_845_, v___x_850_, v___x_851_, v___x_850_, v___x_851_, v___x_852_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l_Lean_Meta_mkLambdaFVars(v_xs_822_, v_e_x27_844_, v___x_850_, v___x_851_, v___x_850_, v___x_851_, v___x_852_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_856_, v_a_828_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
lean_inc_ref(v_e_821_);
v___x_859_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_821_, v_xs_822_, v_b_823_, v_a_826_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_871_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_871_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
lean_inc(v_a_858_);
v___x_864_ = l_Lean_mkApp3(v_a_860_, v_e_821_, v_a_858_, v_a_854_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v___x_864_);
lean_ctor_set(v___x_848_, 0, v_a_858_);
v___x_866_ = v___x_848_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_858_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*2 + 1, v_contextDependent_846_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*2, v___x_850_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_866_);
v___x_868_ = v___x_862_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_858_);
lean_dec(v_a_854_);
lean_del_object(v___x_848_);
lean_dec_ref(v_e_821_);
v_a_872_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_859_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_859_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_a_854_);
lean_del_object(v___x_848_);
lean_dec_ref(v_b_823_);
lean_dec_ref(v_xs_822_);
lean_dec_ref(v_e_821_);
v_a_880_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_857_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_857_);
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
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_a_854_);
lean_del_object(v___x_848_);
lean_dec_ref(v_b_823_);
lean_dec_ref(v_xs_822_);
lean_dec_ref(v_e_821_);
v_a_888_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_855_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_855_);
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
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_del_object(v___x_848_);
lean_dec_ref(v_e_x27_844_);
lean_dec_ref(v_b_823_);
lean_dec_ref(v_xs_822_);
lean_dec_ref(v_e_821_);
v_a_896_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_853_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_853_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_823_);
lean_dec_ref(v_xs_822_);
lean_dec_ref(v_e_821_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main___boxed(lean_object* v_simpBody_906_, lean_object* v_e_907_, lean_object* v_xs_908_, lean_object* v_b_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_906_, v_e_907_, v_xs_908_, v_b_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(lean_object* v_k_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v_b_927_, lean_object* v_c_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
v___x_934_ = lean_apply_12(v_k_921_, v_b_927_, v_c_928_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, lean_box(0));
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed(lean_object* v_k_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v_b_941_, lean_object* v_c_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(v_k_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v_b_941_, v_c_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(lean_object* v_e_949_, lean_object* v_k_950_, uint8_t v_cleanupAnnotations_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___f_962_; uint8_t v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
v___f_962_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_962_, 0, v_k_950_);
lean_closure_set(v___f_962_, 1, v___y_952_);
lean_closure_set(v___f_962_, 2, v___y_953_);
lean_closure_set(v___f_962_, 3, v___y_954_);
lean_closure_set(v___f_962_, 4, v___y_955_);
lean_closure_set(v___f_962_, 5, v___y_956_);
v___x_963_ = 1;
v___x_964_ = 0;
v___x_965_ = lean_box(0);
v___x_966_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_949_, v___x_963_, v___x_964_, v___x_963_, v___x_964_, v___x_965_, v___f_962_, v_cleanupAnnotations_951_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_966_) == 0)
{
return v___x_966_;
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___boxed(lean_object* v_e_975_, lean_object* v_k_976_, lean_object* v_cleanupAnnotations_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_988_; lean_object* v_res_989_; 
v_cleanupAnnotations_boxed_988_ = lean_unbox(v_cleanupAnnotations_977_);
v_res_989_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_975_, v_k_976_, v_cleanupAnnotations_boxed_988_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(lean_object* v_00_u03b1_990_, lean_object* v_e_991_, lean_object* v_k_992_, uint8_t v_cleanupAnnotations_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_991_, v_k_992_, v_cleanupAnnotations_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_e_1006_, lean_object* v_k_1007_, lean_object* v_cleanupAnnotations_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1019_; lean_object* v_res_1020_; 
v_cleanupAnnotations_boxed_1019_ = lean_unbox(v_cleanupAnnotations_1008_);
v_res_1020_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(v_00_u03b1_1005_, v_e_1006_, v_k_1007_, v_cleanupAnnotations_boxed_1019_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(lean_object* v___y_1021_, lean_object* v_transientCache_1022_, lean_object* v_funext_1023_, lean_object* v_a_x3f_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v_numSteps_1027_; lean_object* v_persistentCache_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1038_; 
v___x_1026_ = lean_st_ref_take(v___y_1021_);
v_numSteps_1027_ = lean_ctor_get(v___x_1026_, 0);
v_persistentCache_1028_ = lean_ctor_get(v___x_1026_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; lean_object* v_unused_1040_; 
v_unused_1039_ = lean_ctor_get(v___x_1026_, 3);
lean_dec(v_unused_1039_);
v_unused_1040_ = lean_ctor_get(v___x_1026_, 2);
lean_dec(v_unused_1040_);
v___x_1030_ = v___x_1026_;
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_persistentCache_1028_);
lean_inc(v_numSteps_1027_);
lean_dec(v___x_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 3, v_funext_1023_);
lean_ctor_set(v___x_1030_, 2, v_transientCache_1022_);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_numSteps_1027_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_persistentCache_1028_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_transientCache_1022_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_funext_1023_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_st_ref_set(v___y_1021_, v___x_1033_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0___boxed(lean_object* v___y_1041_, lean_object* v_transientCache_1042_, lean_object* v_funext_1043_, lean_object* v_a_x3f_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1041_, v_transientCache_1042_, v_funext_1043_, v_a_x3f_1044_);
lean_dec(v_a_x3f_1044_);
lean_dec(v___y_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(lean_object* v_simpBody_1047_, lean_object* v_e_1048_, lean_object* v_xs_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_transientCache_1063_; lean_object* v_funext_1064_; lean_object* v_a_1066_; lean_object* v___x_1077_; 
v___x_1061_ = lean_st_ref_get(v___y_1053_);
v___x_1062_ = lean_st_ref_get(v___y_1053_);
v_transientCache_1063_ = lean_ctor_get(v___x_1061_, 2);
lean_inc_ref(v_transientCache_1063_);
lean_dec(v___x_1061_);
v_funext_1064_ = lean_ctor_get(v___x_1062_, 3);
lean_inc_ref(v_funext_1064_);
lean_dec(v___x_1062_);
v___x_1077_ = l_Lean_Meta_Sym_shareCommon___redArg(v_b_1050_, v___y_1055_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_1047_, v_e_1048_, v_xs_1049_, v_a_1078_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1096_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1096_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1096_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
lean_inc(v_a_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v___x_1086_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1053_, v_transientCache_1063_, v_funext_1064_, v___x_1085_);
lean_dec_ref(v___x_1085_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v___x_1086_, 0);
lean_dec(v_unused_1094_);
v___x_1088_ = v___x_1086_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v___x_1086_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_a_1080_);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1080_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
else
{
lean_object* v_a_1097_; 
v_a_1097_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1079_, 1);
v_a_1066_ = v_a_1097_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1098_; 
lean_dec_ref(v_xs_1049_);
lean_dec_ref(v_e_1048_);
lean_dec_ref(v_simpBody_1047_);
v_a_1098_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1077_, 1);
v_a_1066_ = v_a_1098_;
goto v___jp_1065_;
}
v___jp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1053_, v_transientCache_1063_, v_funext_1064_, v___x_1067_);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1076_);
v___x_1070_ = v___x_1068_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_dec(v___x_1068_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
lean_ctor_set(v___x_1070_, 0, v_a_1066_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1066_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed(lean_object* v_simpBody_1099_, lean_object* v_e_1100_, lean_object* v_xs_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(v_simpBody_1099_, v_e_1100_, v_xs_1101_, v_b_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27(lean_object* v_simpBody_1114_, lean_object* v_e_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___f_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; 
lean_inc_ref(v_e_1115_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed), 14, 2);
lean_closure_set(v___f_1126_, 0, v_simpBody_1114_);
lean_closure_set(v___f_1126_, 1, v_e_1115_);
v___x_1127_ = 0;
v___x_1128_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_1115_, v___f_1126_, v___x_1127_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed(lean_object* v_simpBody_1129_, lean_object* v_e_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v_simpBody_1129_, v_e_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object* v_e_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLambda___closed__0));
v___x_1155_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v___x_1154_, v_e_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda___boxed(lean_object* v_e_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
return v_res_1167_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
}
#ifdef __cplusplus
}
#endif
