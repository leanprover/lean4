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
size_t lean_usize_shift_left(size_t, size_t);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1;
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
lean_dec_ref(v___x_53_);
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
lean_dec_ref(v___x_206_);
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
lean_dec_ref(v___x_212_);
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
lean_dec_ref(v___x_280_);
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
lean_dec_ref(v___x_275_);
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
lean_dec_ref(v___x_365_);
lean_inc_ref(v_00_u03b2_356_);
v___x_367_ = l_Lean_Meta_getLevel(v_00_u03b2_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref(v___x_367_);
lean_inc(v_a_366_);
v___x_369_ = l_Lean_Meta_getLevel(v_a_366_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___f_375_; lean_object* v___x_376_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_369_);
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; 
v___x_466_ = ((size_t)5ULL);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_shift_left(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_469_; size_t v___x_470_; size_t v___x_471_; 
v___x_469_ = ((size_t)1ULL);
v___x_470_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0);
v___x_471_ = lean_usize_sub(v___x_470_, v___x_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(lean_object* v_x_472_, size_t v_x_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v_es_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_496_; 
v_es_475_ = lean_ctor_get(v_x_472_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_x_472_);
if (v_isSharedCheck_496_ == 0)
{
v___x_477_ = v_x_472_;
v_isShared_478_ = v_isSharedCheck_496_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_es_475_);
lean_dec(v_x_472_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_496_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v_j_483_; lean_object* v___x_484_; 
v___x_479_ = lean_box(2);
v___x_480_ = ((size_t)5ULL);
v___x_481_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1);
v___x_482_ = lean_usize_land(v_x_473_, v___x_481_);
v_j_483_ = lean_usize_to_nat(v___x_482_);
v___x_484_ = lean_array_get(v___x_479_, v_es_475_, v_j_483_);
lean_dec(v_j_483_);
lean_dec_ref(v_es_475_);
switch(lean_obj_tag(v___x_484_))
{
case 0:
{
lean_object* v_key_485_; lean_object* v_val_486_; uint8_t v___x_487_; 
v_key_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_key_485_);
v_val_486_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_val_486_);
lean_dec_ref(v___x_484_);
v___x_487_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_474_, v_key_485_);
lean_dec(v_key_485_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec(v_val_486_);
lean_del_object(v___x_477_);
v___x_488_ = lean_box(0);
return v___x_488_;
}
else
{
lean_object* v___x_490_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set_tag(v___x_477_, 1);
lean_ctor_set(v___x_477_, 0, v_val_486_);
v___x_490_ = v___x_477_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_val_486_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
case 1:
{
lean_object* v_node_492_; size_t v___x_493_; 
lean_del_object(v___x_477_);
v_node_492_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_node_492_);
lean_dec_ref(v___x_484_);
v___x_493_ = lean_usize_shift_right(v_x_473_, v___x_480_);
v_x_472_ = v_node_492_;
v_x_473_ = v___x_493_;
goto _start;
}
default: 
{
lean_object* v___x_495_; 
lean_del_object(v___x_477_);
v___x_495_ = lean_box(0);
return v___x_495_;
}
}
}
}
else
{
lean_object* v_ks_497_; lean_object* v_vs_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_ks_497_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_ks_497_);
v_vs_498_ = lean_ctor_get(v_x_472_, 1);
lean_inc_ref(v_vs_498_);
lean_dec_ref(v_x_472_);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_ks_497_, v_vs_498_, v___x_499_, v_x_474_);
lean_dec_ref(v_vs_498_);
lean_dec_ref(v_ks_497_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___boxed(lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
size_t v_x_6888__boxed_504_; lean_object* v_res_505_; 
v_x_6888__boxed_504_ = lean_unbox_usize(v_x_502_);
lean_dec(v_x_502_);
v_res_505_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_501_, v_x_6888__boxed_504_, v_x_503_);
lean_dec_ref(v_x_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
uint64_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; 
v___x_508_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_507_);
v___x_509_ = lean_uint64_to_usize(v___x_508_);
v___x_510_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_506_, v___x_509_, v_x_507_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg___boxed(lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_511_, v_x_512_);
lean_dec_ref(v_x_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
lean_object* v_ks_518_; lean_object* v_vs_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_543_; 
v_ks_518_ = lean_ctor_get(v_x_514_, 0);
v_vs_519_ = lean_ctor_get(v_x_514_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_543_ == 0)
{
v___x_521_ = v_x_514_;
v_isShared_522_ = v_isSharedCheck_543_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_vs_519_);
lean_inc(v_ks_518_);
lean_dec(v_x_514_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_543_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_array_get_size(v_ks_518_);
v___x_524_ = lean_nat_dec_lt(v_x_515_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
lean_dec(v_x_515_);
v___x_525_ = lean_array_push(v_ks_518_, v_x_516_);
v___x_526_ = lean_array_push(v_vs_519_, v_x_517_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_526_);
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_528_ = v___x_521_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
lean_object* v_k_x27_530_; uint8_t v___x_531_; 
v_k_x27_530_ = lean_array_fget_borrowed(v_ks_518_, v_x_515_);
v___x_531_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_516_, v_k_x27_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_533_; 
if (v_isShared_522_ == 0)
{
v___x_533_ = v___x_521_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_ks_518_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_vs_519_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_x_515_, v___x_534_);
lean_dec(v_x_515_);
v_x_514_ = v___x_533_;
v_x_515_ = v___x_535_;
goto _start;
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_538_ = lean_array_fset(v_ks_518_, v_x_515_, v_x_516_);
v___x_539_ = lean_array_fset(v_vs_519_, v_x_515_, v_x_517_);
lean_dec(v_x_515_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_539_);
lean_ctor_set(v___x_521_, 0, v___x_538_);
v___x_541_ = v___x_521_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(lean_object* v_n_544_, lean_object* v_k_545_, lean_object* v_v_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_n_544_, v___x_547_, v_k_545_, v_v_546_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(lean_object* v_x_550_, size_t v_x_551_, size_t v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v_es_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v_j_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_es_555_ = lean_ctor_get(v_x_550_, 0);
v___x_556_ = ((size_t)5ULL);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1);
v___x_559_ = lean_usize_land(v_x_551_, v___x_558_);
v_j_560_ = lean_usize_to_nat(v___x_559_);
v___x_561_ = lean_array_get_size(v_es_555_);
v___x_562_ = lean_nat_dec_lt(v_j_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec(v_j_560_);
lean_dec(v_x_554_);
lean_dec_ref(v_x_553_);
return v_x_550_;
}
else
{
lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_599_; 
lean_inc_ref(v_es_555_);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_600_);
v___x_564_ = v_x_550_;
v_isShared_565_ = v_isSharedCheck_599_;
goto v_resetjp_563_;
}
else
{
lean_dec(v_x_550_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_599_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_v_566_; lean_object* v___x_567_; lean_object* v_xs_x27_568_; lean_object* v___y_570_; 
v_v_566_ = lean_array_fget(v_es_555_, v_j_560_);
v___x_567_ = lean_box(0);
v_xs_x27_568_ = lean_array_fset(v_es_555_, v_j_560_, v___x_567_);
switch(lean_obj_tag(v_v_566_))
{
case 0:
{
lean_object* v_key_575_; lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
v_key_575_ = lean_ctor_get(v_v_566_, 0);
v_val_576_ = lean_ctor_get(v_v_566_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_v_566_);
if (v_isSharedCheck_586_ == 0)
{
v___x_578_ = v_v_566_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_inc(v_key_575_);
lean_dec(v_v_566_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint8_t v___x_580_; 
v___x_580_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_553_, v_key_575_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_del_object(v___x_578_);
v___x_581_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_575_, v_val_576_, v_x_553_, v_x_554_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
v___y_570_ = v___x_582_;
goto v___jp_569_;
}
else
{
lean_object* v___x_584_; 
lean_dec(v_val_576_);
lean_dec(v_key_575_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v_x_554_);
lean_ctor_set(v___x_578_, 0, v_x_553_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_x_553_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_x_554_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v___y_570_ = v___x_584_;
goto v___jp_569_;
}
}
}
}
case 1:
{
lean_object* v_node_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_597_; 
v_node_587_ = lean_ctor_get(v_v_566_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_v_566_);
if (v_isSharedCheck_597_ == 0)
{
v___x_589_ = v_v_566_;
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_node_587_);
lean_dec(v_v_566_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_591_ = lean_usize_shift_right(v_x_551_, v___x_556_);
v___x_592_ = lean_usize_add(v_x_552_, v___x_557_);
v___x_593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_node_587_, v___x_591_, v___x_592_, v_x_553_, v_x_554_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_593_);
v___x_595_ = v___x_589_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v___y_570_ = v___x_595_;
goto v___jp_569_;
}
}
}
default: 
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_x_553_);
lean_ctor_set(v___x_598_, 1, v_x_554_);
v___y_570_ = v___x_598_;
goto v___jp_569_;
}
}
v___jp_569_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_array_fset(v_xs_x27_568_, v_j_560_, v___y_570_);
lean_dec(v_j_560_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_571_);
v___x_573_ = v___x_564_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
else
{
lean_object* v_ks_601_; lean_object* v_vs_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_622_; 
v_ks_601_ = lean_ctor_get(v_x_550_, 0);
v_vs_602_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_622_ == 0)
{
v___x_604_ = v_x_550_;
v_isShared_605_ = v_isSharedCheck_622_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_vs_602_);
lean_inc(v_ks_601_);
lean_dec(v_x_550_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_622_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_ks_601_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_vs_602_);
v___x_607_ = v_reuseFailAlloc_621_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v_newNode_608_; uint8_t v___y_610_; size_t v___x_616_; uint8_t v___x_617_; 
v_newNode_608_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v___x_607_, v_x_553_, v_x_554_);
v___x_616_ = ((size_t)7ULL);
v___x_617_ = lean_usize_dec_le(v___x_616_, v_x_552_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_618_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_608_);
v___x_619_ = lean_unsigned_to_nat(4u);
v___x_620_ = lean_nat_dec_lt(v___x_618_, v___x_619_);
lean_dec(v___x_618_);
v___y_610_ = v___x_620_;
goto v___jp_609_;
}
else
{
v___y_610_ = v___x_617_;
goto v___jp_609_;
}
v___jp_609_:
{
if (v___y_610_ == 0)
{
lean_object* v_ks_611_; lean_object* v_vs_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_ks_611_ = lean_ctor_get(v_newNode_608_, 0);
lean_inc_ref(v_ks_611_);
v_vs_612_ = lean_ctor_get(v_newNode_608_, 1);
lean_inc_ref(v_vs_612_);
lean_dec_ref(v_newNode_608_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0);
v___x_615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_x_552_, v_ks_611_, v_vs_612_, v___x_613_, v___x_614_);
lean_dec_ref(v_vs_612_);
lean_dec_ref(v_ks_611_);
return v___x_615_;
}
else
{
return v_newNode_608_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(size_t v_depth_623_, lean_object* v_keys_624_, lean_object* v_vals_625_, lean_object* v_i_626_, lean_object* v_entries_627_){
_start:
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_array_get_size(v_keys_624_);
v___x_629_ = lean_nat_dec_lt(v_i_626_, v___x_628_);
if (v___x_629_ == 0)
{
lean_dec(v_i_626_);
return v_entries_627_;
}
else
{
lean_object* v_k_630_; lean_object* v_v_631_; uint64_t v___x_632_; size_t v_h_633_; size_t v___x_634_; lean_object* v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v_h_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_k_630_ = lean_array_fget_borrowed(v_keys_624_, v_i_626_);
v_v_631_ = lean_array_fget_borrowed(v_vals_625_, v_i_626_);
v___x_632_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_630_);
v_h_633_ = lean_uint64_to_usize(v___x_632_);
v___x_634_ = ((size_t)5ULL);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_sub(v_depth_623_, v___x_636_);
v___x_638_ = lean_usize_mul(v___x_634_, v___x_637_);
v_h_639_ = lean_usize_shift_right(v_h_633_, v___x_638_);
v___x_640_ = lean_nat_add(v_i_626_, v___x_635_);
lean_dec(v_i_626_);
lean_inc(v_v_631_);
lean_inc(v_k_630_);
v___x_641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_entries_627_, v_h_639_, v_depth_623_, v_k_630_, v_v_631_);
v_i_626_ = v___x_640_;
v_entries_627_ = v___x_641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_643_, lean_object* v_keys_644_, lean_object* v_vals_645_, lean_object* v_i_646_, lean_object* v_entries_647_){
_start:
{
size_t v_depth_boxed_648_; lean_object* v_res_649_; 
v_depth_boxed_648_ = lean_unbox_usize(v_depth_643_);
lean_dec(v_depth_643_);
v_res_649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_boxed_648_, v_keys_644_, v_vals_645_, v_i_646_, v_entries_647_);
lean_dec_ref(v_vals_645_);
lean_dec_ref(v_keys_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___boxed(lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
size_t v_x_7047__boxed_655_; size_t v_x_7048__boxed_656_; lean_object* v_res_657_; 
v_x_7047__boxed_655_ = lean_unbox_usize(v_x_651_);
lean_dec(v_x_651_);
v_x_7048__boxed_656_ = lean_unbox_usize(v_x_652_);
lean_dec(v_x_652_);
v_res_657_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_650_, v_x_7047__boxed_655_, v_x_7048__boxed_656_, v_x_653_, v_x_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
uint64_t v___x_661_; size_t v___x_662_; size_t v___x_663_; lean_object* v___x_664_; 
v___x_661_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_659_);
v___x_662_ = lean_uint64_to_usize(v___x_661_);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_658_, v___x_662_, v___x_663_, v_x_659_, v_x_660_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(lean_object* v_e_665_, lean_object* v_xs_666_, lean_object* v_b_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_674_; 
lean_inc(v_a_672_);
lean_inc_ref(v_a_671_);
lean_inc(v_a_670_);
lean_inc_ref(v_a_669_);
v___x_674_ = lean_infer_type(v_e_665_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_711_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_711_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_711_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_711_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v_funext_680_; lean_object* v___x_681_; 
v___x_679_ = lean_st_ref_get(v_a_668_);
v_funext_680_ = lean_ctor_get(v___x_679_, 3);
lean_inc_ref(v_funext_680_);
lean_dec(v___x_679_);
v___x_681_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_funext_680_, v_a_675_);
if (lean_obj_tag(v___x_681_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_684_; 
lean_dec(v_a_675_);
lean_dec_ref(v_b_667_);
lean_dec_ref(v_xs_666_);
v_val_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_682_);
lean_dec_ref(v___x_681_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_val_682_);
v___x_684_ = v___x_677_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_val_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v___x_686_; 
lean_dec(v___x_681_);
lean_del_object(v___x_677_);
lean_inc(v_a_672_);
lean_inc_ref(v_a_671_);
lean_inc(v_a_670_);
lean_inc_ref(v_a_669_);
v___x_686_ = lean_infer_type(v_b_667_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref(v___x_686_);
v___x_688_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(v_xs_666_, v_a_687_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_710_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_710_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_710_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_710_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_numSteps_694_; lean_object* v_persistentCache_695_; lean_object* v_transientCache_696_; lean_object* v_funext_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_709_; 
v___x_693_ = lean_st_ref_take(v_a_668_);
v_numSteps_694_ = lean_ctor_get(v___x_693_, 0);
v_persistentCache_695_ = lean_ctor_get(v___x_693_, 1);
v_transientCache_696_ = lean_ctor_get(v___x_693_, 2);
v_funext_697_ = lean_ctor_get(v___x_693_, 3);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_709_ == 0)
{
v___x_699_ = v___x_693_;
v_isShared_700_ = v_isSharedCheck_709_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_funext_697_);
lean_inc(v_transientCache_696_);
lean_inc(v_persistentCache_695_);
lean_inc(v_numSteps_694_);
lean_dec(v___x_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_709_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
lean_inc(v_a_689_);
v___x_701_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_funext_697_, v_a_675_, v_a_689_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 3, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_numSteps_694_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_persistentCache_695_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_transientCache_696_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v___x_701_);
v___x_703_ = v_reuseFailAlloc_708_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_st_ref_set(v_a_668_, v___x_703_);
if (v_isShared_692_ == 0)
{
v___x_706_ = v___x_691_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_689_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
else
{
lean_dec(v_a_675_);
return v___x_688_;
}
}
else
{
lean_dec(v_a_675_);
lean_dec_ref(v_xs_666_);
return v___x_686_;
}
}
}
}
else
{
lean_dec_ref(v_b_667_);
lean_dec_ref(v_xs_666_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg___boxed(lean_object* v_e_712_, lean_object* v_xs_713_, lean_object* v_b_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_712_, v_xs_713_, v_b_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(lean_object* v_e_722_, lean_object* v_xs_723_, lean_object* v_b_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_722_, v_xs_723_, v_b_724_, v_a_727_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___boxed(lean_object* v_e_736_, lean_object* v_xs_737_, lean_object* v_b_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(v_e_736_, v_xs_737_, v_b_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(lean_object* v_00_u03b2_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_751_, v_x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___boxed(lean_object* v_00_u03b2_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(v_00_u03b2_754_, v_x_755_, v_x_756_);
lean_dec_ref(v_x_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1(lean_object* v_00_u03b2_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_x_759_, v_x_760_, v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(lean_object* v_00_u03b2_763_, lean_object* v_x_764_, size_t v_x_765_, lean_object* v_x_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_764_, v_x_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___boxed(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
size_t v_x_7310__boxed_772_; lean_object* v_res_773_; 
v_x_7310__boxed_772_ = lean_unbox_usize(v_x_770_);
lean_dec(v_x_770_);
v_res_773_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(v_00_u03b2_768_, v_x_769_, v_x_7310__boxed_772_, v_x_771_);
lean_dec_ref(v_x_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(lean_object* v_00_u03b2_774_, lean_object* v_x_775_, size_t v_x_776_, size_t v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_775_, v_x_776_, v_x_777_, v_x_778_, v_x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___boxed(lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
size_t v_x_7321__boxed_787_; size_t v_x_7322__boxed_788_; lean_object* v_res_789_; 
v_x_7321__boxed_787_ = lean_unbox_usize(v_x_783_);
lean_dec(v_x_783_);
v_x_7322__boxed_788_ = lean_unbox_usize(v_x_784_);
lean_dec(v_x_784_);
v_res_789_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(v_00_u03b2_781_, v_x_782_, v_x_7321__boxed_787_, v_x_7322__boxed_788_, v_x_785_, v_x_786_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_790_, lean_object* v_keys_791_, lean_object* v_vals_792_, lean_object* v_heq_793_, lean_object* v_i_794_, lean_object* v_k_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_791_, v_vals_792_, v_i_794_, v_k_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_797_, lean_object* v_keys_798_, lean_object* v_vals_799_, lean_object* v_heq_800_, lean_object* v_i_801_, lean_object* v_k_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(v_00_u03b2_797_, v_keys_798_, v_vals_799_, v_heq_800_, v_i_801_, v_k_802_);
lean_dec_ref(v_k_802_);
lean_dec_ref(v_vals_799_);
lean_dec_ref(v_keys_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_804_, lean_object* v_n_805_, lean_object* v_k_806_, lean_object* v_v_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v_n_805_, v_k_806_, v_v_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_809_, size_t v_depth_810_, lean_object* v_keys_811_, lean_object* v_vals_812_, lean_object* v_heq_813_, lean_object* v_i_814_, lean_object* v_entries_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_810_, v_keys_811_, v_vals_812_, v_i_814_, v_entries_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_817_, lean_object* v_depth_818_, lean_object* v_keys_819_, lean_object* v_vals_820_, lean_object* v_heq_821_, lean_object* v_i_822_, lean_object* v_entries_823_){
_start:
{
size_t v_depth_boxed_824_; lean_object* v_res_825_; 
v_depth_boxed_824_ = lean_unbox_usize(v_depth_818_);
lean_dec(v_depth_818_);
v_res_825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(v_00_u03b2_817_, v_depth_boxed_824_, v_keys_819_, v_vals_820_, v_heq_821_, v_i_822_, v_entries_823_);
lean_dec_ref(v_vals_820_);
lean_dec_ref(v_keys_819_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_x_827_, v_x_828_, v_x_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(lean_object* v_simpBody_832_, lean_object* v_e_833_, lean_object* v_xs_834_, lean_object* v_b_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; 
lean_inc(v_a_844_);
lean_inc_ref(v_a_843_);
lean_inc(v_a_842_);
lean_inc_ref(v_a_841_);
lean_inc(v_a_840_);
lean_inc_ref(v_a_839_);
lean_inc(v_a_838_);
lean_inc_ref(v_a_837_);
lean_inc(v_a_836_);
lean_inc_ref(v_b_835_);
v___x_846_ = lean_apply_11(v_simpBody_832_, v_b_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, lean_box(0));
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_917_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_917_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_917_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_917_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
if (lean_obj_tag(v_a_847_) == 0)
{
uint8_t v_contextDependent_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
lean_dec_ref(v_b_835_);
lean_dec_ref(v_xs_834_);
lean_dec_ref(v_e_833_);
v_contextDependent_851_ = lean_ctor_get_uint8(v_a_847_, 1);
lean_dec_ref(v_a_847_);
v___x_852_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_851_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_852_);
v___x_854_ = v___x_849_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
else
{
lean_object* v_e_x27_856_; lean_object* v_proof_857_; uint8_t v_contextDependent_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_916_; 
lean_del_object(v___x_849_);
v_e_x27_856_ = lean_ctor_get(v_a_847_, 0);
v_proof_857_ = lean_ctor_get(v_a_847_, 1);
v_contextDependent_858_ = lean_ctor_get_uint8(v_a_847_, sizeof(void*)*2 + 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_a_847_);
if (v_isSharedCheck_916_ == 0)
{
v___x_860_ = v_a_847_;
v_isShared_861_ = v_isSharedCheck_916_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_proof_857_);
lean_inc(v_e_x27_856_);
lean_dec(v_a_847_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_916_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
uint8_t v___x_862_; uint8_t v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; 
v___x_862_ = 0;
v___x_863_ = 1;
v___x_864_ = 1;
v___x_865_ = l_Lean_Meta_mkLambdaFVars(v_xs_834_, v_proof_857_, v___x_862_, v___x_863_, v___x_862_, v___x_863_, v___x_864_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_865_);
v___x_867_ = l_Lean_Meta_mkLambdaFVars(v_xs_834_, v_e_x27_856_, v___x_862_, v___x_863_, v___x_862_, v___x_863_, v___x_864_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v___x_869_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_868_, v_a_840_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref(v___x_869_);
lean_inc_ref(v_e_833_);
v___x_871_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_833_, v_xs_834_, v_b_835_, v_a_838_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_883_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_883_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_883_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_883_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
lean_inc(v_a_870_);
v___x_876_ = l_Lean_mkApp3(v_a_872_, v_e_833_, v_a_870_, v_a_866_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___x_876_);
lean_ctor_set(v___x_860_, 0, v_a_870_);
v___x_878_ = v___x_860_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_870_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_882_, sizeof(void*)*2 + 1, v_contextDependent_858_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
lean_ctor_set_uint8(v___x_878_, sizeof(void*)*2, v___x_862_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_878_);
v___x_880_ = v___x_874_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_870_);
lean_dec(v_a_866_);
lean_del_object(v___x_860_);
lean_dec_ref(v_e_833_);
v_a_884_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_871_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_871_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_a_866_);
lean_del_object(v___x_860_);
lean_dec_ref(v_b_835_);
lean_dec_ref(v_xs_834_);
lean_dec_ref(v_e_833_);
v_a_892_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_869_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_869_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_a_866_);
lean_del_object(v___x_860_);
lean_dec_ref(v_b_835_);
lean_dec_ref(v_xs_834_);
lean_dec_ref(v_e_833_);
v_a_900_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_867_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_867_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_del_object(v___x_860_);
lean_dec_ref(v_e_x27_856_);
lean_dec_ref(v_b_835_);
lean_dec_ref(v_xs_834_);
lean_dec_ref(v_e_833_);
v_a_908_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_865_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_865_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_835_);
lean_dec_ref(v_xs_834_);
lean_dec_ref(v_e_833_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main___boxed(lean_object* v_simpBody_918_, lean_object* v_e_919_, lean_object* v_xs_920_, lean_object* v_b_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_918_, v_e_919_, v_xs_920_, v_b_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(lean_object* v_k_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v_b_939_, lean_object* v_c_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
v___x_946_ = lean_apply_12(v_k_933_, v_b_939_, v_c_940_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, lean_box(0));
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed(lean_object* v_k_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v_b_953_, lean_object* v_c_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(v_k_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v_b_953_, v_c_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(lean_object* v_e_961_, lean_object* v_k_962_, uint8_t v_cleanupAnnotations_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___f_974_; uint8_t v___x_975_; uint8_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
lean_inc(v___y_964_);
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_974_, 0, v_k_962_);
lean_closure_set(v___f_974_, 1, v___y_964_);
lean_closure_set(v___f_974_, 2, v___y_965_);
lean_closure_set(v___f_974_, 3, v___y_966_);
lean_closure_set(v___f_974_, 4, v___y_967_);
lean_closure_set(v___f_974_, 5, v___y_968_);
v___x_975_ = 1;
v___x_976_ = 0;
v___x_977_ = lean_box(0);
v___x_978_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_961_, v___x_975_, v___x_976_, v___x_975_, v___x_976_, v___x_977_, v___f_974_, v_cleanupAnnotations_963_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_978_) == 0)
{
return v___x_978_;
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___boxed(lean_object* v_e_987_, lean_object* v_k_988_, lean_object* v_cleanupAnnotations_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1000_; lean_object* v_res_1001_; 
v_cleanupAnnotations_boxed_1000_ = lean_unbox(v_cleanupAnnotations_989_);
v_res_1001_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_987_, v_k_988_, v_cleanupAnnotations_boxed_1000_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(lean_object* v_00_u03b1_1002_, lean_object* v_e_1003_, lean_object* v_k_1004_, uint8_t v_cleanupAnnotations_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_1003_, v_k_1004_, v_cleanupAnnotations_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___boxed(lean_object* v_00_u03b1_1017_, lean_object* v_e_1018_, lean_object* v_k_1019_, lean_object* v_cleanupAnnotations_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1031_; lean_object* v_res_1032_; 
v_cleanupAnnotations_boxed_1031_ = lean_unbox(v_cleanupAnnotations_1020_);
v_res_1032_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(v_00_u03b1_1017_, v_e_1018_, v_k_1019_, v_cleanupAnnotations_boxed_1031_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(lean_object* v___y_1033_, lean_object* v_transientCache_1034_, lean_object* v_funext_1035_, lean_object* v_a_x3f_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v_numSteps_1039_; lean_object* v_persistentCache_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1050_; 
v___x_1038_ = lean_st_ref_take(v___y_1033_);
v_numSteps_1039_ = lean_ctor_get(v___x_1038_, 0);
v_persistentCache_1040_ = lean_ctor_get(v___x_1038_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; lean_object* v_unused_1052_; 
v_unused_1051_ = lean_ctor_get(v___x_1038_, 3);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v___x_1038_, 2);
lean_dec(v_unused_1052_);
v___x_1042_ = v___x_1038_;
v_isShared_1043_ = v_isSharedCheck_1050_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_persistentCache_1040_);
lean_inc(v_numSteps_1039_);
lean_dec(v___x_1038_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1050_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 3, v_funext_1035_);
lean_ctor_set(v___x_1042_, 2, v_transientCache_1034_);
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_numSteps_1039_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_persistentCache_1040_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_transientCache_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_funext_1035_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_st_ref_set(v___y_1033_, v___x_1045_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0___boxed(lean_object* v___y_1053_, lean_object* v_transientCache_1054_, lean_object* v_funext_1055_, lean_object* v_a_x3f_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1053_, v_transientCache_1054_, v_funext_1055_, v_a_x3f_1056_);
lean_dec(v_a_x3f_1056_);
lean_dec(v___y_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(lean_object* v_simpBody_1059_, lean_object* v_e_1060_, lean_object* v_xs_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_transientCache_1075_; lean_object* v_funext_1076_; lean_object* v_a_1078_; lean_object* v___x_1089_; 
v___x_1073_ = lean_st_ref_get(v___y_1065_);
v___x_1074_ = lean_st_ref_get(v___y_1065_);
v_transientCache_1075_ = lean_ctor_get(v___x_1073_, 2);
lean_inc_ref(v_transientCache_1075_);
lean_dec(v___x_1073_);
v_funext_1076_ = lean_ctor_get(v___x_1074_, 3);
lean_inc_ref(v_funext_1076_);
lean_dec(v___x_1074_);
v___x_1089_ = l_Lean_Meta_Sym_shareCommon___redArg(v_b_1062_, v___y_1067_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_1059_, v_e_1060_, v_xs_1061_, v_a_1090_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1108_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1108_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1108_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
lean_inc(v_a_1092_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 1);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v___x_1098_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1065_, v_transientCache_1075_, v_funext_1076_, v___x_1097_);
lean_dec_ref(v___x_1097_);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v___x_1098_, 0);
lean_dec(v_unused_1106_);
v___x_1100_ = v___x_1098_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_dec(v___x_1098_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v_a_1092_);
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1092_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
else
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1109_);
lean_dec_ref(v___x_1091_);
v_a_1078_ = v_a_1109_;
goto v___jp_1077_;
}
}
else
{
lean_object* v_a_1110_; 
lean_dec_ref(v_xs_1061_);
lean_dec_ref(v_e_1060_);
lean_dec_ref(v_simpBody_1059_);
v_a_1110_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1110_);
lean_dec_ref(v___x_1089_);
v_a_1078_ = v_a_1110_;
goto v___jp_1077_;
}
v___jp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1065_, v_transientCache_1075_, v_funext_1076_, v___x_1079_);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v___x_1080_, 0);
lean_dec(v_unused_1088_);
v___x_1082_ = v___x_1080_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v___x_1080_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 0, v_a_1078_);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1078_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed(lean_object* v_simpBody_1111_, lean_object* v_e_1112_, lean_object* v_xs_1113_, lean_object* v_b_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(v_simpBody_1111_, v_e_1112_, v_xs_1113_, v_b_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27(lean_object* v_simpBody_1126_, lean_object* v_e_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___f_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; 
lean_inc_ref(v_e_1127_);
v___f_1138_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed), 14, 2);
lean_closure_set(v___f_1138_, 0, v_simpBody_1126_);
lean_closure_set(v___f_1138_, 1, v_e_1127_);
v___x_1139_ = 0;
v___x_1140_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_1127_, v___f_1138_, v___x_1139_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed(lean_object* v_simpBody_1141_, lean_object* v_e_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v_simpBody_1141_, v_e_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object* v_e_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLambda___closed__0));
v___x_1167_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v___x_1166_, v_e_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda___boxed(lean_object* v_e_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
return v_res_1179_;
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
