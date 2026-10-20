// Lean compiler output
// Module: Lean.Compiler.ClosedTermCache
// Imports: public import Lean.Environment
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_Expr_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_takeNewEntries___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedClosedTermCache_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedClosedTermCache;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Data.PersistentHashMap"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__0 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__0_value;
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.PersistentHashMap.find!"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__1_value;
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "key is not in the map"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "closedTermCacheExt"};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 48, 235, 129, 20, 167, 228, 119)}};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_closedTermCacheExt;
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isClosedTermName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedClosedTermCache_default___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache_default___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__0, &l_Lean_instInhabitedClosedTermCache_default___closed__0_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_box(0);
v___x_5_ = l_Lean_NameSet_empty;
v___x_6_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__1, &l_Lean_instInhabitedClosedTermCache_default___closed__1_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__1);
v___x_7_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_5_);
lean_ctor_set(v___x_7_, 2, v___x_4_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache_default(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__2, &l_Lean_instInhabitedClosedTermCache_default___closed__2_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__2);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_instInhabitedClosedTermCache_default;
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__2(lean_object* v_msg_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_box(0);
v___x_12_ = lean_panic_fn_borrowed(v___x_11_, v_msg_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_13_, lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_ks_17_; lean_object* v_vs_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_42_; 
v_ks_17_ = lean_ctor_get(v_x_13_, 0);
v_vs_18_ = lean_ctor_get(v_x_13_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_42_ == 0)
{
v___x_20_ = v_x_13_;
v_isShared_21_ = v_isSharedCheck_42_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_vs_18_);
lean_inc(v_ks_17_);
lean_dec(v_x_13_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_42_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = lean_array_get_size(v_ks_17_);
v___x_23_ = lean_nat_dec_lt(v_x_14_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
lean_dec(v_x_14_);
v___x_24_ = lean_array_push(v_ks_17_, v_x_15_);
v___x_25_ = lean_array_push(v_vs_18_, v_x_16_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v___x_25_);
lean_ctor_set(v___x_20_, 0, v___x_24_);
v___x_27_ = v___x_20_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
else
{
lean_object* v_k_x27_29_; uint8_t v___x_30_; 
v_k_x27_29_ = lean_array_fget_borrowed(v_ks_17_, v_x_14_);
v___x_30_ = lean_expr_eqv(v_x_15_, v_k_x27_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_32_; 
if (v_isShared_21_ == 0)
{
v___x_32_ = v___x_20_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_ks_17_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_vs_18_);
v___x_32_ = v_reuseFailAlloc_36_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_x_14_, v___x_33_);
lean_dec(v_x_14_);
v_x_13_ = v___x_32_;
v_x_14_ = v___x_34_;
goto _start;
}
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_37_ = lean_array_fset(v_ks_17_, v_x_14_, v_x_15_);
v___x_38_ = lean_array_fset(v_vs_18_, v_x_14_, v_x_16_);
lean_dec(v_x_14_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v___x_38_);
lean_ctor_set(v___x_20_, 0, v___x_37_);
v___x_40_ = v___x_20_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_n_43_, lean_object* v_k_44_, lean_object* v_v_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_n_43_, v___x_46_, v_k_44_, v_v_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_49_, size_t v_x_50_, size_t v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v_es_54_; size_t v___x_55_; size_t v___x_56_; lean_object* v_j_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v_es_54_ = lean_ctor_get(v_x_49_, 0);
v___x_55_ = ((size_t)31ULL);
v___x_56_ = lean_usize_land(v_x_50_, v___x_55_);
v_j_57_ = lean_usize_to_nat(v___x_56_);
v___x_58_ = lean_array_get_size(v_es_54_);
v___x_59_ = lean_nat_dec_lt(v_j_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_dec(v_j_57_);
lean_dec(v_x_53_);
lean_dec_ref(v_x_52_);
return v_x_49_;
}
else
{
lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_98_; 
lean_inc_ref(v_es_54_);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; 
v_unused_99_ = lean_ctor_get(v_x_49_, 0);
lean_dec(v_unused_99_);
v___x_61_ = v_x_49_;
v_isShared_62_ = v_isSharedCheck_98_;
goto v_resetjp_60_;
}
else
{
lean_dec(v_x_49_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_98_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_v_63_; lean_object* v___x_64_; lean_object* v_xs_x27_65_; lean_object* v___y_67_; 
v_v_63_ = lean_array_fget(v_es_54_, v_j_57_);
v___x_64_ = lean_box(0);
v_xs_x27_65_ = lean_array_fset(v_es_54_, v_j_57_, v___x_64_);
switch(lean_obj_tag(v_v_63_))
{
case 0:
{
lean_object* v_key_72_; lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_83_; 
v_key_72_ = lean_ctor_get(v_v_63_, 0);
v_val_73_ = lean_ctor_get(v_v_63_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_v_63_);
if (v_isSharedCheck_83_ == 0)
{
v___x_75_ = v_v_63_;
v_isShared_76_ = v_isSharedCheck_83_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_inc(v_key_72_);
lean_dec(v_v_63_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_83_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
uint8_t v___x_77_; 
v___x_77_ = lean_expr_eqv(v_x_52_, v_key_72_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_del_object(v___x_75_);
v___x_78_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_72_, v_val_73_, v_x_52_, v_x_53_);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___y_67_ = v___x_79_;
goto v___jp_66_;
}
else
{
lean_object* v___x_81_; 
lean_dec(v_val_73_);
lean_dec(v_key_72_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v_x_53_);
lean_ctor_set(v___x_75_, 0, v_x_52_);
v___x_81_ = v___x_75_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_x_52_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_x_53_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
v___y_67_ = v___x_81_;
goto v___jp_66_;
}
}
}
}
case 1:
{
lean_object* v_node_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_96_; 
v_node_84_ = lean_ctor_get(v_v_63_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_v_63_);
if (v_isSharedCheck_96_ == 0)
{
v___x_86_ = v_v_63_;
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_node_84_);
lean_dec(v_v_63_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_88_ = ((size_t)5ULL);
v___x_89_ = lean_usize_shift_right(v_x_50_, v___x_88_);
v___x_90_ = ((size_t)1ULL);
v___x_91_ = lean_usize_add(v_x_51_, v___x_90_);
v___x_92_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_node_84_, v___x_89_, v___x_91_, v_x_52_, v_x_53_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_92_);
v___x_94_ = v___x_86_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
v___y_67_ = v___x_94_;
goto v___jp_66_;
}
}
}
default: 
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v_x_52_);
lean_ctor_set(v___x_97_, 1, v_x_53_);
v___y_67_ = v___x_97_;
goto v___jp_66_;
}
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_array_fset(v_xs_x27_65_, v_j_57_, v___y_67_);
lean_dec(v_j_57_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_68_);
v___x_70_ = v___x_61_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
else
{
lean_object* v_ks_100_; lean_object* v_vs_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_119_; 
v_ks_100_ = lean_ctor_get(v_x_49_, 0);
v_vs_101_ = lean_ctor_get(v_x_49_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_119_ == 0)
{
v___x_103_ = v_x_49_;
v_isShared_104_ = v_isSharedCheck_119_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_vs_101_);
lean_inc(v_ks_100_);
lean_dec(v_x_49_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_119_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_ks_100_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_vs_101_);
v___x_106_ = v_reuseFailAlloc_118_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v_newNode_107_; size_t v___x_108_; uint8_t v___x_109_; 
v_newNode_107_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v___x_106_, v_x_52_, v_x_53_);
v___x_108_ = ((size_t)7ULL);
v___x_109_ = lean_usize_dec_le(v___x_108_, v_x_51_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_107_);
v___x_111_ = lean_unsigned_to_nat(4u);
v___x_112_ = lean_nat_dec_lt(v___x_110_, v___x_111_);
lean_dec(v___x_110_);
if (v___x_112_ == 0)
{
lean_object* v_ks_113_; lean_object* v_vs_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_ks_113_ = lean_ctor_get(v_newNode_107_, 0);
lean_inc_ref(v_ks_113_);
v_vs_114_ = lean_ctor_get(v_newNode_107_, 1);
lean_inc_ref(v_vs_114_);
lean_dec_ref(v_newNode_107_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___x_117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_x_51_, v_ks_113_, v_vs_114_, v___x_115_, v___x_116_);
lean_dec_ref(v_vs_114_);
lean_dec_ref(v_ks_113_);
return v___x_117_;
}
else
{
return v_newNode_107_;
}
}
else
{
return v_newNode_107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(size_t v_depth_120_, lean_object* v_keys_121_, lean_object* v_vals_122_, lean_object* v_i_123_, lean_object* v_entries_124_){
_start:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_array_get_size(v_keys_121_);
v___x_126_ = lean_nat_dec_lt(v_i_123_, v___x_125_);
if (v___x_126_ == 0)
{
lean_dec(v_i_123_);
return v_entries_124_;
}
else
{
lean_object* v_k_127_; lean_object* v_v_128_; uint64_t v___x_129_; size_t v_h_130_; size_t v___x_131_; lean_object* v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v_h_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_k_127_ = lean_array_fget_borrowed(v_keys_121_, v_i_123_);
v_v_128_ = lean_array_fget_borrowed(v_vals_122_, v_i_123_);
v___x_129_ = l_Lean_Expr_hash(v_k_127_);
v_h_130_ = lean_uint64_to_usize(v___x_129_);
v___x_131_ = ((size_t)5ULL);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = ((size_t)1ULL);
v___x_134_ = lean_usize_sub(v_depth_120_, v___x_133_);
v___x_135_ = lean_usize_mul(v___x_131_, v___x_134_);
v_h_136_ = lean_usize_shift_right(v_h_130_, v___x_135_);
v___x_137_ = lean_nat_add(v_i_123_, v___x_132_);
lean_dec(v_i_123_);
lean_inc(v_v_128_);
lean_inc(v_k_127_);
v___x_138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_entries_124_, v_h_136_, v_depth_120_, v_k_127_, v_v_128_);
v_i_123_ = v___x_137_;
v_entries_124_ = v___x_138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_140_, lean_object* v_keys_141_, lean_object* v_vals_142_, lean_object* v_i_143_, lean_object* v_entries_144_){
_start:
{
size_t v_depth_boxed_145_; lean_object* v_res_146_; 
v_depth_boxed_145_ = lean_unbox_usize(v_depth_140_);
lean_dec(v_depth_140_);
v_res_146_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_boxed_145_, v_keys_141_, v_vals_142_, v_i_143_, v_entries_144_);
lean_dec_ref(v_vals_142_);
lean_dec_ref(v_keys_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
size_t v_x_600__boxed_152_; size_t v_x_601__boxed_153_; lean_object* v_res_154_; 
v_x_600__boxed_152_ = lean_unbox_usize(v_x_148_);
lean_dec(v_x_148_);
v_x_601__boxed_153_ = lean_unbox_usize(v_x_149_);
lean_dec(v_x_149_);
v_res_154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_147_, v_x_600__boxed_152_, v_x_601__boxed_153_, v_x_150_, v_x_151_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
uint64_t v___x_158_; size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v___x_158_ = l_Lean_Expr_hash(v_x_156_);
v___x_159_ = lean_uint64_to_usize(v___x_158_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_155_, v___x_159_, v___x_160_, v_x_156_, v_x_157_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object* v_keys_162_, lean_object* v_vals_163_, lean_object* v_i_164_, lean_object* v_k_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_array_get_size(v_keys_162_);
v___x_167_ = lean_nat_dec_lt(v_i_164_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_dec(v_i_164_);
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v_k_x27_169_; uint8_t v___x_170_; 
v_k_x27_169_ = lean_array_fget_borrowed(v_keys_162_, v_i_164_);
v___x_170_ = lean_expr_eqv(v_k_165_, v_k_x27_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_i_164_, v___x_171_);
lean_dec(v_i_164_);
v_i_164_ = v___x_172_;
goto _start;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_array_fget_borrowed(v_vals_163_, v_i_164_);
lean_dec(v_i_164_);
lean_inc(v___x_174_);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_176_, lean_object* v_vals_177_, lean_object* v_i_178_, lean_object* v_k_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_176_, v_vals_177_, v_i_178_, v_k_179_);
lean_dec_ref(v_k_179_);
lean_dec_ref(v_vals_177_);
lean_dec_ref(v_keys_176_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_181_, size_t v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v_es_184_; lean_object* v___x_185_; size_t v___x_186_; size_t v___x_187_; lean_object* v_j_188_; lean_object* v___x_189_; 
v_es_184_ = lean_ctor_get(v_x_181_, 0);
v___x_185_ = lean_box(2);
v___x_186_ = ((size_t)31ULL);
v___x_187_ = lean_usize_land(v_x_182_, v___x_186_);
v_j_188_ = lean_usize_to_nat(v___x_187_);
v___x_189_ = lean_array_get_borrowed(v___x_185_, v_es_184_, v_j_188_);
lean_dec(v_j_188_);
switch(lean_obj_tag(v___x_189_))
{
case 0:
{
lean_object* v_key_190_; lean_object* v_val_191_; uint8_t v___x_192_; 
v_key_190_ = lean_ctor_get(v___x_189_, 0);
v_val_191_ = lean_ctor_get(v___x_189_, 1);
v___x_192_ = lean_expr_eqv(v_x_183_, v_key_190_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v___x_194_; 
lean_inc(v_val_191_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_val_191_);
return v___x_194_;
}
}
case 1:
{
lean_object* v_node_195_; size_t v___x_196_; size_t v___x_197_; 
v_node_195_ = lean_ctor_get(v___x_189_, 0);
v___x_196_ = ((size_t)5ULL);
v___x_197_ = lean_usize_shift_right(v_x_182_, v___x_196_);
v_x_181_ = v_node_195_;
v_x_182_ = v___x_197_;
goto _start;
}
default: 
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
}
else
{
lean_object* v_ks_200_; lean_object* v_vs_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_ks_200_ = lean_ctor_get(v_x_181_, 0);
v_vs_201_ = lean_ctor_get(v_x_181_, 1);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_ks_200_, v_vs_201_, v___x_202_, v_x_183_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
size_t v_x_784__boxed_207_; lean_object* v_res_208_; 
v_x_784__boxed_207_ = lean_unbox_usize(v_x_205_);
lean_dec(v_x_205_);
v_res_208_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_204_, v_x_784__boxed_207_, v_x_206_);
lean_dec_ref(v_x_206_);
lean_dec_ref(v_x_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
uint64_t v___x_211_; size_t v___x_212_; lean_object* v___x_213_; 
v___x_211_ = l_Lean_Expr_hash(v_x_210_);
v___x_212_ = lean_uint64_to_usize(v___x_211_);
v___x_213_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_209_, v___x_212_, v_x_210_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(v_x_214_, v_x_215_);
lean_dec_ref(v_x_215_);
lean_dec_ref(v_x_214_);
return v_res_216_;
}
}
static lean_object* _init_l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_220_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__2));
v___x_221_ = lean_unsigned_to_nat(14u);
v___x_222_ = lean_unsigned_to_nat(178u);
v___x_223_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__1));
v___x_224_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__0));
v___x_225_ = l_mkPanicMessageWithDecl(v___x_224_, v___x_223_, v___x_222_, v___x_221_, v___x_220_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3(lean_object* v_newState_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
return v_x_227_;
}
else
{
lean_object* v_head_229_; lean_object* v_tail_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_257_; 
v_head_229_ = lean_ctor_get(v_x_228_, 0);
v_tail_230_ = lean_ctor_get(v_x_228_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_257_ == 0)
{
v___x_232_ = v_x_228_;
v_isShared_233_ = v_isSharedCheck_257_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_tail_230_);
lean_inc(v_head_229_);
lean_dec(v_x_228_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_257_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___y_235_; lean_object* v_map_252_; lean_object* v___x_253_; 
v_map_252_ = lean_ctor_get(v_newState_226_, 0);
v___x_253_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(v_map_252_, v_head_229_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3, &l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3_once, _init_l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3);
v___x_255_ = l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__2(v___x_254_);
v___y_235_ = v___x_255_;
goto v___jp_234_;
}
else
{
lean_object* v_val_256_; 
v_val_256_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_253_, 1);
v___y_235_ = v_val_256_;
goto v___jp_234_;
}
v___jp_234_:
{
lean_object* v_map_236_; lean_object* v_constNames_237_; lean_object* v_revExprs_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_251_; 
v_map_236_ = lean_ctor_get(v_x_227_, 0);
v_constNames_237_ = lean_ctor_get(v_x_227_, 1);
v_revExprs_238_ = lean_ctor_get(v_x_227_, 2);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_251_ == 0)
{
v___x_240_ = v_x_227_;
v_isShared_241_ = v_isSharedCheck_251_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_revExprs_238_);
lean_inc(v_constNames_237_);
lean_inc(v_map_236_);
lean_dec(v_x_227_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_251_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
lean_inc(v___y_235_);
lean_inc(v_head_229_);
v___x_242_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(v_map_236_, v_head_229_, v___y_235_);
v___x_243_ = l_Lean_NameSet_insert(v_constNames_237_, v___y_235_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v_revExprs_238_);
v___x_245_ = v___x_232_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_head_229_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_revExprs_238_);
v___x_245_ = v_reuseFailAlloc_250_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 2, v___x_245_);
lean_ctor_set(v___x_240_, 1, v___x_243_);
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v___x_245_);
v___x_247_ = v_reuseFailAlloc_249_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
v_x_227_ = v___x_247_;
v_x_228_ = v_tail_230_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___boxed(lean_object* v_newState_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3(v_newState_258_, v_x_259_, v_x_260_);
lean_dec_ref(v_newState_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(lean_object* v_oldState_262_, lean_object* v_newState_263_, lean_object* v_x_264_, lean_object* v_s_265_){
_start:
{
lean_object* v_revExprs_266_; lean_object* v_revExprs_267_; lean_object* v_newExprs_268_; lean_object* v___x_269_; 
v_revExprs_266_ = lean_ctor_get(v_newState_263_, 2);
v_revExprs_267_ = lean_ctor_get(v_oldState_262_, 2);
lean_inc(v_revExprs_266_);
v_newExprs_268_ = l_Lean_takeNewEntries___redArg(v_revExprs_266_, v_revExprs_267_);
v___x_269_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3(v_newState_263_, v_s_265_, v_newExprs_268_);
lean_dec_ref(v_newState_263_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object* v_oldState_270_, lean_object* v_newState_271_, lean_object* v_x_272_, lean_object* v_s_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(v_oldState_270_, v_newState_271_, v_x_272_, v_s_273_);
lean_dec(v_x_272_);
lean_dec_ref(v_oldState_270_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(lean_object* v___x_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object* v___x_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(v___x_278_);
return v_res_280_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_282_; lean_object* v___f_283_; 
v___x_282_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__2, &l_Lean_instInhabitedClosedTermCache_default___closed__2_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__2);
v___f_283_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_283_, 0, v___x_282_);
return v___f_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; 
v___f_292_ = lean_obj_once(&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_, &l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_);
v___x_293_ = ((lean_object*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_));
v___x_294_ = lean_box(0);
v___x_295_ = ((lean_object*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_));
v___x_296_ = 0;
v___x_297_ = l_Lean_registerEnvExtension___redArg(v___f_292_, v___x_293_, v___x_294_, v___x_295_, v___x_296_, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_();
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_300_, lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(v_x_301_, v_x_302_, v_x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(v_x_306_, v_x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1(v_00_u03b2_309_, v_x_310_, v_x_311_);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_x_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_313_, lean_object* v_x_314_, size_t v_x_315_, size_t v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_314_, v_x_315_, v_x_316_, v_x_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
size_t v_x_1007__boxed_326_; size_t v_x_1008__boxed_327_; lean_object* v_res_328_; 
v_x_1007__boxed_326_ = lean_unbox_usize(v_x_322_);
lean_dec(v_x_322_);
v_x_1008__boxed_327_ = lean_unbox_usize(v_x_323_);
lean_dec(v_x_323_);
v_res_328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_320_, v_x_321_, v_x_1007__boxed_326_, v_x_1008__boxed_327_, v_x_324_, v_x_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_329_, lean_object* v_x_330_, size_t v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_330_, v_x_331_, v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_334_, lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
size_t v_x_1024__boxed_338_; lean_object* v_res_339_; 
v_x_1024__boxed_338_ = lean_unbox_usize(v_x_336_);
lean_dec(v_x_336_);
v_res_339_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_334_, v_x_335_, v_x_1024__boxed_338_, v_x_337_);
lean_dec_ref(v_x_337_);
lean_dec_ref(v_x_335_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_340_, lean_object* v_n_341_, lean_object* v_k_342_, lean_object* v_v_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_n_341_, v_k_342_, v_v_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object* v_00_u03b2_345_, size_t v_depth_346_, lean_object* v_keys_347_, lean_object* v_vals_348_, lean_object* v_heq_349_, lean_object* v_i_350_, lean_object* v_entries_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_346_, v_keys_347_, v_vals_348_, v_i_350_, v_entries_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_353_, lean_object* v_depth_354_, lean_object* v_keys_355_, lean_object* v_vals_356_, lean_object* v_heq_357_, lean_object* v_i_358_, lean_object* v_entries_359_){
_start:
{
size_t v_depth_boxed_360_; lean_object* v_res_361_; 
v_depth_boxed_360_ = lean_unbox_usize(v_depth_354_);
lean_dec(v_depth_354_);
v_res_361_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_00_u03b2_353_, v_depth_boxed_360_, v_keys_355_, v_vals_356_, v_heq_357_, v_i_358_, v_entries_359_);
lean_dec_ref(v_vals_356_);
lean_dec_ref(v_keys_355_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object* v_00_u03b2_362_, lean_object* v_keys_363_, lean_object* v_vals_364_, lean_object* v_heq_365_, lean_object* v_i_366_, lean_object* v_k_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_363_, v_vals_364_, v_i_366_, v_k_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_369_, lean_object* v_keys_370_, lean_object* v_vals_371_, lean_object* v_heq_372_, lean_object* v_i_373_, lean_object* v_k_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6(v_00_u03b2_369_, v_keys_370_, v_vals_371_, v_heq_372_, v_i_373_, v_k_374_);
lean_dec_ref(v_k_374_);
lean_dec_ref(v_vals_371_);
lean_dec_ref(v_keys_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_x_377_, v_x_378_, v_x_379_, v_x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lam__0(lean_object* v_e_382_, lean_object* v_n_383_, lean_object* v_s_384_){
_start:
{
lean_object* v_map_385_; lean_object* v_constNames_386_; lean_object* v_revExprs_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_397_; 
v_map_385_ = lean_ctor_get(v_s_384_, 0);
v_constNames_386_ = lean_ctor_get(v_s_384_, 1);
v_revExprs_387_ = lean_ctor_get(v_s_384_, 2);
v_isSharedCheck_397_ = !lean_is_exclusive(v_s_384_);
if (v_isSharedCheck_397_ == 0)
{
v___x_389_ = v_s_384_;
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_revExprs_387_);
lean_inc(v_constNames_386_);
lean_inc(v_map_385_);
lean_dec(v_s_384_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
lean_inc(v_n_383_);
lean_inc_ref(v_e_382_);
v___x_391_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(v_map_385_, v_e_382_, v_n_383_);
v___x_392_ = l_Lean_NameSet_insert(v_constNames_386_, v_n_383_);
v___x_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_393_, 0, v_e_382_);
lean_ctor_set(v___x_393_, 1, v_revExprs_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 2, v___x_393_);
lean_ctor_set(v___x_389_, 1, v___x_392_);
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_395_ = v___x_389_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName(lean_object* v_env_398_, lean_object* v_e_399_, lean_object* v_n_400_){
_start:
{
lean_object* v___x_401_; lean_object* v_asyncMode_402_; uint8_t v_logWrites_403_; lean_object* v___f_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_401_ = l_Lean_closedTermCacheExt;
v_asyncMode_402_ = lean_ctor_get(v___x_401_, 2);
v_logWrites_403_ = lean_ctor_get_uint8(v___x_401_, sizeof(void*)*6);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_cacheClosedTermName___lam__0), 3, 2);
lean_closure_set(v___f_404_, 0, v_e_399_);
lean_closure_set(v___f_404_, 1, v_n_400_);
v___x_405_ = lean_box(0);
v___x_406_ = 1;
if (v_logWrites_403_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_401_, v_env_398_, v___f_404_, v_asyncMode_402_, v___x_405_, v___x_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_401_, v_env_398_);
lean_dec_ref(v_env_398_);
v___x_409_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_401_, v___x_408_, v___f_404_, v_asyncMode_402_, v___x_405_, v___x_406_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f(lean_object* v_env_410_, lean_object* v_e_411_){
_start:
{
lean_object* v___x_412_; lean_object* v_asyncMode_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v_map_418_; lean_object* v___x_419_; 
v___x_412_ = l_Lean_closedTermCacheExt;
v_asyncMode_413_ = lean_ctor_get(v___x_412_, 2);
v___x_414_ = l_Lean_instInhabitedClosedTermCache_default;
v___x_415_ = lean_box(0);
v___x_416_ = 0;
v___x_417_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_414_, v___x_412_, v_env_410_, v_asyncMode_413_, v___x_415_, v___x_416_);
v_map_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_map_418_);
lean_dec(v___x_417_);
v___x_419_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(v_map_418_, v_e_411_);
lean_dec_ref(v_map_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f___boxed(lean_object* v_env_420_, lean_object* v_e_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_getClosedTermName_x3f(v_env_420_, v_e_421_);
lean_dec_ref(v_e_421_);
return v_res_422_;
}
}
LEAN_EXPORT uint8_t l_Lean_isClosedTermName(lean_object* v_env_423_, lean_object* v_n_424_){
_start:
{
lean_object* v___x_425_; lean_object* v_asyncMode_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v_constNames_431_; uint8_t v___x_432_; 
v___x_425_ = l_Lean_closedTermCacheExt;
v_asyncMode_426_ = lean_ctor_get(v___x_425_, 2);
v___x_427_ = l_Lean_instInhabitedClosedTermCache_default;
v___x_428_ = lean_box(0);
v___x_429_ = 0;
v___x_430_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_427_, v___x_425_, v_env_423_, v_asyncMode_426_, v___x_428_, v___x_429_);
v_constNames_431_ = lean_ctor_get(v___x_430_, 1);
lean_inc(v_constNames_431_);
lean_dec(v___x_430_);
v___x_432_ = l_Lean_NameSet_contains(v_constNames_431_, v_n_424_);
lean_dec(v_constNames_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object* v_env_433_, lean_object* v_n_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Lean_isClosedTermName(v_env_433_, v_n_434_);
lean_dec(v_n_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedClosedTermCache_default = _init_l_Lean_instInhabitedClosedTermCache_default();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache_default);
l_Lean_instInhabitedClosedTermCache = _init_l_Lean_instInhabitedClosedTermCache();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache);
res = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_closedTermCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_closedTermCacheExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ClosedTermCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_ClosedTermCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_ClosedTermCache(builtin);
}
#ifdef __cplusplus
}
#endif
