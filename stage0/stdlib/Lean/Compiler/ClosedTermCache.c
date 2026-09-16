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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedClosedTermCache_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedClosedTermCache;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Data.PersistentHashMap"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__0 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__0_value;
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.PersistentHashMap.find!"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__1_value;
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "key is not in the map"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__2(lean_object* v_msg_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_box(0);
v___x_12_ = lean_panic_fn_borrowed(v___x_11_, v_msg_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object* v_keys_13_, lean_object* v_vals_14_, lean_object* v_i_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_array_get_size(v_keys_13_);
v___x_18_ = lean_nat_dec_lt(v_i_15_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
lean_dec(v_i_15_);
v___x_19_ = lean_box(0);
return v___x_19_;
}
else
{
lean_object* v_k_x27_20_; uint8_t v___x_21_; 
v_k_x27_20_ = lean_array_fget_borrowed(v_keys_13_, v_i_15_);
v___x_21_ = lean_expr_eqv(v_k_16_, v_k_x27_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_add(v_i_15_, v___x_22_);
lean_dec(v_i_15_);
v_i_15_ = v___x_23_;
goto _start;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_array_fget_borrowed(v_vals_14_, v_i_15_);
lean_dec(v_i_15_);
lean_inc(v___x_25_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_27_, lean_object* v_vals_28_, lean_object* v_i_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_27_, v_vals_28_, v_i_29_, v_k_30_);
lean_dec_ref(v_k_30_);
lean_dec_ref(v_vals_28_);
lean_dec_ref(v_keys_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_32_, size_t v_x_33_, lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v_es_35_; lean_object* v___x_36_; size_t v___x_37_; size_t v___x_38_; lean_object* v_j_39_; lean_object* v___x_40_; 
v_es_35_ = lean_ctor_get(v_x_32_, 0);
v___x_36_ = lean_box(2);
v___x_37_ = ((size_t)31ULL);
v___x_38_ = lean_usize_land(v_x_33_, v___x_37_);
v_j_39_ = lean_usize_to_nat(v___x_38_);
v___x_40_ = lean_array_get_borrowed(v___x_36_, v_es_35_, v_j_39_);
lean_dec(v_j_39_);
switch(lean_obj_tag(v___x_40_))
{
case 0:
{
lean_object* v_key_41_; lean_object* v_val_42_; uint8_t v___x_43_; 
v_key_41_ = lean_ctor_get(v___x_40_, 0);
v_val_42_ = lean_ctor_get(v___x_40_, 1);
v___x_43_ = lean_expr_eqv(v_x_34_, v_key_41_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
else
{
lean_object* v___x_45_; 
lean_inc(v_val_42_);
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v_val_42_);
return v___x_45_;
}
}
case 1:
{
lean_object* v_node_46_; size_t v___x_47_; size_t v___x_48_; 
v_node_46_ = lean_ctor_get(v___x_40_, 0);
v___x_47_ = ((size_t)5ULL);
v___x_48_ = lean_usize_shift_right(v_x_33_, v___x_47_);
v_x_32_ = v_node_46_;
v_x_33_ = v___x_48_;
goto _start;
}
default: 
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
}
else
{
lean_object* v_ks_51_; lean_object* v_vs_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_ks_51_ = lean_ctor_get(v_x_32_, 0);
v_vs_52_ = lean_ctor_get(v_x_32_, 1);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_ks_51_, v_vs_52_, v___x_53_, v_x_34_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
size_t v_x_554__boxed_58_; lean_object* v_res_59_; 
v_x_554__boxed_58_ = lean_unbox_usize(v_x_56_);
lean_dec(v_x_56_);
v_res_59_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_55_, v_x_554__boxed_58_, v_x_57_);
lean_dec_ref(v_x_57_);
lean_dec_ref(v_x_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
uint64_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; 
v___x_62_ = l_Lean_Expr_hash(v_x_61_);
v___x_63_ = lean_uint64_to_usize(v___x_62_);
v___x_64_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_60_, v___x_63_, v_x_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(v_x_65_, v_x_66_);
lean_dec_ref(v_x_66_);
lean_dec_ref(v_x_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_ks_72_; lean_object* v_vs_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_97_; 
v_ks_72_ = lean_ctor_get(v_x_68_, 0);
v_vs_73_ = lean_ctor_get(v_x_68_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_68_);
if (v_isSharedCheck_97_ == 0)
{
v___x_75_ = v_x_68_;
v_isShared_76_ = v_isSharedCheck_97_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_vs_73_);
lean_inc(v_ks_72_);
lean_dec(v_x_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_97_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_array_get_size(v_ks_72_);
v___x_78_ = lean_nat_dec_lt(v_x_69_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
lean_dec(v_x_69_);
v___x_79_ = lean_array_push(v_ks_72_, v_x_70_);
v___x_80_ = lean_array_push(v_vs_73_, v_x_71_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_80_);
lean_ctor_set(v___x_75_, 0, v___x_79_);
v___x_82_ = v___x_75_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
else
{
lean_object* v_k_x27_84_; uint8_t v___x_85_; 
v_k_x27_84_ = lean_array_fget_borrowed(v_ks_72_, v_x_69_);
v___x_85_ = lean_expr_eqv(v_x_70_, v_k_x27_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_87_; 
if (v_isShared_76_ == 0)
{
v___x_87_ = v___x_75_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_ks_72_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_vs_73_);
v___x_87_ = v_reuseFailAlloc_91_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_add(v_x_69_, v___x_88_);
lean_dec(v_x_69_);
v_x_68_ = v___x_87_;
v_x_69_ = v___x_89_;
goto _start;
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_92_ = lean_array_fset(v_ks_72_, v_x_69_, v_x_70_);
v___x_93_ = lean_array_fset(v_vs_73_, v_x_69_, v_x_71_);
lean_dec(v_x_69_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_93_);
lean_ctor_set(v___x_75_, 0, v___x_92_);
v___x_95_ = v___x_75_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_n_98_, lean_object* v_k_99_, lean_object* v_v_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_n_98_, v___x_101_, v_k_99_, v_v_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_104_, size_t v_x_105_, size_t v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v_es_109_; size_t v___x_110_; size_t v___x_111_; lean_object* v_j_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_es_109_ = lean_ctor_get(v_x_104_, 0);
v___x_110_ = ((size_t)31ULL);
v___x_111_ = lean_usize_land(v_x_105_, v___x_110_);
v_j_112_ = lean_usize_to_nat(v___x_111_);
v___x_113_ = lean_array_get_size(v_es_109_);
v___x_114_ = lean_nat_dec_lt(v_j_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec(v_j_112_);
lean_dec(v_x_108_);
lean_dec_ref(v_x_107_);
return v_x_104_;
}
else
{
lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_153_; 
lean_inc_ref(v_es_109_);
v_isSharedCheck_153_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v_x_104_, 0);
lean_dec(v_unused_154_);
v___x_116_ = v_x_104_;
v_isShared_117_ = v_isSharedCheck_153_;
goto v_resetjp_115_;
}
else
{
lean_dec(v_x_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_153_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_v_118_; lean_object* v___x_119_; lean_object* v_xs_x27_120_; lean_object* v___y_122_; 
v_v_118_ = lean_array_fget(v_es_109_, v_j_112_);
v___x_119_ = lean_box(0);
v_xs_x27_120_ = lean_array_fset(v_es_109_, v_j_112_, v___x_119_);
switch(lean_obj_tag(v_v_118_))
{
case 0:
{
lean_object* v_key_127_; lean_object* v_val_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_138_; 
v_key_127_ = lean_ctor_get(v_v_118_, 0);
v_val_128_ = lean_ctor_get(v_v_118_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_v_118_);
if (v_isSharedCheck_138_ == 0)
{
v___x_130_ = v_v_118_;
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_val_128_);
lean_inc(v_key_127_);
lean_dec(v_v_118_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
uint8_t v___x_132_; 
v___x_132_ = lean_expr_eqv(v_x_107_, v_key_127_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_del_object(v___x_130_);
v___x_133_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_127_, v_val_128_, v_x_107_, v_x_108_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
v___y_122_ = v___x_134_;
goto v___jp_121_;
}
else
{
lean_object* v___x_136_; 
lean_dec(v_val_128_);
lean_dec(v_key_127_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v_x_108_);
lean_ctor_set(v___x_130_, 0, v_x_107_);
v___x_136_ = v___x_130_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_x_107_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_x_108_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v___y_122_ = v___x_136_;
goto v___jp_121_;
}
}
}
}
case 1:
{
lean_object* v_node_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_151_; 
v_node_139_ = lean_ctor_get(v_v_118_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_v_118_);
if (v_isSharedCheck_151_ == 0)
{
v___x_141_ = v_v_118_;
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_node_139_);
lean_dec(v_v_118_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_143_ = ((size_t)5ULL);
v___x_144_ = lean_usize_shift_right(v_x_105_, v___x_143_);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_add(v_x_106_, v___x_145_);
v___x_147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_node_139_, v___x_144_, v___x_146_, v_x_107_, v_x_108_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_147_);
v___x_149_ = v___x_141_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
v___y_122_ = v___x_149_;
goto v___jp_121_;
}
}
}
default: 
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_x_107_);
lean_ctor_set(v___x_152_, 1, v_x_108_);
v___y_122_ = v___x_152_;
goto v___jp_121_;
}
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_array_fset(v_xs_x27_120_, v_j_112_, v___y_122_);
lean_dec(v_j_112_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_123_);
v___x_125_ = v___x_116_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
else
{
lean_object* v_ks_155_; lean_object* v_vs_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_174_; 
v_ks_155_ = lean_ctor_get(v_x_104_, 0);
v_vs_156_ = lean_ctor_get(v_x_104_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_174_ == 0)
{
v___x_158_ = v_x_104_;
v_isShared_159_ = v_isSharedCheck_174_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_vs_156_);
lean_inc(v_ks_155_);
lean_dec(v_x_104_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_174_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_ks_155_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_vs_156_);
v___x_161_ = v_reuseFailAlloc_173_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v_newNode_162_; size_t v___x_163_; uint8_t v___x_164_; 
v_newNode_162_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v___x_161_, v_x_107_, v_x_108_);
v___x_163_ = ((size_t)7ULL);
v___x_164_ = lean_usize_dec_le(v___x_163_, v_x_106_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_165_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_162_);
v___x_166_ = lean_unsigned_to_nat(4u);
v___x_167_ = lean_nat_dec_lt(v___x_165_, v___x_166_);
lean_dec(v___x_165_);
if (v___x_167_ == 0)
{
lean_object* v_ks_168_; lean_object* v_vs_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_ks_168_ = lean_ctor_get(v_newNode_162_, 0);
lean_inc_ref(v_ks_168_);
v_vs_169_ = lean_ctor_get(v_newNode_162_, 1);
lean_inc_ref(v_vs_169_);
lean_dec_ref(v_newNode_162_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___x_172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_x_106_, v_ks_168_, v_vs_169_, v___x_170_, v___x_171_);
lean_dec_ref(v_vs_169_);
lean_dec_ref(v_ks_168_);
return v___x_172_;
}
else
{
return v_newNode_162_;
}
}
else
{
return v_newNode_162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(size_t v_depth_175_, lean_object* v_keys_176_, lean_object* v_vals_177_, lean_object* v_i_178_, lean_object* v_entries_179_){
_start:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_array_get_size(v_keys_176_);
v___x_181_ = lean_nat_dec_lt(v_i_178_, v___x_180_);
if (v___x_181_ == 0)
{
lean_dec(v_i_178_);
return v_entries_179_;
}
else
{
lean_object* v_k_182_; lean_object* v_v_183_; uint64_t v___x_184_; size_t v_h_185_; size_t v___x_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v_h_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_k_182_ = lean_array_fget_borrowed(v_keys_176_, v_i_178_);
v_v_183_ = lean_array_fget_borrowed(v_vals_177_, v_i_178_);
v___x_184_ = l_Lean_Expr_hash(v_k_182_);
v_h_185_ = lean_uint64_to_usize(v___x_184_);
v___x_186_ = ((size_t)5ULL);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_sub(v_depth_175_, v___x_188_);
v___x_190_ = lean_usize_mul(v___x_186_, v___x_189_);
v_h_191_ = lean_usize_shift_right(v_h_185_, v___x_190_);
v___x_192_ = lean_nat_add(v_i_178_, v___x_187_);
lean_dec(v_i_178_);
lean_inc(v_v_183_);
lean_inc(v_k_182_);
v___x_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_entries_179_, v_h_191_, v_depth_175_, v_k_182_, v_v_183_);
v_i_178_ = v___x_192_;
v_entries_179_ = v___x_193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_195_, lean_object* v_keys_196_, lean_object* v_vals_197_, lean_object* v_i_198_, lean_object* v_entries_199_){
_start:
{
size_t v_depth_boxed_200_; lean_object* v_res_201_; 
v_depth_boxed_200_ = lean_unbox_usize(v_depth_195_);
lean_dec(v_depth_195_);
v_res_201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_boxed_200_, v_keys_196_, v_vals_197_, v_i_198_, v_entries_199_);
lean_dec_ref(v_vals_197_);
lean_dec_ref(v_keys_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
size_t v_x_689__boxed_207_; size_t v_x_690__boxed_208_; lean_object* v_res_209_; 
v_x_689__boxed_207_ = lean_unbox_usize(v_x_203_);
lean_dec(v_x_203_);
v_x_690__boxed_208_ = lean_unbox_usize(v_x_204_);
lean_dec(v_x_204_);
v_res_209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_202_, v_x_689__boxed_207_, v_x_690__boxed_208_, v_x_205_, v_x_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
uint64_t v___x_213_; size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_213_ = l_Lean_Expr_hash(v_x_211_);
v___x_214_ = lean_uint64_to_usize(v___x_213_);
v___x_215_ = ((size_t)1ULL);
v___x_216_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_210_, v___x_214_, v___x_215_, v_x_211_, v_x_212_);
return v___x_216_;
}
}
static lean_object* _init_l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_220_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__2));
v___x_221_ = lean_unsigned_to_nat(14u);
v___x_222_ = lean_unsigned_to_nat(178u);
v___x_223_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__1));
v___x_224_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__0));
v___x_225_ = l_mkPanicMessageWithDecl(v___x_224_, v___x_223_, v___x_222_, v___x_221_, v___x_220_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3(lean_object* v_newState_226_, lean_object* v_x_227_, lean_object* v_x_228_){
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
v___x_253_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(v_map_252_, v_head_229_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3, &l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3_once, _init_l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___closed__3);
v___x_255_ = l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__2(v___x_254_);
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
v___x_242_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(v_map_236_, v_head_229_, v___y_235_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3___boxed(lean_object* v_newState_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3(v_newState_258_, v_x_259_, v_x_260_);
lean_dec_ref(v_newState_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(lean_object* v_oldState_264_, lean_object* v_newState_265_, lean_object* v_x_266_, lean_object* v_s_267_){
_start:
{
lean_object* v_revExprs_268_; lean_object* v_revExprs_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_newExprs_274_; lean_object* v___x_275_; 
v_revExprs_268_ = lean_ctor_get(v_newState_265_, 2);
v_revExprs_269_ = lean_ctor_get(v_oldState_264_, 2);
v___x_270_ = l_List_lengthTR___redArg(v_revExprs_268_);
v___x_271_ = l_List_lengthTR___redArg(v_revExprs_269_);
v___x_272_ = lean_nat_sub(v___x_270_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_270_);
v___x_273_ = ((lean_object*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_));
lean_inc(v_revExprs_268_);
v_newExprs_274_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_revExprs_268_, v_revExprs_268_, v___x_272_, v___x_273_);
v___x_275_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__3(v_newState_265_, v_s_267_, v_newExprs_274_);
lean_dec_ref(v_newState_265_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(lean_object* v_oldState_276_, lean_object* v_newState_277_, lean_object* v_x_278_, lean_object* v_s_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(v_oldState_276_, v_newState_277_, v_x_278_, v_s_279_);
lean_dec(v_x_278_);
lean_dec_ref(v_oldState_276_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(lean_object* v___x_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(lean_object* v___x_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(v___x_284_);
return v_res_286_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_288_; lean_object* v___f_289_; 
v___x_288_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__2, &l_Lean_instInhabitedClosedTermCache_default___closed__2_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__2);
v___f_289_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_289_, 0, v___x_288_);
return v___f_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___f_293_ = lean_obj_once(&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_, &l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_);
v___x_294_ = ((lean_object*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_));
v___x_295_ = lean_box(0);
v___x_296_ = l_Lean_registerEnvExtension___redArg(v___f_293_, v___x_294_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2____boxed(lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_();
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(v_x_300_, v_x_301_, v_x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(v_x_305_, v_x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1(v_00_u03b2_308_, v_x_309_, v_x_310_);
lean_dec_ref(v_x_310_);
lean_dec_ref(v_x_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_312_, lean_object* v_x_313_, size_t v_x_314_, size_t v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_313_, v_x_314_, v_x_315_, v_x_316_, v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
size_t v_x_1014__boxed_325_; size_t v_x_1015__boxed_326_; lean_object* v_res_327_; 
v_x_1014__boxed_325_ = lean_unbox_usize(v_x_321_);
lean_dec(v_x_321_);
v_x_1015__boxed_326_ = lean_unbox_usize(v_x_322_);
lean_dec(v_x_322_);
v_res_327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_319_, v_x_320_, v_x_1014__boxed_325_, v_x_1015__boxed_326_, v_x_323_, v_x_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_328_, lean_object* v_x_329_, size_t v_x_330_, lean_object* v_x_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_329_, v_x_330_, v_x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_333_, lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
size_t v_x_1031__boxed_337_; lean_object* v_res_338_; 
v_x_1031__boxed_337_ = lean_unbox_usize(v_x_335_);
lean_dec(v_x_335_);
v_res_338_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_333_, v_x_334_, v_x_1031__boxed_337_, v_x_336_);
lean_dec_ref(v_x_336_);
lean_dec_ref(v_x_334_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_339_, lean_object* v_n_340_, lean_object* v_k_341_, lean_object* v_v_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_n_340_, v_k_341_, v_v_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object* v_00_u03b2_344_, size_t v_depth_345_, lean_object* v_keys_346_, lean_object* v_vals_347_, lean_object* v_heq_348_, lean_object* v_i_349_, lean_object* v_entries_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_345_, v_keys_346_, v_vals_347_, v_i_349_, v_entries_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_352_, lean_object* v_depth_353_, lean_object* v_keys_354_, lean_object* v_vals_355_, lean_object* v_heq_356_, lean_object* v_i_357_, lean_object* v_entries_358_){
_start:
{
size_t v_depth_boxed_359_; lean_object* v_res_360_; 
v_depth_boxed_359_ = lean_unbox_usize(v_depth_353_);
lean_dec(v_depth_353_);
v_res_360_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_00_u03b2_352_, v_depth_boxed_359_, v_keys_354_, v_vals_355_, v_heq_356_, v_i_357_, v_entries_358_);
lean_dec_ref(v_vals_355_);
lean_dec_ref(v_keys_354_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object* v_00_u03b2_361_, lean_object* v_keys_362_, lean_object* v_vals_363_, lean_object* v_heq_364_, lean_object* v_i_365_, lean_object* v_k_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_362_, v_vals_363_, v_i_365_, v_k_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_368_, lean_object* v_keys_369_, lean_object* v_vals_370_, lean_object* v_heq_371_, lean_object* v_i_372_, lean_object* v_k_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1_spec__2_spec__6(v_00_u03b2_368_, v_keys_369_, v_vals_370_, v_heq_371_, v_i_372_, v_k_373_);
lean_dec_ref(v_k_373_);
lean_dec_ref(v_vals_370_);
lean_dec_ref(v_keys_369_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_x_376_, v_x_377_, v_x_378_, v_x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lam__0(lean_object* v_e_381_, lean_object* v_n_382_, lean_object* v_s_383_){
_start:
{
lean_object* v_map_384_; lean_object* v_constNames_385_; lean_object* v_revExprs_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_396_; 
v_map_384_ = lean_ctor_get(v_s_383_, 0);
v_constNames_385_ = lean_ctor_get(v_s_383_, 1);
v_revExprs_386_ = lean_ctor_get(v_s_383_, 2);
v_isSharedCheck_396_ = !lean_is_exclusive(v_s_383_);
if (v_isSharedCheck_396_ == 0)
{
v___x_388_ = v_s_383_;
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_revExprs_386_);
lean_inc(v_constNames_385_);
lean_inc(v_map_384_);
lean_dec(v_s_383_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
lean_inc(v_n_382_);
lean_inc_ref(v_e_381_);
v___x_390_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__0___redArg(v_map_384_, v_e_381_, v_n_382_);
v___x_391_ = l_Lean_NameSet_insert(v_constNames_385_, v_n_382_);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v_e_381_);
lean_ctor_set(v___x_392_, 1, v_revExprs_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 2, v___x_392_);
lean_ctor_set(v___x_388_, 1, v___x_391_);
lean_ctor_set(v___x_388_, 0, v___x_390_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName(lean_object* v_env_397_, lean_object* v_e_398_, lean_object* v_n_399_){
_start:
{
lean_object* v___x_400_; lean_object* v_asyncMode_401_; lean_object* v___f_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_400_ = l_Lean_closedTermCacheExt;
v_asyncMode_401_ = lean_ctor_get(v___x_400_, 2);
v___f_402_ = lean_alloc_closure((void*)(l_Lean_cacheClosedTermName___lam__0), 3, 2);
lean_closure_set(v___f_402_, 0, v_e_398_);
lean_closure_set(v___f_402_, 1, v_n_399_);
v___x_403_ = lean_box(0);
v___x_404_ = l_Lean_EnvExtension_modifyState___redArg(v___x_400_, v_env_397_, v___f_402_, v_asyncMode_401_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f(lean_object* v_env_405_, lean_object* v_e_406_){
_start:
{
lean_object* v___x_407_; lean_object* v_asyncMode_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_map_412_; lean_object* v___x_413_; 
v___x_407_ = l_Lean_closedTermCacheExt;
v_asyncMode_408_ = lean_ctor_get(v___x_407_, 2);
v___x_409_ = l_Lean_instInhabitedClosedTermCache_default;
v___x_410_ = lean_box(0);
v___x_411_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_409_, v___x_407_, v_env_405_, v_asyncMode_408_, v___x_410_);
v_map_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_map_412_);
lean_dec(v___x_411_);
v___x_413_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2__spec__1___redArg(v_map_412_, v_e_406_);
lean_dec_ref(v_map_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f___boxed(lean_object* v_env_414_, lean_object* v_e_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_getClosedTermName_x3f(v_env_414_, v_e_415_);
lean_dec_ref(v_e_415_);
return v_res_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_isClosedTermName(lean_object* v_env_417_, lean_object* v_n_418_){
_start:
{
lean_object* v___x_419_; lean_object* v_asyncMode_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_constNames_424_; uint8_t v___x_425_; 
v___x_419_ = l_Lean_closedTermCacheExt;
v_asyncMode_420_ = lean_ctor_get(v___x_419_, 2);
v___x_421_ = l_Lean_instInhabitedClosedTermCache_default;
v___x_422_ = lean_box(0);
v___x_423_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_421_, v___x_419_, v_env_417_, v_asyncMode_420_, v___x_422_);
v_constNames_424_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_constNames_424_);
lean_dec(v___x_423_);
v___x_425_ = l_Lean_NameSet_contains(v_constNames_424_, v_n_418_);
lean_dec(v_constNames_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object* v_env_426_, lean_object* v_n_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lean_isClosedTermName(v_env_426_, v_n_427_);
lean_dec(v_n_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
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
res = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3608529163____hygCtx___hyg_2_();
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
