// Lean compiler output
// Module: Lean.Meta.Sym.MaxFVar
// Imports: public import Lean.Meta.Sym.SymM
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Meta.Sym.MaxFVar"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.Sym.getMaxFVar\?"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object* v_fvarId1_x3f_1_, lean_object* v_fvarId2_x3f_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
if (lean_obj_tag(v_fvarId1_x3f_1_) == 1)
{
if (lean_obj_tag(v_fvarId2_x3f_2_) == 1)
{
lean_object* v_val_7_; lean_object* v_val_8_; uint8_t v___x_9_; 
v_val_7_ = lean_ctor_get(v_fvarId1_x3f_1_, 0);
v_val_8_ = lean_ctor_get(v_fvarId2_x3f_2_, 0);
v___x_9_ = l_Lean_instBEqFVarId_beq(v_val_7_, v_val_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_inc_ref(v_a_3_);
lean_inc(v_val_7_);
v___x_10_ = l_Lean_FVarId_getDecl___redArg(v_val_7_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
lean_dec_ref(v___x_10_);
lean_inc_ref(v_a_3_);
lean_inc(v_val_8_);
v___x_12_ = l_Lean_FVarId_getDecl___redArg(v_val_8_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_26_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_26_ == 0)
{
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_26_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_26_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_17_ = l_Lean_LocalDecl_index(v_a_13_);
lean_dec(v_a_13_);
v___x_18_ = l_Lean_LocalDecl_index(v_a_11_);
lean_dec(v_a_11_);
v___x_19_ = lean_nat_dec_lt(v___x_17_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v___x_17_);
if (v___x_19_ == 0)
{
lean_object* v___x_21_; 
lean_dec_ref(v_fvarId1_x3f_1_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_fvarId2_x3f_2_);
v___x_21_ = v___x_15_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_fvarId2_x3f_2_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
else
{
lean_object* v___x_24_; 
lean_dec_ref(v_fvarId2_x3f_2_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_fvarId1_x3f_1_);
v___x_24_ = v___x_15_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_fvarId1_x3f_1_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
else
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
lean_dec(v_a_11_);
lean_dec_ref(v_fvarId2_x3f_2_);
lean_dec_ref(v_fvarId1_x3f_1_);
v_a_27_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_34_ == 0)
{
v___x_29_ = v___x_12_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_12_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_27_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
lean_dec_ref(v_fvarId2_x3f_2_);
lean_dec_ref(v_fvarId1_x3f_1_);
v_a_35_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_10_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_10_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
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
else
{
lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
v_isSharedCheck_49_ = !lean_is_exclusive(v_fvarId2_x3f_2_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v_fvarId2_x3f_2_, 0);
lean_dec(v_unused_50_);
v___x_44_ = v_fvarId2_x3f_2_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_dec(v_fvarId2_x3f_2_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 0);
lean_ctor_set(v___x_44_, 0, v_fvarId1_x3f_1_);
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_fvarId1_x3f_1_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
else
{
lean_object* v___x_51_; 
lean_dec(v_fvarId2_x3f_2_);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v_fvarId1_x3f_1_);
return v___x_51_;
}
}
else
{
lean_object* v___x_52_; 
lean_dec(v_fvarId1_x3f_1_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_fvarId2_x3f_2_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object* v_fvarId1_x3f_53_, lean_object* v_fvarId2_x3f_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_53_, v_fvarId2_x3f_54_, v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object* v_fvarId1_x3f_60_, lean_object* v_fvarId2_x3f_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_60_, v_fvarId2_x3f_61_, v_a_62_, v_a_64_, v_a_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object* v_fvarId1_x3f_68_, lean_object* v_fvarId2_x3f_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(v_fvarId1_x3f_68_, v_fvarId2_x3f_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object* v_e_78_, lean_object* v_k_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
uint8_t v___y_88_; uint8_t v___x_131_; 
v___x_131_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = l_Lean_Expr_hasMVar(v_e_78_);
v___y_88_ = v___x_132_;
goto v___jp_87_;
}
else
{
v___y_88_ = v___x_131_;
goto v___jp_87_;
}
v___jp_87_:
{
if (v___y_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_maxFVar_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
v___x_91_ = lean_st_ref_get(v_a_81_);
v_maxFVar_92_ = lean_ctor_get(v___x_91_, 1);
lean_inc_ref(v_maxFVar_92_);
lean_dec(v___x_91_);
v___f_93_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
v___f_94_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
lean_inc_ref(v_e_78_);
v___x_95_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_93_, v___f_94_, v_maxFVar_92_, v_e_78_);
if (lean_obj_tag(v___x_95_) == 1)
{
lean_object* v_val_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v_val_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_val_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 0);
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_val_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v___x_95_);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
v___x_104_ = lean_apply_7(v_k_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, lean_box(0));
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_130_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_130_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_130_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_130_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v_share_110_; lean_object* v_maxFVar_111_; lean_object* v_proofInstInfo_112_; lean_object* v_inferType_113_; lean_object* v_getLevel_114_; lean_object* v_congrInfo_115_; lean_object* v_defEqI_116_; uint8_t v_debug_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_129_; 
v___x_109_ = lean_st_ref_take(v_a_81_);
v_share_110_ = lean_ctor_get(v___x_109_, 0);
v_maxFVar_111_ = lean_ctor_get(v___x_109_, 1);
v_proofInstInfo_112_ = lean_ctor_get(v___x_109_, 2);
v_inferType_113_ = lean_ctor_get(v___x_109_, 3);
v_getLevel_114_ = lean_ctor_get(v___x_109_, 4);
v_congrInfo_115_ = lean_ctor_get(v___x_109_, 5);
v_defEqI_116_ = lean_ctor_get(v___x_109_, 6);
v_debug_117_ = lean_ctor_get_uint8(v___x_109_, sizeof(void*)*7);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_129_ == 0)
{
v___x_119_ = v___x_109_;
v_isShared_120_ = v_isSharedCheck_129_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_defEqI_116_);
lean_inc(v_congrInfo_115_);
lean_inc(v_getLevel_114_);
lean_inc(v_inferType_113_);
lean_inc(v_proofInstInfo_112_);
lean_inc(v_maxFVar_111_);
lean_inc(v_share_110_);
lean_dec(v___x_109_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_129_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
lean_inc(v_a_105_);
v___x_121_ = l_Lean_PersistentHashMap_insert___redArg(v___f_93_, v___f_94_, v_maxFVar_111_, v_e_78_, v_a_105_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_share_110_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_proofInstInfo_112_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_inferType_113_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v_getLevel_114_);
lean_ctor_set(v_reuseFailAlloc_128_, 5, v_congrInfo_115_);
lean_ctor_set(v_reuseFailAlloc_128_, 6, v_defEqI_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_128_, sizeof(void*)*7, v_debug_117_);
v___x_123_ = v_reuseFailAlloc_128_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_st_ref_set(v_a_81_, v___x_123_);
if (v_isShared_108_ == 0)
{
v___x_126_ = v___x_107_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_105_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_78_);
return v___x_104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object* v_e_133_, lean_object* v_k_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(v_e_133_, v_k_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
return v_res_142_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_instMonadEIO(lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_toApplicative_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_221_; 
v___x_156_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_157_ = l_StateRefT_x27_instMonad___redArg(v___x_156_);
v_toApplicative_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v___x_157_, 1);
lean_dec(v_unused_222_);
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_221_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_toApplicative_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_221_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_toFunctor_162_; lean_object* v_toSeq_163_; lean_object* v_toSeqLeft_164_; lean_object* v_toSeqRight_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_219_; 
v_toFunctor_162_ = lean_ctor_get(v_toApplicative_158_, 0);
v_toSeq_163_ = lean_ctor_get(v_toApplicative_158_, 2);
v_toSeqLeft_164_ = lean_ctor_get(v_toApplicative_158_, 3);
v_toSeqRight_165_ = lean_ctor_get(v_toApplicative_158_, 4);
v_isSharedCheck_219_ = !lean_is_exclusive(v_toApplicative_158_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_dec(v_unused_220_);
v___x_167_ = v_toApplicative_158_;
v_isShared_168_ = v_isSharedCheck_219_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_toSeqRight_165_);
lean_inc(v_toSeqLeft_164_);
lean_inc(v_toSeq_163_);
lean_inc(v_toFunctor_162_);
lean_dec(v_toApplicative_158_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_219_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_178_; 
v___f_169_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__1));
v___f_170_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__2));
lean_inc_ref(v_toFunctor_162_);
v___f_171_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_171_, 0, v_toFunctor_162_);
v___f_172_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_172_, 0, v_toFunctor_162_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___f_171_);
lean_ctor_set(v___x_173_, 1, v___f_172_);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_174_, 0, v_toSeqRight_165_);
v___f_175_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_175_, 0, v_toSeqLeft_164_);
v___f_176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_176_, 0, v_toSeq_163_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 4, v___f_174_);
lean_ctor_set(v___x_167_, 3, v___f_175_);
lean_ctor_set(v___x_167_, 2, v___f_176_);
lean_ctor_set(v___x_167_, 1, v___f_169_);
lean_ctor_set(v___x_167_, 0, v___x_173_);
v___x_178_ = v___x_167_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___f_169_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v___f_176_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v___f_175_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v___f_174_);
v___x_178_ = v_reuseFailAlloc_218_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___f_170_);
lean_ctor_set(v___x_160_, 0, v___x_178_);
v___x_180_ = v___x_160_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___f_170_);
v___x_180_ = v_reuseFailAlloc_217_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v_toApplicative_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_215_; 
v___x_181_ = l_StateRefT_x27_instMonad___redArg(v___x_180_);
v_toApplicative_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v___x_181_, 1);
lean_dec(v_unused_216_);
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_215_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_toApplicative_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_215_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_toFunctor_186_; lean_object* v_toSeq_187_; lean_object* v_toSeqLeft_188_; lean_object* v_toSeqRight_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_213_; 
v_toFunctor_186_ = lean_ctor_get(v_toApplicative_182_, 0);
v_toSeq_187_ = lean_ctor_get(v_toApplicative_182_, 2);
v_toSeqLeft_188_ = lean_ctor_get(v_toApplicative_182_, 3);
v_toSeqRight_189_ = lean_ctor_get(v_toApplicative_182_, 4);
v_isSharedCheck_213_ = !lean_is_exclusive(v_toApplicative_182_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_toApplicative_182_, 1);
lean_dec(v_unused_214_);
v___x_191_ = v_toApplicative_182_;
v_isShared_192_ = v_isSharedCheck_213_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_toSeqRight_189_);
lean_inc(v_toSeqLeft_188_);
lean_inc(v_toSeq_187_);
lean_inc(v_toFunctor_186_);
lean_dec(v_toApplicative_182_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_213_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___x_202_; 
v___f_193_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__3));
v___f_194_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__4));
lean_inc_ref(v_toFunctor_186_);
v___f_195_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_195_, 0, v_toFunctor_186_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_196_, 0, v_toFunctor_186_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___f_195_);
lean_ctor_set(v___x_197_, 1, v___f_196_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_198_, 0, v_toSeqRight_189_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_199_, 0, v_toSeqLeft_188_);
v___f_200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_200_, 0, v_toSeq_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 4, v___f_198_);
lean_ctor_set(v___x_191_, 3, v___f_199_);
lean_ctor_set(v___x_191_, 2, v___f_200_);
lean_ctor_set(v___x_191_, 1, v___f_193_);
lean_ctor_set(v___x_191_, 0, v___x_197_);
v___x_202_ = v___x_191_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___f_193_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v___f_200_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v___f_199_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v___f_198_);
v___x_202_ = v_reuseFailAlloc_212_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___f_194_);
lean_ctor_set(v___x_184_, 0, v___x_202_);
v___x_204_ = v___x_184_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___f_194_);
v___x_204_ = v_reuseFailAlloc_211_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___x_4716__overap_209_; lean_object* v___x_210_; 
v___x_205_ = l_StateRefT_x27_instMonad___redArg(v___x_204_);
v___x_206_ = lean_box(0);
v___x_207_ = l_instInhabitedOfMonad___redArg(v___x_205_, v___x_206_);
v___f_208_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_208_, 0, v___x_207_);
v___x_4716__overap_209_ = lean_panic_fn(v___f_208_, v_msg_148_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
v___x_210_ = lean_apply_7(v___x_4716__overap_209_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, lean_box(0));
return v___x_210_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object* v_msg_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v_msg_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_ks_236_; lean_object* v_vs_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_261_; 
v_ks_236_ = lean_ctor_get(v_x_232_, 0);
v_vs_237_ = lean_ctor_get(v_x_232_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_261_ == 0)
{
v___x_239_ = v_x_232_;
v_isShared_240_ = v_isSharedCheck_261_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_vs_237_);
lean_inc(v_ks_236_);
lean_dec(v_x_232_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_261_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_array_get_size(v_ks_236_);
v___x_242_ = lean_nat_dec_lt(v_x_233_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec(v_x_233_);
v___x_243_ = lean_array_push(v_ks_236_, v_x_234_);
v___x_244_ = lean_array_push(v_vs_237_, v_x_235_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_244_);
lean_ctor_set(v___x_239_, 0, v___x_243_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_object* v_k_x27_248_; uint8_t v___x_249_; 
v_k_x27_248_ = lean_array_fget_borrowed(v_ks_236_, v_x_233_);
v___x_249_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_234_, v_k_x27_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_251_; 
if (v_isShared_240_ == 0)
{
v___x_251_ = v___x_239_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_ks_236_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_vs_237_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_add(v_x_233_, v___x_252_);
lean_dec(v_x_233_);
v_x_232_ = v___x_251_;
v_x_233_ = v___x_253_;
goto _start;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = lean_array_fset(v_ks_236_, v_x_233_, v_x_234_);
v___x_257_ = lean_array_fset(v_vs_237_, v_x_233_, v_x_235_);
lean_dec(v_x_233_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_257_);
lean_ctor_set(v___x_239_, 0, v___x_256_);
v___x_259_ = v___x_239_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_n_262_, lean_object* v_k_263_, lean_object* v_v_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_262_, v___x_265_, v_k_263_, v_v_264_);
return v___x_266_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; 
v___x_267_ = ((size_t)5ULL);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_shift_left(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; 
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_272_ = lean_usize_sub(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_274_, size_t v_x_275_, size_t v_x_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v_es_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; lean_object* v_j_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_es_279_ = lean_ctor_get(v_x_274_, 0);
v___x_280_ = ((size_t)5ULL);
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_283_ = lean_usize_land(v_x_275_, v___x_282_);
v_j_284_ = lean_usize_to_nat(v___x_283_);
v___x_285_ = lean_array_get_size(v_es_279_);
v___x_286_ = lean_nat_dec_lt(v_j_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec(v_j_284_);
lean_dec(v_x_278_);
lean_dec_ref(v_x_277_);
return v_x_274_;
}
else
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_323_; 
lean_inc_ref(v_es_279_);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v_x_274_, 0);
lean_dec(v_unused_324_);
v___x_288_ = v_x_274_;
v_isShared_289_ = v_isSharedCheck_323_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_x_274_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_323_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_v_290_; lean_object* v___x_291_; lean_object* v_xs_x27_292_; lean_object* v___y_294_; 
v_v_290_ = lean_array_fget(v_es_279_, v_j_284_);
v___x_291_ = lean_box(0);
v_xs_x27_292_ = lean_array_fset(v_es_279_, v_j_284_, v___x_291_);
switch(lean_obj_tag(v_v_290_))
{
case 0:
{
lean_object* v_key_299_; lean_object* v_val_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v_key_299_ = lean_ctor_get(v_v_290_, 0);
v_val_300_ = lean_ctor_get(v_v_290_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_v_290_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v_v_290_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_val_300_);
lean_inc(v_key_299_);
lean_dec(v_v_290_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint8_t v___x_304_; 
v___x_304_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_277_, v_key_299_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_del_object(v___x_302_);
v___x_305_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_299_, v_val_300_, v_x_277_, v_x_278_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___y_294_ = v___x_306_;
goto v___jp_293_;
}
else
{
lean_object* v___x_308_; 
lean_dec(v_val_300_);
lean_dec(v_key_299_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v_x_278_);
lean_ctor_set(v___x_302_, 0, v_x_277_);
v___x_308_ = v___x_302_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_x_277_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_x_278_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
v___y_294_ = v___x_308_;
goto v___jp_293_;
}
}
}
}
case 1:
{
lean_object* v_node_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_321_; 
v_node_311_ = lean_ctor_get(v_v_290_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_v_290_);
if (v_isSharedCheck_321_ == 0)
{
v___x_313_ = v_v_290_;
v_isShared_314_ = v_isSharedCheck_321_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_node_311_);
lean_dec(v_v_290_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_321_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_315_ = lean_usize_shift_right(v_x_275_, v___x_280_);
v___x_316_ = lean_usize_add(v_x_276_, v___x_281_);
v___x_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_311_, v___x_315_, v___x_316_, v_x_277_, v_x_278_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_317_);
v___x_319_ = v___x_313_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
v___y_294_ = v___x_319_;
goto v___jp_293_;
}
}
}
default: 
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_x_277_);
lean_ctor_set(v___x_322_, 1, v_x_278_);
v___y_294_ = v___x_322_;
goto v___jp_293_;
}
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_array_fset(v_xs_x27_292_, v_j_284_, v___y_294_);
lean_dec(v_j_284_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_295_);
v___x_297_ = v___x_288_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
else
{
lean_object* v_ks_325_; lean_object* v_vs_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_346_; 
v_ks_325_ = lean_ctor_get(v_x_274_, 0);
v_vs_326_ = lean_ctor_get(v_x_274_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_346_ == 0)
{
v___x_328_ = v_x_274_;
v_isShared_329_ = v_isSharedCheck_346_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_vs_326_);
lean_inc(v_ks_325_);
lean_dec(v_x_274_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_346_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_ks_325_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_vs_326_);
v___x_331_ = v_reuseFailAlloc_345_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v_newNode_332_; uint8_t v___y_334_; size_t v___x_340_; uint8_t v___x_341_; 
v_newNode_332_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_331_, v_x_277_, v_x_278_);
v___x_340_ = ((size_t)7ULL);
v___x_341_ = lean_usize_dec_le(v___x_340_, v_x_276_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_332_);
v___x_343_ = lean_unsigned_to_nat(4u);
v___x_344_ = lean_nat_dec_lt(v___x_342_, v___x_343_);
lean_dec(v___x_342_);
v___y_334_ = v___x_344_;
goto v___jp_333_;
}
else
{
v___y_334_ = v___x_341_;
goto v___jp_333_;
}
v___jp_333_:
{
if (v___y_334_ == 0)
{
lean_object* v_ks_335_; lean_object* v_vs_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_ks_335_ = lean_ctor_get(v_newNode_332_, 0);
lean_inc_ref(v_ks_335_);
v_vs_336_ = lean_ctor_get(v_newNode_332_, 1);
lean_inc_ref(v_vs_336_);
lean_dec_ref(v_newNode_332_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2);
v___x_339_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_276_, v_ks_335_, v_vs_336_, v___x_337_, v___x_338_);
lean_dec_ref(v_vs_336_);
lean_dec_ref(v_ks_335_);
return v___x_339_;
}
else
{
return v_newNode_332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_347_, lean_object* v_keys_348_, lean_object* v_vals_349_, lean_object* v_i_350_, lean_object* v_entries_351_){
_start:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_array_get_size(v_keys_348_);
v___x_353_ = lean_nat_dec_lt(v_i_350_, v___x_352_);
if (v___x_353_ == 0)
{
lean_dec(v_i_350_);
return v_entries_351_;
}
else
{
lean_object* v_k_354_; lean_object* v_v_355_; uint64_t v___x_356_; size_t v_h_357_; size_t v___x_358_; lean_object* v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v_h_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_k_354_ = lean_array_fget_borrowed(v_keys_348_, v_i_350_);
v_v_355_ = lean_array_fget_borrowed(v_vals_349_, v_i_350_);
v___x_356_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_354_);
v_h_357_ = lean_uint64_to_usize(v___x_356_);
v___x_358_ = ((size_t)5ULL);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_sub(v_depth_347_, v___x_360_);
v___x_362_ = lean_usize_mul(v___x_358_, v___x_361_);
v_h_363_ = lean_usize_shift_right(v_h_357_, v___x_362_);
v___x_364_ = lean_nat_add(v_i_350_, v___x_359_);
lean_dec(v_i_350_);
lean_inc(v_v_355_);
lean_inc(v_k_354_);
v___x_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_351_, v_h_363_, v_depth_347_, v_k_354_, v_v_355_);
v_i_350_ = v___x_364_;
v_entries_351_ = v___x_365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_367_, lean_object* v_keys_368_, lean_object* v_vals_369_, lean_object* v_i_370_, lean_object* v_entries_371_){
_start:
{
size_t v_depth_boxed_372_; lean_object* v_res_373_; 
v_depth_boxed_372_ = lean_unbox_usize(v_depth_367_);
lean_dec(v_depth_367_);
v_res_373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_372_, v_keys_368_, v_vals_369_, v_i_370_, v_entries_371_);
lean_dec_ref(v_vals_369_);
lean_dec_ref(v_keys_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
size_t v_x_5354__boxed_379_; size_t v_x_5355__boxed_380_; lean_object* v_res_381_; 
v_x_5354__boxed_379_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_x_5355__boxed_380_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_res_381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_374_, v_x_5354__boxed_379_, v_x_5355__boxed_380_, v_x_377_, v_x_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
uint64_t v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v___x_388_; 
v___x_385_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_383_);
v___x_386_ = lean_uint64_to_usize(v___x_385_);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_382_, v___x_386_, v___x_387_, v_x_383_, v_x_384_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_389_, lean_object* v_vals_390_, lean_object* v_i_391_, lean_object* v_k_392_){
_start:
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = lean_array_get_size(v_keys_389_);
v___x_394_ = lean_nat_dec_lt(v_i_391_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_dec(v_i_391_);
v___x_395_ = lean_box(0);
return v___x_395_;
}
else
{
lean_object* v_k_x27_396_; uint8_t v___x_397_; 
v_k_x27_396_ = lean_array_fget_borrowed(v_keys_389_, v_i_391_);
v___x_397_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_392_, v_k_x27_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_i_391_, v___x_398_);
lean_dec(v_i_391_);
v_i_391_ = v___x_399_;
goto _start;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_array_fget_borrowed(v_vals_390_, v_i_391_);
lean_dec(v_i_391_);
lean_inc(v___x_401_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_403_, lean_object* v_vals_404_, lean_object* v_i_405_, lean_object* v_k_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_403_, v_vals_404_, v_i_405_, v_k_406_);
lean_dec_ref(v_k_406_);
lean_dec_ref(v_vals_404_);
lean_dec_ref(v_keys_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_408_, size_t v_x_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v_es_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_432_; 
v_es_411_ = lean_ctor_get(v_x_408_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_408_);
if (v_isSharedCheck_432_ == 0)
{
v___x_413_ = v_x_408_;
v_isShared_414_ = v_isSharedCheck_432_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_es_411_);
lean_dec(v_x_408_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_432_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v_j_419_; lean_object* v___x_420_; 
v___x_415_ = lean_box(2);
v___x_416_ = ((size_t)5ULL);
v___x_417_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_418_ = lean_usize_land(v_x_409_, v___x_417_);
v_j_419_ = lean_usize_to_nat(v___x_418_);
v___x_420_ = lean_array_get(v___x_415_, v_es_411_, v_j_419_);
lean_dec(v_j_419_);
lean_dec_ref(v_es_411_);
switch(lean_obj_tag(v___x_420_))
{
case 0:
{
lean_object* v_key_421_; lean_object* v_val_422_; uint8_t v___x_423_; 
v_key_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_key_421_);
v_val_422_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_val_422_);
lean_dec_ref(v___x_420_);
v___x_423_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_410_, v_key_421_);
lean_dec(v_key_421_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
lean_dec(v_val_422_);
lean_del_object(v___x_413_);
v___x_424_ = lean_box(0);
return v___x_424_;
}
else
{
lean_object* v___x_426_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 1);
lean_ctor_set(v___x_413_, 0, v_val_422_);
v___x_426_ = v___x_413_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_val_422_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
case 1:
{
lean_object* v_node_428_; size_t v___x_429_; 
lean_del_object(v___x_413_);
v_node_428_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_node_428_);
lean_dec_ref(v___x_420_);
v___x_429_ = lean_usize_shift_right(v_x_409_, v___x_416_);
v_x_408_ = v_node_428_;
v_x_409_ = v___x_429_;
goto _start;
}
default: 
{
lean_object* v___x_431_; 
lean_del_object(v___x_413_);
v___x_431_ = lean_box(0);
return v___x_431_;
}
}
}
}
else
{
lean_object* v_ks_433_; lean_object* v_vs_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_ks_433_ = lean_ctor_get(v_x_408_, 0);
lean_inc_ref(v_ks_433_);
v_vs_434_ = lean_ctor_get(v_x_408_, 1);
lean_inc_ref(v_vs_434_);
lean_dec_ref(v_x_408_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_433_, v_vs_434_, v___x_435_, v_x_410_);
lean_dec_ref(v_vs_434_);
lean_dec_ref(v_ks_433_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
size_t v_x_5554__boxed_440_; lean_object* v_res_441_; 
v_x_5554__boxed_440_ = lean_unbox_usize(v_x_438_);
lean_dec(v_x_438_);
v_res_441_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_437_, v_x_5554__boxed_440_, v_x_439_);
lean_dec_ref(v_x_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint64_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_443_);
v___x_445_ = lean_uint64_to_usize(v___x_444_);
v___x_446_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_442_, v___x_445_, v_x_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_447_, v_x_448_);
lean_dec_ref(v_x_448_);
return v_res_449_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_453_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_454_ = lean_unsigned_to_nat(37u);
v___x_455_ = lean_unsigned_to_nat(52u);
v___x_456_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_457_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_458_ = l_mkPanicMessageWithDecl(v___x_457_, v___x_456_, v___x_455_, v___x_454_, v___x_453_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___y_468_; lean_object* v_a_496_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; uint8_t v___y_554_; lean_object* v_d_574_; lean_object* v_b_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_585_; 
switch(lean_obj_tag(v_e_459_))
{
case 1:
{
lean_object* v_fvarId_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_fvarId_612_ = lean_ctor_get(v_e_459_, 0);
lean_inc(v_fvarId_612_);
lean_dec_ref(v_e_459_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_fvarId_612_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
case 2:
{
lean_object* v_mvarId_615_; uint8_t v___y_617_; uint8_t v___x_658_; 
v_mvarId_615_ = lean_ctor_get(v_e_459_, 0);
v___x_658_ = l_Lean_Expr_hasFVar(v_e_459_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = l_Lean_Expr_hasMVar(v_e_459_);
v___y_617_ = v___x_659_;
goto v___jp_616_;
}
else
{
v___y_617_ = v___x_658_;
goto v___jp_616_;
}
v___jp_616_:
{
if (v___y_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec_ref(v_e_459_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v_maxFVar_621_; lean_object* v___x_622_; 
v___x_620_ = lean_st_ref_get(v_a_461_);
v_maxFVar_621_ = lean_ctor_get(v___x_620_, 1);
lean_inc_ref(v_maxFVar_621_);
lean_dec(v___x_620_);
v___x_622_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_621_, v_e_459_);
if (lean_obj_tag(v___x_622_) == 1)
{
lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_e_459_);
v_val_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 0);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_val_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v___x_622_);
lean_inc(v_mvarId_615_);
v___x_631_ = l_Lean_MVarId_getDecl(v_mvarId_615_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v_lctx_633_; lean_object* v_decls_634_; uint8_t v___x_635_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
v_lctx_633_ = lean_ctor_get(v_a_632_, 1);
lean_inc_ref(v_lctx_633_);
lean_dec(v_a_632_);
v_decls_634_ = lean_ctor_get(v_lctx_633_, 1);
v___x_635_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_LocalContext_lastDecl(v_lctx_633_);
if (lean_obj_tag(v___x_636_) == 1)
{
lean_object* v_val_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_val_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_val_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = l_Lean_LocalDecl_fvarId(v_val_637_);
lean_dec(v_val_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v_a_496_ = v___x_643_;
goto v___jp_495_;
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v___x_636_);
v___x_646_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_647_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_646_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
v_a_496_ = v_a_648_;
goto v___jp_495_;
}
else
{
lean_dec_ref(v_e_459_);
return v___x_647_;
}
}
}
else
{
lean_object* v___x_649_; 
lean_dec_ref(v_lctx_633_);
v___x_649_ = lean_box(0);
v_a_496_ = v___x_649_;
goto v___jp_495_;
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_e_459_);
v_a_650_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_631_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_631_);
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
}
}
case 5:
{
lean_object* v_fn_660_; lean_object* v_arg_661_; uint8_t v___y_663_; uint8_t v___x_682_; 
v_fn_660_ = lean_ctor_get(v_e_459_, 0);
v_arg_661_ = lean_ctor_get(v_e_459_, 1);
v___x_682_ = l_Lean_Expr_hasFVar(v_e_459_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_Expr_hasMVar(v_e_459_);
v___y_663_ = v___x_683_;
goto v___jp_662_;
}
else
{
v___y_663_ = v___x_682_;
goto v___jp_662_;
}
v___jp_662_:
{
if (v___y_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v_e_459_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v_maxFVar_667_; lean_object* v___x_668_; 
v___x_666_ = lean_st_ref_get(v_a_461_);
v_maxFVar_667_ = lean_ctor_get(v___x_666_, 1);
lean_inc_ref(v_maxFVar_667_);
lean_dec(v___x_666_);
v___x_668_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_667_, v_e_459_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v_val_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v_e_459_);
v_val_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_val_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 0);
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_val_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v___x_677_; 
lean_dec(v___x_668_);
lean_inc_ref(v_fn_660_);
v___x_677_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_660_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref(v___x_677_);
lean_inc_ref(v_arg_661_);
v___x_679_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_661_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref(v___x_679_);
v___x_681_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_678_, v_a_680_, v_a_462_, v_a_464_, v_a_465_);
v___y_585_ = v___x_681_;
goto v___jp_584_;
}
else
{
lean_dec(v_a_678_);
v___y_585_ = v___x_679_;
goto v___jp_584_;
}
}
else
{
v___y_585_ = v___x_677_;
goto v___jp_584_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_684_; lean_object* v_body_685_; 
v_binderType_684_ = lean_ctor_get(v_e_459_, 1);
v_body_685_ = lean_ctor_get(v_e_459_, 2);
lean_inc_ref(v_body_685_);
lean_inc_ref(v_binderType_684_);
v_d_574_ = v_binderType_684_;
v_b_575_ = v_body_685_;
v___y_576_ = v_a_460_;
v___y_577_ = v_a_461_;
v___y_578_ = v_a_462_;
v___y_579_ = v_a_463_;
v___y_580_ = v_a_464_;
v___y_581_ = v_a_465_;
goto v___jp_573_;
}
case 7:
{
lean_object* v_binderType_686_; lean_object* v_body_687_; 
v_binderType_686_ = lean_ctor_get(v_e_459_, 1);
v_body_687_ = lean_ctor_get(v_e_459_, 2);
lean_inc_ref(v_body_687_);
lean_inc_ref(v_binderType_686_);
v_d_574_ = v_binderType_686_;
v_b_575_ = v_body_687_;
v___y_576_ = v_a_460_;
v___y_577_ = v_a_461_;
v___y_578_ = v_a_462_;
v___y_579_ = v_a_463_;
v___y_580_ = v_a_464_;
v___y_581_ = v_a_465_;
goto v___jp_573_;
}
case 8:
{
lean_object* v_type_688_; lean_object* v_value_689_; lean_object* v_body_690_; uint8_t v___y_692_; uint8_t v___x_715_; 
v_type_688_ = lean_ctor_get(v_e_459_, 1);
v_value_689_ = lean_ctor_get(v_e_459_, 2);
v_body_690_ = lean_ctor_get(v_e_459_, 3);
v___x_715_ = l_Lean_Expr_hasFVar(v_e_459_);
if (v___x_715_ == 0)
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_Expr_hasMVar(v_e_459_);
v___y_692_ = v___x_716_;
goto v___jp_691_;
}
else
{
v___y_692_ = v___x_715_;
goto v___jp_691_;
}
v___jp_691_:
{
if (v___y_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref(v_e_459_);
v___x_693_ = lean_box(0);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v_maxFVar_696_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_get(v_a_461_);
v_maxFVar_696_ = lean_ctor_get(v___x_695_, 1);
lean_inc_ref(v_maxFVar_696_);
lean_dec(v___x_695_);
v___x_697_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_696_, v_e_459_);
if (lean_obj_tag(v___x_697_) == 1)
{
lean_object* v_val_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v_e_459_);
v_val_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_val_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_val_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v___x_697_);
lean_inc_ref(v_type_688_);
v___x_706_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_688_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
lean_inc_ref(v_value_689_);
v___x_708_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_689_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref(v___x_708_);
v___x_710_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_707_, v_a_709_, v_a_462_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref(v___x_710_);
lean_inc_ref(v_body_690_);
v___x_712_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_690_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
v___x_714_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_711_, v_a_713_, v_a_462_, v_a_464_, v_a_465_);
v___y_468_ = v___x_714_;
goto v___jp_467_;
}
else
{
lean_dec(v_a_711_);
v___y_468_ = v___x_712_;
goto v___jp_467_;
}
}
else
{
v___y_468_ = v___x_710_;
goto v___jp_467_;
}
}
else
{
lean_dec(v_a_707_);
v___y_468_ = v___x_708_;
goto v___jp_467_;
}
}
else
{
v___y_468_ = v___x_706_;
goto v___jp_467_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_717_; uint8_t v___y_719_; uint8_t v___x_760_; 
v_expr_717_ = lean_ctor_get(v_e_459_, 1);
lean_inc_ref(v_expr_717_);
lean_dec_ref(v_e_459_);
v___x_760_ = l_Lean_Expr_hasFVar(v_expr_717_);
if (v___x_760_ == 0)
{
uint8_t v___x_761_; 
v___x_761_ = l_Lean_Expr_hasMVar(v_expr_717_);
v___y_719_ = v___x_761_;
goto v___jp_718_;
}
else
{
v___y_719_ = v___x_760_;
goto v___jp_718_;
}
v___jp_718_:
{
if (v___y_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec_ref(v_expr_717_);
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v_maxFVar_723_; lean_object* v___x_724_; 
v___x_722_ = lean_st_ref_get(v_a_461_);
v_maxFVar_723_ = lean_ctor_get(v___x_722_, 1);
lean_inc_ref(v_maxFVar_723_);
lean_dec(v___x_722_);
v___x_724_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_723_, v_expr_717_);
if (lean_obj_tag(v___x_724_) == 1)
{
lean_object* v_val_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_expr_717_);
v_val_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_val_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 0);
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_val_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v___x_733_; 
lean_dec(v___x_724_);
lean_inc_ref(v_expr_717_);
v___x_733_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_717_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_759_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_759_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_759_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_759_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v_share_739_; lean_object* v_maxFVar_740_; lean_object* v_proofInstInfo_741_; lean_object* v_inferType_742_; lean_object* v_getLevel_743_; lean_object* v_congrInfo_744_; lean_object* v_defEqI_745_; uint8_t v_debug_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_758_; 
v___x_738_ = lean_st_ref_take(v_a_461_);
v_share_739_ = lean_ctor_get(v___x_738_, 0);
v_maxFVar_740_ = lean_ctor_get(v___x_738_, 1);
v_proofInstInfo_741_ = lean_ctor_get(v___x_738_, 2);
v_inferType_742_ = lean_ctor_get(v___x_738_, 3);
v_getLevel_743_ = lean_ctor_get(v___x_738_, 4);
v_congrInfo_744_ = lean_ctor_get(v___x_738_, 5);
v_defEqI_745_ = lean_ctor_get(v___x_738_, 6);
v_debug_746_ = lean_ctor_get_uint8(v___x_738_, sizeof(void*)*7);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_758_ == 0)
{
v___x_748_ = v___x_738_;
v_isShared_749_ = v_isSharedCheck_758_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_defEqI_745_);
lean_inc(v_congrInfo_744_);
lean_inc(v_getLevel_743_);
lean_inc(v_inferType_742_);
lean_inc(v_proofInstInfo_741_);
lean_inc(v_maxFVar_740_);
lean_inc(v_share_739_);
lean_dec(v___x_738_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_758_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
lean_inc(v_a_734_);
v___x_750_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_740_, v_expr_717_, v_a_734_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_share_739_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_proofInstInfo_741_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_inferType_742_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v_getLevel_743_);
lean_ctor_set(v_reuseFailAlloc_757_, 5, v_congrInfo_744_);
lean_ctor_set(v_reuseFailAlloc_757_, 6, v_defEqI_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_757_, sizeof(void*)*7, v_debug_746_);
v___x_752_ = v_reuseFailAlloc_757_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_st_ref_set(v_a_461_, v___x_752_);
if (v_isShared_737_ == 0)
{
v___x_755_ = v___x_736_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_734_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_717_);
return v___x_733_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_762_; uint8_t v___y_764_; uint8_t v___x_805_; 
v_struct_762_ = lean_ctor_get(v_e_459_, 2);
v___x_805_ = l_Lean_Expr_hasFVar(v_e_459_);
if (v___x_805_ == 0)
{
uint8_t v___x_806_; 
v___x_806_ = l_Lean_Expr_hasMVar(v_e_459_);
v___y_764_ = v___x_806_;
goto v___jp_763_;
}
else
{
v___y_764_ = v___x_805_;
goto v___jp_763_;
}
v___jp_763_:
{
if (v___y_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec_ref(v_e_459_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
else
{
lean_object* v___x_767_; lean_object* v_maxFVar_768_; lean_object* v___x_769_; 
v___x_767_ = lean_st_ref_get(v_a_461_);
v_maxFVar_768_ = lean_ctor_get(v___x_767_, 1);
lean_inc_ref(v_maxFVar_768_);
lean_dec(v___x_767_);
v___x_769_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_768_, v_e_459_);
if (lean_obj_tag(v___x_769_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_e_459_);
v_val_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_val_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 0);
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_val_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v___x_769_);
lean_inc_ref(v_struct_762_);
v___x_778_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_762_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_804_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_804_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_804_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_804_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v_share_784_; lean_object* v_maxFVar_785_; lean_object* v_proofInstInfo_786_; lean_object* v_inferType_787_; lean_object* v_getLevel_788_; lean_object* v_congrInfo_789_; lean_object* v_defEqI_790_; uint8_t v_debug_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_803_; 
v___x_783_ = lean_st_ref_take(v_a_461_);
v_share_784_ = lean_ctor_get(v___x_783_, 0);
v_maxFVar_785_ = lean_ctor_get(v___x_783_, 1);
v_proofInstInfo_786_ = lean_ctor_get(v___x_783_, 2);
v_inferType_787_ = lean_ctor_get(v___x_783_, 3);
v_getLevel_788_ = lean_ctor_get(v___x_783_, 4);
v_congrInfo_789_ = lean_ctor_get(v___x_783_, 5);
v_defEqI_790_ = lean_ctor_get(v___x_783_, 6);
v_debug_791_ = lean_ctor_get_uint8(v___x_783_, sizeof(void*)*7);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_803_ == 0)
{
v___x_793_ = v___x_783_;
v_isShared_794_ = v_isSharedCheck_803_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_defEqI_790_);
lean_inc(v_congrInfo_789_);
lean_inc(v_getLevel_788_);
lean_inc(v_inferType_787_);
lean_inc(v_proofInstInfo_786_);
lean_inc(v_maxFVar_785_);
lean_inc(v_share_784_);
lean_dec(v___x_783_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_803_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
lean_inc(v_a_779_);
v___x_795_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_785_, v_e_459_, v_a_779_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_share_784_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_proofInstInfo_786_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_inferType_787_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_getLevel_788_);
lean_ctor_set(v_reuseFailAlloc_802_, 5, v_congrInfo_789_);
lean_ctor_set(v_reuseFailAlloc_802_, 6, v_defEqI_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_802_, sizeof(void*)*7, v_debug_791_);
v___x_797_ = v_reuseFailAlloc_802_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_st_ref_set(v_a_461_, v___x_797_);
if (v_isShared_782_ == 0)
{
v___x_800_ = v___x_781_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_779_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_459_);
return v___x_778_;
}
}
}
}
}
default: 
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_e_459_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
v___jp_467_:
{
if (lean_obj_tag(v___y_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_494_; 
v_a_469_ = lean_ctor_get(v___y_468_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___y_468_);
if (v_isSharedCheck_494_ == 0)
{
v___x_471_ = v___y_468_;
v_isShared_472_ = v_isSharedCheck_494_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___y_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_494_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v_share_474_; lean_object* v_maxFVar_475_; lean_object* v_proofInstInfo_476_; lean_object* v_inferType_477_; lean_object* v_getLevel_478_; lean_object* v_congrInfo_479_; lean_object* v_defEqI_480_; uint8_t v_debug_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_493_; 
v___x_473_ = lean_st_ref_take(v_a_461_);
v_share_474_ = lean_ctor_get(v___x_473_, 0);
v_maxFVar_475_ = lean_ctor_get(v___x_473_, 1);
v_proofInstInfo_476_ = lean_ctor_get(v___x_473_, 2);
v_inferType_477_ = lean_ctor_get(v___x_473_, 3);
v_getLevel_478_ = lean_ctor_get(v___x_473_, 4);
v_congrInfo_479_ = lean_ctor_get(v___x_473_, 5);
v_defEqI_480_ = lean_ctor_get(v___x_473_, 6);
v_debug_481_ = lean_ctor_get_uint8(v___x_473_, sizeof(void*)*7);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_493_ == 0)
{
v___x_483_ = v___x_473_;
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_defEqI_480_);
lean_inc(v_congrInfo_479_);
lean_inc(v_getLevel_478_);
lean_inc(v_inferType_477_);
lean_inc(v_proofInstInfo_476_);
lean_inc(v_maxFVar_475_);
lean_inc(v_share_474_);
lean_dec(v___x_473_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
lean_inc(v_a_469_);
v___x_485_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_475_, v_e_459_, v_a_469_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_share_474_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_proofInstInfo_476_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_inferType_477_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_getLevel_478_);
lean_ctor_set(v_reuseFailAlloc_492_, 5, v_congrInfo_479_);
lean_ctor_set(v_reuseFailAlloc_492_, 6, v_defEqI_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*7, v_debug_481_);
v___x_487_ = v_reuseFailAlloc_492_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = lean_st_ref_set(v_a_461_, v___x_487_);
if (v_isShared_472_ == 0)
{
v___x_490_ = v___x_471_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_469_);
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
else
{
lean_dec_ref(v_e_459_);
return v___y_468_;
}
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v_share_498_; lean_object* v_maxFVar_499_; lean_object* v_proofInstInfo_500_; lean_object* v_inferType_501_; lean_object* v_getLevel_502_; lean_object* v_congrInfo_503_; lean_object* v_defEqI_504_; uint8_t v_debug_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v___x_497_ = lean_st_ref_take(v_a_461_);
v_share_498_ = lean_ctor_get(v___x_497_, 0);
v_maxFVar_499_ = lean_ctor_get(v___x_497_, 1);
v_proofInstInfo_500_ = lean_ctor_get(v___x_497_, 2);
v_inferType_501_ = lean_ctor_get(v___x_497_, 3);
v_getLevel_502_ = lean_ctor_get(v___x_497_, 4);
v_congrInfo_503_ = lean_ctor_get(v___x_497_, 5);
v_defEqI_504_ = lean_ctor_get(v___x_497_, 6);
v_debug_505_ = lean_ctor_get_uint8(v___x_497_, sizeof(void*)*7);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_515_ == 0)
{
v___x_507_ = v___x_497_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_defEqI_504_);
lean_inc(v_congrInfo_503_);
lean_inc(v_getLevel_502_);
lean_inc(v_inferType_501_);
lean_inc(v_proofInstInfo_500_);
lean_inc(v_maxFVar_499_);
lean_inc(v_share_498_);
lean_dec(v___x_497_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_inc(v_a_496_);
v___x_509_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_499_, v_e_459_, v_a_496_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_share_498_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_proofInstInfo_500_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_inferType_501_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_getLevel_502_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v_congrInfo_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v_defEqI_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_514_, sizeof(void*)*7, v_debug_505_);
v___x_511_ = v_reuseFailAlloc_514_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_st_ref_set(v_a_461_, v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_a_496_);
return v___x_513_;
}
}
}
v___jp_516_:
{
if (lean_obj_tag(v___y_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_544_; 
v_a_519_ = lean_ctor_get(v___y_518_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___y_518_);
if (v_isSharedCheck_544_ == 0)
{
v___x_521_ = v___y_518_;
v_isShared_522_ = v_isSharedCheck_544_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___y_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_544_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v_share_524_; lean_object* v_maxFVar_525_; lean_object* v_proofInstInfo_526_; lean_object* v_inferType_527_; lean_object* v_getLevel_528_; lean_object* v_congrInfo_529_; lean_object* v_defEqI_530_; uint8_t v_debug_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_543_; 
v___x_523_ = lean_st_ref_take(v___y_517_);
v_share_524_ = lean_ctor_get(v___x_523_, 0);
v_maxFVar_525_ = lean_ctor_get(v___x_523_, 1);
v_proofInstInfo_526_ = lean_ctor_get(v___x_523_, 2);
v_inferType_527_ = lean_ctor_get(v___x_523_, 3);
v_getLevel_528_ = lean_ctor_get(v___x_523_, 4);
v_congrInfo_529_ = lean_ctor_get(v___x_523_, 5);
v_defEqI_530_ = lean_ctor_get(v___x_523_, 6);
v_debug_531_ = lean_ctor_get_uint8(v___x_523_, sizeof(void*)*7);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_543_ == 0)
{
v___x_533_ = v___x_523_;
v_isShared_534_ = v_isSharedCheck_543_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_defEqI_530_);
lean_inc(v_congrInfo_529_);
lean_inc(v_getLevel_528_);
lean_inc(v_inferType_527_);
lean_inc(v_proofInstInfo_526_);
lean_inc(v_maxFVar_525_);
lean_inc(v_share_524_);
lean_dec(v___x_523_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_543_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
lean_inc(v_a_519_);
v___x_535_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_525_, v_e_459_, v_a_519_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_share_524_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_proofInstInfo_526_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_inferType_527_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_getLevel_528_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v_congrInfo_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 6, v_defEqI_530_);
lean_ctor_set_uint8(v_reuseFailAlloc_542_, sizeof(void*)*7, v_debug_531_);
v___x_537_ = v_reuseFailAlloc_542_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_st_ref_set(v___y_517_, v___x_537_);
if (v_isShared_522_ == 0)
{
v___x_540_ = v___x_521_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_519_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_459_);
return v___y_518_;
}
}
v___jp_545_:
{
if (v___y_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___y_550_);
lean_dec_ref(v___y_546_);
lean_dec_ref(v_e_459_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v_maxFVar_558_; lean_object* v___x_559_; 
v___x_557_ = lean_st_ref_get(v___y_547_);
v_maxFVar_558_ = lean_ctor_get(v___x_557_, 1);
lean_inc_ref(v_maxFVar_558_);
lean_dec(v___x_557_);
v___x_559_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_558_, v_e_459_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec_ref(v___y_550_);
lean_dec_ref(v___y_546_);
lean_dec_ref(v_e_459_);
v_val_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_val_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v___x_559_);
v___x_568_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_550_, v___y_548_, v___y_547_, v___y_553_, v___y_552_, v___y_551_, v___y_549_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_568_);
v___x_570_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_546_, v___y_548_, v___y_547_, v___y_553_, v___y_552_, v___y_551_, v___y_549_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_570_);
v___x_572_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_569_, v_a_571_, v___y_553_, v___y_551_, v___y_549_);
v___y_517_ = v___y_547_;
v___y_518_ = v___x_572_;
goto v___jp_516_;
}
else
{
lean_dec(v_a_569_);
v___y_517_ = v___y_547_;
v___y_518_ = v___x_570_;
goto v___jp_516_;
}
}
else
{
lean_dec_ref(v___y_546_);
v___y_517_ = v___y_547_;
v___y_518_ = v___x_568_;
goto v___jp_516_;
}
}
}
}
v___jp_573_:
{
uint8_t v___x_582_; 
v___x_582_ = l_Lean_Expr_hasFVar(v_e_459_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; 
v___x_583_ = l_Lean_Expr_hasMVar(v_e_459_);
v___y_546_ = v_b_575_;
v___y_547_ = v___y_577_;
v___y_548_ = v___y_576_;
v___y_549_ = v___y_581_;
v___y_550_ = v_d_574_;
v___y_551_ = v___y_580_;
v___y_552_ = v___y_579_;
v___y_553_ = v___y_578_;
v___y_554_ = v___x_583_;
goto v___jp_545_;
}
else
{
v___y_546_ = v_b_575_;
v___y_547_ = v___y_577_;
v___y_548_ = v___y_576_;
v___y_549_ = v___y_581_;
v___y_550_ = v_d_574_;
v___y_551_ = v___y_580_;
v___y_552_ = v___y_579_;
v___y_553_ = v___y_578_;
v___y_554_ = v___x_582_;
goto v___jp_545_;
}
}
v___jp_584_:
{
if (lean_obj_tag(v___y_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_611_; 
v_a_586_ = lean_ctor_get(v___y_585_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___y_585_);
if (v_isSharedCheck_611_ == 0)
{
v___x_588_ = v___y_585_;
v_isShared_589_ = v_isSharedCheck_611_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___y_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_611_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v_share_591_; lean_object* v_maxFVar_592_; lean_object* v_proofInstInfo_593_; lean_object* v_inferType_594_; lean_object* v_getLevel_595_; lean_object* v_congrInfo_596_; lean_object* v_defEqI_597_; uint8_t v_debug_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_610_; 
v___x_590_ = lean_st_ref_take(v_a_461_);
v_share_591_ = lean_ctor_get(v___x_590_, 0);
v_maxFVar_592_ = lean_ctor_get(v___x_590_, 1);
v_proofInstInfo_593_ = lean_ctor_get(v___x_590_, 2);
v_inferType_594_ = lean_ctor_get(v___x_590_, 3);
v_getLevel_595_ = lean_ctor_get(v___x_590_, 4);
v_congrInfo_596_ = lean_ctor_get(v___x_590_, 5);
v_defEqI_597_ = lean_ctor_get(v___x_590_, 6);
v_debug_598_ = lean_ctor_get_uint8(v___x_590_, sizeof(void*)*7);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_610_ == 0)
{
v___x_600_ = v___x_590_;
v_isShared_601_ = v_isSharedCheck_610_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_defEqI_597_);
lean_inc(v_congrInfo_596_);
lean_inc(v_getLevel_595_);
lean_inc(v_inferType_594_);
lean_inc(v_proofInstInfo_593_);
lean_inc(v_maxFVar_592_);
lean_inc(v_share_591_);
lean_dec(v___x_590_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_610_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_inc(v_a_586_);
v___x_602_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_592_, v_e_459_, v_a_586_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_share_591_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_proofInstInfo_593_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_inferType_594_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_getLevel_595_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v_congrInfo_596_);
lean_ctor_set(v_reuseFailAlloc_609_, 6, v_defEqI_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_609_, sizeof(void*)*7, v_debug_598_);
v___x_604_ = v_reuseFailAlloc_609_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_st_ref_set(v_a_461_, v___x_604_);
if (v_isShared_589_ == 0)
{
v___x_607_ = v___x_588_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_586_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_459_);
return v___y_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_819_, v_x_820_, v_x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_823_, lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_824_, v_x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_827_, v_x_828_, v_x_829_);
lean_dec_ref(v_x_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_831_, lean_object* v_x_832_, size_t v_x_833_, size_t v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_832_, v_x_833_, v_x_834_, v_x_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
size_t v_x_6264__boxed_844_; size_t v_x_6265__boxed_845_; lean_object* v_res_846_; 
v_x_6264__boxed_844_ = lean_unbox_usize(v_x_840_);
lean_dec(v_x_840_);
v_x_6265__boxed_845_ = lean_unbox_usize(v_x_841_);
lean_dec(v_x_841_);
v_res_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_838_, v_x_839_, v_x_6264__boxed_844_, v_x_6265__boxed_845_, v_x_842_, v_x_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, size_t v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_848_, v_x_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_852_, lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
size_t v_x_6281__boxed_856_; lean_object* v_res_857_; 
v_x_6281__boxed_856_ = lean_unbox_usize(v_x_854_);
lean_dec(v_x_854_);
v_res_857_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_852_, v_x_853_, v_x_6281__boxed_856_, v_x_855_);
lean_dec_ref(v_x_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_858_, lean_object* v_n_859_, lean_object* v_k_860_, lean_object* v_v_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_859_, v_k_860_, v_v_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_863_, size_t v_depth_864_, lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_heq_867_, lean_object* v_i_868_, lean_object* v_entries_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_864_, v_keys_865_, v_vals_866_, v_i_868_, v_entries_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_871_, lean_object* v_depth_872_, lean_object* v_keys_873_, lean_object* v_vals_874_, lean_object* v_heq_875_, lean_object* v_i_876_, lean_object* v_entries_877_){
_start:
{
size_t v_depth_boxed_878_; lean_object* v_res_879_; 
v_depth_boxed_878_ = lean_unbox_usize(v_depth_872_);
lean_dec(v_depth_872_);
v_res_879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_871_, v_depth_boxed_878_, v_keys_873_, v_vals_874_, v_heq_875_, v_i_876_, v_entries_877_);
lean_dec_ref(v_vals_874_);
lean_dec_ref(v_keys_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_880_, lean_object* v_keys_881_, lean_object* v_vals_882_, lean_object* v_heq_883_, lean_object* v_i_884_, lean_object* v_k_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_881_, v_vals_882_, v_i_884_, v_k_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_887_, lean_object* v_keys_888_, lean_object* v_vals_889_, lean_object* v_heq_890_, lean_object* v_i_891_, lean_object* v_k_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_887_, v_keys_888_, v_vals_889_, v_heq_890_, v_i_891_, v_k_892_);
lean_dec_ref(v_k_892_);
lean_dec_ref(v_vals_889_);
lean_dec_ref(v_keys_888_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_895_, v_x_896_, v_x_897_, v_x_898_);
return v___x_899_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_MaxFVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_MaxFVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_MaxFVar(builtin);
}
#ifdef __cplusplus
}
#endif
