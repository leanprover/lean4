// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: Init Lean.Compiler.LCNF.CompilerM
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2;
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
static lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1;
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs(lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instFVarIdHashSetInhabited;
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_Code_elimDead___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__7(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_Code_elimDead___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_4);
x_8 = lean_hashset_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 1, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_array_get_size(x_1);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_12);
x_16 = lean_hashset_mk_idx(x_14, x_15);
x_17 = lean_array_uget(x_1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_uset(x_1, x_16, x_18);
x_1 = x_19;
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_List_foldl___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashSetImp_moveEntries___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_name_eq(x_6, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_name_eq(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6(x_11, x_2, x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_6);
x_8 = lean_hashset_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_5, x_8);
x_10 = l_List_elem___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_array_uset(x_5, x_8, x_13);
x_15 = lean_nat_dec_le(x_12, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_1);
x_16 = l_Lean_HashSetImp_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__3(x_12, x_14);
return x_16;
}
else
{
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_inc(x_2);
x_17 = l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6(x_9, x_2, x_2);
lean_dec(x_2);
x_18 = lean_array_uset(x_5, x_8, x_17);
lean_ctor_set(x_1, 1, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
x_22 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_21);
x_23 = lean_hashset_mk_idx(x_21, x_22);
x_24 = lean_array_uget(x_20, x_23);
x_25 = l_List_elem___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_19, x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_array_uset(x_20, x_23, x_28);
x_30 = lean_nat_dec_le(x_27, x_21);
lean_dec(x_21);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_HashSetImp_expand___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__3(x_27, x_29);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
lean_inc(x_2);
x_33 = l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6(x_24, x_2, x_2);
lean_dec(x_2);
x_34 = lean_array_uset(x_20, x_23, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instFVarIdHashSetInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.ElimDead", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.collectLocalDeclsType.go", 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1;
x_2 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2;
x_3 = lean_unsigned_to_nat(25u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_1, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
case 6:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
case 8:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4;
x_12 = l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__7(x_11);
return x_12;
}
case 10:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4;
x_14 = l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__7(x_13);
return x_14;
}
case 11:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4;
x_16 = l_panic___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__7(x_15);
return x_16;
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_1, x_3);
return x_4;
}
default: 
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_collectLocalDeclsArgs___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_1, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_5);
return x_6;
}
case 4:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_1, x_7);
x_10 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_9, x_8);
return x_10;
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_9, x_1);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_9, x_1);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_9, x_1);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_12, x_13, x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashset_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_List_elem___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_st_ref_take(x_5, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_14, x_12);
x_17 = lean_st_ref_set(x_5, x_16, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_box(0);
x_2 = x_20;
x_4 = x_21;
x_10 = x_18;
goto _start;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__4(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_9 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ElimDead_elimDead___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Compiler_LCNF_eraseLetDecl(x_8, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_ctor_get(x_8, 3);
lean_inc(x_23);
x_24 = lean_st_ref_take(x_2, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_25, x_23);
x_28 = lean_st_ref_set(x_2, x_27, x_26);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; size_t x_31; size_t x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_32 = lean_ptr_addr(x_11);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_1, 0);
lean_dec(x_36);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
else
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_11);
lean_ctor_set(x_28, 0, x_37);
return x_28;
}
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
}
else
{
lean_object* x_38; size_t x_39; size_t x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_40 = lean_ptr_addr(x_11);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_42 = x_1;
} else {
 lean_dec_ref(x_1);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_11);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_11);
lean_dec(x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
return x_10;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_10, 0);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_10);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 1:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_51);
x_52 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_51, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_get(x_2, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
x_59 = l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(x_56, x_58);
lean_dec(x_58);
lean_dec(x_56);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_1);
x_60 = 1;
x_61 = l_Lean_Compiler_LCNF_eraseFunDecl(x_50, x_60, x_3, x_4, x_5, x_6, x_57);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_53);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_inc(x_50);
x_66 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_50, x_2, x_3, x_4, x_5, x_6, x_57);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; size_t x_69; size_t x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_70 = lean_ptr_addr(x_53);
x_71 = lean_usize_dec_eq(x_69, x_70);
if (x_71 == 0)
{
uint8_t x_72; 
lean_dec(x_50);
x_72 = !lean_is_exclusive(x_1);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_1, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_1, 0);
lean_dec(x_74);
lean_ctor_set(x_1, 1, x_53);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set(x_66, 0, x_1);
return x_66;
}
else
{
lean_object* x_75; 
lean_dec(x_1);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_53);
lean_ctor_set(x_66, 0, x_75);
return x_66;
}
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_77 = lean_ptr_addr(x_68);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_1, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_1, 0);
lean_dec(x_81);
lean_ctor_set(x_1, 1, x_53);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set(x_66, 0, x_1);
return x_66;
}
else
{
lean_object* x_82; 
lean_dec(x_1);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_68);
lean_ctor_set(x_82, 1, x_53);
lean_ctor_set(x_66, 0, x_82);
return x_66;
}
}
else
{
lean_dec(x_68);
lean_dec(x_53);
lean_ctor_set(x_66, 0, x_1);
return x_66;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_66, 0);
x_84 = lean_ctor_get(x_66, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_66);
x_85 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_86 = lean_ptr_addr(x_53);
x_87 = lean_usize_dec_eq(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_50);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_88 = x_1;
} else {
 lean_dec_ref(x_1);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_53);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
else
{
size_t x_91; size_t x_92; uint8_t x_93; 
x_91 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_92 = lean_ptr_addr(x_83);
x_93 = lean_usize_dec_eq(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_94 = x_1;
} else {
 lean_dec_ref(x_1);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_83);
lean_ctor_set(x_95, 1, x_53);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_84);
return x_96;
}
else
{
lean_object* x_97; 
lean_dec(x_83);
lean_dec(x_53);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_84);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_66);
if (x_98 == 0)
{
return x_66;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_66, 0);
x_100 = lean_ctor_get(x_66, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_66);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_52);
if (x_102 == 0)
{
return x_52;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_52, 0);
x_104 = lean_ctor_get(x_52, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_52);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
case 2:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_1, 1);
lean_inc(x_107);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_107);
x_108 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_107, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_st_ref_get(x_2, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_106, 0);
lean_inc(x_114);
x_115 = l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(x_112, x_114);
lean_dec(x_114);
lean_dec(x_112);
if (x_115 == 0)
{
uint8_t x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_107);
lean_dec(x_2);
lean_dec(x_1);
x_116 = 1;
x_117 = l_Lean_Compiler_LCNF_eraseFunDecl(x_106, x_116, x_3, x_4, x_5, x_6, x_113);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
lean_ctor_set(x_117, 0, x_109);
return x_117;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_109);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
lean_object* x_122; 
lean_inc(x_106);
x_122 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_106, x_2, x_3, x_4, x_5, x_6, x_113);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; size_t x_125; size_t x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ptr_addr(x_107);
lean_dec(x_107);
x_126 = lean_ptr_addr(x_109);
x_127 = lean_usize_dec_eq(x_125, x_126);
if (x_127 == 0)
{
uint8_t x_128; 
lean_dec(x_106);
x_128 = !lean_is_exclusive(x_1);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_1, 1);
lean_dec(x_129);
x_130 = lean_ctor_get(x_1, 0);
lean_dec(x_130);
lean_ctor_set(x_1, 1, x_109);
lean_ctor_set(x_1, 0, x_124);
lean_ctor_set(x_122, 0, x_1);
return x_122;
}
else
{
lean_object* x_131; 
lean_dec(x_1);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_124);
lean_ctor_set(x_131, 1, x_109);
lean_ctor_set(x_122, 0, x_131);
return x_122;
}
}
else
{
size_t x_132; size_t x_133; uint8_t x_134; 
x_132 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_133 = lean_ptr_addr(x_124);
x_134 = lean_usize_dec_eq(x_132, x_133);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_1);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_1, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_1, 0);
lean_dec(x_137);
lean_ctor_set(x_1, 1, x_109);
lean_ctor_set(x_1, 0, x_124);
lean_ctor_set(x_122, 0, x_1);
return x_122;
}
else
{
lean_object* x_138; 
lean_dec(x_1);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_109);
lean_ctor_set(x_122, 0, x_138);
return x_122;
}
}
else
{
lean_dec(x_124);
lean_dec(x_109);
lean_ctor_set(x_122, 0, x_1);
return x_122;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; size_t x_141; size_t x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_122, 0);
x_140 = lean_ctor_get(x_122, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_122);
x_141 = lean_ptr_addr(x_107);
lean_dec(x_107);
x_142 = lean_ptr_addr(x_109);
x_143 = lean_usize_dec_eq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_106);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_144 = x_1;
} else {
 lean_dec_ref(x_1);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(2, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_139);
lean_ctor_set(x_145, 1, x_109);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_140);
return x_146;
}
else
{
size_t x_147; size_t x_148; uint8_t x_149; 
x_147 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_148 = lean_ptr_addr(x_139);
x_149 = lean_usize_dec_eq(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_150 = x_1;
} else {
 lean_dec_ref(x_1);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(2, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_139);
lean_ctor_set(x_151, 1, x_109);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_140);
return x_152;
}
else
{
lean_object* x_153; 
lean_dec(x_139);
lean_dec(x_109);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_140);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_122);
if (x_154 == 0)
{
return x_122;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_122, 0);
x_156 = lean_ctor_get(x_122, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_122);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_108);
if (x_158 == 0)
{
return x_108;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_108, 0);
x_160 = lean_ctor_get(x_108, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_108);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
case 3:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_162 = lean_ctor_get(x_1, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_1, 1);
lean_inc(x_163);
x_164 = lean_st_ref_take(x_2, x_7);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_165, x_162);
x_168 = lean_st_ref_set(x_2, x_167, x_166);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_168, 1);
x_171 = lean_ctor_get(x_168, 0);
lean_dec(x_171);
x_172 = lean_array_get_size(x_163);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_nat_dec_lt(x_173, x_172);
if (x_174 == 0)
{
lean_dec(x_172);
lean_dec(x_163);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_168, 0, x_1);
return x_168;
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_le(x_172, x_172);
if (x_175 == 0)
{
lean_dec(x_172);
lean_dec(x_163);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_168, 0, x_1);
return x_168;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_free_object(x_168);
x_176 = 0;
x_177 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_178 = lean_box(0);
x_179 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2(x_163, x_176, x_177, x_178, x_2, x_3, x_4, x_5, x_6, x_170);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_163);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_179, 0);
lean_dec(x_181);
lean_ctor_set(x_179, 0, x_1);
return x_179;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_184 = lean_ctor_get(x_168, 1);
lean_inc(x_184);
lean_dec(x_168);
x_185 = lean_array_get_size(x_163);
x_186 = lean_unsigned_to_nat(0u);
x_187 = lean_nat_dec_lt(x_186, x_185);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_185);
lean_dec(x_163);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_1);
lean_ctor_set(x_188, 1, x_184);
return x_188;
}
else
{
uint8_t x_189; 
x_189 = lean_nat_dec_le(x_185, x_185);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_185);
lean_dec(x_163);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_184);
return x_190;
}
else
{
size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_191 = 0;
x_192 = lean_usize_of_nat(x_185);
lean_dec(x_185);
x_193 = lean_box(0);
x_194 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2(x_163, x_191, x_192, x_193, x_2, x_3, x_4, x_5, x_6, x_184);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_163);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_1);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
}
case 4:
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_1, 0);
lean_inc(x_198);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_ctor_get(x_198, 1);
x_202 = lean_ctor_get(x_198, 2);
x_203 = lean_ctor_get(x_198, 3);
x_204 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
lean_inc(x_2);
lean_inc(x_203);
x_205 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__3(x_203, x_204, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_st_ref_take(x_2, x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_202);
x_211 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_209, x_202);
x_212 = lean_st_ref_set(x_2, x_211, x_210);
lean_dec(x_2);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; size_t x_215; size_t x_216; uint8_t x_217; 
x_214 = lean_ctor_get(x_212, 0);
lean_dec(x_214);
x_215 = lean_ptr_addr(x_203);
lean_dec(x_203);
x_216 = lean_ptr_addr(x_206);
x_217 = lean_usize_dec_eq(x_215, x_216);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_1);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_1, 0);
lean_dec(x_219);
lean_ctor_set(x_198, 3, x_206);
lean_ctor_set(x_212, 0, x_1);
return x_212;
}
else
{
lean_object* x_220; 
lean_dec(x_1);
lean_ctor_set(x_198, 3, x_206);
x_220 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_220, 0, x_198);
lean_ctor_set(x_212, 0, x_220);
return x_212;
}
}
else
{
lean_dec(x_206);
lean_free_object(x_198);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_ctor_set(x_212, 0, x_1);
return x_212;
}
}
else
{
lean_object* x_221; size_t x_222; size_t x_223; uint8_t x_224; 
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
lean_dec(x_212);
x_222 = lean_ptr_addr(x_203);
lean_dec(x_203);
x_223 = lean_ptr_addr(x_206);
x_224 = lean_usize_dec_eq(x_222, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_225 = x_1;
} else {
 lean_dec_ref(x_1);
 x_225 = lean_box(0);
}
lean_ctor_set(x_198, 3, x_206);
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(4, 1, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_198);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_221);
return x_227;
}
else
{
lean_object* x_228; 
lean_dec(x_206);
lean_free_object(x_198);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_1);
lean_ctor_set(x_228, 1, x_221);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_free_object(x_198);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_2);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_205);
if (x_229 == 0)
{
return x_205;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_205, 0);
x_231 = lean_ctor_get(x_205, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_205);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_198, 0);
x_234 = lean_ctor_get(x_198, 1);
x_235 = lean_ctor_get(x_198, 2);
x_236 = lean_ctor_get(x_198, 3);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_198);
x_237 = l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1;
lean_inc(x_2);
lean_inc(x_236);
x_238 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__3(x_236, x_237, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; size_t x_248; size_t x_249; uint8_t x_250; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_st_ref_take(x_2, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
lean_inc(x_235);
x_244 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_242, x_235);
x_245 = lean_st_ref_set(x_2, x_244, x_243);
lean_dec(x_2);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_247 = x_245;
} else {
 lean_dec_ref(x_245);
 x_247 = lean_box(0);
}
x_248 = lean_ptr_addr(x_236);
lean_dec(x_236);
x_249 = lean_ptr_addr(x_239);
x_250 = lean_usize_dec_eq(x_248, x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_251 = x_1;
} else {
 lean_dec_ref(x_1);
 x_251 = lean_box(0);
}
x_252 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_252, 0, x_233);
lean_ctor_set(x_252, 1, x_234);
lean_ctor_set(x_252, 2, x_235);
lean_ctor_set(x_252, 3, x_239);
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(4, 1, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_252);
if (lean_is_scalar(x_247)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_247;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_246);
return x_254;
}
else
{
lean_object* x_255; 
lean_dec(x_239);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
if (lean_is_scalar(x_247)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_247;
}
lean_ctor_set(x_255, 0, x_1);
lean_ctor_set(x_255, 1, x_246);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_2);
lean_dec(x_1);
x_256 = lean_ctor_get(x_238, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_238, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_258 = x_238;
} else {
 lean_dec_ref(x_238);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
case 5:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_260 = lean_ctor_get(x_1, 0);
lean_inc(x_260);
x_261 = lean_st_ref_take(x_2, x_7);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = l_Lean_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDeclsType_go___spec__1(x_262, x_260);
x_265 = lean_st_ref_set(x_2, x_264, x_263);
lean_dec(x_2);
x_266 = !lean_is_exclusive(x_265);
if (x_266 == 0)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_265, 0);
lean_dec(x_267);
lean_ctor_set(x_265, 0, x_1);
return x_265;
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_265, 1);
lean_inc(x_268);
lean_dec(x_265);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_1);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
default: 
{
lean_object* x_270; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_1);
lean_ctor_set(x_270, 1, x_7);
return x_270;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_Code_elimDead___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(8u);
x_8 = l_Lean_mkHashSetImp___rarg(x_7);
x_9 = lean_st_mk_ref(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_1, x_10, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_Code_elimDead___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSet___at_Lean_Compiler_LCNF_Code_elimDead___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = l_Lean_Compiler_LCNF_Code_elimDead(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 4, x_16);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_1, 4, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
x_28 = lean_ctor_get(x_1, 4);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_31 = lean_ctor_get(x_1, 5);
lean_inc(x_31);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_32 = l_Lean_Compiler_LCNF_Code_elimDead(x_28, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_27);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*6, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*6 + 1, x_30);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1 = _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__1);
l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2 = _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__2);
l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3 = _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__3);
l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4 = _init_l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_collectLocalDeclsType_go___closed__4);
l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1 = _init_l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ElimDead_elimDead___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
