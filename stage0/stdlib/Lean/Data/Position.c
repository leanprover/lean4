// Lean compiler output
// Module: Lean.Data.Position
// Imports: Lean.Data.Format Lean.Data.Json.FromToJson.Basic Lean.ToExpr
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Position_instToExpr___closed__0;
lean_object* l_Lean_mkNatLit(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_FileMap_ofString___closed__1;
static lean_object* l_Lean_Position_lt___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Position_instToExpr;
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_FileMap_ofString___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
static lean_object* l_Lean_instToJsonPosition___closed__0;
static lean_object* l_Lean_fromJsonPosition___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
LEAN_EXPORT uint8_t l_Lean_instDecidableEqPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadFileMap_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_ctorIdx(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l_Lean_Position_instToExpr___lam__0___closed__0;
static lean_object* l_Lean_instFromJsonPosition___closed__0;
static lean_object* l_Lean_fromJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
LEAN_EXPORT lean_object* l_Lean_instDecidableEqPosition___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedFileMap___closed__0;
lean_object* l_List_foldl___at___Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
LEAN_EXPORT lean_object* l_Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_(lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Position_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_instInhabitedFileMap___closed__1;
static lean_object* l_Lean_fromJsonPosition___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Position_instToString___lam__0(lean_object*);
static lean_object* l_Lean_Position_instToFormat___lam__0___closed__4;
static lean_object* l_Lean_reprPosition___redArg___closed__15____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
static lean_object* l_Lean_reprPosition___redArg___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
static lean_object* l_Lean_reprPosition___redArg___closed__16____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
LEAN_EXPORT lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
LEAN_EXPORT lean_object* l_Lean_Position_instToString;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_decEqPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_27_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Position_instToFormat;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
LEAN_EXPORT lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_instInhabitedFileMap___closed__2;
lean_object* l_Array_back_x3f___redArg(lean_object*);
static lean_object* l_Lean_Position_instToFormat___lam__0___closed__3;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFileMap;
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart(lean_object*, lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
static lean_object* l_Lean_Position_instToExpr___lam__0___closed__3;
static lean_object* l_Lean_reprPosition___redArg___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
static lean_object* l_Lean_reprPosition___redArg___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprPosition;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lean_toJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50__spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
LEAN_EXPORT lean_object* l_Lean_Position_lt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
LEAN_EXPORT lean_object* l_Lean_reprPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_(lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
static lean_object* l_Lean_fromJsonPosition___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reprPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Position_instToExpr___lam__0(lean_object*);
uint8_t l_Prod_lexLtDec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_reprPosition___redArg____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonPosition;
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine___boxed(lean_object*);
static lean_object* l_Lean_toJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_;
static lean_object* l_Lean_fromJsonPosition___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
lean_object* l_String_Iterator_nextn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonPosition;
static lean_object* l_Lean_instInhabitedPosition___closed__0;
LEAN_EXPORT lean_object* l_String_toFileMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Position_instToFormat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
LEAN_EXPORT lean_object* l_Lean_FileMap_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPosition;
LEAN_EXPORT lean_object* l_Lean_decEqPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_27____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Position_instToExpr___lam__0___closed__2;
static lean_object* l_Lean_Position_instToFormat___lam__0___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
static lean_object* l_Lean_Position_instToExpr___lam__0___closed__1;
LEAN_EXPORT uint8_t l_Lean_Position_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_reprPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
LEAN_EXPORT lean_object* l_Lean_Position_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadFileMap_ctorIdx___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_reprPosition___redArg___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
LEAN_EXPORT lean_object* l_Lean_toJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Position_instToFormat___lam__0___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_fromJsonPosition___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
static lean_object* l_Lean_reprPosition___redArg___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Position_instToFormat___lam__0___closed__2;
static lean_object* l_Lean_fromJsonPosition___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60__spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Position_instToFormat___lam__0___closed__0;
static lean_object* l_Lean_instReprPosition___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Position_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Position_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Position_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedPosition___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedPosition() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPosition___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_decEqPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_27_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_decEqPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_27____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_decEqPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_27_(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqPosition(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_decEqPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_27_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqPosition___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instDecidableEqPosition(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_reprPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42__spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("line", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprPosition___redArg___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprPosition___redArg___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprPosition___redArg___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = l_Lean_reprPosition___redArg___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprPosition___redArg___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("column", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__15____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprPosition___redArg___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprPosition___redArg___closed__16____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprPosition___redArg___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_reprPosition___redArg____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_reprPosition___redArg___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_6 = l_Lean_reprPosition___redArg___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_7 = l_Lean_reprPosition___redArg___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_8 = l_Nat_reprFast(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_7);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_reprPosition___redArg___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_reprPosition___redArg___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = l_Lean_reprPosition___redArg___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_21 = l_Nat_reprFast(x_4);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_10);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_reprPosition___redArg___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_27 = l_Lean_reprPosition___redArg___closed__15____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = l_Lean_reprPosition___redArg___closed__16____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_10);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_1);
x_35 = l_Lean_reprPosition___redArg___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_36 = l_Lean_reprPosition___redArg___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_37 = l_Lean_reprPosition___redArg___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_38 = l_Nat_reprFast(x_33);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = 0;
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_reprPosition___redArg___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_reprPosition___redArg___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_35);
x_51 = l_Lean_reprPosition___redArg___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_52 = l_Nat_reprFast(x_34);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_41);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_reprPosition___redArg___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_58 = l_Lean_reprPosition___redArg___closed__15____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_60 = l_Lean_reprPosition___redArg___closed__16____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_41);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reprPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reprPosition___redArg____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_reprPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reprPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprPosition___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_reprPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprPosition() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprPosition___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lean_toJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_toJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_toJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_6 = l_Lean_JsonNumber_fromNat(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_11 = l_Lean_JsonNumber_fromNat(x_4);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_toJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_;
x_18 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lean_toJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50__spec__0(x_16, x_17);
x_19 = l_Lean_Json_mkObj(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_23 = l_Lean_JsonNumber_fromNat(x_20);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_29 = l_Lean_JsonNumber_fromNat(x_21);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_toJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_;
x_36 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lean_toJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50__spec__0(x_34, x_35);
x_37 = l_Lean_Json_mkObj(x_36);
return x_37;
}
}
}
static lean_object* _init_l_Lean_instToJsonPosition___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_toJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonPosition() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonPosition___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getNat_x3f(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Position", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_fromJsonPosition___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_2 = l_Lean_fromJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_fromJsonPosition___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_fromJsonPosition___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_2 = l_Lean_fromJsonPosition___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_fromJsonPosition___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_fromJsonPosition___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_2 = l_Lean_fromJsonPosition___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_fromJsonPosition___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_2 = l_Lean_fromJsonPosition___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_fromJsonPosition___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_fromJsonPosition___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_2 = l_Lean_fromJsonPosition___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_fromJsonPosition___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_fromJsonPosition___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_2 = l_Lean_fromJsonPosition___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_fromJsonPosition___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_fromJsonPosition___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_;
x_17 = l_Lean_Json_getObjValAs_x3f___at___Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60__spec__0(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_fromJsonPosition___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_fromJsonPosition___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60__spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_fromJsonPosition____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFromJsonPosition___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Position_lt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Position_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_10 = l_Lean_Position_lt___closed__0;
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_11 = l_Prod_lexLtDec___redArg(x_9, x_10, x_10, x_2, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_17 = l_Lean_Position_lt___closed__0;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_14);
x_19 = l_Prod_lexLtDec___redArg(x_16, x_17, x_17, x_18, x_1);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_24 = x_2;
} else {
 lean_dec_ref(x_2);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_26 = l_Lean_Position_lt___closed__0;
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
x_29 = l_Prod_lexLtDec___redArg(x_25, x_26, x_26, x_27, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Position_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Position_lt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Position_instToFormat___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟨", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Position_instToFormat___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Position_instToFormat___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Position_instToFormat___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Position_instToFormat___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Position_instToFormat___lam__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Position_instToFormat___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟩", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Position_instToFormat___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Position_instToFormat___lam__0___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToFormat___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Position_instToFormat___lam__0___closed__1;
x_6 = l_Nat_reprFast(x_3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_5);
x_8 = l_Lean_Position_instToFormat___lam__0___closed__3;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Nat_reprFast(x_4);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Position_instToFormat___lam__0___closed__5;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_Lean_Position_instToFormat___lam__0___closed__1;
x_18 = l_Nat_reprFast(x_15);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Position_instToFormat___lam__0___closed__3;
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Nat_reprFast(x_16);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Position_instToFormat___lam__0___closed__5;
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Position_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Position_instToFormat___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Position_instToFormat___lam__0___closed__0;
x_5 = l_Nat_reprFast(x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = l_Lean_Position_instToFormat___lam__0___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_reprFast(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_Position_instToFormat___lam__0___closed__4;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Position_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Position_instToString___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mk", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Position_instToExpr___lam__0___closed__0;
x_2 = l_Lean_fromJsonPosition___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = l_Lean_fromJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Position_instToExpr___lam__0___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Position_instToExpr___lam__0___closed__2;
x_5 = l_Lean_mkNatLit(x_2);
x_6 = l_Lean_mkNatLit(x_3);
x_7 = l_Lean_Position_instToExpr___lam__0___closed__3;
x_8 = lean_array_push(x_7, x_5);
x_9 = lean_array_push(x_8, x_6);
x_10 = l_Lean_mkAppN(x_4, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_fromJsonPosition___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Position_instToExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Position_instToExpr___lam__0), 1, 0);
x_2 = l_Lean_Position_instToExpr___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FileMap_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedFileMap___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedFileMap___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedFileMap___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedFileMap___closed__1;
x_2 = l_Lean_instInhabitedFileMap___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedFileMap() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedFileMap___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadFileMap_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadFileMap_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MonadFileMap_ctorIdx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FileMap_getLastLine(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = l_Lean_FileMap_getLastLine(x_1);
x_6 = lean_nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_dec(x_5);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_getLine(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_2);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_8 = 10;
x_9 = lean_uint32_dec_eq(x_6, x_8);
if (x_9 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_7);
x_13 = lean_array_push(x_4, x_7);
x_2 = x_7;
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_array_push(x_4, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_FileMap_ofString___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_FileMap_ofString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_FileMap_ofString___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ofString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_FileMap_ofString___closed__1;
x_5 = l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_3, x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_string_utf8_at_end(x_2, x_3);
x_5 = x_12;
goto block_10;
}
else
{
x_5 = x_11;
goto block_10;
}
block_10:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_string_utf8_next(x_2, x_3);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_3 = x_6;
x_4 = x_8;
goto _start;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_5, x_8);
x_10 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_nat_add(x_5, x_6);
x_12 = lean_nat_shiftr(x_11, x_8);
lean_dec(x_11);
x_13 = lean_array_get_borrowed(x_7, x_4, x_12);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_13, x_2);
if (x_15 == 0)
{
lean_dec(x_6);
x_6 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
x_18 = l_Lean_FileMap_getLine(x_1, x_12);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_20 = lean_array_get_borrowed(x_7, x_4, x_5);
x_21 = l_Lean_FileMap_getLine(x_1, x_5);
lean_dec(x_5);
lean_inc(x_20);
x_22 = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(x_2, x_3, x_20, x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_24; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_array_get_size(x_4);
x_24 = lean_nat_dec_le(x_6, x_7);
if (x_24 == 0)
{
x_8 = x_24;
goto block_23;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Array_back_x21___redArg(x_5, x_4);
x_26 = lean_nat_dec_le(x_2, x_25);
lean_dec(x_25);
x_8 = x_26;
goto block_23;
}
block_23:
{
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = l_Array_isEmpty___redArg(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_FileMap_getLastLine(x_1);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = l_Array_back_x21___redArg(x_5, x_4);
lean_dec_ref(x_4);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_14);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = l_Array_back_x21___redArg(x_5, x_4);
lean_dec_ref(x_4);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_19 = l_Lean_instInhabitedPosition___closed__0;
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_7, x_20);
lean_dec(x_7);
x_22 = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(x_1, x_2, x_3, x_4, x_5, x_21);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_toPosition(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ofPosition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = l_Array_isEmpty___redArg(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_back_x21___redArg(x_18, x_6);
lean_dec_ref(x_6);
x_8 = x_19;
goto block_12;
}
else
{
lean_object* x_20; 
lean_dec_ref(x_6);
x_20 = lean_unsigned_to_nat(0u);
x_8 = x_20;
goto block_12;
}
}
else
{
lean_object* x_21; 
x_21 = lean_array_fget(x_6, x_14);
lean_dec(x_14);
lean_dec_ref(x_6);
x_8 = x_21;
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(0, 2, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_String_Iterator_nextn(x_9, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_2, x_4);
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = l_Array_back_x3f___redArg(x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(0u);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_array_fget_borrowed(x_3, x_5);
lean_dec(x_5);
lean_inc(x_11);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_lineStart(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_toFileMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FileMap_ofString(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Position(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedPosition___closed__0 = _init_l_Lean_instInhabitedPosition___closed__0();
lean_mark_persistent(l_Lean_instInhabitedPosition___closed__0);
l_Lean_instInhabitedPosition = _init_l_Lean_instInhabitedPosition();
lean_mark_persistent(l_Lean_instInhabitedPosition);
l_Lean_reprPosition___redArg___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__15____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__15____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__15____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_reprPosition___redArg___closed__16____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_ = _init_l_Lean_reprPosition___redArg___closed__16____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_();
lean_mark_persistent(l_Lean_reprPosition___redArg___closed__16____x40_Lean_Data_Position_1632782336____hygCtx___hyg_42_);
l_Lean_instReprPosition___closed__0 = _init_l_Lean_instReprPosition___closed__0();
lean_mark_persistent(l_Lean_instReprPosition___closed__0);
l_Lean_instReprPosition = _init_l_Lean_instReprPosition();
lean_mark_persistent(l_Lean_instReprPosition);
l_Lean_toJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_ = _init_l_Lean_toJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_();
lean_mark_persistent(l_Lean_toJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_50_);
l_Lean_instToJsonPosition___closed__0 = _init_l_Lean_instToJsonPosition___closed__0();
lean_mark_persistent(l_Lean_instToJsonPosition___closed__0);
l_Lean_instToJsonPosition = _init_l_Lean_instToJsonPosition();
lean_mark_persistent(l_Lean_instToJsonPosition);
l_Lean_fromJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__0____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__1____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__2____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__3____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__4____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__5____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__6____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__7____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__8____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__9____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__10____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__11____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__12____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__13____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_fromJsonPosition___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_ = _init_l_Lean_fromJsonPosition___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_();
lean_mark_persistent(l_Lean_fromJsonPosition___closed__14____x40_Lean_Data_Position_1632782336____hygCtx___hyg_60_);
l_Lean_instFromJsonPosition___closed__0 = _init_l_Lean_instFromJsonPosition___closed__0();
lean_mark_persistent(l_Lean_instFromJsonPosition___closed__0);
l_Lean_instFromJsonPosition = _init_l_Lean_instFromJsonPosition();
lean_mark_persistent(l_Lean_instFromJsonPosition);
l_Lean_Position_lt___closed__0 = _init_l_Lean_Position_lt___closed__0();
lean_mark_persistent(l_Lean_Position_lt___closed__0);
l_Lean_Position_instToFormat___lam__0___closed__0 = _init_l_Lean_Position_instToFormat___lam__0___closed__0();
lean_mark_persistent(l_Lean_Position_instToFormat___lam__0___closed__0);
l_Lean_Position_instToFormat___lam__0___closed__1 = _init_l_Lean_Position_instToFormat___lam__0___closed__1();
lean_mark_persistent(l_Lean_Position_instToFormat___lam__0___closed__1);
l_Lean_Position_instToFormat___lam__0___closed__2 = _init_l_Lean_Position_instToFormat___lam__0___closed__2();
lean_mark_persistent(l_Lean_Position_instToFormat___lam__0___closed__2);
l_Lean_Position_instToFormat___lam__0___closed__3 = _init_l_Lean_Position_instToFormat___lam__0___closed__3();
lean_mark_persistent(l_Lean_Position_instToFormat___lam__0___closed__3);
l_Lean_Position_instToFormat___lam__0___closed__4 = _init_l_Lean_Position_instToFormat___lam__0___closed__4();
lean_mark_persistent(l_Lean_Position_instToFormat___lam__0___closed__4);
l_Lean_Position_instToFormat___lam__0___closed__5 = _init_l_Lean_Position_instToFormat___lam__0___closed__5();
lean_mark_persistent(l_Lean_Position_instToFormat___lam__0___closed__5);
l_Lean_Position_instToFormat = _init_l_Lean_Position_instToFormat();
lean_mark_persistent(l_Lean_Position_instToFormat);
l_Lean_Position_instToString = _init_l_Lean_Position_instToString();
lean_mark_persistent(l_Lean_Position_instToString);
l_Lean_Position_instToExpr___lam__0___closed__0 = _init_l_Lean_Position_instToExpr___lam__0___closed__0();
lean_mark_persistent(l_Lean_Position_instToExpr___lam__0___closed__0);
l_Lean_Position_instToExpr___lam__0___closed__1 = _init_l_Lean_Position_instToExpr___lam__0___closed__1();
lean_mark_persistent(l_Lean_Position_instToExpr___lam__0___closed__1);
l_Lean_Position_instToExpr___lam__0___closed__2 = _init_l_Lean_Position_instToExpr___lam__0___closed__2();
lean_mark_persistent(l_Lean_Position_instToExpr___lam__0___closed__2);
l_Lean_Position_instToExpr___lam__0___closed__3 = _init_l_Lean_Position_instToExpr___lam__0___closed__3();
lean_mark_persistent(l_Lean_Position_instToExpr___lam__0___closed__3);
l_Lean_Position_instToExpr___closed__0 = _init_l_Lean_Position_instToExpr___closed__0();
lean_mark_persistent(l_Lean_Position_instToExpr___closed__0);
l_Lean_Position_instToExpr = _init_l_Lean_Position_instToExpr();
lean_mark_persistent(l_Lean_Position_instToExpr);
l_Lean_instInhabitedFileMap___closed__0 = _init_l_Lean_instInhabitedFileMap___closed__0();
lean_mark_persistent(l_Lean_instInhabitedFileMap___closed__0);
l_Lean_instInhabitedFileMap___closed__1 = _init_l_Lean_instInhabitedFileMap___closed__1();
lean_mark_persistent(l_Lean_instInhabitedFileMap___closed__1);
l_Lean_instInhabitedFileMap___closed__2 = _init_l_Lean_instInhabitedFileMap___closed__2();
lean_mark_persistent(l_Lean_instInhabitedFileMap___closed__2);
l_Lean_instInhabitedFileMap = _init_l_Lean_instInhabitedFileMap();
lean_mark_persistent(l_Lean_instInhabitedFileMap);
l_Lean_FileMap_ofString___closed__0 = _init_l_Lean_FileMap_ofString___closed__0();
lean_mark_persistent(l_Lean_FileMap_ofString___closed__0);
l_Lean_FileMap_ofString___closed__1 = _init_l_Lean_FileMap_ofString___closed__1();
lean_mark_persistent(l_Lean_FileMap_ofString___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
