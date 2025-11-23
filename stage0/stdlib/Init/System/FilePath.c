// Lean compiler output
// Module: Init.System.FilePath
// Imports: public import Init.Data.String.Basic import Init.Data.String.Modify import Init.Data.String.Search
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
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators;
lean_object* l_String_revFindAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00String_mapAux___at___00System_FilePath_normalize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instInhabitedFilePath_default;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object*);
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6;
LEAN_EXPORT lean_object* l_System_FilePath_instHDivString___lam__0(lean_object*, lean_object*);
static lean_object* l_System_FilePath_exeExtension___closed__0;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static uint8_t l_System_FilePath_pathSeparator___closed__0;
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object*);
static lean_object* l_System_instInhabitedFilePath_default___closed__0;
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instReprFilePath;
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_exeExtension;
static uint8_t l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instHashableFilePath_hash___boxed(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00String_mapAux___at___00System_FilePath_normalize_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2;
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath_decEq___boxed(lean_object*, lean_object*);
static lean_object* l_System_FilePath_join___closed__0;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_System_instReprFilePath___lam__0___closed__0;
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath;
uint32_t l_Char_toUpper(uint32_t);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_System_instReprFilePath___lam__0___closed__1;
LEAN_EXPORT uint64_t l_System_instHashableFilePath_hash(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0(lean_object*, uint32_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object*);
static lean_object* l_System_FilePath_pathSeparators___closed__1;
static lean_object* l_System_FilePath_fileName___closed__1;
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___boxed(lean_object*);
LEAN_EXPORT uint32_t l_System_FilePath_extSeparator;
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object*);
static lean_object* l_System_FilePath_components___closed__0;
static lean_object* l_System_FilePath_instDiv___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_SearchPath_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l_System_instToStringFilePath;
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(lean_object*, lean_object*);
static uint8_t l_System_FilePath_normalize___closed__1;
lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
static lean_object* l_System_FilePath_fileName___closed__0;
static lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
lean_object* l_String_revPosOfAux(lean_object*, uint32_t, lean_object*);
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5;
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
LEAN_EXPORT uint32_t l_System_FilePath_pathSeparator;
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
static lean_object* l_System_FilePath_isAbsolute___closed__0;
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next___redArg(lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7;
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object*);
static lean_object* l_System_SearchPath_toString___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_System_instHashableFilePath;
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object*);
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_FilePath_components_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_SearchPath_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_System_instInhabitedFilePath;
static lean_object* l_System_FilePath_pathSeparators___closed__0;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_System_FilePath_normalize___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_instDiv;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT uint32_t l_System_SearchPath_separator;
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_System_FilePath_extension___closed__0;
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_FilePath_components_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath_decEq(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
static lean_object* l_System_FilePath_fileName___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0(lean_object*, lean_object*);
static lean_object* l_System_instHashableFilePath___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_instHDivString;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object*);
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3;
LEAN_EXPORT lean_object* l_System_FilePath_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_System_instInhabitedFilePath_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_System_instInhabitedFilePath_default() {
_start:
{
lean_object* x_1; 
x_1 = l_System_instInhabitedFilePath_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_System_instInhabitedFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_System_instInhabitedFilePath_default___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_System_instDecidableEqFilePath_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_System_instDecidableEqFilePath(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_System_instHashableFilePath_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = lean_string_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_System_instHashableFilePath_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_System_instHashableFilePath_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_System_instHashableFilePath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_instHashableFilePath_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_System_instHashableFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_System_instHashableFilePath___closed__0;
return x_1;
}
}
static lean_object* _init_l_System_instReprFilePath___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_System_instReprFilePath___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_instReprFilePath___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_System_instReprFilePath___lam__0___closed__1;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Repr_addAppParen(x_6, x_2);
return x_7;
}
}
static lean_object* _init_l_System_instReprFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_instReprFilePath___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_instReprFilePath___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
static lean_object* _init_l_System_instToStringFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_instToStringFilePath___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_instToStringFilePath___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static uint8_t _init_l_System_FilePath_pathSeparator___closed__0() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
return x_1;
}
}
static uint32_t _init_l_System_FilePath_pathSeparator() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__0;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 47;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 92;
return x_3;
}
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators___closed__0;
x_2 = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__0;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_System_FilePath_pathSeparators___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_pathSeparators___closed__1;
return x_3;
}
}
}
static uint32_t _init_l_System_FilePath_extSeparator() {
_start:
{
uint32_t x_1; 
x_1 = 46;
return x_1;
}
}
static lean_object* _init_l_System_FilePath_exeExtension___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exe", 3, 3);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_exeExtension() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__0;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_System_instInhabitedFilePath_default___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_exeExtension___closed__0;
return x_3;
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unbox_uint32(x_4);
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00String_mapAux___at___00System_FilePath_normalize_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_10; uint8_t x_11; 
x_10 = lean_string_utf8_byte_size(x_2);
x_11 = lean_nat_dec_eq(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = lean_string_utf8_get_fast(x_2, x_3);
x_13 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_12, x_1);
if (x_13 == 0)
{
x_4 = x_12;
goto block_9;
}
else
{
uint32_t x_14; 
x_14 = l_System_FilePath_pathSeparator;
x_4 = x_14;
goto block_9;
}
}
else
{
lean_dec(x_3);
return x_2;
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_5 = lean_string_utf8_set(x_2, x_3, x_4);
x_6 = l_Char_utf8Size(x_4);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_2 = x_5;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_10; uint8_t x_11; 
x_10 = lean_string_utf8_byte_size(x_2);
x_11 = lean_nat_dec_eq(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = lean_string_utf8_get_fast(x_2, x_3);
x_13 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_12, x_1);
if (x_13 == 0)
{
x_4 = x_12;
goto block_9;
}
else
{
uint32_t x_14; 
x_14 = l_System_FilePath_pathSeparator;
x_4 = x_14;
goto block_9;
}
}
else
{
lean_dec(x_3);
return x_2;
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_5 = lean_string_utf8_set(x_2, x_3, x_4);
x_6 = l_Char_utf8Size(x_4);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_8 = l_String_mapAux___at___00String_mapAux___at___00System_FilePath_normalize_spec__1_spec__1(x_1, x_5, x_7);
return x_8;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_pathSeparators;
x_2 = l_List_lengthTR___redArg(x_1);
return x_2;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_System_FilePath_normalize___closed__0;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_8; uint8_t x_18; uint8_t x_26; 
x_26 = l_System_FilePath_pathSeparator___closed__0;
if (x_26 == 0)
{
x_18 = x_26;
goto block_25;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_string_length(x_1);
x_29 = lean_nat_dec_le(x_27, x_28);
lean_dec(x_28);
x_18 = x_29;
goto block_25;
}
block_7:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_System_FilePath_pathSeparators;
x_4 = l_System_FilePath_normalize___closed__1;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_mapAux___at___00System_FilePath_normalize_spec__1(x_3, x_2, x_5);
return x_6;
}
else
{
return x_2;
}
}
block_17:
{
if (x_8 == 0)
{
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_string_utf8_get(x_1, x_9);
x_11 = 58;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_13; uint32_t x_14; uint32_t x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_get(x_1, x_13);
x_15 = l_Char_toUpper(x_14);
x_16 = lean_string_utf8_set(x_1, x_13, x_15);
x_2 = x_16;
goto block_7;
}
}
}
block_25:
{
if (x_18 == 0)
{
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_19; uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_string_utf8_get(x_1, x_19);
x_21 = 97;
x_22 = lean_uint32_dec_le(x_21, x_20);
if (x_22 == 0)
{
x_8 = x_22;
goto block_17;
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 122;
x_24 = lean_uint32_dec_le(x_20, x_23);
x_8 = x_24;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00String_mapAux___at___00System_FilePath_normalize_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_mapAux___at___00String_mapAux___at___00System_FilePath_normalize_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_mapAux___at___00System_FilePath_normalize_spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unbox_uint32(x_6);
x_9 = lean_unbox_uint32(x_7);
x_10 = lean_uint32_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 58;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_6; lean_object* x_15; lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_15 = l_System_FilePath_pathSeparators;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_get(x_1, x_16);
x_18 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_17, x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_System_FilePath_pathSeparator___closed__0;
if (x_19 == 0)
{
x_6 = x_19;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_string_length(x_1);
x_22 = lean_nat_dec_lt(x_20, x_21);
lean_dec(x_21);
x_6 = x_22;
goto block_14;
}
}
else
{
lean_dec_ref(x_1);
return x_18;
}
block_5:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_System_FilePath_isAbsolute___closed__0;
x_4 = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(x_2, x_3);
lean_dec(x_2);
return x_4;
}
block_14:
{
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_byte_size(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_String_Slice_Pos_next_x3f(x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_2 = x_11;
goto block_5;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_String_Slice_Pos_get_x3f(x_9, x_12);
lean_dec(x_12);
lean_dec_ref(x_9);
x_2 = x_13;
goto block_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_System_FilePath_isAbsolute(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_FilePath_isAbsolute(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_System_FilePath_isRelative(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparator;
x_2 = l_System_instInhabitedFilePath_default___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc_ref(x_2);
x_3 = l_System_FilePath_isAbsolute(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_System_FilePath_join___closed__0;
x_5 = lean_string_append(x_1, x_4);
x_6 = lean_string_append(x_5, x_2);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
static lean_object* _init_l_System_FilePath_instDiv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_join), 2, 0);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_instDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_instDiv___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_instHDivString___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_instHDivString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_instHDivString___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_System_FilePath_pathSeparators;
x_3 = lean_alloc_closure((void*)(l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_String_revFindAux(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_16; 
x_2 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
x_16 = x_25;
goto block_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_string_utf8_extract(x_1, x_27, x_26);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_16 = x_29;
goto block_24;
}
block_15:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_string_length(x_1);
x_6 = lean_nat_dec_eq(x_5, x_4);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(x_2, x_9);
lean_dec_ref(x_9);
lean_dec(x_2);
if (x_10 == 0)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_extract(x_1, x_11, x_4);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = lean_box(0);
return x_14;
}
}
block_24:
{
uint8_t x_17; 
lean_inc_ref(x_1);
x_17 = l_System_FilePath_isAbsolute(x_1);
if (x_17 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_18 = l_System_FilePath_pathSeparators;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_string_utf8_get(x_1, x_19);
x_21 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_20, x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(3u);
x_3 = x_16;
x_4 = x_22;
goto block_15;
}
else
{
lean_object* x_23; 
x_23 = lean_unsigned_to_nat(1u);
x_3 = x_16;
x_4 = x_23;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_System_FilePath_fileName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("..", 2, 2);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_fileName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_System_FilePath_fileName___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_10; lean_object* x_17; 
x_17 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
if (lean_obj_tag(x_17) == 0)
{
x_10 = x_1;
goto block_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_System_FilePath_fileName___closed__2;
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_21 = lean_string_utf8_byte_size(x_1);
x_22 = lean_string_utf8_extract(x_1, x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_1);
x_10 = x_22;
goto block_16;
}
block_9:
{
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_System_FilePath_fileName___closed__0;
x_5 = lean_string_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_2);
x_7 = lean_box(0);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec_ref(x_2);
x_8 = lean_box(0);
return x_8;
}
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_System_FilePath_fileName___closed__1;
x_15 = lean_string_dec_eq(x_10, x_14);
x_2 = x_10;
x_3 = x_15;
goto block_9;
}
else
{
x_2 = x_10;
x_3 = x_13;
goto block_9;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = 46;
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = l_String_revPosOfAux(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_2);
x_11 = lean_string_utf8_extract(x_3, x_9, x_8);
lean_dec(x_8);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_free_object(x_6);
lean_dec(x_8);
lean_dec(x_3);
return x_2;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_2);
x_15 = lean_string_utf8_extract(x_3, x_13, x_12);
lean_dec(x_12);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
return x_2;
}
}
}
}
}
}
static lean_object* _init_l_System_FilePath_extension___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 46;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = 46;
x_5 = lean_string_utf8_byte_size(x_3);
lean_inc(x_5);
x_6 = l_String_revPosOfAux(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_System_FilePath_extension___closed__0;
x_13 = lean_nat_add(x_9, x_12);
lean_dec(x_9);
x_14 = lean_string_utf8_extract(x_3, x_13, x_5);
lean_dec(x_5);
lean_dec(x_13);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; 
lean_free_object(x_6);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_15 = lean_box(0);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_System_FilePath_extension___closed__0;
x_20 = lean_nat_add(x_16, x_19);
lean_dec(x_16);
x_21 = lean_string_utf8_extract(x_3, x_20, x_5);
lean_dec(x_5);
lean_dec(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
x_23 = lean_box(0);
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_System_FilePath_join(x_4, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_System_FilePath_fileName___closed__1;
x_9 = lean_string_append(x_4, x_8);
x_10 = lean_string_append(x_9, x_2);
x_11 = l_System_FilePath_withFileName(x_1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_System_FilePath_withFileName(x_1, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_addExtension(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_fileStem(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_System_FilePath_fileName___closed__1;
x_9 = lean_string_append(x_4, x_8);
x_10 = lean_string_append(x_9, x_2);
x_11 = l_System_FilePath_withFileName(x_1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_System_FilePath_withFileName(x_1, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_withExtension(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_join___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_System_FilePath_join___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2;
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3;
x_3 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2;
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_FilePath_components_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_14 = x_2;
} else {
 lean_dec_ref(x_2);
 x_14 = lean_box(0);
}
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_34; 
lean_dec(x_14);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_nat_sub(x_37, x_36);
x_39 = lean_nat_dec_eq(x_35, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_inc(x_35);
lean_ctor_set_tag(x_13, 1);
lean_inc(x_35);
x_19 = x_13;
x_20 = x_35;
x_21 = x_35;
goto block_27;
}
else
{
lean_object* x_40; 
lean_free_object(x_13);
x_40 = lean_box(3);
lean_inc(x_35);
x_19 = x_40;
x_20 = x_35;
x_21 = x_35;
goto block_27;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_nat_sub(x_43, x_42);
x_45 = lean_nat_dec_eq(x_41, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_inc(x_41);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
lean_inc(x_41);
x_19 = x_46;
x_20 = x_41;
x_21 = x_41;
goto block_27;
}
else
{
lean_object* x_47; 
x_47 = lean_box(3);
lean_inc(x_41);
x_19 = x_47;
x_20 = x_41;
x_21 = x_41;
goto block_27;
}
}
}
case 1:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = l_String_Slice_Pos_next___redArg(x_1, x_49);
lean_dec(x_49);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_50);
x_15 = x_13;
goto block_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
lean_inc(x_51);
lean_dec(x_13);
x_52 = l_String_Slice_Pos_next___redArg(x_1, x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_15 = x_53;
goto block_18;
}
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_13, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_13, 3);
lean_inc(x_57);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_58 = x_13;
} else {
 lean_dec_ref(x_13);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
x_61 = lean_ctor_get(x_1, 2);
x_62 = lean_nat_sub(x_61, x_60);
x_63 = lean_nat_dec_lt(x_56, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_lt(x_64, x_57);
lean_dec(x_57);
if (x_65 == 0)
{
lean_dec(x_14);
goto block_33;
}
else
{
lean_object* x_66; 
x_66 = lean_box(3);
x_15 = x_66;
goto block_18;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; 
x_67 = lean_ctor_get(x_54, 0);
x_68 = lean_ctor_get(x_54, 1);
x_69 = lean_ctor_get(x_54, 2);
x_70 = lean_nat_add(x_60, x_56);
x_71 = lean_string_get_byte_fast(x_59, x_70);
x_72 = lean_nat_add(x_68, x_57);
x_73 = lean_string_get_byte_fast(x_67, x_72);
x_74 = lean_uint8_dec_eq(x_71, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_79; 
x_75 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_57, x_75);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_sub(x_57, x_80);
lean_dec(x_57);
x_82 = lean_array_fget_borrowed(x_55, x_81);
lean_dec(x_81);
x_83 = lean_nat_dec_eq(x_82, x_75);
if (x_83 == 0)
{
lean_object* x_84; 
lean_inc(x_82);
lean_dec(x_58);
x_84 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_84, 0, x_54);
lean_ctor_set(x_84, 1, x_55);
lean_ctor_set(x_84, 2, x_56);
lean_ctor_set(x_84, 3, x_82);
x_15 = x_84;
goto block_18;
}
else
{
lean_object* x_85; 
lean_inc(x_56);
x_85 = l_String_Slice_pos_x3f(x_1, x_56);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_nat_add(x_56, x_80);
lean_dec(x_56);
x_87 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_1, x_86);
x_76 = x_87;
goto block_78;
}
else
{
lean_object* x_88; 
lean_dec(x_56);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec_ref(x_85);
x_76 = x_88;
goto block_78;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_58);
lean_dec(x_57);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_56, x_89);
lean_dec(x_56);
x_91 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_1, x_90);
x_92 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_92, 0, x_54);
lean_ctor_set(x_92, 1, x_55);
lean_ctor_set(x_92, 2, x_91);
lean_ctor_set(x_92, 3, x_75);
x_15 = x_92;
goto block_18;
}
block_78:
{
lean_object* x_77; 
if (lean_is_scalar(x_58)) {
 x_77 = lean_alloc_ctor(2, 4, 0);
} else {
 x_77 = x_58;
}
lean_ctor_set(x_77, 0, x_54);
lean_ctor_set(x_77, 1, x_55);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_75);
x_15 = x_77;
goto block_18;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_14);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_56, x_93);
lean_dec(x_56);
x_95 = lean_nat_add(x_57, x_93);
lean_dec(x_57);
x_96 = lean_nat_sub(x_69, x_68);
x_97 = lean_nat_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_96);
if (lean_is_scalar(x_58)) {
 x_98 = lean_alloc_ctor(2, 4, 0);
} else {
 x_98 = x_58;
}
lean_ctor_set(x_98, 0, x_54);
lean_ctor_set(x_98, 1, x_55);
lean_ctor_set(x_98, 2, x_94);
lean_ctor_set(x_98, 3, x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_12);
lean_ctor_set(x_99, 1, x_98);
x_2 = x_99;
goto _start;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_95);
x_101 = lean_nat_sub(x_94, x_96);
lean_dec(x_96);
x_102 = l_String_Slice_pos_x21(x_1, x_101);
lean_dec(x_101);
x_103 = l_String_Slice_pos_x21(x_1, x_94);
x_104 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_58)) {
 x_105 = lean_alloc_ctor(2, 4, 0);
} else {
 x_105 = x_58;
}
lean_ctor_set(x_105, 0, x_54);
lean_ctor_set(x_105, 1, x_55);
lean_ctor_set(x_105, 2, x_94);
lean_ctor_set(x_105, 3, x_104);
x_19 = x_105;
x_20 = x_102;
x_21 = x_103;
goto block_27;
}
}
}
}
default: 
{
lean_dec(x_14);
goto block_33;
}
}
block_18:
{
lean_object* x_16; 
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
goto _start;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_1);
x_22 = l_String_Slice_slice_x21(x_1, x_12, x_20);
lean_dec(x_20);
lean_dec(x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_19);
x_4 = x_26;
x_5 = x_23;
x_6 = x_24;
x_7 = x_25;
goto block_11;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_nat_add(x_29, x_12);
lean_dec(x_12);
x_32 = lean_box(1);
lean_inc(x_30);
lean_inc_ref(x_28);
x_4 = x_32;
x_5 = x_28;
x_6 = x_31;
x_7 = x_30;
goto block_11;
}
}
else
{
lean_dec_ref(x_1);
return x_3;
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_array_push(x_3, x_8);
x_2 = x_4;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_FilePath_components_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_FilePath_components_spec__1___redArg(x_1, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_System_FilePath_components___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_System_FilePath_normalize(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_split___at___00System_FilePath_components_spec__0(x_5);
x_7 = l_System_FilePath_components___closed__0;
x_8 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_FilePath_components_spec__1___redArg(x_5, x_6, x_7);
x_9 = lean_array_to_list(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00System_FilePath_components_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_System_FilePath_join___closed__0;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
static lean_object* _init_l_System_instCoeStringFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_instCoeStringFilePath___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_instCoeStringFilePath___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static uint32_t _init_l_System_SearchPath_separator() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__0;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 58;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 59;
return x_3;
}
}
}
static lean_object* _init_l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_SearchPath_separator;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_SearchPath_parse_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get_uint32(x_13, sizeof(void*)*1);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_nat_sub(x_20, x_19);
x_22 = lean_nat_dec_eq(x_16, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_23 = l_String_Slice_Pos_next___redArg(x_1, x_16);
lean_inc(x_23);
lean_ctor_set(x_13, 0, x_23);
x_24 = lean_nat_add(x_19, x_16);
x_25 = lean_string_utf8_get_fast(x_18, x_24);
lean_dec(x_24);
x_26 = lean_uint32_dec_eq(x_25, x_17);
if (x_26 == 0)
{
lean_dec(x_23);
lean_dec(x_16);
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_1);
x_28 = l_String_Slice_slice_x21(x_1, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
lean_dec_ref(x_28);
lean_ctor_set(x_2, 0, x_23);
x_4 = x_2;
x_5 = x_29;
x_6 = x_30;
x_7 = x_31;
goto block_11;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_13);
lean_dec(x_16);
lean_free_object(x_2);
x_32 = lean_nat_add(x_19, x_15);
lean_dec(x_15);
x_33 = lean_box(1);
lean_inc(x_20);
lean_inc_ref(x_18);
x_4 = x_33;
x_5 = x_18;
x_6 = x_32;
x_7 = x_20;
goto block_11;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint32_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get_uint32(x_13, sizeof(void*)*1);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_1, 2);
x_40 = lean_nat_sub(x_39, x_38);
x_41 = lean_nat_dec_eq(x_35, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; uint8_t x_46; 
x_42 = l_String_Slice_Pos_next___redArg(x_1, x_35);
lean_inc(x_42);
x_43 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint32(x_43, sizeof(void*)*1, x_36);
x_44 = lean_nat_add(x_38, x_35);
x_45 = lean_string_utf8_get_fast(x_37, x_44);
lean_dec(x_44);
x_46 = lean_uint32_dec_eq(x_45, x_36);
if (x_46 == 0)
{
lean_dec(x_42);
lean_dec(x_35);
lean_ctor_set(x_2, 1, x_43);
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc_ref(x_1);
x_48 = l_String_Slice_slice_x21(x_1, x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 2);
lean_inc(x_51);
lean_dec_ref(x_48);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_42);
x_4 = x_2;
x_5 = x_49;
x_6 = x_50;
x_7 = x_51;
goto block_11;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_free_object(x_2);
x_52 = lean_nat_add(x_38, x_34);
lean_dec(x_34);
x_53 = lean_box(1);
lean_inc(x_39);
lean_inc_ref(x_37);
x_4 = x_53;
x_5 = x_37;
x_6 = x_52;
x_7 = x_39;
goto block_11;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint32_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint32(x_54, sizeof(void*)*1);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
x_61 = lean_ctor_get(x_1, 2);
x_62 = lean_nat_sub(x_61, x_60);
x_63 = lean_nat_dec_eq(x_56, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint32_t x_67; uint8_t x_68; 
x_64 = l_String_Slice_Pos_next___redArg(x_1, x_56);
lean_inc(x_64);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 1, 4);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint32(x_65, sizeof(void*)*1, x_57);
x_66 = lean_nat_add(x_60, x_56);
x_67 = lean_string_utf8_get_fast(x_59, x_66);
lean_dec(x_66);
x_68 = lean_uint32_dec_eq(x_67, x_57);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_64);
lean_dec(x_56);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_65);
x_2 = x_69;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc_ref(x_1);
x_71 = l_String_Slice_slice_x21(x_1, x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
x_72 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 2);
lean_inc(x_74);
lean_dec_ref(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_65);
x_4 = x_75;
x_5 = x_72;
x_6 = x_73;
x_7 = x_74;
goto block_11;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_58);
lean_dec(x_56);
x_76 = lean_nat_add(x_60, x_55);
lean_dec(x_55);
x_77 = lean_box(1);
lean_inc(x_61);
lean_inc_ref(x_59);
x_4 = x_77;
x_5 = x_59;
x_6 = x_76;
x_7 = x_61;
goto block_11;
}
}
}
else
{
lean_dec_ref(x_1);
return x_3;
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_array_push(x_3, x_8);
x_2 = x_4;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_SearchPath_parse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_SearchPath_parse_spec__1___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_split___at___00System_SearchPath_parse_spec__0(x_4);
x_6 = l_System_FilePath_components___closed__0;
x_7 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00System_SearchPath_parse_spec__1___redArg(x_4, x_5, x_6);
x_8 = lean_array_to_list(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00System_SearchPath_parse_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_SearchPath_separator;
x_2 = l_System_instInhabitedFilePath_default___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_System_SearchPath_toString___closed__0;
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(x_1, x_3);
x_5 = l_String_intercalate(x_2, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_instInhabitedFilePath_default___closed__0 = _init_l_System_instInhabitedFilePath_default___closed__0();
lean_mark_persistent(l_System_instInhabitedFilePath_default___closed__0);
l_System_instInhabitedFilePath_default = _init_l_System_instInhabitedFilePath_default();
lean_mark_persistent(l_System_instInhabitedFilePath_default);
l_System_instInhabitedFilePath = _init_l_System_instInhabitedFilePath();
lean_mark_persistent(l_System_instInhabitedFilePath);
l_System_instHashableFilePath___closed__0 = _init_l_System_instHashableFilePath___closed__0();
lean_mark_persistent(l_System_instHashableFilePath___closed__0);
l_System_instHashableFilePath = _init_l_System_instHashableFilePath();
lean_mark_persistent(l_System_instHashableFilePath);
l_System_instReprFilePath___lam__0___closed__0 = _init_l_System_instReprFilePath___lam__0___closed__0();
lean_mark_persistent(l_System_instReprFilePath___lam__0___closed__0);
l_System_instReprFilePath___lam__0___closed__1 = _init_l_System_instReprFilePath___lam__0___closed__1();
lean_mark_persistent(l_System_instReprFilePath___lam__0___closed__1);
l_System_instReprFilePath = _init_l_System_instReprFilePath();
lean_mark_persistent(l_System_instReprFilePath);
l_System_instToStringFilePath = _init_l_System_instToStringFilePath();
lean_mark_persistent(l_System_instToStringFilePath);
l_System_FilePath_pathSeparator___closed__0 = _init_l_System_FilePath_pathSeparator___closed__0();
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators___closed__0___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__0___boxed__const__1);
l_System_FilePath_pathSeparators___closed__0 = _init_l_System_FilePath_pathSeparators___closed__0();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__0);
l_System_FilePath_pathSeparators___closed__1___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1___boxed__const__1);
l_System_FilePath_pathSeparators___closed__1 = _init_l_System_FilePath_pathSeparators___closed__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1);
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean_mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
l_System_FilePath_exeExtension___closed__0 = _init_l_System_FilePath_exeExtension___closed__0();
lean_mark_persistent(l_System_FilePath_exeExtension___closed__0);
l_System_FilePath_exeExtension = _init_l_System_FilePath_exeExtension();
lean_mark_persistent(l_System_FilePath_exeExtension);
l_System_FilePath_normalize___closed__0 = _init_l_System_FilePath_normalize___closed__0();
lean_mark_persistent(l_System_FilePath_normalize___closed__0);
l_System_FilePath_normalize___closed__1 = _init_l_System_FilePath_normalize___closed__1();
l_System_FilePath_isAbsolute___closed__0___boxed__const__1 = _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1();
lean_mark_persistent(l_System_FilePath_isAbsolute___closed__0___boxed__const__1);
l_System_FilePath_isAbsolute___closed__0 = _init_l_System_FilePath_isAbsolute___closed__0();
lean_mark_persistent(l_System_FilePath_isAbsolute___closed__0);
l_System_FilePath_join___closed__0 = _init_l_System_FilePath_join___closed__0();
lean_mark_persistent(l_System_FilePath_join___closed__0);
l_System_FilePath_instDiv___closed__0 = _init_l_System_FilePath_instDiv___closed__0();
lean_mark_persistent(l_System_FilePath_instDiv___closed__0);
l_System_FilePath_instDiv = _init_l_System_FilePath_instDiv();
lean_mark_persistent(l_System_FilePath_instDiv);
l_System_FilePath_instHDivString = _init_l_System_FilePath_instHDivString();
lean_mark_persistent(l_System_FilePath_instHDivString);
l_System_FilePath_fileName___closed__0 = _init_l_System_FilePath_fileName___closed__0();
lean_mark_persistent(l_System_FilePath_fileName___closed__0);
l_System_FilePath_fileName___closed__1 = _init_l_System_FilePath_fileName___closed__1();
lean_mark_persistent(l_System_FilePath_fileName___closed__1);
l_System_FilePath_fileName___closed__2 = _init_l_System_FilePath_fileName___closed__2();
lean_mark_persistent(l_System_FilePath_fileName___closed__2);
l_System_FilePath_extension___closed__0 = _init_l_System_FilePath_extension___closed__0();
lean_mark_persistent(l_System_FilePath_extension___closed__0);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1();
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7);
l_System_FilePath_components___closed__0 = _init_l_System_FilePath_components___closed__0();
lean_mark_persistent(l_System_FilePath_components___closed__0);
l_System_instCoeStringFilePath = _init_l_System_instCoeStringFilePath();
lean_mark_persistent(l_System_instCoeStringFilePath);
l_System_SearchPath_separator = _init_l_System_SearchPath_separator();
l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0 = _init_l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0);
l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__1 = _init_l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__1();
lean_mark_persistent(l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__1);
l_System_SearchPath_toString___closed__0 = _init_l_System_SearchPath_toString___closed__0();
lean_mark_persistent(l_System_SearchPath_toString___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
