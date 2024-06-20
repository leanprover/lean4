// Lean compiler output
// Module: Lake.Util.Git
// Imports: Init Lake.Util.Proc Lake.Util.Lift
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
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_String_endsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__4;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
static lean_object* l_Lake_GitRepo_getHeadRevision___closed__2;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
LEAN_EXPORT lean_object* l_Lake_instToStringGitRepo(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Git_filterUrl_x3f___closed__2;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_object* l_Lake_GitRepo_quietInit___closed__4;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_quietInit___closed__5;
static lean_object* l_Lake_GitRepo_cwd___closed__1;
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
LEAN_EXPORT uint8_t l_String_anyAux___at_Lake_Git_isFullObjectName___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__5;
static lean_object* l_Lake_GitRepo_fetch___closed__1;
static lean_object* l_Lake_GitRepo_branchExists___closed__4;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_quietInit___closed__1;
static lean_object* l_Lake_GitRepo_quietInit___closed__3;
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_clone___closed__2;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_dropRight(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_clone___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_cwd;
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__3;
static lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_clone___closed__3;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1;
uint8_t l_String_startsWith(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_captureProc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
static lean_object* l_Lake_GitRepo_captureGit___closed__2;
static lean_object* l_Lake_Git_upstreamBranch___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_getHeadRevision___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_branchExists___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at_Lake_Git_isFullObjectName___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_testProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_defaultRemote;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
uint8_t l_Char_isDigit(uint32_t);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringGitRepo___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__2;
static lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__2;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_captureGit___closed__1;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__1;
static lean_object* l_Lake_GitRepo_quietInit___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Git_defaultRemote___closed__1;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__1;
static lean_object* l_Lake_GitRepo_fetch___closed__2;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__1;
static lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__3;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__6;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_Git_upstreamBranch;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_Git_defaultRemote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("origin", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Git_defaultRemote() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Git_defaultRemote___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Git_upstreamBranch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("master", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Git_upstreamBranch() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Git_upstreamBranch___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".git", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lake_Git_filterUrl_x3f___closed__1;
lean_inc(x_1);
x_3 = l_String_startsWith(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_Git_filterUrl_x3f___closed__2;
lean_inc(x_1);
x_5 = l_String_endsWith(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(4u);
x_8 = l_String_dropRight(x_1, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at_Lake_Git_isFullObjectName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = l_Char_isDigit(x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 97;
x_9 = lean_uint32_dec_le(x_8, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = 1;
return x_10;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 102;
x_12 = lean_uint32_dec_le(x_6, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_14;
goto _start;
}
}
}
else
{
lean_object* x_16; 
x_16 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(40u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_anyAux___at_Lake_Git_isFullObjectName___spec__1(x_1, x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at_Lake_Git_isFullObjectName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at_Lake_Git_isFullObjectName___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Git_isFullObjectName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringGitRepo(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringGitRepo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToStringGitRepo(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_cwd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_cwd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_GitRepo_cwd___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_isDir(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_GitRepo_dirExists(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_captureGit___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_captureGit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l_Lake_GitRepo_captureGit___closed__1;
x_7 = l_Lake_Git_filterUrl_x3f___closed__1;
x_8 = l_Lake_GitRepo_captureGit___closed__2;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
x_11 = l_Lake_captureProc(x_10, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_GitRepo_captureGit___closed__1;
x_6 = l_Lake_Git_filterUrl_x3f___closed__1;
x_7 = l_Lake_GitRepo_captureGit___closed__2;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_8);
x_10 = l_Lake_captureProc_x3f(x_9, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l_Lake_GitRepo_captureGit___closed__1;
x_7 = l_Lake_Git_filterUrl_x3f___closed__1;
x_8 = l_Lake_GitRepo_captureGit___closed__2;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
x_11 = 1;
x_12 = l_Lake_proc(x_10, x_11, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lake_GitRepo_captureGit___closed__1;
x_6 = l_Lake_Git_filterUrl_x3f___closed__1;
x_7 = l_Lake_GitRepo_captureGit___closed__2;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_8);
x_10 = l_Lake_testProc(x_9, x_3);
return x_10;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clone", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_clone___closed__1;
x_2 = l_Lake_GitRepo_clone___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = l_Lake_GitRepo_clone___closed__3;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_2);
x_8 = lean_box(0);
x_9 = l_Lake_GitRepo_captureGit___closed__1;
x_10 = l_Lake_Git_filterUrl_x3f___closed__1;
x_11 = l_Lake_GitRepo_captureGit___closed__2;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_7);
lean_ctor_set(x_13, 3, x_8);
lean_ctor_set(x_13, 4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_12);
x_14 = 1;
x_15 = l_Lake_proc(x_13, x_14, x_3, x_4);
return x_15;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_quietInit___closed__1;
x_2 = l_Lake_GitRepo_quietInit___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-q", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_quietInit___closed__3;
x_2 = l_Lake_GitRepo_quietInit___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Lake_GitRepo_captureGit___closed__1;
x_6 = l_Lake_Git_filterUrl_x3f___closed__1;
x_7 = l_Lake_GitRepo_quietInit___closed__5;
x_8 = l_Lake_GitRepo_captureGit___closed__2;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
x_11 = 1;
x_12 = l_Lake_proc(x_10, x_11, x_2, x_3);
return x_12;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fetch", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_quietInit___closed__1;
x_2 = l_Lake_GitRepo_fetch___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = l_Lake_GitRepo_fetch___closed__2;
x_6 = lean_array_push(x_5, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lake_GitRepo_captureGit___closed__1;
x_9 = l_Lake_Git_filterUrl_x3f___closed__1;
x_10 = l_Lake_GitRepo_captureGit___closed__2;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_11);
x_13 = 1;
x_14 = l_Lake_proc(x_12, x_13, x_3, x_4);
return x_14;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkout", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_clone___closed__1;
x_2 = l_Lake_GitRepo_checkoutBranch___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-B", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_checkoutBranch___closed__2;
x_2 = l_Lake_GitRepo_checkoutBranch___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = l_Lake_GitRepo_checkoutBranch___closed__4;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lake_GitRepo_captureGit___closed__1;
x_9 = l_Lake_Git_filterUrl_x3f___closed__1;
x_10 = l_Lake_GitRepo_captureGit___closed__2;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_11);
x_13 = 1;
x_14 = l_Lake_proc(x_12, x_13, x_3, x_4);
return x_14;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--detach", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_checkoutBranch___closed__2;
x_2 = l_Lake_GitRepo_checkoutDetach___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = l_Lake_GitRepo_checkoutDetach___closed__2;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lake_GitRepo_captureGit___closed__1;
x_9 = l_Lake_Git_filterUrl_x3f___closed__1;
x_10 = l_Lake_GitRepo_captureGit___closed__2;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_11);
x_13 = 1;
x_14 = l_Lake_proc(x_12, x_13, x_3, x_4);
return x_14;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_clone___closed__1;
x_2 = l_Lake_GitRepo_resolveRevision_x3f___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--verify", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_resolveRevision_x3f___closed__2;
x_2 = l_Lake_GitRepo_resolveRevision_x3f___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lake_GitRepo_resolveRevision_x3f___closed__4;
x_5 = lean_array_push(x_4, x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lake_GitRepo_captureGit___closed__1;
x_8 = l_Lake_Git_filterUrl_x3f___closed__1;
x_9 = l_Lake_GitRepo_captureGit___closed__2;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_10);
x_12 = l_Lake_captureProc_x3f(x_11, x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lake_GitRepo_resolveRevision_x3f___closed__4;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lake_GitRepo_captureGit___closed__1;
x_9 = l_Lake_Git_filterUrl_x3f___closed__1;
x_10 = l_Lake_GitRepo_captureGit___closed__2;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_11);
x_13 = l_Lake_captureProc(x_12, x_3, x_4);
return x_13;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEAD", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevision___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_resolveRevision_x3f___closed__4;
x_2 = l_Lake_GitRepo_getHeadRevision___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Lake_GitRepo_captureGit___closed__1;
x_6 = l_Lake_Git_filterUrl_x3f___closed__1;
x_7 = l_Lake_GitRepo_getHeadRevision___closed__2;
x_8 = l_Lake_GitRepo_captureGit___closed__2;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
x_11 = l_Lake_captureProc(x_10, x_2, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lake_GitRepo_captureGit___closed__1;
x_5 = l_Lake_Git_filterUrl_x3f___closed__1;
x_6 = l_Lake_GitRepo_getHeadRevision___closed__2;
x_7 = l_Lake_GitRepo_captureGit___closed__2;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_8);
x_10 = l_Lake_captureProc_x3f(x_9, x_2);
return x_10;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot find revision ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" in repository ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__1;
x_7 = lean_string_append(x_6, x_1);
x_8 = l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_2);
x_11 = l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = 3;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_array_get_size(x_4);
x_16 = lean_array_push(x_4, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_10 = lean_array_push(x_1, x_2);
x_11 = l_Lake_Git_filterUrl_x3f___closed__1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_12);
x_14 = l_Lake_captureProc_x3f(x_13, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Lake_GitRepo_resolveRemoteRevision___lambda__1(x_2, x_6, x_17, x_8, x_16);
lean_dec(x_2);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRemoteRevision___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__3;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lake_GitRepo_resolveRemoteRevision___lambda__3___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_2);
x_12 = lean_string_append(x_11, x_7);
x_13 = l_Lake_GitRepo_resolveRevision_x3f___closed__4;
x_14 = lean_array_push(x_13, x_12);
lean_inc(x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = l_Lake_GitRepo_captureGit___closed__1;
x_17 = l_Lake_Git_filterUrl_x3f___closed__1;
x_18 = l_Lake_GitRepo_captureGit___closed__2;
x_19 = 0;
lean_inc(x_15);
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_19);
x_21 = l_Lake_captureProc_x3f(x_20, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_Lake_GitRepo_resolveRemoteRevision___lambda__2(x_13, x_2, x_16, x_15, x_18, x_3, x_24, x_5, x_23);
lean_dec(x_3);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lake_Git_isFullObjectName(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lake_GitRepo_resolveRemoteRevision___lambda__3(x_2, x_1, x_3, x_7, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_GitRepo_resolveRemoteRevision___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_GitRepo_resolveRemoteRevision___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_GitRepo_resolveRemoteRevision___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_GitRepo_resolveRemoteRevision(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_6 = l_Lake_GitRepo_fetch___closed__2;
lean_inc(x_3);
x_7 = lean_array_push(x_6, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l_Lake_GitRepo_captureGit___closed__1;
x_10 = l_Lake_Git_filterUrl_x3f___closed__1;
x_11 = l_Lake_GitRepo_captureGit___closed__2;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_7);
lean_ctor_set(x_13, 3, x_8);
lean_ctor_set(x_13, 4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_12);
x_14 = 1;
x_15 = l_Lake_proc(x_13, x_14, x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lake_Git_upstreamBranch;
x_20 = l_Lake_GitRepo_resolveRemoteRevision(x_19, x_3, x_1, x_18, x_17);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lake_GitRepo_resolveRemoteRevision(x_23, x_3, x_1, x_22, x_21);
lean_dec(x_3);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_15, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_15, 0, x_30);
return x_15;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_34 = x_16;
} else {
 lean_dec_ref(x_16);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refs/heads/", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("show-ref", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_clone___closed__1;
x_2 = l_Lake_GitRepo_branchExists___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_branchExists___closed__3;
x_2 = l_Lake_GitRepo_resolveRevision_x3f___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_4 = l_Lake_GitRepo_branchExists___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__3;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Lake_GitRepo_branchExists___closed__4;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lake_GitRepo_captureGit___closed__1;
x_12 = l_Lake_Git_filterUrl_x3f___closed__1;
x_13 = l_Lake_GitRepo_captureGit___closed__2;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_14);
x_16 = l_Lake_testProc(x_15, x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_branchExists(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("^{commit}", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_4 = l_Lake_GitRepo_revisionExists___closed__1;
x_5 = lean_string_append(x_1, x_4);
x_6 = l_Lake_GitRepo_resolveRevision_x3f___closed__4;
x_7 = lean_array_push(x_6, x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lake_GitRepo_captureGit___closed__1;
x_10 = l_Lake_Git_filterUrl_x3f___closed__1;
x_11 = l_Lake_GitRepo_captureGit___closed__2;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_7);
lean_ctor_set(x_13, 3, x_8);
lean_ctor_set(x_13, 4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_12);
x_14 = l_Lake_testProc(x_13, x_3);
return x_14;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("describe", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_findTag_x3f___closed__1;
x_2 = l_Lake_GitRepo_findTag_x3f___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--tags", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_findTag_x3f___closed__3;
x_2 = l_Lake_GitRepo_findTag_x3f___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exact-match", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_findTag_x3f___closed__5;
x_2 = l_Lake_GitRepo_findTag_x3f___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lake_GitRepo_findTag_x3f___closed__7;
x_5 = lean_array_push(x_4, x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lake_GitRepo_captureGit___closed__1;
x_8 = l_Lake_Git_filterUrl_x3f___closed__1;
x_9 = l_Lake_GitRepo_captureGit___closed__2;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_10);
x_12 = l_Lake_captureProc_x3f(x_11, x_3);
return x_12;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("remote", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_clone___closed__1;
x_2 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get-url", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
x_2 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__4;
x_5 = lean_array_push(x_4, x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lake_GitRepo_captureGit___closed__1;
x_8 = l_Lake_Git_filterUrl_x3f___closed__1;
x_9 = l_Lake_GitRepo_captureGit___closed__2;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_10);
x_12 = l_Lake_captureProc_x3f(x_11, x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__4;
x_5 = lean_array_push(x_4, x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lake_GitRepo_captureGit___closed__1;
x_8 = l_Lake_Git_filterUrl_x3f___closed__1;
x_9 = l_Lake_GitRepo_captureGit___closed__2;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_10);
x_12 = l_Lake_captureProc_x3f(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lake_Git_filterUrl_x3f(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec(x_13);
x_30 = l_Lake_Git_filterUrl_x3f(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diff", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_quietInit___closed__1;
x_2 = l_Lake_GitRepo_hasNoDiff___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exit-code", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_hasNoDiff___closed__2;
x_2 = l_Lake_GitRepo_hasNoDiff___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lake_GitRepo_captureGit___closed__1;
x_5 = l_Lake_Git_filterUrl_x3f___closed__1;
x_6 = l_Lake_GitRepo_hasNoDiff___closed__4;
x_7 = l_Lake_GitRepo_captureGit___closed__2;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_8);
x_10 = l_Lake_testProc(x_9, x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lake_GitRepo_captureGit___closed__1;
x_5 = l_Lake_Git_filterUrl_x3f___closed__1;
x_6 = l_Lake_GitRepo_hasNoDiff___closed__4;
x_7 = l_Lake_GitRepo_captureGit___closed__2;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_8);
x_10 = l_Lake_testProc(x_9, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = lean_box(x_8);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_box(x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lift(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Git_defaultRemote___closed__1 = _init_l_Lake_Git_defaultRemote___closed__1();
lean_mark_persistent(l_Lake_Git_defaultRemote___closed__1);
l_Lake_Git_defaultRemote = _init_l_Lake_Git_defaultRemote();
lean_mark_persistent(l_Lake_Git_defaultRemote);
l_Lake_Git_upstreamBranch___closed__1 = _init_l_Lake_Git_upstreamBranch___closed__1();
lean_mark_persistent(l_Lake_Git_upstreamBranch___closed__1);
l_Lake_Git_upstreamBranch = _init_l_Lake_Git_upstreamBranch();
lean_mark_persistent(l_Lake_Git_upstreamBranch);
l_Lake_Git_filterUrl_x3f___closed__1 = _init_l_Lake_Git_filterUrl_x3f___closed__1();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__1);
l_Lake_Git_filterUrl_x3f___closed__2 = _init_l_Lake_Git_filterUrl_x3f___closed__2();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__2);
l_Lake_GitRepo_cwd___closed__1 = _init_l_Lake_GitRepo_cwd___closed__1();
lean_mark_persistent(l_Lake_GitRepo_cwd___closed__1);
l_Lake_GitRepo_cwd = _init_l_Lake_GitRepo_cwd();
lean_mark_persistent(l_Lake_GitRepo_cwd);
l_Lake_GitRepo_captureGit___closed__1 = _init_l_Lake_GitRepo_captureGit___closed__1();
lean_mark_persistent(l_Lake_GitRepo_captureGit___closed__1);
l_Lake_GitRepo_captureGit___closed__2 = _init_l_Lake_GitRepo_captureGit___closed__2();
lean_mark_persistent(l_Lake_GitRepo_captureGit___closed__2);
l_Lake_GitRepo_clone___closed__1 = _init_l_Lake_GitRepo_clone___closed__1();
lean_mark_persistent(l_Lake_GitRepo_clone___closed__1);
l_Lake_GitRepo_clone___closed__2 = _init_l_Lake_GitRepo_clone___closed__2();
lean_mark_persistent(l_Lake_GitRepo_clone___closed__2);
l_Lake_GitRepo_clone___closed__3 = _init_l_Lake_GitRepo_clone___closed__3();
lean_mark_persistent(l_Lake_GitRepo_clone___closed__3);
l_Lake_GitRepo_quietInit___closed__1 = _init_l_Lake_GitRepo_quietInit___closed__1();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__1);
l_Lake_GitRepo_quietInit___closed__2 = _init_l_Lake_GitRepo_quietInit___closed__2();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__2);
l_Lake_GitRepo_quietInit___closed__3 = _init_l_Lake_GitRepo_quietInit___closed__3();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__3);
l_Lake_GitRepo_quietInit___closed__4 = _init_l_Lake_GitRepo_quietInit___closed__4();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__4);
l_Lake_GitRepo_quietInit___closed__5 = _init_l_Lake_GitRepo_quietInit___closed__5();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__5);
l_Lake_GitRepo_fetch___closed__1 = _init_l_Lake_GitRepo_fetch___closed__1();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__1);
l_Lake_GitRepo_fetch___closed__2 = _init_l_Lake_GitRepo_fetch___closed__2();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__2);
l_Lake_GitRepo_checkoutBranch___closed__1 = _init_l_Lake_GitRepo_checkoutBranch___closed__1();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__1);
l_Lake_GitRepo_checkoutBranch___closed__2 = _init_l_Lake_GitRepo_checkoutBranch___closed__2();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__2);
l_Lake_GitRepo_checkoutBranch___closed__3 = _init_l_Lake_GitRepo_checkoutBranch___closed__3();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__3);
l_Lake_GitRepo_checkoutBranch___closed__4 = _init_l_Lake_GitRepo_checkoutBranch___closed__4();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__4);
l_Lake_GitRepo_checkoutDetach___closed__1 = _init_l_Lake_GitRepo_checkoutDetach___closed__1();
lean_mark_persistent(l_Lake_GitRepo_checkoutDetach___closed__1);
l_Lake_GitRepo_checkoutDetach___closed__2 = _init_l_Lake_GitRepo_checkoutDetach___closed__2();
lean_mark_persistent(l_Lake_GitRepo_checkoutDetach___closed__2);
l_Lake_GitRepo_resolveRevision_x3f___closed__1 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__1();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__1);
l_Lake_GitRepo_resolveRevision_x3f___closed__2 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__2);
l_Lake_GitRepo_resolveRevision_x3f___closed__3 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__3);
l_Lake_GitRepo_resolveRevision_x3f___closed__4 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__4);
l_Lake_GitRepo_getHeadRevision___closed__1 = _init_l_Lake_GitRepo_getHeadRevision___closed__1();
lean_mark_persistent(l_Lake_GitRepo_getHeadRevision___closed__1);
l_Lake_GitRepo_getHeadRevision___closed__2 = _init_l_Lake_GitRepo_getHeadRevision___closed__2();
lean_mark_persistent(l_Lake_GitRepo_getHeadRevision___closed__2);
l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__1 = _init_l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__1();
lean_mark_persistent(l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__1);
l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__2 = _init_l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__2();
lean_mark_persistent(l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__2);
l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__3 = _init_l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__3();
lean_mark_persistent(l_Lake_GitRepo_resolveRemoteRevision___lambda__1___closed__3);
l_Lake_GitRepo_resolveRemoteRevision___lambda__3___closed__1 = _init_l_Lake_GitRepo_resolveRemoteRevision___lambda__3___closed__1();
lean_mark_persistent(l_Lake_GitRepo_resolveRemoteRevision___lambda__3___closed__1);
l_Lake_GitRepo_branchExists___closed__1 = _init_l_Lake_GitRepo_branchExists___closed__1();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__1);
l_Lake_GitRepo_branchExists___closed__2 = _init_l_Lake_GitRepo_branchExists___closed__2();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__2);
l_Lake_GitRepo_branchExists___closed__3 = _init_l_Lake_GitRepo_branchExists___closed__3();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__3);
l_Lake_GitRepo_branchExists___closed__4 = _init_l_Lake_GitRepo_branchExists___closed__4();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__4);
l_Lake_GitRepo_revisionExists___closed__1 = _init_l_Lake_GitRepo_revisionExists___closed__1();
lean_mark_persistent(l_Lake_GitRepo_revisionExists___closed__1);
l_Lake_GitRepo_findTag_x3f___closed__1 = _init_l_Lake_GitRepo_findTag_x3f___closed__1();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__1);
l_Lake_GitRepo_findTag_x3f___closed__2 = _init_l_Lake_GitRepo_findTag_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__2);
l_Lake_GitRepo_findTag_x3f___closed__3 = _init_l_Lake_GitRepo_findTag_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__3);
l_Lake_GitRepo_findTag_x3f___closed__4 = _init_l_Lake_GitRepo_findTag_x3f___closed__4();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__4);
l_Lake_GitRepo_findTag_x3f___closed__5 = _init_l_Lake_GitRepo_findTag_x3f___closed__5();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__5);
l_Lake_GitRepo_findTag_x3f___closed__6 = _init_l_Lake_GitRepo_findTag_x3f___closed__6();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__6);
l_Lake_GitRepo_findTag_x3f___closed__7 = _init_l_Lake_GitRepo_findTag_x3f___closed__7();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__7);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__1();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__2 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__3 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__4 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__4();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__4);
l_Lake_GitRepo_hasNoDiff___closed__1 = _init_l_Lake_GitRepo_hasNoDiff___closed__1();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__1);
l_Lake_GitRepo_hasNoDiff___closed__2 = _init_l_Lake_GitRepo_hasNoDiff___closed__2();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__2);
l_Lake_GitRepo_hasNoDiff___closed__3 = _init_l_Lake_GitRepo_hasNoDiff___closed__3();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__3);
l_Lake_GitRepo_hasNoDiff___closed__4 = _init_l_Lake_GitRepo_hasNoDiff___closed__4();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
