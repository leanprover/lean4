// Lean compiler output
// Module: Leanpkg.Git
// Imports: Init Leanpkg.LeanVersion
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
lean_object* l_Leanpkg_gitdefaultRevision___boxed(lean_object*);
lean_object* l_Leanpkg_gitParseOriginRevision(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_gitParseRevision___closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Leanpkg_gitParseRevision(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_gitParseRevision___closed__6;
lean_object* l_Leanpkg_gitdefaultRevision_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_upstreamGitBranch___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Leanpkg_gitParseRevision___closed__2;
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Leanpkg_gitParseRevision___closed__3;
lean_object* l_Leanpkg_gitParseRevision___closed__1;
lean_object* l_Leanpkg_gitLatestOriginRevision___closed__2;
lean_object* l_Leanpkg_gitdefaultRevision_match__1(lean_object*);
lean_object* l_Leanpkg_gitLatestOriginRevision___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_gitLatestOriginRevision___closed__1;
lean_object* l_Leanpkg_gitRevisionExists___closed__1;
lean_object* l_Leanpkg_gitParseOriginRevision___closed__1;
lean_object* l_Leanpkg_gitParseRevision___closed__7;
lean_object* l_Leanpkg_upstreamGitBranch___closed__1;
lean_object* l_Leanpkg_gitParseOriginRevision___closed__3;
lean_object* l_Leanpkg_gitRevisionExists(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Leanpkg_leanVersionString___closed__3;
lean_object* l_Leanpkg_gitParseRevision___closed__8;
lean_object* l_IO_Process_run(lean_object*, lean_object*);
lean_object* l_Leanpkg_gitParseRevision___closed__4;
extern uint8_t l_Lean_version_isRelease;
lean_object* l_Leanpkg_gitParseOriginRevision___closed__2;
lean_object* l_Leanpkg_upstreamGitBranch___closed__3;
lean_object* l_Leanpkg_gitHeadRevision(lean_object*, lean_object*);
lean_object* l_Leanpkg_gitLatestOriginRevision(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Leanpkg_leanVersionStringCore;
lean_object* l_String_trim(lean_object*);
lean_object* l_Leanpkg_gitdefaultRevision(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Leanpkg_gitHeadRevision___closed__1;
lean_object* l_Leanpkg_gitParseRevision___closed__9;
lean_object* l_Leanpkg_upstreamGitBranch;
static lean_object* _init_l_Leanpkg_upstreamGitBranch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean-");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_upstreamGitBranch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_upstreamGitBranch___closed__1;
x_2 = l_Leanpkg_leanVersionStringCore;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_upstreamGitBranch___closed__3() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_version_isRelease;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Leanpkg_leanVersionString___closed__3;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Leanpkg_upstreamGitBranch___closed__2;
return x_3;
}
}
}
static lean_object* _init_l_Leanpkg_upstreamGitBranch() {
_start:
{
lean_object* x_1; 
x_1 = l_Leanpkg_upstreamGitBranch___closed__3;
return x_1;
}
}
lean_object* l_Leanpkg_gitdefaultRevision_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Leanpkg_gitdefaultRevision_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_gitdefaultRevision_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Leanpkg_gitdefaultRevision(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Leanpkg_upstreamGitBranch;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
lean_object* l_Leanpkg_gitdefaultRevision___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Leanpkg_gitdefaultRevision(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__1() {
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
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rev-parse");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_gitParseRevision___closed__2;
x_2 = l_Leanpkg_gitParseRevision___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-q");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_gitParseRevision___closed__4;
x_2 = l_Leanpkg_gitParseRevision___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("--verify");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_gitParseRevision___closed__6;
x_2 = l_Leanpkg_gitParseRevision___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_gitParseRevision___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("git");
return x_1;
}
}
lean_object* l_Leanpkg_gitParseRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Leanpkg_gitParseRevision___closed__8;
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Leanpkg_gitParseRevision___closed__1;
x_8 = l_Leanpkg_gitParseRevision___closed__9;
x_9 = l_Array_empty___closed__1;
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_9);
x_11 = l_IO_Process_run(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_String_trim(x_13);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_String_trim(x_15);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Leanpkg_gitHeadRevision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HEAD");
return x_1;
}
}
lean_object* l_Leanpkg_gitHeadRevision(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Leanpkg_gitHeadRevision___closed__1;
x_4 = l_Leanpkg_gitParseRevision(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Leanpkg_gitParseOriginRevision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("origin/");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_gitParseOriginRevision___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot find revision ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_gitParseOriginRevision___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" in repository ");
return x_1;
}
}
lean_object* l_Leanpkg_gitParseOriginRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = l_Leanpkg_gitParseOriginRevision___closed__1;
x_5 = lean_string_append(x_4, x_2);
x_6 = l_Leanpkg_gitParseOriginRevision___closed__2;
x_7 = lean_string_append(x_6, x_2);
x_8 = l_Leanpkg_gitParseOriginRevision___closed__3;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_1);
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_inc(x_1);
x_14 = l_Leanpkg_gitParseRevision(x_1, x_5, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Leanpkg_gitParseRevision(x_1, x_2, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_13);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Leanpkg_gitLatestOriginRevision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fetch");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_gitLatestOriginRevision___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l_Leanpkg_gitLatestOriginRevision___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Leanpkg_gitLatestOriginRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Leanpkg_gitParseRevision___closed__1;
x_6 = l_Leanpkg_gitParseRevision___closed__9;
x_7 = l_Leanpkg_gitLatestOriginRevision___closed__2;
x_8 = l_Array_empty___closed__1;
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_8);
x_10 = l_IO_Process_run(x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Leanpkg_gitdefaultRevision(x_2);
x_13 = l_Leanpkg_gitParseOriginRevision(x_1, x_12, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Leanpkg_gitLatestOriginRevision___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Leanpkg_gitLatestOriginRevision(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Leanpkg_gitRevisionExists___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("^{commit}");
return x_1;
}
}
lean_object* l_Leanpkg_gitRevisionExists(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Leanpkg_gitRevisionExists___closed__1;
x_5 = lean_string_append(x_2, x_4);
x_6 = l_Leanpkg_gitParseRevision(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = 1;
x_10 = lean_box(x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Leanpkg_LeanVersion(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Leanpkg_Git(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Leanpkg_LeanVersion(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Leanpkg_upstreamGitBranch___closed__1 = _init_l_Leanpkg_upstreamGitBranch___closed__1();
lean_mark_persistent(l_Leanpkg_upstreamGitBranch___closed__1);
l_Leanpkg_upstreamGitBranch___closed__2 = _init_l_Leanpkg_upstreamGitBranch___closed__2();
lean_mark_persistent(l_Leanpkg_upstreamGitBranch___closed__2);
l_Leanpkg_upstreamGitBranch___closed__3 = _init_l_Leanpkg_upstreamGitBranch___closed__3();
lean_mark_persistent(l_Leanpkg_upstreamGitBranch___closed__3);
l_Leanpkg_upstreamGitBranch = _init_l_Leanpkg_upstreamGitBranch();
lean_mark_persistent(l_Leanpkg_upstreamGitBranch);
l_Leanpkg_gitParseRevision___closed__1 = _init_l_Leanpkg_gitParseRevision___closed__1();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__1);
l_Leanpkg_gitParseRevision___closed__2 = _init_l_Leanpkg_gitParseRevision___closed__2();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__2);
l_Leanpkg_gitParseRevision___closed__3 = _init_l_Leanpkg_gitParseRevision___closed__3();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__3);
l_Leanpkg_gitParseRevision___closed__4 = _init_l_Leanpkg_gitParseRevision___closed__4();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__4);
l_Leanpkg_gitParseRevision___closed__5 = _init_l_Leanpkg_gitParseRevision___closed__5();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__5);
l_Leanpkg_gitParseRevision___closed__6 = _init_l_Leanpkg_gitParseRevision___closed__6();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__6);
l_Leanpkg_gitParseRevision___closed__7 = _init_l_Leanpkg_gitParseRevision___closed__7();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__7);
l_Leanpkg_gitParseRevision___closed__8 = _init_l_Leanpkg_gitParseRevision___closed__8();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__8);
l_Leanpkg_gitParseRevision___closed__9 = _init_l_Leanpkg_gitParseRevision___closed__9();
lean_mark_persistent(l_Leanpkg_gitParseRevision___closed__9);
l_Leanpkg_gitHeadRevision___closed__1 = _init_l_Leanpkg_gitHeadRevision___closed__1();
lean_mark_persistent(l_Leanpkg_gitHeadRevision___closed__1);
l_Leanpkg_gitParseOriginRevision___closed__1 = _init_l_Leanpkg_gitParseOriginRevision___closed__1();
lean_mark_persistent(l_Leanpkg_gitParseOriginRevision___closed__1);
l_Leanpkg_gitParseOriginRevision___closed__2 = _init_l_Leanpkg_gitParseOriginRevision___closed__2();
lean_mark_persistent(l_Leanpkg_gitParseOriginRevision___closed__2);
l_Leanpkg_gitParseOriginRevision___closed__3 = _init_l_Leanpkg_gitParseOriginRevision___closed__3();
lean_mark_persistent(l_Leanpkg_gitParseOriginRevision___closed__3);
l_Leanpkg_gitLatestOriginRevision___closed__1 = _init_l_Leanpkg_gitLatestOriginRevision___closed__1();
lean_mark_persistent(l_Leanpkg_gitLatestOriginRevision___closed__1);
l_Leanpkg_gitLatestOriginRevision___closed__2 = _init_l_Leanpkg_gitLatestOriginRevision___closed__2();
lean_mark_persistent(l_Leanpkg_gitLatestOriginRevision___closed__2);
l_Leanpkg_gitRevisionExists___closed__1 = _init_l_Leanpkg_gitRevisionExists___closed__1();
lean_mark_persistent(l_Leanpkg_gitRevisionExists___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
