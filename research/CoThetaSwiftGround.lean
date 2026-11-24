import PEqualNP.CoThetaWholeBase
namespace CoThetaWholeBase.CertifiedData
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 30000
set_option maxHeartbeats 0
def atom7 (i : Nat) : Sig := (if i < 3 then (if i < 1 then x0 else (if i < 2 then x1 else x2)) else (if i < 5 then (if i < 4 then x3 else x4) else (if i < 6 then x5 else x6)))
def w7 : Sig := neg x0
def w8 : Sig := neg x2
def w9 : Sig := neg x3
def w10 : Sig := bin false w9 x0
def w11 : Sig := bin true w9 x0
def w12 : Sig := bin false w9 x1
def w13 : Sig := bin true w9 x1
def w14 : Sig := bin false w9 x2
def w15 : Sig := bin true w9 x2
def w16 : Sig := bin false w9 x4
def w17 : Sig := bin true w9 x4
def w18 : Sig := bin false w9 x5
def w19 : Sig := bin true w9 x5
def w20 : Sig := bin false w9 x6
def w21 : Sig := bin true w9 x6
def w22 : Sig := bin false x0 x1
def w23 : Sig := bin true x0 x1
def w24 : Sig := bin false x0 x2
def w25 : Sig := bin true x0 x2
def w26 : Sig := bin false x0 x3
def w27 : Sig := bin true x0 x3
def w28 : Sig := bin false x0 x4
def w29 : Sig := bin true x0 x4
def w30 : Sig := bin false x0 x5
def w31 : Sig := bin true x0 x5
def w32 : Sig := bin false x0 x6
def w33 : Sig := bin true x0 x6
def w34 : Sig := bin false x1 x2
def w35 : Sig := bin true x1 x2
def w36 : Sig := bin false x1 x3
def w37 : Sig := bin true x1 x3
def w38 : Sig := bin false x1 x4
def w39 : Sig := bin true x1 x4
def w40 : Sig := bin false x1 x5
def w41 : Sig := bin true x1 x5
def w42 : Sig := bin false x1 x6
def w43 : Sig := bin true x1 x6
def w44 : Sig := bin false x2 x3
def w45 : Sig := bin true x2 x3
def w46 : Sig := bin false x2 x4
def w47 : Sig := bin true x2 x4
def w48 : Sig := bin false x2 x5
def w49 : Sig := bin true x2 x5
def w50 : Sig := bin false x2 x6
def w51 : Sig := bin true x2 x6
def w52 : Sig := bin false x3 x4
def w53 : Sig := bin true x3 x4
def w54 : Sig := bin false x3 x5
def w55 : Sig := bin true x3 x5
def w56 : Sig := bin false x3 x6
def w57 : Sig := bin true x3 x6
def w58 : Sig := bin false x4 x5
def w59 : Sig := bin true x4 x5
def w60 : Sig := bin false x4 x6
def w61 : Sig := bin true x4 x6
def w62 : Sig := bin false x5 x6
def w63 : Sig := bin true x5 x6
def w64 : Sig := bin false w8 x0
def w65 : Sig := bin true w8 x0
def w66 : Sig := bin false w8 x1
def w67 : Sig := bin true w8 x1
def w68 : Sig := bin false w8 x3
def w69 : Sig := bin true w8 x3
def w70 : Sig := bin false w8 x4
def w71 : Sig := bin true w8 x4
def w72 : Sig := bin false w8 x5
def w73 : Sig := bin true w8 x5
def w74 : Sig := bin false w8 x6
def w75 : Sig := bin true w8 x6
def w76 : Sig := bin false w7 x1
def w77 : Sig := bin true w7 x1
def w78 : Sig := bin false w7 x2
def w79 : Sig := bin true w7 x2
def w80 : Sig := bin false w7 x3
def w81 : Sig := bin true w7 x3
def w82 : Sig := bin false w7 x4
def w83 : Sig := bin true w7 x4
def w84 : Sig := bin false w7 x5
def w85 : Sig := bin true w7 x5
def w86 : Sig := bin false w7 x6
def w87 : Sig := bin true w7 x6
def w88 : Sig := neg x1
def w89 : Sig := neg x4
def w90 : Sig := neg x5
def w91 : Sig := neg x6
def w92 : Sig := bin false w91 w9
def w93 : Sig := bin true w91 w9
def w94 : Sig := bin false w91 x0
def w95 : Sig := bin true w91 x0
def w96 : Sig := bin false w91 x1
def w97 : Sig := bin true w91 x1
def w98 : Sig := bin false w91 x2
def w99 : Sig := bin true w91 x2
def w100 : Sig := bin false w91 x3
def w101 : Sig := bin true w91 x3
def w102 : Sig := bin false w91 x4
def w103 : Sig := bin true w91 x4
def w104 : Sig := bin false w91 x5
def w105 : Sig := bin true w91 x5
def w106 : Sig := bin false w91 w8
def w107 : Sig := bin true w91 w8
def w108 : Sig := bin false w91 w7
def w109 : Sig := bin true w91 w7
def w110 : Sig := bin false w90 w9
def w111 : Sig := bin true w90 w9
def w112 : Sig := bin false w90 x0
def w113 : Sig := bin true w90 x0
def w114 : Sig := bin false w90 x1
def w115 : Sig := bin true w90 x1
def w116 : Sig := bin false w90 x2
def w117 : Sig := bin true w90 x2
def w118 : Sig := bin false w90 x3
def w119 : Sig := bin true w90 x3
def w120 : Sig := bin false w90 x4
def w121 : Sig := bin true w90 x4
def w122 : Sig := bin false w90 x6
def w123 : Sig := bin true w90 x6
def w124 : Sig := bin false w90 w8
def w125 : Sig := bin true w90 w8
def w126 : Sig := bin false w90 w7
def w127 : Sig := bin true w90 w7
def w128 : Sig := bin false w89 w9
def w129 : Sig := bin true w89 w9
def w130 : Sig := bin false w89 x0
def w131 : Sig := bin true w89 x0
def w132 : Sig := bin false w89 x1
def w133 : Sig := bin true w89 x1
def w134 : Sig := bin false w89 x2
def w135 : Sig := bin true w89 x2
def w136 : Sig := bin false w89 x3
def w137 : Sig := bin true w89 x3
def w138 : Sig := bin false w89 x5
def w139 : Sig := bin true w89 x5
def w140 : Sig := bin false w89 x6
def w141 : Sig := bin true w89 x6
def w142 : Sig := bin false w89 w8
def w143 : Sig := bin true w89 w8
def w144 : Sig := bin false w89 w7
def w145 : Sig := bin true w89 w7
def w146 : Sig := bin false w10 x1
def w147 : Sig := bin true w10 x1
def w148 : Sig := bin false w10 x2
def w149 : Sig := bin true w10 x2
def w150 : Sig := bin false w10 x4
def w151 : Sig := bin true w10 x4
def w152 : Sig := bin false w10 x5
def w153 : Sig := bin true w10 x5
def w154 : Sig := bin false w10 x6
def w155 : Sig := bin true w10 x6
def w156 : Sig := bin true w12 x0
def w157 : Sig := bin false w12 x2
def w158 : Sig := bin true w12 x2
def w159 : Sig := bin false w12 x4
def w160 : Sig := bin true w12 x4
def w161 : Sig := bin false w12 x5
def w162 : Sig := bin true w12 x5
def w163 : Sig := bin false w12 x6
def w164 : Sig := bin true w12 x6
def w165 : Sig := bin true w14 x0
def w166 : Sig := bin true w14 x1
def w167 : Sig := bin false w14 x4
def w168 : Sig := bin true w14 x4
def w169 : Sig := bin false w14 x5
def w170 : Sig := bin true w14 x5
def w171 : Sig := bin false w14 x6
def w172 : Sig := bin true w14 x6
def w173 : Sig := bin true w16 x0
def w174 : Sig := bin true w16 x1
def w175 : Sig := bin true w16 x2
def w176 : Sig := bin false w16 x5
def w177 : Sig := bin true w16 x5
def w178 : Sig := bin false w16 x6
def w179 : Sig := bin true w16 x6
def w180 : Sig := bin true w18 x0
def w181 : Sig := bin true w18 x1
def w182 : Sig := bin true w18 x2
def w183 : Sig := bin true w18 x4
def w184 : Sig := bin false w18 x6
def w185 : Sig := bin true w18 x6
def w186 : Sig := bin true w20 x0
def w187 : Sig := bin true w20 x1
def w188 : Sig := bin true w20 x2
def w189 : Sig := bin true w20 x4
def w190 : Sig := bin true w20 x5
def w191 : Sig := bin false w9 w8
def w192 : Sig := bin true w9 w8
def w193 : Sig := bin false w9 w88
def w194 : Sig := bin true w9 w88
def w195 : Sig := bin false w88 x0
def w196 : Sig := bin true w88 x0
def w197 : Sig := bin false w88 x2
def w198 : Sig := bin true w88 x2
def w199 : Sig := bin false w88 x3
def w200 : Sig := bin true w88 x3
def w201 : Sig := bin false w88 x4
def w202 : Sig := bin true w88 x4
def w203 : Sig := bin false w88 x5
def w204 : Sig := bin true w88 x5
def w205 : Sig := bin false w88 x6
def w206 : Sig := bin true w88 x6
def w207 : Sig := bin false w9 w7
def w208 : Sig := bin true w9 w7
def w209 : Sig := bin true w9 w22
def w210 : Sig := bin false w22 x2
def w211 : Sig := bin true w22 x2
def w212 : Sig := bin false w22 x3
def w213 : Sig := bin true w22 x3
def w214 : Sig := bin false w22 x4
def w215 : Sig := bin true w22 x4
def w216 : Sig := bin false w22 x5
def w217 : Sig := bin true w22 x5
def w218 : Sig := bin false w22 x6
def w219 : Sig := bin true w22 x6
def w220 : Sig := bin true w9 w24
def w221 : Sig := bin true w24 x1
def w222 : Sig := bin false w24 x3
def w223 : Sig := bin true w24 x3
def w224 : Sig := bin false w24 x4
def w225 : Sig := bin true w24 x4
def w226 : Sig := bin false w24 x5
def w227 : Sig := bin true w24 x5
def w228 : Sig := bin false w24 x6
def w229 : Sig := bin true w24 x6
def w230 : Sig := bin true w26 x1
def w231 : Sig := bin true w26 x2
def w232 : Sig := bin false w26 x4
def w233 : Sig := bin true w26 x4
def w234 : Sig := bin false w26 x5
def w235 : Sig := bin true w26 x5
def w236 : Sig := bin false w26 x6
def w237 : Sig := bin true w26 x6
def w238 : Sig := bin true w9 w28
def w239 : Sig := bin true w28 x1
def w240 : Sig := bin true w28 x2
def w241 : Sig := bin true w28 x3
def w242 : Sig := bin false w28 x5
def w243 : Sig := bin true w28 x5
def w244 : Sig := bin false w28 x6
def w245 : Sig := bin true w28 x6
def w246 : Sig := bin true w9 w30
def w247 : Sig := bin true w30 x1
def w248 : Sig := bin true w30 x2
def w249 : Sig := bin true w30 x3
def w250 : Sig := bin true w30 x4
def w251 : Sig := bin false w30 x6
def w252 : Sig := bin true w30 x6
def w253 : Sig := bin true w9 w32
def w254 : Sig := bin true w32 x1
def w255 : Sig := bin true w32 x2
def w256 : Sig := bin true w32 x3
def w257 : Sig := bin true w32 x4
def w258 : Sig := bin true w32 x5
def w259 : Sig := bin false w11 x1
def w260 : Sig := bin true w11 x1
def w261 : Sig := bin false w11 x2
def w262 : Sig := bin true w11 x2
def w263 : Sig := bin false w11 x4
def w264 : Sig := bin true w11 x4
def w265 : Sig := bin false w11 x5
def w266 : Sig := bin true w11 x5
def w267 : Sig := bin false w11 x6
def w268 : Sig := bin true w11 x6
def w269 : Sig := bin true w9 w34
def w270 : Sig := bin true x0 w34
def w271 : Sig := bin false w34 x3
def w272 : Sig := bin true w34 x3
def w273 : Sig := bin false w34 x4
def w274 : Sig := bin true w34 x4
def w275 : Sig := bin false w34 x5
def w276 : Sig := bin true w34 x5
def w277 : Sig := bin false w34 x6
def w278 : Sig := bin true w34 x6
def w279 : Sig := bin true x0 w36
def w280 : Sig := bin true w36 x2
def w281 : Sig := bin false w36 x4
def w282 : Sig := bin true w36 x4
def w283 : Sig := bin false w36 x5
def w284 : Sig := bin true w36 x5
def w285 : Sig := bin false w36 x6
def w286 : Sig := bin true w36 x6
def w287 : Sig := bin true w9 w38
def w288 : Sig := bin true x0 w38
def w289 : Sig := bin true w38 x2
def w290 : Sig := bin true w38 x3
def w291 : Sig := bin false w38 x5
def w292 : Sig := bin true w38 x5
def w293 : Sig := bin false w38 x6
def w294 : Sig := bin true w38 x6
def w295 : Sig := bin true w9 w40
def w296 : Sig := bin true x0 w40
def w297 : Sig := bin true w40 x2
def w298 : Sig := bin true w40 x3
def w299 : Sig := bin true w40 x4
def w300 : Sig := bin false w40 x6
def w301 : Sig := bin true w40 x6
def w302 : Sig := bin true w9 w42
def w303 : Sig := bin true x0 w42
def w304 : Sig := bin true w42 x2
def w305 : Sig := bin true w42 x3
def w306 : Sig := bin true w42 x4
def w307 : Sig := bin true w42 x5
def w308 : Sig := bin false x0 w13
def w309 : Sig := bin false w13 x2
def w310 : Sig := bin true w13 x2
def w311 : Sig := bin false w13 x4
def w312 : Sig := bin true w13 x4
def w313 : Sig := bin false w13 x5
def w314 : Sig := bin true w13 x5
def w315 : Sig := bin false w13 x6
def w316 : Sig := bin true w13 x6
def w317 : Sig := bin false w9 w23
def w318 : Sig := bin false w23 x2
def w319 : Sig := bin true w23 x2
def w320 : Sig := bin false w23 x3
def w321 : Sig := bin true w23 x3
def w322 : Sig := bin false w23 x4
def w323 : Sig := bin true w23 x4
def w324 : Sig := bin false w23 x5
def w325 : Sig := bin true w23 x5
def w326 : Sig := bin false w23 x6
def w327 : Sig := bin true w23 x6
def w328 : Sig := bin true x0 w44
def w329 : Sig := bin true x1 w44
def w330 : Sig := bin false w44 x4
def w331 : Sig := bin true w44 x4
def w332 : Sig := bin false w44 x5
def w333 : Sig := bin true w44 x5
def w334 : Sig := bin false w44 x6
def w335 : Sig := bin true w44 x6
def w336 : Sig := bin true w9 w46
def w337 : Sig := bin true x0 w46
def w338 : Sig := bin true x1 w46
def w339 : Sig := bin true w46 x3
def w340 : Sig := bin false w46 x5
def w341 : Sig := bin true w46 x5
def w342 : Sig := bin false w46 x6
def w343 : Sig := bin true w46 x6
def w344 : Sig := bin true w9 w48
def w345 : Sig := bin true x0 w48
def w346 : Sig := bin true x1 w48
def w347 : Sig := bin true w48 x3
def w348 : Sig := bin true w48 x4
def w349 : Sig := bin false w48 x6
def w350 : Sig := bin true w48 x6
def w351 : Sig := bin true w9 w50
def w352 : Sig := bin true x0 w50
def w353 : Sig := bin true x1 w50
def w354 : Sig := bin true w50 x3
def w355 : Sig := bin true w50 x4
def w356 : Sig := bin true w50 x5
def w357 : Sig := bin false x0 w15
def w358 : Sig := bin false x1 w15
def w359 : Sig := bin false w15 x4
def w360 : Sig := bin true w15 x4
def w361 : Sig := bin false w15 x5
def w362 : Sig := bin true w15 x5
def w363 : Sig := bin false w15 x6
def w364 : Sig := bin true w15 x6
def w365 : Sig := bin false w9 w25
def w366 : Sig := bin false x1 w25
def w367 : Sig := bin false w25 x3
def w368 : Sig := bin true w25 x3
def w369 : Sig := bin false w25 x4
def w370 : Sig := bin true w25 x4
def w371 : Sig := bin false w25 x5
def w372 : Sig := bin true w25 x5
def w373 : Sig := bin false w25 x6
def w374 : Sig := bin true w25 x6
def w375 : Sig := bin false w9 w35
def w376 : Sig := bin false x0 w35
def w377 : Sig := bin false w35 x3
def w378 : Sig := bin true w35 x3
def w379 : Sig := bin false w35 x4
def w380 : Sig := bin true w35 x4
def w381 : Sig := bin false w35 x5
def w382 : Sig := bin true w35 x5
def w383 : Sig := bin false w35 x6
def w384 : Sig := bin true w35 x6
def w385 : Sig := bin true x0 w52
def w386 : Sig := bin true x1 w52
def w387 : Sig := bin true x2 w52
def w388 : Sig := bin false w52 x5
def w389 : Sig := bin true w52 x5
def w390 : Sig := bin false w52 x6
def w391 : Sig := bin true w52 x6
def w392 : Sig := bin true x0 w54
def w393 : Sig := bin true x1 w54
def w394 : Sig := bin true x2 w54
def w395 : Sig := bin true w54 x4
def w396 : Sig := bin false w54 x6
def w397 : Sig := bin true w54 x6
def w398 : Sig := bin true x0 w56
def w399 : Sig := bin true x1 w56
def w400 : Sig := bin true x2 w56
def w401 : Sig := bin true w56 x4
def w402 : Sig := bin true w56 x5
def w403 : Sig := bin false x1 w27
def w404 : Sig := bin false x2 w27
def w405 : Sig := bin false w27 x4
def w406 : Sig := bin true w27 x4
def w407 : Sig := bin false w27 x5
def w408 : Sig := bin true w27 x5
def w409 : Sig := bin false w27 x6
def w410 : Sig := bin true w27 x6
def w411 : Sig := bin false x0 w37
def w412 : Sig := bin false x2 w37
def w413 : Sig := bin false w37 x4
def w414 : Sig := bin true w37 x4
def w415 : Sig := bin false w37 x5
def w416 : Sig := bin true w37 x5
def w417 : Sig := bin false w37 x6
def w418 : Sig := bin true w37 x6
def w419 : Sig := bin false x0 w45
def w420 : Sig := bin false x1 w45
def w421 : Sig := bin false w45 x4
def w422 : Sig := bin true w45 x4
def w423 : Sig := bin false w45 x5
def w424 : Sig := bin true w45 x5
def w425 : Sig := bin false w45 x6
def w426 : Sig := bin true w45 x6
def w427 : Sig := bin true w9 w58
def w428 : Sig := bin true x0 w58
def w429 : Sig := bin true x1 w58
def w430 : Sig := bin true x2 w58
def w431 : Sig := bin true x3 w58
def w432 : Sig := bin false w58 x6
def w433 : Sig := bin true w58 x6
def w434 : Sig := bin true w9 w60
def w435 : Sig := bin true x0 w60
def w436 : Sig := bin true x1 w60
def w437 : Sig := bin true x2 w60
def w438 : Sig := bin true x3 w60
def w439 : Sig := bin true w60 x5
def w440 : Sig := bin false x0 w17
def w441 : Sig := bin false x1 w17
def w442 : Sig := bin false x2 w17
def w443 : Sig := bin false w17 x5
def w444 : Sig := bin true w17 x5
def w445 : Sig := bin false w17 x6
def w446 : Sig := bin true w17 x6
def w447 : Sig := bin false w9 w29
def w448 : Sig := bin false x1 w29
def w449 : Sig := bin false x2 w29
def w450 : Sig := bin false x3 w29
def w451 : Sig := bin false w29 x5
def w452 : Sig := bin true w29 x5
def w453 : Sig := bin false w29 x6
def w454 : Sig := bin true w29 x6
def w455 : Sig := bin false w9 w39
def w456 : Sig := bin false x0 w39
def w457 : Sig := bin false x2 w39
def w458 : Sig := bin false x3 w39
def w459 : Sig := bin false w39 x5
def w460 : Sig := bin true w39 x5
def w461 : Sig := bin false w39 x6
def w462 : Sig := bin true w39 x6
def w463 : Sig := bin false w9 w47
def w464 : Sig := bin false x0 w47
def w465 : Sig := bin false x1 w47
def w466 : Sig := bin false x3 w47
def w467 : Sig := bin false w47 x5
def w468 : Sig := bin true w47 x5
def w469 : Sig := bin false w47 x6
def w470 : Sig := bin true w47 x6
def w471 : Sig := bin false x0 w53
def w472 : Sig := bin false x1 w53
def w473 : Sig := bin false x2 w53
def w474 : Sig := bin false w53 x5
def w475 : Sig := bin true w53 x5
def w476 : Sig := bin false w53 x6
def w477 : Sig := bin true w53 x6
def w478 : Sig := bin true w9 w62
def w479 : Sig := bin true x0 w62
def w480 : Sig := bin true x1 w62
def w481 : Sig := bin true x2 w62
def w482 : Sig := bin true x3 w62
def w483 : Sig := bin true x4 w62
def w484 : Sig := bin false x0 w19
def w485 : Sig := bin false x1 w19
def w486 : Sig := bin false x2 w19
def w487 : Sig := bin false x4 w19
def w488 : Sig := bin false w19 x6
def w489 : Sig := bin true w19 x6
def w490 : Sig := bin false w9 w31
def w491 : Sig := bin false x1 w31
def w492 : Sig := bin false x2 w31
def w493 : Sig := bin false x3 w31
def w494 : Sig := bin false x4 w31
def w495 : Sig := bin false w31 x6
def w496 : Sig := bin true w31 x6
def w497 : Sig := bin false w9 w41
def w498 : Sig := bin false x0 w41
def w499 : Sig := bin false x2 w41
def w500 : Sig := bin false x3 w41
def w501 : Sig := bin false x4 w41
def w502 : Sig := bin false w41 x6
def w503 : Sig := bin true w41 x6
def w504 : Sig := bin false w9 w49
def w505 : Sig := bin false x0 w49
def w506 : Sig := bin false x1 w49
def w507 : Sig := bin false x3 w49
def w508 : Sig := bin false x4 w49
def w509 : Sig := bin false w49 x6
def w510 : Sig := bin true w49 x6
def w511 : Sig := bin false x0 w55
def w512 : Sig := bin false x1 w55
def w513 : Sig := bin false x2 w55
def w514 : Sig := bin false x4 w55
def w515 : Sig := bin false w55 x6
def w516 : Sig := bin true w55 x6
def w517 : Sig := bin false w9 w59
def w518 : Sig := bin false x0 w59
def w519 : Sig := bin false x1 w59
def w520 : Sig := bin false x2 w59
def w521 : Sig := bin false x3 w59
def w522 : Sig := bin false w59 x6
def w523 : Sig := bin true w59 x6
def w524 : Sig := bin false x0 w21
def w525 : Sig := bin false x1 w21
def w526 : Sig := bin false x2 w21
def w527 : Sig := bin false x4 w21
def w528 : Sig := bin false x5 w21
def w529 : Sig := bin false w9 w33
def w530 : Sig := bin false x1 w33
def w531 : Sig := bin false x2 w33
def w532 : Sig := bin false x3 w33
def w533 : Sig := bin false x4 w33
def w534 : Sig := bin false x5 w33
def w535 : Sig := bin false w9 w43
def w536 : Sig := bin false x0 w43
def w537 : Sig := bin false x2 w43
def w538 : Sig := bin false x3 w43
def w539 : Sig := bin false x4 w43
def w540 : Sig := bin false x5 w43
def w541 : Sig := bin false w9 w51
def w542 : Sig := bin false x0 w51
def w543 : Sig := bin false x1 w51
def w544 : Sig := bin false x3 w51
def w545 : Sig := bin false x4 w51
def w546 : Sig := bin false x5 w51
def w547 : Sig := bin false x0 w57
def w548 : Sig := bin false x1 w57
def w549 : Sig := bin false x2 w57
def w550 : Sig := bin false x4 w57
def w551 : Sig := bin false x5 w57
def w552 : Sig := bin false w9 w61
def w553 : Sig := bin false x0 w61
def w554 : Sig := bin false x1 w61
def w555 : Sig := bin false x2 w61
def w556 : Sig := bin false x3 w61
def w557 : Sig := bin false x5 w61
def w558 : Sig := bin false w9 w63
def w559 : Sig := bin false x0 w63
def w560 : Sig := bin false x1 w63
def w561 : Sig := bin false x2 w63
def w562 : Sig := bin false x3 w63
def w563 : Sig := bin false x4 w63
def w564 : Sig := bin false w64 x1
def w565 : Sig := bin true w64 x1
def w566 : Sig := bin false w64 x3
def w567 : Sig := bin true w64 x3
def w568 : Sig := bin false w64 x4
def w569 : Sig := bin true w64 x4
def w570 : Sig := bin false w64 x5
def w571 : Sig := bin true w64 x5
def w572 : Sig := bin false w64 x6
def w573 : Sig := bin true w64 x6
def w574 : Sig := bin true w66 x0
def w575 : Sig := bin false w66 x3
def w576 : Sig := bin true w66 x3
def w577 : Sig := bin false w66 x4
def w578 : Sig := bin true w66 x4
def w579 : Sig := bin false w66 x5
def w580 : Sig := bin true w66 x5
def w581 : Sig := bin false w66 x6
def w582 : Sig := bin true w66 x6
def w583 : Sig := bin true w68 x0
def w584 : Sig := bin true w68 x1
def w585 : Sig := bin false w68 x4
def w586 : Sig := bin true w68 x4
def w587 : Sig := bin false w68 x5
def w588 : Sig := bin true w68 x5
def w589 : Sig := bin false w68 x6
def w590 : Sig := bin true w68 x6
def w591 : Sig := bin true w70 x0
def w592 : Sig := bin true w70 x1
def w593 : Sig := bin true w70 x3
def w594 : Sig := bin false w70 x5
def w595 : Sig := bin true w70 x5
def w596 : Sig := bin false w70 x6
def w597 : Sig := bin true w70 x6
def w598 : Sig := bin true w72 x0
def w599 : Sig := bin true w72 x1
def w600 : Sig := bin true w72 x3
def w601 : Sig := bin true w72 x4
def w602 : Sig := bin false w72 x6
def w603 : Sig := bin true w72 x6
def w604 : Sig := bin true w74 x0
def w605 : Sig := bin true w74 x1
def w606 : Sig := bin true w74 x3
def w607 : Sig := bin true w74 x4
def w608 : Sig := bin true w74 x5
def w609 : Sig := bin false w8 w88
def w610 : Sig := bin true w8 w88
def w611 : Sig := bin false w8 w7
def w612 : Sig := bin true w8 w7
def w613 : Sig := bin true w8 w22
def w614 : Sig := bin true w8 w26
def w615 : Sig := bin true w8 w28
def w616 : Sig := bin true w8 w30
def w617 : Sig := bin true w8 w32
def w618 : Sig := bin false w65 x1
def w619 : Sig := bin true w65 x1
def w620 : Sig := bin false w65 x3
def w621 : Sig := bin true w65 x3
def w622 : Sig := bin false w65 x4
def w623 : Sig := bin true w65 x4
def w624 : Sig := bin false w65 x5
def w625 : Sig := bin true w65 x5
def w626 : Sig := bin false w65 x6
def w627 : Sig := bin true w65 x6
def w628 : Sig := bin true w8 w36
def w629 : Sig := bin true w8 w38
def w630 : Sig := bin true w8 w40
def w631 : Sig := bin true w8 w42
def w632 : Sig := bin false x0 w67
def w633 : Sig := bin false w67 x3
def w634 : Sig := bin true w67 x3
def w635 : Sig := bin false w67 x4
def w636 : Sig := bin true w67 x4
def w637 : Sig := bin false w67 x5
def w638 : Sig := bin true w67 x5
def w639 : Sig := bin false w67 x6
def w640 : Sig := bin true w67 x6
def w641 : Sig := bin false w8 w23
def w642 : Sig := bin true w8 w52
def w643 : Sig := bin true w8 w54
def w644 : Sig := bin true w8 w56
def w645 : Sig := bin false x0 w69
def w646 : Sig := bin false x1 w69
def w647 : Sig := bin false w69 x4
def w648 : Sig := bin true w69 x4
def w649 : Sig := bin false w69 x5
def w650 : Sig := bin true w69 x5
def w651 : Sig := bin false w69 x6
def w652 : Sig := bin true w69 x6
def w653 : Sig := bin false w8 w27
def w654 : Sig := bin false w8 w37
def w655 : Sig := bin true w8 w58
def w656 : Sig := bin true w8 w60
def w657 : Sig := bin false x0 w71
def w658 : Sig := bin false x1 w71
def w659 : Sig := bin false x3 w71
def w660 : Sig := bin false w71 x5
def w661 : Sig := bin true w71 x5
def w662 : Sig := bin false w71 x6
def w663 : Sig := bin true w71 x6
def w664 : Sig := bin false w8 w29
def w665 : Sig := bin false w8 w39
def w666 : Sig := bin false w8 w53
def w667 : Sig := bin true w8 w62
def w668 : Sig := bin false x0 w73
def w669 : Sig := bin false x1 w73
def w670 : Sig := bin false x3 w73
def w671 : Sig := bin false x4 w73
def w672 : Sig := bin false w73 x6
def w673 : Sig := bin true w73 x6
def w674 : Sig := bin false w8 w31
def w675 : Sig := bin false w8 w41
def w676 : Sig := bin false w8 w55
def w677 : Sig := bin false w8 w59
def w678 : Sig := bin false x0 w75
def w679 : Sig := bin false x1 w75
def w680 : Sig := bin false x3 w75
def w681 : Sig := bin false x4 w75
def w682 : Sig := bin false x5 w75
def w683 : Sig := bin false w8 w33
def w684 : Sig := bin false w8 w43
def w685 : Sig := bin false w8 w57
def w686 : Sig := bin false w8 w61
def w687 : Sig := bin false w8 w63
def w688 : Sig := bin false w88 w7
def w689 : Sig := bin true w88 w7
def w690 : Sig := bin false w76 x2
def w691 : Sig := bin true w76 x2
def w692 : Sig := bin false w76 x3
def w693 : Sig := bin true w76 x3
def w694 : Sig := bin false w76 x4
def w695 : Sig := bin true w76 x4
def w696 : Sig := bin false w76 x5
def w697 : Sig := bin true w76 x5
def w698 : Sig := bin false w76 x6
def w699 : Sig := bin true w76 x6
def w700 : Sig := bin true w78 x1
def w701 : Sig := bin false w78 x3
def w702 : Sig := bin true w78 x3
def w703 : Sig := bin false w78 x4
def w704 : Sig := bin true w78 x4
def w705 : Sig := bin false w78 x5
def w706 : Sig := bin true w78 x5
def w707 : Sig := bin false w78 x6
def w708 : Sig := bin true w78 x6
def w709 : Sig := bin true w80 x1
def w710 : Sig := bin true w80 x2
def w711 : Sig := bin false w80 x4
def w712 : Sig := bin true w80 x4
def w713 : Sig := bin false w80 x5
def w714 : Sig := bin true w80 x5
def w715 : Sig := bin false w80 x6
def w716 : Sig := bin true w80 x6
def w717 : Sig := bin true w82 x1
def w718 : Sig := bin true w82 x2
def w719 : Sig := bin true w82 x3
def w720 : Sig := bin false w82 x5
def w721 : Sig := bin true w82 x5
def w722 : Sig := bin false w82 x6
def w723 : Sig := bin true w82 x6
def w724 : Sig := bin true w84 x1
def w725 : Sig := bin true w84 x2
def w726 : Sig := bin true w84 x3
def w727 : Sig := bin true w84 x4
def w728 : Sig := bin false w84 x6
def w729 : Sig := bin true w84 x6
def w730 : Sig := bin true w86 x1
def w731 : Sig := bin true w86 x2
def w732 : Sig := bin true w86 x3
def w733 : Sig := bin true w86 x4
def w734 : Sig := bin true w86 x5
def w735 : Sig := bin true w7 w34
def w736 : Sig := bin true w7 w36
def w737 : Sig := bin true w7 w38
def w738 : Sig := bin true w7 w40
def w739 : Sig := bin true w7 w42
def w740 : Sig := bin false w77 x2
def w741 : Sig := bin true w77 x2
def w742 : Sig := bin false w77 x3
def w743 : Sig := bin true w77 x3
def w744 : Sig := bin false w77 x4
def w745 : Sig := bin true w77 x4
def w746 : Sig := bin false w77 x5
def w747 : Sig := bin true w77 x5
def w748 : Sig := bin false w77 x6
def w749 : Sig := bin true w77 x6
def w750 : Sig := bin true w7 w44
def w751 : Sig := bin true w7 w46
def w752 : Sig := bin true w7 w48
def w753 : Sig := bin true w7 w50
def w754 : Sig := bin false x1 w79
def w755 : Sig := bin false w79 x3
def w756 : Sig := bin true w79 x3
def w757 : Sig := bin false w79 x4
def w758 : Sig := bin true w79 x4
def w759 : Sig := bin false w79 x5
def w760 : Sig := bin true w79 x5
def w761 : Sig := bin false w79 x6
def w762 : Sig := bin true w79 x6
def w763 : Sig := bin false w7 w35
def w764 : Sig := bin true w7 w52
def w765 : Sig := bin true w7 w54
def w766 : Sig := bin true w7 w56
def w767 : Sig := bin false x1 w81
def w768 : Sig := bin false x2 w81
def w769 : Sig := bin false w81 x4
def w770 : Sig := bin true w81 x4
def w771 : Sig := bin false w81 x5
def w772 : Sig := bin true w81 x5
def w773 : Sig := bin false w81 x6
def w774 : Sig := bin true w81 x6
def w775 : Sig := bin false w7 w37
def w776 : Sig := bin false w7 w45
def w777 : Sig := bin true w7 w58
def w778 : Sig := bin true w7 w60
def w779 : Sig := bin false x1 w83
def w780 : Sig := bin false x2 w83
def w781 : Sig := bin false x3 w83
def w782 : Sig := bin false w83 x5
def w783 : Sig := bin true w83 x5
def w784 : Sig := bin false w83 x6
def w785 : Sig := bin true w83 x6
def w786 : Sig := bin false w7 w39
def w787 : Sig := bin false w7 w47
def w788 : Sig := bin false w7 w53
def w789 : Sig := bin true w7 w62
def w790 : Sig := bin false x1 w85
def w791 : Sig := bin false x2 w85
def w792 : Sig := bin false x3 w85
def w793 : Sig := bin false x4 w85
def w794 : Sig := bin false w85 x6
def w795 : Sig := bin true w85 x6
def w796 : Sig := bin false w7 w41
def w797 : Sig := bin false w7 w49
def w798 : Sig := bin false w7 w55
def w799 : Sig := bin false w7 w59
def w800 : Sig := bin false x1 w87
def w801 : Sig := bin false x2 w87
def w802 : Sig := bin false x3 w87
def w803 : Sig := bin false x4 w87
def w804 : Sig := bin false x5 w87
def w805 : Sig := bin false w7 w43
def w806 : Sig := bin false w7 w51
def w807 : Sig := bin false w7 w57
def w808 : Sig := bin false w7 w61
def w809 : Sig := bin false w7 w63
def w810 : Sig := neg w38
def w811 : Sig := neg w40
def w812 : Sig := neg w42
def w813 : Sig := neg w58
def w814 : Sig := neg w60
def w815 : Sig := neg w39
def w816 : Sig := neg w62
def w817 : Sig := neg w41
def w818 : Sig := neg w59
def w819 : Sig := neg w43
def w820 : Sig := neg w61
def w821 : Sig := neg w63
def w881 : Sig := bin true w108 x5
def w908 : Sig := bin true w98 x5
def w915 : Sig := bin true w100 x5
def w966 : Sig := bin true w817 x6
def w1003 : Sig := bin true w116 x6
def w1016 : Sig := bin true w120 x6
def w1022 : Sig := bin false w816 x0
def w1024 : Sig := bin false w816 x1
def w1026 : Sig := bin false w816 x2
def w1028 : Sig := bin false w816 x3
def w1030 : Sig := bin false w816 x4
def w1067 : Sig := bin true w144 x3
def w1094 : Sig := bin true w134 x3
def w1109 : Sig := bin true w138 x3
def w1131 : Sig := bin false w813 x2
def w1152 : Sig := bin true w193 x4
def w1175 : Sig := bin true w148 x1
def w1177 : Sig := bin true w148 x4
def w1179 : Sig := bin true w148 x5
def w1181 : Sig := bin true w148 x6
def w1187 : Sig := bin true w150 x6
def w1188 : Sig := bin true w152 x1
def w1189 : Sig := bin true w152 x2
def w1190 : Sig := bin true w152 x4
def w1192 : Sig := bin true w152 x6
def w1195 : Sig := bin true w154 x4
def w1199 : Sig := bin true w157 x0
def w1201 : Sig := bin true w157 x4
def w1203 : Sig := bin true w157 x5
def w1205 : Sig := bin true w157 x6
def w1206 : Sig := bin true w159 x0
def w1207 : Sig := bin true w159 x2
def w1209 : Sig := bin true w159 x5
def w1211 : Sig := bin true w159 x6
def w1217 : Sig := bin true w163 x0
def w1218 : Sig := bin true w163 x2
def w1219 : Sig := bin true w163 x4
def w1220 : Sig := bin true w163 x5
def w1237 : Sig := bin true w169 x4
def w1242 : Sig := bin true w171 x4
def w1262 : Sig := bin true w176 x2
def w1293 : Sig := bin true w184 x0
def w1294 : Sig := bin true w184 x1
def w1295 : Sig := bin true w184 x2
def w1296 : Sig := bin true w184 x4
def w1349 : Sig := bin true w541 x4
def w1368 : Sig := bin true w309 x4
def w1370 : Sig := bin true w318 x3
def w1371 : Sig := bin true w318 x4
def w1372 : Sig := bin true w318 x5
def w1373 : Sig := bin true w318 x6
def w1374 : Sig := bin true x1 w450
def w1375 : Sig := bin true x2 w450
def w1376 : Sig := bin true w450 x5
def w1377 : Sig := bin true w450 x6
def w1378 : Sig := bin true x0 w413
def w1379 : Sig := bin true x2 w413
def w1380 : Sig := bin true w413 x5
def w1381 : Sig := bin true w413 x6
def w1383 : Sig := bin true x1 w534
def w1384 : Sig := bin true x2 w534
def w1385 : Sig := bin true x3 w534
def w1386 : Sig := bin true x4 w534
def w1388 : Sig := bin true x0 w502
def w1389 : Sig := bin true x2 w502
def w1390 : Sig := bin true x3 w502
def w1391 : Sig := bin true x4 w502
def w1450 : Sig := bin false w93 x2
def w1466 : Sig := bin false w129 x0
def w1468 : Sig := bin false w129 x1
def w1470 : Sig := bin false w129 x2
def w1472 : Sig := bin false w129 x5
def w1474 : Sig := bin false w129 x6
def w1504 : Sig := bin true w566 x1
def w1506 : Sig := bin true w566 x4
def w1508 : Sig := bin true w566 x5
def w1510 : Sig := bin true w566 x6
def w1516 : Sig := bin true w568 x6
def w1517 : Sig := bin true w570 x1
def w1518 : Sig := bin true w570 x3
def w1519 : Sig := bin true w570 x4
def w1521 : Sig := bin true w570 x6
def w1524 : Sig := bin true w572 x4
def w1532 : Sig := bin true w575 x5
def w1535 : Sig := bin true w577 x0
def w1536 : Sig := bin true w577 x3
def w1538 : Sig := bin true w577 x5
def w1540 : Sig := bin true w577 x6
def w1542 : Sig := bin true w579 x3
def w1546 : Sig := bin true w581 x0
def w1547 : Sig := bin true w581 x3
def w1548 : Sig := bin true w581 x4
def w1549 : Sig := bin true w581 x5
def w1560 : Sig := bin true w585 x0
def w1561 : Sig := bin true w585 x1
def w1563 : Sig := bin true w585 x5
def w1565 : Sig := bin true w585 x6
def w1567 : Sig := bin true w587 x1
def w1596 : Sig := bin true w596 x0
def w1624 : Sig := bin true w602 x0
def w1625 : Sig := bin true w602 x1
def w1626 : Sig := bin true w602 x3
def w1627 : Sig := bin true w602 x4
def w1799 : Sig := bin true w688 x2
def w1813 : Sig := bin true w195 x4
def w1817 : Sig := bin true w195 x6
def w1828 : Sig := bin true w199 x2
def w1843 : Sig := bin true w203 x2
def w1853 : Sig := bin false w812 x0
def w1855 : Sig := bin false w812 x2
def w1857 : Sig := bin false w812 x3
def w1859 : Sig := bin false w812 x4
def w1861 : Sig := bin false w812 x5
def w1867 : Sig := bin false w811 x3
def w1873 : Sig := bin false w810 x0
def w1875 : Sig := bin false w810 x2
def w1877 : Sig := bin false w810 x3
def w1879 : Sig := bin false w810 x5
def w1881 : Sig := bin false w810 x6
def w1889 : Sig := bin false w194 x5
def w1893 : Sig := bin false w610 x0
def w1895 : Sig := bin false w610 x3
def w1897 : Sig := bin false w610 x4
def w1899 : Sig := bin false w610 x5
def w1901 : Sig := bin false w610 x6
def w1904 : Sig := bin true w690 x3
def w1906 : Sig := bin true w690 x4
def w1908 : Sig := bin true w690 x5
def w1910 : Sig := bin true w690 x6
def w1915 : Sig := bin true w692 x5
def w1918 : Sig := bin true w694 x2
def w1919 : Sig := bin true w694 x3
def w1921 : Sig := bin true w694 x5
def w1923 : Sig := bin true w694 x6
def w1925 : Sig := bin true w696 x3
def w1929 : Sig := bin true w698 x2
def w1930 : Sig := bin true w698 x3
def w1931 : Sig := bin true w698 x4
def w1932 : Sig := bin true w698 x5
def w1965 : Sig := bin true w711 x1
def w1966 : Sig := bin true w711 x2
def w1968 : Sig := bin true w711 x5
def w1970 : Sig := bin true w711 x6
def w1977 : Sig := bin true w715 x2
def w1997 : Sig := bin true w720 x2
def w2002 : Sig := bin true w722 x2
def w2029 : Sig := bin true w728 x1
def w2030 : Sig := bin true w728 x2
def w2031 : Sig := bin true w728 x3
def w2032 : Sig := bin true w728 x4
def w2091 : Sig := bin true w808 x2
def w2105 : Sig := bin true x0 w554
def w2106 : Sig := bin true w554 x2
def w2107 : Sig := bin true w554 x3
def w2108 : Sig := bin true w554 x5
def w2109 : Sig := bin true w744 x2
def w2110 : Sig := bin true w748 x2
def w2115 : Sig := bin false x1 w470
def w2170 : Sig := bin false w109 x4
def w2174 : Sig := bin false w127 x1
def w2176 : Sig := bin false w127 x2
def w2178 : Sig := bin false w127 x3
def w2180 : Sig := bin false w127 x4
def w2182 : Sig := bin false w127 x6
def w2192 : Sig := bin false w145 x6
def w2194 : Sig := bin false w208 x1
def w2196 : Sig := bin false w208 x2
def w2198 : Sig := bin false w208 x4
def w2200 : Sig := bin false w208 x5
def w2202 : Sig := bin false w208 x6
def w2204 : Sig := bin false w612 x1
def w2206 : Sig := bin false w612 x3
def w2208 : Sig := bin false w612 x4
def w2210 : Sig := bin false w612 x5
def w2212 : Sig := bin false w612 x6
def w2225 : Sig := bin true w210 x3
def w2227 : Sig := bin true w210 x4
def w2229 : Sig := bin true w210 x5
def w2231 : Sig := bin true w210 x6
def w2232 : Sig := bin true w212 x2
def w2234 : Sig := bin true w212 x4
def w2236 : Sig := bin true w212 x5
def w2238 : Sig := bin true w212 x6
def w2239 : Sig := bin true w214 x2
def w2240 : Sig := bin true w214 x3
def w2242 : Sig := bin true w214 x5
def w2244 : Sig := bin true w214 x6
def w2245 : Sig := bin true w216 x2
def w2246 : Sig := bin true w216 x3
def w2247 : Sig := bin true w216 x4
def w2249 : Sig := bin true w216 x6
def w2250 : Sig := bin true w218 x2
def w2251 : Sig := bin true w218 x3
def w2252 : Sig := bin true w218 x4
def w2253 : Sig := bin true w218 x5
def w2302 : Sig := bin true w222 x1
def w2304 : Sig := bin true w222 x4
def w2306 : Sig := bin true w222 x5
def w2308 : Sig := bin true w222 x6
def w2309 : Sig := bin true w224 x1
def w2310 : Sig := bin true w224 x3
def w2312 : Sig := bin true w224 x5
def w2314 : Sig := bin true w224 x6
def w2315 : Sig := bin true w226 x1
def w2316 : Sig := bin true w226 x3
def w2317 : Sig := bin true w226 x4
def w2319 : Sig := bin true w226 x6
def w2320 : Sig := bin true w228 x1
def w2321 : Sig := bin true w228 x3
def w2322 : Sig := bin true w228 x4
def w2323 : Sig := bin true w228 x5
def w2334 : Sig := bin true w261 x4
def w2351 : Sig := bin true w232 x1
def w2352 : Sig := bin true w232 x2
def w2354 : Sig := bin true w232 x5
def w2356 : Sig := bin true w232 x6
def w2357 : Sig := bin true w234 x1
def w2358 : Sig := bin true w234 x2
def w2359 : Sig := bin true w234 x4
def w2361 : Sig := bin true w234 x6
def w2362 : Sig := bin true w236 x1
def w2363 : Sig := bin true w236 x2
def w2364 : Sig := bin true w236 x4
def w2365 : Sig := bin true w236 x5
def w2383 : Sig := bin true w419 x1
def w2385 : Sig := bin true w419 x4
def w2387 : Sig := bin true w419 x5
def w2389 : Sig := bin true w419 x6
def w2390 : Sig := bin true w242 x1
def w2391 : Sig := bin true w242 x2
def w2392 : Sig := bin true w242 x3
def w2394 : Sig := bin true w242 x6
def w2430 : Sig := bin true w464 x6
def w2438 : Sig := bin true w471 x6
def w2439 : Sig := bin true w251 x1
def w2440 : Sig := bin true w251 x2
def w2441 : Sig := bin true w251 x3
def w2442 : Sig := bin true w251 x4
def w2468 : Sig := bin true w505 x1
def w2470 : Sig := bin true w505 x3
def w2472 : Sig := bin true w505 x4
def w2474 : Sig := bin true w505 x6
def w2476 : Sig := bin true w511 x1
def w2478 : Sig := bin true w511 x2
def w2480 : Sig := bin true w511 x4
def w2482 : Sig := bin true w511 x6
def w2490 : Sig := bin true w518 x6
def w2520 : Sig := bin true w542 x4
def w2528 : Sig := bin true w547 x4
def w2546 : Sig := bin true w559 x4
def w2549 : Sig := bin false w95 x2
def w2569 : Sig := bin false w131 x2
def w2633 : Sig := bin true w267 x4
def w2736 : Sig := bin false w196 x3
def w2740 : Sig := bin false w196 x5
def w2744 : Sig := bin true x0 w271
def w2746 : Sig := bin true w271 x4
def w2748 : Sig := bin true w271 x5
def w2750 : Sig := bin true w271 x6
def w2751 : Sig := bin true x0 w273
def w2752 : Sig := bin true w273 x3
def w2754 : Sig := bin true w273 x5
def w2756 : Sig := bin true w273 x6
def w2757 : Sig := bin true x0 w275
def w2758 : Sig := bin true w275 x3
def w2759 : Sig := bin true w275 x4
def w2761 : Sig := bin true w275 x6
def w2762 : Sig := bin true x0 w277
def w2763 : Sig := bin true w277 x3
def w2764 : Sig := bin true w277 x4
def w2765 : Sig := bin true w277 x5
def w2784 : Sig := bin true w754 x3
def w2788 : Sig := bin true w754 x5
def w2799 : Sig := bin true x0 w281
def w2800 : Sig := bin true w281 x2
def w2802 : Sig := bin true w281 x5
def w2804 : Sig := bin true w281 x6
def w2810 : Sig := bin true x0 w285
def w2811 : Sig := bin true w285 x2
def w2812 : Sig := bin true w285 x4
def w2813 : Sig := bin true w285 x5
def w2826 : Sig := bin true w767 x5
def w2841 : Sig := bin true w420 x5
def w2844 : Sig := bin true x0 w291
def w2845 : Sig := bin true w291 x2
def w2846 : Sig := bin true w291 x3
def w2848 : Sig := bin true w291 x6
def w2849 : Sig := bin true x0 w293
def w2850 : Sig := bin true w293 x2
def w2851 : Sig := bin true w293 x3
def w2852 : Sig := bin true w293 x5
def w2870 : Sig := bin true w779 x3
def w2872 : Sig := bin true w779 x5
def w2883 : Sig := bin true x0 w465
def w2885 : Sig := bin true w465 x3
def w2887 : Sig := bin true w465 x5
def w2889 : Sig := bin true w465 x6
def w2894 : Sig := bin true w472 x5
def w2897 : Sig := bin true x0 w300
def w2898 : Sig := bin true w300 x2
def w2899 : Sig := bin true w300 x3
def w2900 : Sig := bin true w300 x4
def w2918 : Sig := bin true w790 x3
def w2933 : Sig := bin true w506 x3
def w2949 : Sig := bin true w519 x3
def w2969 : Sig := bin true w800 x3
def w2973 : Sig := bin true w800 x5
def w2982 : Sig := bin true x0 w543
def w2984 : Sig := bin true w543 x3
def w2986 : Sig := bin true w543 x4
def w2988 : Sig := bin true w543 x5
def w2995 : Sig := bin true w548 x5
def w3003 : Sig := bin true w560 x3
def w3016 : Sig := bin false w115 x2
def w3033 : Sig := bin false w147 x2
def w3086 : Sig := bin true w315 x4
def w3215 : Sig := bin false w709 x4
def w3256 : Sig := bin false w724 x6
def w3299 : Sig := bin true w320 x5
def w3323 : Sig := bin true w322 x6
def w3341 : Sig := bin true w324 x3
def w3363 : Sig := bin true w326 x4
def w3389 : Sig := bin false w260 x2
def w3405 : Sig := bin true x0 w330
def w3406 : Sig := bin true x1 w330
def w3408 : Sig := bin true w330 x5
def w3410 : Sig := bin true w330 x6
def w3483 : Sig := bin true x0 w349
def w3484 : Sig := bin true x1 w349
def w3485 : Sig := bin true w349 x3
def w3486 : Sig := bin true w349 x4
def w3954 : Sig := bin false w741 x4
def w3958 : Sig := bin false w741 x6
def w3968 : Sig := bin true x0 w388
def w3969 : Sig := bin true x1 w388
def w3970 : Sig := bin true x2 w388
def w3972 : Sig := bin true w388 x6
def w3973 : Sig := bin true x0 w390
def w3974 : Sig := bin true x1 w390
def w3975 : Sig := bin true x2 w390
def w3976 : Sig := bin true w390 x5
def w3994 : Sig := bin true w458 x5
def w4003 : Sig := bin true x0 w396
def w4004 : Sig := bin true x1 w396
def w4005 : Sig := bin true x2 w396
def w4006 : Sig := bin true w396 x4
def w4055 : Sig := bin true x2 w532
def w4074 : Sig := bin true x2 w556
def w4085 : Sig := bin false w101 x4
def w4111 : Sig := bin false w576 x4
def w4191 : Sig := bin true x2 w769
def w4226 : Sig := bin true x2 w773
def w4263 : Sig := bin true w405 x6
def w4317 : Sig := bin false w621 x4
def w4364 : Sig := bin true x2 w417
def w4382 : Sig := bin false w634 x4
def w4389 : Sig := bin false w743 x4
def w4393 : Sig := bin false w743 x6
def w4394 : Sig := bin false x2 w321
def w4395 : Sig := bin false w321 x4
def w4465 : Sig := bin false w378 x4
def w4470 : Sig := bin true x0 w432
def w4471 : Sig := bin true x1 w432
def w4472 : Sig := bin true x2 w432
def w4473 : Sig := bin true x3 w432
def w4485 : Sig := bin true x2 w793
def w4495 : Sig := bin true x2 w501
def w4506 : Sig := bin true x2 w514
def w4557 : Sig := bin false x3 w121
def w4613 : Sig := bin false x3 w569
def w4742 : Sig := bin true x2 w451
def w4784 : Sig := bin false x3 w623
def w4838 : Sig := bin false x2 w312
def w4844 : Sig := bin false x3 w636
def w4852 : Sig := bin false w745 x6
def w4853 : Sig := bin false x2 w323
def w4854 : Sig := bin false x3 w323
def w4906 : Sig := bin false x3 w370
def w4989 : Sig := bin true x3 w540
def w5001 : Sig := bin true x2 w557
def w5012 : Sig := bin false w139 x6
def w5037 : Sig := bin true x4 w488
def w5054 : Sig := bin false w580 x6
def w5105 : Sig := bin true x2 w794
def w5139 : Sig := bin true x4 w495
def w5160 : Sig := bin false w625 x6
def w5189 : Sig := bin false x2 w314
def w5191 : Sig := bin false w314 x6
def w5196 : Sig := bin false w638 x6
def w5200 : Sig := bin false x4 w747
def w5201 : Sig := bin false w747 x6
def w5203 : Sig := bin false x2 w325
def w5206 : Sig := bin false w325 x6
def w5250 : Sig := bin false w382 x6
def w5259 : Sig := bin true x2 w515
def w5272 : Sig := bin false x4 w650
def w5273 : Sig := bin false w650 x6
def w5287 : Sig := bin false x4 w416
def w5288 : Sig := bin false w416 x6
def w5290 : Sig := bin false x0 w424
def w5314 : Sig := bin false x3 w661
def w5315 : Sig := bin false w661 x6
def w5324 : Sig := bin false x3 w452
def w5330 : Sig := bin false w460 x6
def w5355 : Sig := bin false x5 w155
def w5375 : Sig := bin false x5 w573
def w5440 : Sig := bin false x5 w268
def w5444 : Sig := bin false x5 w627
def w5462 : Sig := bin false x2 w316
def w5464 : Sig := bin false x5 w316
def w5468 : Sig := bin false x5 w640
def w5471 : Sig := bin false x4 w749
def w5473 : Sig := bin false x2 w327
def w5476 : Sig := bin false x5 w327
def w5490 : Sig := bin false x1 w364
def w5492 : Sig := bin false x5 w364
def w5500 : Sig := bin false x5 w374
def w5515 : Sig := bin false x4 w652
def w5516 : Sig := bin false x5 w652
def w5524 : Sig := bin false x5 w410
def w5527 : Sig := bin false x4 w418
def w5540 : Sig := bin false x5 w446
def w5543 : Sig := bin false x3 w663
def w5544 : Sig := bin false x5 w663
def w5545 : Sig := bin false x1 w785
def w5551 : Sig := bin false x3 w454
def w5552 : Sig := bin false x5 w454
def w5668 : Sig := bin true w26 w413
def w5669 : Sig := bin true w30 w502
def w5670 : Sig := bin true w5290 x1
def w5681 : Sig := bin true x0 w2115
def s (i : Nat) : Sig := (if i < 626 then (if i < 313 then (if i < 156 then (if i < 78 then (if i < 39 then (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then x0 else x1) else (if i < 3 then x2 else x3)) else (if i < 6 then (if i < 5 then x4 else x5) else (if i < 7 then x6 else (if i < 8 then w7 else w8)))) else (if i < 14 then (if i < 11 then (if i < 10 then w9 else w10) else (if i < 12 then w11 else (if i < 13 then w12 else w13))) else (if i < 16 then (if i < 15 then w14 else w15) else (if i < 17 then w16 else (if i < 18 then w17 else w18))))) else (if i < 29 then (if i < 24 then (if i < 21 then (if i < 20 then w19 else w20) else (if i < 22 then w21 else (if i < 23 then w22 else w23))) else (if i < 26 then (if i < 25 then w24 else w25) else (if i < 27 then w26 else (if i < 28 then w27 else w28)))) else (if i < 34 then (if i < 31 then (if i < 30 then w29 else w30) else (if i < 32 then w31 else (if i < 33 then w32 else w33))) else (if i < 36 then (if i < 35 then w34 else w35) else (if i < 37 then w36 else (if i < 38 then w37 else w38)))))) else (if i < 58 then (if i < 48 then (if i < 43 then (if i < 41 then (if i < 40 then w39 else w40) else (if i < 42 then w41 else w42)) else (if i < 45 then (if i < 44 then w43 else w44) else (if i < 46 then w45 else (if i < 47 then w46 else w47)))) else (if i < 53 then (if i < 50 then (if i < 49 then w48 else w49) else (if i < 51 then w50 else (if i < 52 then w51 else w52))) else (if i < 55 then (if i < 54 then w53 else w54) else (if i < 56 then w55 else (if i < 57 then w56 else w57))))) else (if i < 68 then (if i < 63 then (if i < 60 then (if i < 59 then w58 else w59) else (if i < 61 then w60 else (if i < 62 then w61 else w62))) else (if i < 65 then (if i < 64 then w63 else w64) else (if i < 66 then w65 else (if i < 67 then w66 else w67)))) else (if i < 73 then (if i < 70 then (if i < 69 then w68 else w69) else (if i < 71 then w70 else (if i < 72 then w71 else w72))) else (if i < 75 then (if i < 74 then w73 else w74) else (if i < 76 then w75 else (if i < 77 then w76 else w77))))))) else (if i < 117 then (if i < 97 then (if i < 87 then (if i < 82 then (if i < 80 then (if i < 79 then w78 else w79) else (if i < 81 then w80 else w81)) else (if i < 84 then (if i < 83 then w82 else w83) else (if i < 85 then w84 else (if i < 86 then w85 else w86)))) else (if i < 92 then (if i < 89 then (if i < 88 then w87 else w88) else (if i < 90 then w89 else (if i < 91 then w90 else w91))) else (if i < 94 then (if i < 93 then w92 else w93) else (if i < 95 then w94 else (if i < 96 then w95 else w96))))) else (if i < 107 then (if i < 102 then (if i < 99 then (if i < 98 then w97 else w98) else (if i < 100 then w99 else (if i < 101 then w100 else w101))) else (if i < 104 then (if i < 103 then w102 else w103) else (if i < 105 then w104 else (if i < 106 then w105 else w106)))) else (if i < 112 then (if i < 109 then (if i < 108 then w107 else w108) else (if i < 110 then w109 else (if i < 111 then w110 else w111))) else (if i < 114 then (if i < 113 then w112 else w113) else (if i < 115 then w114 else (if i < 116 then w115 else w116)))))) else (if i < 136 then (if i < 126 then (if i < 121 then (if i < 119 then (if i < 118 then w117 else w118) else (if i < 120 then w119 else w120)) else (if i < 123 then (if i < 122 then w121 else w122) else (if i < 124 then w123 else (if i < 125 then w124 else w125)))) else (if i < 131 then (if i < 128 then (if i < 127 then w126 else w127) else (if i < 129 then w128 else (if i < 130 then w129 else w130))) else (if i < 133 then (if i < 132 then w131 else w132) else (if i < 134 then w133 else (if i < 135 then w134 else w135))))) else (if i < 146 then (if i < 141 then (if i < 138 then (if i < 137 then w136 else w137) else (if i < 139 then w138 else (if i < 140 then w139 else w140))) else (if i < 143 then (if i < 142 then w141 else w142) else (if i < 144 then w143 else (if i < 145 then w144 else w145)))) else (if i < 151 then (if i < 148 then (if i < 147 then w146 else w147) else (if i < 149 then w148 else (if i < 150 then w149 else w150))) else (if i < 153 then (if i < 152 then w151 else w152) else (if i < 154 then w153 else (if i < 155 then w154 else w155)))))))) else (if i < 234 then (if i < 195 then (if i < 175 then (if i < 165 then (if i < 160 then (if i < 158 then (if i < 157 then w156 else w157) else (if i < 159 then w158 else w159)) else (if i < 162 then (if i < 161 then w160 else w161) else (if i < 163 then w162 else (if i < 164 then w163 else w164)))) else (if i < 170 then (if i < 167 then (if i < 166 then w165 else w166) else (if i < 168 then w167 else (if i < 169 then w168 else w169))) else (if i < 172 then (if i < 171 then w170 else w171) else (if i < 173 then w172 else (if i < 174 then w173 else w174))))) else (if i < 185 then (if i < 180 then (if i < 177 then (if i < 176 then w175 else w176) else (if i < 178 then w177 else (if i < 179 then w178 else w179))) else (if i < 182 then (if i < 181 then w180 else w181) else (if i < 183 then w182 else (if i < 184 then w183 else w184)))) else (if i < 190 then (if i < 187 then (if i < 186 then w185 else w186) else (if i < 188 then w187 else (if i < 189 then w188 else w189))) else (if i < 192 then (if i < 191 then w190 else w191) else (if i < 193 then w192 else (if i < 194 then w193 else w194)))))) else (if i < 214 then (if i < 204 then (if i < 199 then (if i < 197 then (if i < 196 then w195 else w196) else (if i < 198 then w197 else w198)) else (if i < 201 then (if i < 200 then w199 else w200) else (if i < 202 then w201 else (if i < 203 then w202 else w203)))) else (if i < 209 then (if i < 206 then (if i < 205 then w204 else w205) else (if i < 207 then w206 else (if i < 208 then w207 else w208))) else (if i < 211 then (if i < 210 then w209 else w210) else (if i < 212 then w211 else (if i < 213 then w212 else w213))))) else (if i < 224 then (if i < 219 then (if i < 216 then (if i < 215 then w214 else w215) else (if i < 217 then w216 else (if i < 218 then w217 else w218))) else (if i < 221 then (if i < 220 then w219 else w220) else (if i < 222 then w221 else (if i < 223 then w222 else w223)))) else (if i < 229 then (if i < 226 then (if i < 225 then w224 else w225) else (if i < 227 then w226 else (if i < 228 then w227 else w228))) else (if i < 231 then (if i < 230 then w229 else w230) else (if i < 232 then w231 else (if i < 233 then w232 else w233))))))) else (if i < 273 then (if i < 253 then (if i < 243 then (if i < 238 then (if i < 236 then (if i < 235 then w234 else w235) else (if i < 237 then w236 else w237)) else (if i < 240 then (if i < 239 then w238 else w239) else (if i < 241 then w240 else (if i < 242 then w241 else w242)))) else (if i < 248 then (if i < 245 then (if i < 244 then w243 else w244) else (if i < 246 then w245 else (if i < 247 then w246 else w247))) else (if i < 250 then (if i < 249 then w248 else w249) else (if i < 251 then w250 else (if i < 252 then w251 else w252))))) else (if i < 263 then (if i < 258 then (if i < 255 then (if i < 254 then w253 else w254) else (if i < 256 then w255 else (if i < 257 then w256 else w257))) else (if i < 260 then (if i < 259 then w258 else w259) else (if i < 261 then w260 else (if i < 262 then w261 else w262)))) else (if i < 268 then (if i < 265 then (if i < 264 then w263 else w264) else (if i < 266 then w265 else (if i < 267 then w266 else w267))) else (if i < 270 then (if i < 269 then w268 else w269) else (if i < 271 then w270 else (if i < 272 then w271 else w272)))))) else (if i < 293 then (if i < 283 then (if i < 278 then (if i < 275 then (if i < 274 then w273 else w274) else (if i < 276 then w275 else (if i < 277 then w276 else w277))) else (if i < 280 then (if i < 279 then w278 else w279) else (if i < 281 then w280 else (if i < 282 then w281 else w282)))) else (if i < 288 then (if i < 285 then (if i < 284 then w283 else w284) else (if i < 286 then w285 else (if i < 287 then w286 else w287))) else (if i < 290 then (if i < 289 then w288 else w289) else (if i < 291 then w290 else (if i < 292 then w291 else w292))))) else (if i < 303 then (if i < 298 then (if i < 295 then (if i < 294 then w293 else w294) else (if i < 296 then w295 else (if i < 297 then w296 else w297))) else (if i < 300 then (if i < 299 then w298 else w299) else (if i < 301 then w300 else (if i < 302 then w301 else w302)))) else (if i < 308 then (if i < 305 then (if i < 304 then w303 else w304) else (if i < 306 then w305 else (if i < 307 then w306 else w307))) else (if i < 310 then (if i < 309 then w308 else w309) else (if i < 311 then w310 else (if i < 312 then w311 else w312))))))))) else (if i < 469 then (if i < 391 then (if i < 352 then (if i < 332 then (if i < 322 then (if i < 317 then (if i < 315 then (if i < 314 then w313 else w314) else (if i < 316 then w315 else w316)) else (if i < 319 then (if i < 318 then w317 else w318) else (if i < 320 then w319 else (if i < 321 then w320 else w321)))) else (if i < 327 then (if i < 324 then (if i < 323 then w322 else w323) else (if i < 325 then w324 else (if i < 326 then w325 else w326))) else (if i < 329 then (if i < 328 then w327 else w328) else (if i < 330 then w329 else (if i < 331 then w330 else w331))))) else (if i < 342 then (if i < 337 then (if i < 334 then (if i < 333 then w332 else w333) else (if i < 335 then w334 else (if i < 336 then w335 else w336))) else (if i < 339 then (if i < 338 then w337 else w338) else (if i < 340 then w339 else (if i < 341 then w340 else w341)))) else (if i < 347 then (if i < 344 then (if i < 343 then w342 else w343) else (if i < 345 then w344 else (if i < 346 then w345 else w346))) else (if i < 349 then (if i < 348 then w347 else w348) else (if i < 350 then w349 else (if i < 351 then w350 else w351)))))) else (if i < 371 then (if i < 361 then (if i < 356 then (if i < 354 then (if i < 353 then w352 else w353) else (if i < 355 then w354 else w355)) else (if i < 358 then (if i < 357 then w356 else w357) else (if i < 359 then w358 else (if i < 360 then w359 else w360)))) else (if i < 366 then (if i < 363 then (if i < 362 then w361 else w362) else (if i < 364 then w363 else (if i < 365 then w364 else w365))) else (if i < 368 then (if i < 367 then w366 else w367) else (if i < 369 then w368 else (if i < 370 then w369 else w370))))) else (if i < 381 then (if i < 376 then (if i < 373 then (if i < 372 then w371 else w372) else (if i < 374 then w373 else (if i < 375 then w374 else w375))) else (if i < 378 then (if i < 377 then w376 else w377) else (if i < 379 then w378 else (if i < 380 then w379 else w380)))) else (if i < 386 then (if i < 383 then (if i < 382 then w381 else w382) else (if i < 384 then w383 else (if i < 385 then w384 else w385))) else (if i < 388 then (if i < 387 then w386 else w387) else (if i < 389 then w388 else (if i < 390 then w389 else w390))))))) else (if i < 430 then (if i < 410 then (if i < 400 then (if i < 395 then (if i < 393 then (if i < 392 then w391 else w392) else (if i < 394 then w393 else w394)) else (if i < 397 then (if i < 396 then w395 else w396) else (if i < 398 then w397 else (if i < 399 then w398 else w399)))) else (if i < 405 then (if i < 402 then (if i < 401 then w400 else w401) else (if i < 403 then w402 else (if i < 404 then w403 else w404))) else (if i < 407 then (if i < 406 then w405 else w406) else (if i < 408 then w407 else (if i < 409 then w408 else w409))))) else (if i < 420 then (if i < 415 then (if i < 412 then (if i < 411 then w410 else w411) else (if i < 413 then w412 else (if i < 414 then w413 else w414))) else (if i < 417 then (if i < 416 then w415 else w416) else (if i < 418 then w417 else (if i < 419 then w418 else w419)))) else (if i < 425 then (if i < 422 then (if i < 421 then w420 else w421) else (if i < 423 then w422 else (if i < 424 then w423 else w424))) else (if i < 427 then (if i < 426 then w425 else w426) else (if i < 428 then w427 else (if i < 429 then w428 else w429)))))) else (if i < 449 then (if i < 439 then (if i < 434 then (if i < 432 then (if i < 431 then w430 else w431) else (if i < 433 then w432 else w433)) else (if i < 436 then (if i < 435 then w434 else w435) else (if i < 437 then w436 else (if i < 438 then w437 else w438)))) else (if i < 444 then (if i < 441 then (if i < 440 then w439 else w440) else (if i < 442 then w441 else (if i < 443 then w442 else w443))) else (if i < 446 then (if i < 445 then w444 else w445) else (if i < 447 then w446 else (if i < 448 then w447 else w448))))) else (if i < 459 then (if i < 454 then (if i < 451 then (if i < 450 then w449 else w450) else (if i < 452 then w451 else (if i < 453 then w452 else w453))) else (if i < 456 then (if i < 455 then w454 else w455) else (if i < 457 then w456 else (if i < 458 then w457 else w458)))) else (if i < 464 then (if i < 461 then (if i < 460 then w459 else w460) else (if i < 462 then w461 else (if i < 463 then w462 else w463))) else (if i < 466 then (if i < 465 then w464 else w465) else (if i < 467 then w466 else (if i < 468 then w467 else w468)))))))) else (if i < 547 then (if i < 508 then (if i < 488 then (if i < 478 then (if i < 473 then (if i < 471 then (if i < 470 then w469 else w470) else (if i < 472 then w471 else w472)) else (if i < 475 then (if i < 474 then w473 else w474) else (if i < 476 then w475 else (if i < 477 then w476 else w477)))) else (if i < 483 then (if i < 480 then (if i < 479 then w478 else w479) else (if i < 481 then w480 else (if i < 482 then w481 else w482))) else (if i < 485 then (if i < 484 then w483 else w484) else (if i < 486 then w485 else (if i < 487 then w486 else w487))))) else (if i < 498 then (if i < 493 then (if i < 490 then (if i < 489 then w488 else w489) else (if i < 491 then w490 else (if i < 492 then w491 else w492))) else (if i < 495 then (if i < 494 then w493 else w494) else (if i < 496 then w495 else (if i < 497 then w496 else w497)))) else (if i < 503 then (if i < 500 then (if i < 499 then w498 else w499) else (if i < 501 then w500 else (if i < 502 then w501 else w502))) else (if i < 505 then (if i < 504 then w503 else w504) else (if i < 506 then w505 else (if i < 507 then w506 else w507)))))) else (if i < 527 then (if i < 517 then (if i < 512 then (if i < 510 then (if i < 509 then w508 else w509) else (if i < 511 then w510 else w511)) else (if i < 514 then (if i < 513 then w512 else w513) else (if i < 515 then w514 else (if i < 516 then w515 else w516)))) else (if i < 522 then (if i < 519 then (if i < 518 then w517 else w518) else (if i < 520 then w519 else (if i < 521 then w520 else w521))) else (if i < 524 then (if i < 523 then w522 else w523) else (if i < 525 then w524 else (if i < 526 then w525 else w526))))) else (if i < 537 then (if i < 532 then (if i < 529 then (if i < 528 then w527 else w528) else (if i < 530 then w529 else (if i < 531 then w530 else w531))) else (if i < 534 then (if i < 533 then w532 else w533) else (if i < 535 then w534 else (if i < 536 then w535 else w536)))) else (if i < 542 then (if i < 539 then (if i < 538 then w537 else w538) else (if i < 540 then w539 else (if i < 541 then w540 else w541))) else (if i < 544 then (if i < 543 then w542 else w543) else (if i < 545 then w544 else (if i < 546 then w545 else w546))))))) else (if i < 586 then (if i < 566 then (if i < 556 then (if i < 551 then (if i < 549 then (if i < 548 then w547 else w548) else (if i < 550 then w549 else w550)) else (if i < 553 then (if i < 552 then w551 else w552) else (if i < 554 then w553 else (if i < 555 then w554 else w555)))) else (if i < 561 then (if i < 558 then (if i < 557 then w556 else w557) else (if i < 559 then w558 else (if i < 560 then w559 else w560))) else (if i < 563 then (if i < 562 then w561 else w562) else (if i < 564 then w563 else (if i < 565 then w564 else w565))))) else (if i < 576 then (if i < 571 then (if i < 568 then (if i < 567 then w566 else w567) else (if i < 569 then w568 else (if i < 570 then w569 else w570))) else (if i < 573 then (if i < 572 then w571 else w572) else (if i < 574 then w573 else (if i < 575 then w574 else w575)))) else (if i < 581 then (if i < 578 then (if i < 577 then w576 else w577) else (if i < 579 then w578 else (if i < 580 then w579 else w580))) else (if i < 583 then (if i < 582 then w581 else w582) else (if i < 584 then w583 else (if i < 585 then w584 else w585)))))) else (if i < 606 then (if i < 596 then (if i < 591 then (if i < 588 then (if i < 587 then w586 else w587) else (if i < 589 then w588 else (if i < 590 then w589 else w590))) else (if i < 593 then (if i < 592 then w591 else w592) else (if i < 594 then w593 else (if i < 595 then w594 else w595)))) else (if i < 601 then (if i < 598 then (if i < 597 then w596 else w597) else (if i < 599 then w598 else (if i < 600 then w599 else w600))) else (if i < 603 then (if i < 602 then w601 else w602) else (if i < 604 then w603 else (if i < 605 then w604 else w605))))) else (if i < 616 then (if i < 611 then (if i < 608 then (if i < 607 then w606 else w607) else (if i < 609 then w608 else (if i < 610 then w609 else w610))) else (if i < 613 then (if i < 612 then w611 else w612) else (if i < 614 then w613 else (if i < 615 then w614 else w615)))) else (if i < 621 then (if i < 618 then (if i < 617 then w616 else w617) else (if i < 619 then w618 else (if i < 620 then w619 else w620))) else (if i < 623 then (if i < 622 then w621 else w622) else (if i < 624 then w623 else (if i < 625 then w624 else w625)))))))))) else (if i < 1879 then (if i < 782 then (if i < 704 then (if i < 665 then (if i < 645 then (if i < 635 then (if i < 630 then (if i < 628 then (if i < 627 then w626 else w627) else (if i < 629 then w628 else w629)) else (if i < 632 then (if i < 631 then w630 else w631) else (if i < 633 then w632 else (if i < 634 then w633 else w634)))) else (if i < 640 then (if i < 637 then (if i < 636 then w635 else w636) else (if i < 638 then w637 else (if i < 639 then w638 else w639))) else (if i < 642 then (if i < 641 then w640 else w641) else (if i < 643 then w642 else (if i < 644 then w643 else w644))))) else (if i < 655 then (if i < 650 then (if i < 647 then (if i < 646 then w645 else w646) else (if i < 648 then w647 else (if i < 649 then w648 else w649))) else (if i < 652 then (if i < 651 then w650 else w651) else (if i < 653 then w652 else (if i < 654 then w653 else w654)))) else (if i < 660 then (if i < 657 then (if i < 656 then w655 else w656) else (if i < 658 then w657 else (if i < 659 then w658 else w659))) else (if i < 662 then (if i < 661 then w660 else w661) else (if i < 663 then w662 else (if i < 664 then w663 else w664)))))) else (if i < 684 then (if i < 674 then (if i < 669 then (if i < 667 then (if i < 666 then w665 else w666) else (if i < 668 then w667 else w668)) else (if i < 671 then (if i < 670 then w669 else w670) else (if i < 672 then w671 else (if i < 673 then w672 else w673)))) else (if i < 679 then (if i < 676 then (if i < 675 then w674 else w675) else (if i < 677 then w676 else (if i < 678 then w677 else w678))) else (if i < 681 then (if i < 680 then w679 else w680) else (if i < 682 then w681 else (if i < 683 then w682 else w683))))) else (if i < 694 then (if i < 689 then (if i < 686 then (if i < 685 then w684 else w685) else (if i < 687 then w686 else (if i < 688 then w687 else w688))) else (if i < 691 then (if i < 690 then w689 else w690) else (if i < 692 then w691 else (if i < 693 then w692 else w693)))) else (if i < 699 then (if i < 696 then (if i < 695 then w694 else w695) else (if i < 697 then w696 else (if i < 698 then w697 else w698))) else (if i < 701 then (if i < 700 then w699 else w700) else (if i < 702 then w701 else (if i < 703 then w702 else w703))))))) else (if i < 743 then (if i < 723 then (if i < 713 then (if i < 708 then (if i < 706 then (if i < 705 then w704 else w705) else (if i < 707 then w706 else w707)) else (if i < 710 then (if i < 709 then w708 else w709) else (if i < 711 then w710 else (if i < 712 then w711 else w712)))) else (if i < 718 then (if i < 715 then (if i < 714 then w713 else w714) else (if i < 716 then w715 else (if i < 717 then w716 else w717))) else (if i < 720 then (if i < 719 then w718 else w719) else (if i < 721 then w720 else (if i < 722 then w721 else w722))))) else (if i < 733 then (if i < 728 then (if i < 725 then (if i < 724 then w723 else w724) else (if i < 726 then w725 else (if i < 727 then w726 else w727))) else (if i < 730 then (if i < 729 then w728 else w729) else (if i < 731 then w730 else (if i < 732 then w731 else w732)))) else (if i < 738 then (if i < 735 then (if i < 734 then w733 else w734) else (if i < 736 then w735 else (if i < 737 then w736 else w737))) else (if i < 740 then (if i < 739 then w738 else w739) else (if i < 741 then w740 else (if i < 742 then w741 else w742)))))) else (if i < 762 then (if i < 752 then (if i < 747 then (if i < 745 then (if i < 744 then w743 else w744) else (if i < 746 then w745 else w746)) else (if i < 749 then (if i < 748 then w747 else w748) else (if i < 750 then w749 else (if i < 751 then w750 else w751)))) else (if i < 757 then (if i < 754 then (if i < 753 then w752 else w753) else (if i < 755 then w754 else (if i < 756 then w755 else w756))) else (if i < 759 then (if i < 758 then w757 else w758) else (if i < 760 then w759 else (if i < 761 then w760 else w761))))) else (if i < 772 then (if i < 767 then (if i < 764 then (if i < 763 then w762 else w763) else (if i < 765 then w764 else (if i < 766 then w765 else w766))) else (if i < 769 then (if i < 768 then w767 else w768) else (if i < 770 then w769 else (if i < 771 then w770 else w771)))) else (if i < 777 then (if i < 774 then (if i < 773 then w772 else w773) else (if i < 775 then w774 else (if i < 776 then w775 else w776))) else (if i < 779 then (if i < 778 then w777 else w778) else (if i < 780 then w779 else (if i < 781 then w780 else w781)))))))) else (if i < 1237 then (if i < 821 then (if i < 801 then (if i < 791 then (if i < 786 then (if i < 784 then (if i < 783 then w782 else w783) else (if i < 785 then w784 else w785)) else (if i < 788 then (if i < 787 then w786 else w787) else (if i < 789 then w788 else (if i < 790 then w789 else w790)))) else (if i < 796 then (if i < 793 then (if i < 792 then w791 else w792) else (if i < 794 then w793 else (if i < 795 then w794 else w795))) else (if i < 798 then (if i < 797 then w796 else w797) else (if i < 799 then w798 else (if i < 800 then w799 else w800))))) else (if i < 811 then (if i < 806 then (if i < 803 then (if i < 802 then w801 else w802) else (if i < 804 then w803 else (if i < 805 then w804 else w805))) else (if i < 808 then (if i < 807 then w806 else w807) else (if i < 809 then w808 else (if i < 810 then w809 else w810)))) else (if i < 816 then (if i < 813 then (if i < 812 then w811 else w812) else (if i < 814 then w813 else (if i < 815 then w814 else w815))) else (if i < 818 then (if i < 817 then w816 else w817) else (if i < 819 then w818 else (if i < 820 then w819 else w820)))))) else (if i < 1179 then (if i < 1026 then (if i < 966 then (if i < 908 then (if i < 881 then w821 else w881) else (if i < 915 then w908 else w915)) else (if i < 1016 then (if i < 1003 then w966 else w1003) else (if i < 1022 then w1016 else (if i < 1024 then w1022 else w1024)))) else (if i < 1109 then (if i < 1030 then (if i < 1028 then w1026 else w1028) else (if i < 1067 then w1030 else (if i < 1094 then w1067 else w1094))) else (if i < 1152 then (if i < 1131 then w1109 else w1131) else (if i < 1175 then w1152 else (if i < 1177 then w1175 else w1177))))) else (if i < 1203 then (if i < 1190 then (if i < 1187 then (if i < 1181 then w1179 else w1181) else (if i < 1188 then w1187 else (if i < 1189 then w1188 else w1189))) else (if i < 1195 then (if i < 1192 then w1190 else w1192) else (if i < 1199 then w1195 else (if i < 1201 then w1199 else w1201)))) else (if i < 1211 then (if i < 1206 then (if i < 1205 then w1203 else w1205) else (if i < 1207 then w1206 else (if i < 1209 then w1207 else w1209))) else (if i < 1218 then (if i < 1217 then w1211 else w1217) else (if i < 1219 then w1218 else (if i < 1220 then w1219 else w1220))))))) else (if i < 1516 then (if i < 1380 then (if i < 1370 then (if i < 1294 then (if i < 1262 then (if i < 1242 then w1237 else w1242) else (if i < 1293 then w1262 else w1293)) else (if i < 1296 then (if i < 1295 then w1294 else w1295) else (if i < 1349 then w1296 else (if i < 1368 then w1349 else w1368)))) else (if i < 1375 then (if i < 1372 then (if i < 1371 then w1370 else w1371) else (if i < 1373 then w1372 else (if i < 1374 then w1373 else w1374))) else (if i < 1377 then (if i < 1376 then w1375 else w1376) else (if i < 1378 then w1377 else (if i < 1379 then w1378 else w1379))))) else (if i < 1450 then (if i < 1386 then (if i < 1383 then (if i < 1381 then w1380 else w1381) else (if i < 1384 then w1383 else (if i < 1385 then w1384 else w1385))) else (if i < 1389 then (if i < 1388 then w1386 else w1388) else (if i < 1390 then w1389 else (if i < 1391 then w1390 else w1391)))) else (if i < 1474 then (if i < 1468 then (if i < 1466 then w1450 else w1466) else (if i < 1470 then w1468 else (if i < 1472 then w1470 else w1472))) else (if i < 1506 then (if i < 1504 then w1474 else w1504) else (if i < 1508 then w1506 else (if i < 1510 then w1508 else w1510)))))) else (if i < 1567 then (if i < 1540 then (if i < 1524 then (if i < 1518 then (if i < 1517 then w1516 else w1517) else (if i < 1519 then w1518 else (if i < 1521 then w1519 else w1521))) else (if i < 1535 then (if i < 1532 then w1524 else w1532) else (if i < 1536 then w1535 else (if i < 1538 then w1536 else w1538)))) else (if i < 1549 then (if i < 1546 then (if i < 1542 then w1540 else w1542) else (if i < 1547 then w1546 else (if i < 1548 then w1547 else w1548))) else (if i < 1561 then (if i < 1560 then w1549 else w1560) else (if i < 1563 then w1561 else (if i < 1565 then w1563 else w1565))))) else (if i < 1843 then (if i < 1627 then (if i < 1624 then (if i < 1596 then w1567 else w1596) else (if i < 1625 then w1624 else (if i < 1626 then w1625 else w1626))) else (if i < 1813 then (if i < 1799 then w1627 else w1799) else (if i < 1817 then w1813 else (if i < 1828 then w1817 else w1828)))) else (if i < 1861 then (if i < 1855 then (if i < 1853 then w1843 else w1853) else (if i < 1857 then w1855 else (if i < 1859 then w1857 else w1859))) else (if i < 1873 then (if i < 1867 then w1861 else w1867) else (if i < 1875 then w1873 else (if i < 1877 then w1875 else w1877))))))))) else (if i < 2800 then (if i < 2302 then (if i < 2110 then (if i < 1930 then (if i < 1906 then (if i < 1895 then (if i < 1889 then (if i < 1881 then w1879 else w1881) else (if i < 1893 then w1889 else w1893)) else (if i < 1899 then (if i < 1897 then w1895 else w1897) else (if i < 1901 then w1899 else (if i < 1904 then w1901 else w1904)))) else (if i < 1919 then (if i < 1910 then (if i < 1908 then w1906 else w1908) else (if i < 1915 then w1910 else (if i < 1918 then w1915 else w1918))) else (if i < 1923 then (if i < 1921 then w1919 else w1921) else (if i < 1925 then w1923 else (if i < 1929 then w1925 else w1929))))) else (if i < 2029 then (if i < 1968 then (if i < 1932 then (if i < 1931 then w1930 else w1931) else (if i < 1965 then w1932 else (if i < 1966 then w1965 else w1966))) else (if i < 1977 then (if i < 1970 then w1968 else w1970) else (if i < 1997 then w1977 else (if i < 2002 then w1997 else w2002)))) else (if i < 2105 then (if i < 2031 then (if i < 2030 then w2029 else w2030) else (if i < 2032 then w2031 else (if i < 2091 then w2032 else w2091))) else (if i < 2107 then (if i < 2106 then w2105 else w2106) else (if i < 2108 then w2107 else (if i < 2109 then w2108 else w2109)))))) else (if i < 2225 then (if i < 2194 then (if i < 2176 then (if i < 2170 then (if i < 2115 then w2110 else w2115) else (if i < 2174 then w2170 else w2174)) else (if i < 2180 then (if i < 2178 then w2176 else w2178) else (if i < 2182 then w2180 else (if i < 2192 then w2182 else w2192)))) else (if i < 2204 then (if i < 2198 then (if i < 2196 then w2194 else w2196) else (if i < 2200 then w2198 else (if i < 2202 then w2200 else w2202))) else (if i < 2208 then (if i < 2206 then w2204 else w2206) else (if i < 2210 then w2208 else (if i < 2212 then w2210 else w2212))))) else (if i < 2242 then (if i < 2234 then (if i < 2229 then (if i < 2227 then w2225 else w2227) else (if i < 2231 then w2229 else (if i < 2232 then w2231 else w2232))) else (if i < 2238 then (if i < 2236 then w2234 else w2236) else (if i < 2239 then w2238 else (if i < 2240 then w2239 else w2240)))) else (if i < 2249 then (if i < 2245 then (if i < 2244 then w2242 else w2244) else (if i < 2246 then w2245 else (if i < 2247 then w2246 else w2247))) else (if i < 2251 then (if i < 2250 then w2249 else w2250) else (if i < 2252 then w2251 else (if i < 2253 then w2252 else w2253))))))) else (if i < 2439 then (if i < 2354 then (if i < 2316 then (if i < 2309 then (if i < 2306 then (if i < 2304 then w2302 else w2304) else (if i < 2308 then w2306 else w2308)) else (if i < 2312 then (if i < 2310 then w2309 else w2310) else (if i < 2314 then w2312 else (if i < 2315 then w2314 else w2315)))) else (if i < 2322 then (if i < 2319 then (if i < 2317 then w2316 else w2317) else (if i < 2320 then w2319 else (if i < 2321 then w2320 else w2321))) else (if i < 2334 then (if i < 2323 then w2322 else w2323) else (if i < 2351 then w2334 else (if i < 2352 then w2351 else w2352))))) else (if i < 2383 then (if i < 2361 then (if i < 2357 then (if i < 2356 then w2354 else w2356) else (if i < 2358 then w2357 else (if i < 2359 then w2358 else w2359))) else (if i < 2363 then (if i < 2362 then w2361 else w2362) else (if i < 2364 then w2363 else (if i < 2365 then w2364 else w2365)))) else (if i < 2391 then (if i < 2387 then (if i < 2385 then w2383 else w2385) else (if i < 2389 then w2387 else (if i < 2390 then w2389 else w2390))) else (if i < 2394 then (if i < 2392 then w2391 else w2392) else (if i < 2430 then w2394 else (if i < 2438 then w2430 else w2438)))))) else (if i < 2740 then (if i < 2480 then (if i < 2470 then (if i < 2441 then (if i < 2440 then w2439 else w2440) else (if i < 2442 then w2441 else (if i < 2468 then w2442 else w2468))) else (if i < 2474 then (if i < 2472 then w2470 else w2472) else (if i < 2476 then w2474 else (if i < 2478 then w2476 else w2478)))) else (if i < 2546 then (if i < 2490 then (if i < 2482 then w2480 else w2482) else (if i < 2520 then w2490 else (if i < 2528 then w2520 else w2528))) else (if i < 2569 then (if i < 2549 then w2546 else w2549) else (if i < 2633 then w2569 else (if i < 2736 then w2633 else w2736))))) else (if i < 2758 then (if i < 2751 then (if i < 2746 then (if i < 2744 then w2740 else w2744) else (if i < 2748 then w2746 else (if i < 2750 then w2748 else w2750))) else (if i < 2754 then (if i < 2752 then w2751 else w2752) else (if i < 2756 then w2754 else (if i < 2757 then w2756 else w2757)))) else (if i < 2764 then (if i < 2761 then (if i < 2759 then w2758 else w2759) else (if i < 2762 then w2761 else (if i < 2763 then w2762 else w2763))) else (if i < 2784 then (if i < 2765 then w2764 else w2765) else (if i < 2788 then w2784 else (if i < 2799 then w2788 else w2799)))))))) else (if i < 4263 then (if i < 3016 then (if i < 2883 then (if i < 2844 then (if i < 2811 then (if i < 2804 then (if i < 2802 then w2800 else w2802) else (if i < 2810 then w2804 else w2810)) else (if i < 2813 then (if i < 2812 then w2811 else w2812) else (if i < 2826 then w2813 else (if i < 2841 then w2826 else w2841)))) else (if i < 2850 then (if i < 2846 then (if i < 2845 then w2844 else w2845) else (if i < 2848 then w2846 else (if i < 2849 then w2848 else w2849))) else (if i < 2852 then (if i < 2851 then w2850 else w2851) else (if i < 2870 then w2852 else (if i < 2872 then w2870 else w2872))))) else (if i < 2933 then (if i < 2897 then (if i < 2887 then (if i < 2885 then w2883 else w2885) else (if i < 2889 then w2887 else (if i < 2894 then w2889 else w2894))) else (if i < 2899 then (if i < 2898 then w2897 else w2898) else (if i < 2900 then w2899 else (if i < 2918 then w2900 else w2918)))) else (if i < 2984 then (if i < 2969 then (if i < 2949 then w2933 else w2949) else (if i < 2973 then w2969 else (if i < 2982 then w2973 else w2982))) else (if i < 2988 then (if i < 2986 then w2984 else w2986) else (if i < 2995 then w2988 else (if i < 3003 then w2995 else w3003)))))) else (if i < 3958 then (if i < 3389 then (if i < 3256 then (if i < 3086 then (if i < 3033 then w3016 else w3033) else (if i < 3215 then w3086 else w3215)) else (if i < 3323 then (if i < 3299 then w3256 else w3299) else (if i < 3341 then w3323 else (if i < 3363 then w3341 else w3363)))) else (if i < 3483 then (if i < 3406 then (if i < 3405 then w3389 else w3405) else (if i < 3408 then w3406 else (if i < 3410 then w3408 else w3410))) else (if i < 3485 then (if i < 3484 then w3483 else w3484) else (if i < 3486 then w3485 else (if i < 3954 then w3486 else w3954))))) else (if i < 4003 then (if i < 3973 then (if i < 3969 then (if i < 3968 then w3958 else w3968) else (if i < 3970 then w3969 else (if i < 3972 then w3970 else w3972))) else (if i < 3975 then (if i < 3974 then w3973 else w3974) else (if i < 3976 then w3975 else (if i < 3994 then w3976 else w3994)))) else (if i < 4074 then (if i < 4005 then (if i < 4004 then w4003 else w4004) else (if i < 4006 then w4005 else (if i < 4055 then w4006 else w4055))) else (if i < 4111 then (if i < 4085 then w4074 else w4085) else (if i < 4191 then w4111 else (if i < 4226 then w4191 else w4226))))))) else (if i < 5203 then (if i < 4784 then (if i < 4470 then (if i < 4389 then (if i < 4364 then (if i < 4317 then w4263 else w4317) else (if i < 4382 then w4364 else w4382)) else (if i < 4394 then (if i < 4393 then w4389 else w4393) else (if i < 4395 then w4394 else (if i < 4465 then w4395 else w4465)))) else (if i < 4495 then (if i < 4472 then (if i < 4471 then w4470 else w4471) else (if i < 4473 then w4472 else (if i < 4485 then w4473 else w4485))) else (if i < 4557 then (if i < 4506 then w4495 else w4506) else (if i < 4613 then w4557 else (if i < 4742 then w4613 else w4742))))) else (if i < 5037 then (if i < 4854 then (if i < 4844 then (if i < 4838 then w4784 else w4838) else (if i < 4852 then w4844 else (if i < 4853 then w4852 else w4853))) else (if i < 4989 then (if i < 4906 then w4854 else w4906) else (if i < 5001 then w4989 else (if i < 5012 then w5001 else w5012)))) else (if i < 5189 then (if i < 5105 then (if i < 5054 then w5037 else w5054) else (if i < 5139 then w5105 else (if i < 5160 then w5139 else w5160))) else (if i < 5196 then (if i < 5191 then w5189 else w5191) else (if i < 5200 then w5196 else (if i < 5201 then w5200 else w5201)))))) else (if i < 5471 then (if i < 5315 then (if i < 5273 then (if i < 5250 then (if i < 5206 then w5203 else w5206) else (if i < 5259 then w5250 else (if i < 5272 then w5259 else w5272))) else (if i < 5288 then (if i < 5287 then w5273 else w5287) else (if i < 5290 then w5288 else (if i < 5314 then w5290 else w5314)))) else (if i < 5440 then (if i < 5330 then (if i < 5324 then w5315 else w5324) else (if i < 5355 then w5330 else (if i < 5375 then w5355 else w5375))) else (if i < 5462 then (if i < 5444 then w5440 else w5444) else (if i < 5464 then w5462 else (if i < 5468 then w5464 else w5468))))) else (if i < 5540 then (if i < 5500 then (if i < 5476 then (if i < 5473 then w5471 else w5473) else (if i < 5490 then w5476 else (if i < 5492 then w5490 else w5492))) else (if i < 5516 then (if i < 5515 then w5500 else w5515) else (if i < 5524 then w5516 else (if i < 5527 then w5524 else w5527)))) else (if i < 5552 then (if i < 5544 then (if i < 5543 then w5540 else w5543) else (if i < 5545 then w5544 else (if i < 5551 then w5545 else w5551))) else (if i < 5669 then (if i < 5668 then w5552 else w5668) else (if i < 5670 then w5669 else (if i < 5681 then w5670 else w5681)))))))))))
def pointKey (s : Sig) := (((s.1.toNat%2147483647)*257+s.2.toNat%2147483647+317)%2147483647)^3%2147483647
def stateKey (k t : Nat) (v : List Sig) := (((v.foldl (fun z x => z+pointKey x) 0)%2147483647)*41+k*11+t)%2147483647
def leafD (i : Nat) := let c := i/32; ((if c < 150 then (if c < 75 then (if c < 37 then (if c < 18 then (if c < 9 then (if c < 4 then (if c < 2 then (if c < 1 then 0x981c16040780c1800000080e02030000209000200008008040c000200c0201068000003 else 0x80400058041006008001c06008001e03008e804000500400000001c0a0e) else (if c < 3 then 0xa8080000070101815030100c0a0004804010780c160d008080c05028000202000080000 else 0x48040c1d01818180604000000102020080a0002004020f8241004028240005040281401)) else (if c < 6 then (if c < 5 then 0xd8180e030081810010b00402060d004060400000000200818260103800020b028380400 else 0x202400060801808000080006000700418000000c080101058040100804180103800040f) else (if c < 7 then 0x100400010000006000502800070282c0c0100804000d030080401018340003018040c04 else (if c < 8 then 0x500800000500412020300c0a0b04818160b0000004010000400030300c0c080100c0606 else 0x101400011901802000e088200200000100009824020a030280000000000003090000a00)))) else (if c < 13 then (if c < 11 then (if c < 10 then 0xc81c060011000000200004020f0000000040000c0c00018181a36000341400028141c02 else 0x80c04000080c10030001800100201c020e0e82c34010080804180002c0602080140400) else (if c < 12 then 0x700022020000410030000000000080414100100002000180430030081c0400078640c00 else 0xe0200412000580220000000600008041002038140c0700800200203008141d078240044)) else (if c < 15 then (if c < 14 then 0x80400010300816000280c0204038401000000000810018041a01008100a09000601a00 else 0xd01a0a00814080706804120506800020c068040a08038080a07000041a0b058001003) else (if c < 16 then 0x703404000180c4601098040c22018040201000300c04040340802040300c01000081408 else (if c < 17 then 0x281c00030e80006080981414190101c00060183c340000010040802810060b008000800 else 0x3038000203018080200000640801010080217020240600028200401090040e01))))) else (if c < 27 then (if c < 22 then (if c < 20 then (if c < 19 then 0x58940c090f8000209010481c06008080005000040a010580c001a030601a000002c0009 else 0x50000814018080601018100209000380400008380000000240402000040e0e0c0382217) else (if c < 21 then 0x18681401020080c01000085206000080a0111010200509800020b0c808000a0002c0805 else 0x200c340a008440005000041a0209000020b0381c28000000c0008040000002050101a00)) else (if c < 24 then (if c < 23 then 0x80c060a0281c0202060280e11018040606148000600038340601018680605050000c01 else 0x78140a020100400010001004070580c0005000000c011a004000b010004602048001209) else (if c < 25 then 0x80808060183c00040380000010000012000a0341c21000041c04008300400070001408 else (if c < 26 then 0x30081801010000008028580000118000405030000202058003810010140210028042600 else 0x482c520c058181808128200400000000a170480c240a000001200010040a00070100006)))) else (if c < 32 then (if c < 29 then (if c < 28 then 0x305012020201c2a000780440020080c0201018181a140083000021380006030300c0c07 else 0x3810180005014000503004260a028041400040300200008041c00038041415010081008) else (if c < 30 then 0xc2e0300020340000008000c048040801018080834000080a03038000000000140000 else (if c < 31 then 0x800021e000201403068040000008200802000100a000000400070001c3a070b0702a05 else 0x38040a00070000c1a00814020c008781404018900601000f804070080c02170182c1400))) else (if c < 34 then (if c < 33 then 0x50041a050400c1608000000c000080c14020200802030280000000002c0203040006203 else 0xc0882601010a000200180c060a010140a000300c320a0302004020703800010a0043202) else (if c < 35 then 0x2004000c0000008040101c040d008000803038540c0c0400c120c050000a19090200000 else (if c < 36 then 0x280407000000807008040400010100c11030200a0000020180a07010021c048100000 else 0x180400030702c2c08010040e0a010181205008000a01008000a00018200201028001000)))))) else (if c < 56 then (if c < 46 then (if c < 41 then (if c < 39 then (if c < 38 then 0x80026070007c1a0002804020405028021b0887c08060080c000c01808080002018220c else 0x28181c060580c04000208000001081800000380c0c01000340002000401601040000200) else (if c < 40 then 0x180400000c8500002028000a000301c2c00010280a0901800000405808140400004001b else 0x100408050280c1401000000a0603008001302814061b030000400100141a09040101a2d)) else (if c < 43 then (if c < 42 then 0x81008000001802010080c1a0f008000e00000402c03010000402000200002000001a00 else 0x82c180502028001401800041b0302802010302014020c804202500000220000018080a) else (if c < 44 then 0x80081000000303c02040103c1444040000e02018200018048200a0a0001c0801 else (if c < 45 then 0xd8040207000cc001802048020708800560900804080c0c8000a00040280401058041603 else 0x3422060b000060b000081800008200801000142e040c8001602078000a04080040400)))) else (if c < 51 then (if c < 48 then (if c < 47 then 0x834080003834100003090240100800020000008020d0c8080802088300e16030000601 else 0x381c1e03000383e0201024000601024040b0a83c1400008140c020280c0000038500404) else (if c < 49 then 0x83412000983c32000087408000485036050180c1a01030083e060601402050480c0404 else (if c < 50 then 0x400e000380c1c010a8080205060080e230000002020000c02030300c1c0c008140c02 else 0x5038000406000060800810180002800020b028482206008a40208000140209000000800))) else (if c < 53 then (if c < 52 then 0x200c1e010400808000080c0e000381c02000d82c0400000000005020102a02000005c09 else 0x1c16060a00850030005402080d00002010180c0200018000007018181408010000007) else (if c < 54 then 0x101822000a0140e0001800000005004140402800020f020143c02010041e24008040a00 else (if c < 55 then 0xc0300207020000a020281c02030608004011c0080402028bc00061901414010480c0405 else 0x48880805080640406018080600010140000068101605048181a24008500201060080200))))) else (if c < 65 then (if c < 60 then (if c < 58 then (if c < 57 then 0x50206c080504000210080428060180800010085000010482000010e85c2e00000380006 else 0x10000606008043e000980002010081400050583004000201c08000000400040080c0c05) else (if c < 59 then 0x48040001018044c0c010541200020302006038000201018041c00000000004010401202 else 0x28005801000340200038000200028780000008080202000480a0f00034240a028081203)) else (if c < 62 then (if c < 61 then 0x380c0c020381400000080800000a0dc060e0003010010681c0a0300004000c078000200 else 0x38101e09008280a0302838041c0085c2a000281816170600412000f8a00613000040013) else (if c < 63 then 0x400000000700c00001604800000e82010010682002060000c0000008083200020202e01 else (if c < 64 then 0x1000010100c1411010100600048141c040183c0e04090540801018180000030000806 else 0x10040001020042827070000c02020187e09018041e081200410070000408000200c0200)))) else (if c < 70 then (if c < 67 then (if c < 66 then 0xa0240c02000240e1f0001c0010028002400020141e09088742800030581806008080200 else 0x8041a0002814920c0100c1a23018000e091782c0202000102406000240202028003400) else (if c < 68 then 0x200a22000040c02190283801088540000010000806010540409000181a15098800c02 else (if c < 69 then 0x1000000c83c0008048c40201030100004000400208010080801058240600000000a04 else 0x40001a02120000210040102e0301800240003808140d02808080203000041a00800140b))) else (if c < 72 then (if c < 71 then 0x180002000201804008080006000800413020103400070041800010100800000000208 else 0x40280c06008105000000200a000a80000020480000000100c18020381c0005000000815) else (if c < 73 then 0xc02310000c0c060004400000184c0600050300a000d00042050a00c10050300c1604 else (if c < 74 then 0x818000301828020700018221801810121b0480000020000406000101c0204008000a00 else 0x202000110000c340007044002a040142028010040000008140610028000005050a01600))))))) else (if c < 112 then (if c < 93 then (if c < 84 then (if c < 79 then (if c < 77 then (if c < 76 then 0x10000206000080e0f0000002040900c00370081002000208404010104c0e0b000481000 else 0x83810020505c02000082c1c06000281c00008080e151480406040a0043c0a0480c0602) else (if c < 78 then 0xa00201008100c040780000010180c3800008002c0004824201e110080008028040402 else 0x38640000000400a0b01850260300000180000000100506004180b0804006080b05c3e06)) else (if c < 81 then (if c < 80 then 0x441a041100c04010880000050003402070e000000100004000b040180a00038000209 else 0x18000204000001800030040000010282601008000001020100202000300013030080200) else (if c < 82 then 0x3000040a0001000040400000020082c00100b0040254038000a02060041e04000400204 else (if c < 83 then 0xa80404010180c0002018080a020e00800050306c08060000c08020002c7606010683a02 else 0x8200402048088a0003018240000874002f000140000038040401040140003058080002)))) else (if c < 88 then (if c < 86 then (if c < 85 then 0x30080203078041c0a010004a000100c24010f8180002078e0300d0203808020080c1600 else 0x30081a020080c0a010e80000270280c4001030041e080c81006010700840010200c0009) else (if c < 87 then 0x2440010404402000780c0003010001a010000814090a0002e0001830020f000081e00 else 0x10000640018081e0104014200e05004200e048001c0e0881036000004c1607008180005)) else (if c < 90 then (if c < 89 then 0x8000f00008300e001200a01028001806048001817030400805000000c03000780c00 else 0x20940c040a89810191f804060a140600a030a0000400030006c040786c0a020185c0200) else (if c < 91 then 0x40000e010500808020302400000184c02030180802060002400041381c1c07000043402 else (if c < 92 then 0x4c1600008004808168000a0404818120701834000008804080f018000408000002a02 else 0x81c1a03068200c020001000020189408020b8000a000100806020004400000000c060e))))) else (if c < 102 then (if c < 97 then (if c < 95 then (if c < 94 then 0x13808021900010060e0101400050c0100600000080401010140415030080000008086205 else 0x20000004098003c060782c0600028740a09000040c00040181a020280c00000000c1206) else (if c < 96 then 0x480c0400028101c04030481610000000e030000004010780c120101020060c118082e01 else 0x404400000380000010382404100080484080a80c240c008040c01100280c010a010580d)) else (if c < 99 then (if c < 98 then 0xa0544401010000600060040e010200c0010068080403008500a0c0c0000c120002c0213 else 0xe020682c0403070080e140004806020005808000002c06250b004160e008040a14) else (if c < 100 then 0x18040282004010601002080180400050101c10010100000070001c14090080c4004 else (if c < 101 then 0x20101a0902020180c0180c1402018300e00070281a00008200e0b0202c1002118082200 else 0x8840021b1900448030101c06000281c08080000400090282c0004010041e04020005801)))) else (if c < 107 then (if c < 104 then (if c < 103 then 0x200c08050280002020100c04002181c0a0e0082c04350107010000589c06050d814040a else 0x47003000080a0a0f00000060201402070285008020b05c0401070448a02000381001) else (if c < 105 then 0x40481e00000440207000080200000283004010140201000400804048040002078340606 else (if c < 106 then 0x201420000b81000090700818000100810000080000030180c0412078003a02000401008 else 0x8042e0004000260000800680600824360a000182416028000a0200018000203020000a))) else (if c < 109 then (if c < 108 then 0x485c060c070180a0100800040300024000301810260e040680409010480805018081a08 else 0xb8000a030080406030500c000000024040300008260001010320407808000b058202e0b) else (if c < 110 then 0x80008030d00004030281020000800408000482000010d8081000088080208008047a00 else (if c < 111 then 0x3c0000000000a11078204a0e0884c1004038000015018000009018140600260380409 else 0x2030120b01004202a018200a0e08800000001000000002040020105874020c000340a02)))))) else (if c < 131 then (if c < 121 then (if c < 116 then (if c < 114 then (if c < 113 then 0x201c00000804c081800804061f0000000160700400290481c1a13028040604080301602 else 0xe09040080c810041202000840a0585002050689400000204c0e00000001000000b4140e) else (if c < 115 then 0xe040000b01838040004800002b00008241d010e408000103010150483c1e12000100402 else 0x8044c03010140218010080c1509008061900018000000050020a058300626030000207)) else (if c < 118 then (if c < 117 then 0x98703a100007402060480012140903c3e01040000c0d078000822018243805008143a02 else 0x49405020000e070080002050400c0e0003898140304800b8010981c0234008000203) else (if c < 119 then 0x4814000503050460002000001e09800020700800100a00888100016818120a00004082d else (if c < 120 then 0x430040200c000a04814080e04824020e05010100507808060300820002a088083616 else 0x48102009028381409000340205008105a310300002080c804060102020060303850200a)))) else (if c < 126 then (if c < 123 then (if c < 122 then 0x9024000c000041a0e158080e1e01000320d030140200008f00207008000a07010149013 else 0x504000000006c0e0100000000c000001e1800004160e01804120a0080c004a060100200) else (if c < 124 then 0x200002060282c0c0300014400c0701802000e8000000018000a170e8000c01058081009 else (if c < 125 then 0x30f000070d00000060086c06010183c20040700c001803024080900850060b000040000 else 0x68280809010040035020081003020080c150002c0603000002404000700407020001005))) else (if c < 128 then (if c < 127 then 0x1080c9c0f0003012000480c260d018141c000a008063a090001e000304c0210028200a01 else 0xc8401a0b068300a0018820020d05814320300800180b100180415018180605168380c06) else (if c < 129 then 0x180080a0510804003902800001c0001400060081c16070203c00010b0040812030300000 else (if c < 130 then 0x686400020500006030482000260e8100200200200a130400010000002402040b80c1603 else 0xb0001009058280a000100c0004010180047020241e00020080200000181802048000219))))) else (if c < 140 then (if c < 135 then (if c < 133 then (if c < 132 then 0x24000b02800160e01004021202020103b0503c0c00000100c0b000201001218100009 else 0x801c280006878021103034020e0106c0005000004402000002e080101404000a8240204) else (if c < 134 then 0xc84006020c0e0362500030040000808140c0000000100106c0003000400001008000607 else 0x800c1406000109200058103207000000419010080001020243400030001c0b040380000)) else (if c < 137 then (if c < 136 then 0x20200400038001805008080e0204008360d05804000d0a8500200000000200018580401 else 0x30080601030040006018200600000001608000200c00000040206018000002000100c08) else (if c < 138 then 0x100c1401060340402008340c0e000384e020200c0e000d01c0413140543612060a00e08 else (if c < 139 then 0x60201e05148000c4200000020a528081800030080c06070780e0304028080e040302800 else 0x8601006030602a010f000580e0780c26000088c0606008640205050240e04078000c04)))) else (if c < 145 then (if c < 142 then (if c < 141 then 0x28142a000180808040a810040002840000b0083030050600002110000802000880c0020 else 0x18180e2702000000f0300c0010000002e000183c0015058084201018140c0e0682c3200) else (if c < 143 then 0xd80c0014010042c0f070581000198042c0a00000081d1980010020000800090d8682805 else (if c < 144 then 0x80c09010000c2508800280603800101f00824160d070501609040e01608000100600 else 0xb8200805000541e100a81c0800038482e000000800340680020000e0041e2c060040000))) else (if c < 147 then (if c < 146 then 0x1b800120a0481806000001c2202008181000018080c02010281606088040c00040100200 else 0x1404030c05050120101c7a160180404000200c100c0a81014080682828080e804081c) else (if c < 148 then 0x1840000b030040210060000005038001c0005800040f000300200000101016050840005 else (if c < 149 then 0x10000200008041a03000080006020cc1211010083e02030340001008586a02150400000 else 0x10500200000340e0b0101c0059048140c00000001a090301004000700c0215008080022)))))))) else (if c < 225 then (if c < 187 then (if c < 168 then (if c < 159 then (if c < 154 then (if c < 152 then (if c < 151 then 0x18240806148142403090181e11000181400020200a010a84c00050002d3e041101c3207 else 0x7810101208810040c008981804001ec0004048000e0315804ac250081c340310814000b) else (if c < 153 then 0xa074020b0508006010a09004620000000070283c000000808000c020c81a34000103e09 else 0x8000080102834000108020100e0900402330006c120b01810180c0003c000502810001d)) else (if c < 156 then (if c < 155 then 0x3400000011402080700c0c000000816000182c041304800000f0482416030e02c1601 else 0x40c010084030022080006080180024050000402130b82800020080400000a8101407) else (if c < 157 then 0x820260801808160f0005008000c020760f05040061a0380c000300840120a0408c101b else (if c < 158 then 0x10ac42020503006011303812050384c40030a0200400018b8140e018480000030045a01 else 0xc0580a001101458120100004000d85c0632058000c04010786a07008148204050208a07)))) else (if c < 163 then (if c < 161 then (if c < 160 then 0xf0140e1000818024f078d82600028240e0b07008082906004040b0200406030280c0007 else 0x78000003018200e00020382a120000000060b01c0e040081c060002800361a058043600) else (if c < 162 then 0x9c00040101400030000414000080834135b00806100b8200a0408044001929000260a else 0x70340200010000000008001413008080800020040206040000009210b000000002c080a)) else (if c < 165 then (if c < 164 then 0x288000040604c04000009404130608c040a118080003018002402040180608028b80615 else 0x814260b008581a02010001e00008184a1404008080d0100000000002c040d000383616) else (if c < 166 then 0x9028240202834063d02848020a0100c6807010c00610008082815000040809020000401 else (if c < 167 then 0x1680c0c020880c06000181c0a031a05c6201028080e12000141c00000000000040080a0d else 0x200004020087c10050580408030603c241e1c00c0202010282e190014c0202070041600))))) else (if c < 177 then (if c < 172 then (if c < 170 then (if c < 169 then 0x20980a060000404001382408010014c58060501420010080002050905c2a58018100211 else 0x8004b6040102c0600010541c0b028000000038144600000c01e0a0287c1c01188000e00) else (if c < 171 then 0x10082e08018080e00028446205000000222068ec1219038082a0b0200c0002018341a05 else 0x301418048d8f6060281004090781c32050101c08060083008050203428050006c180f)) else (if c < 174 then (if c < 173 then 0xa82002000580c22050306832080180026030183c1a100106404290200c0415010300c09 else 0x40100e03000080200008040605000a816480f00016200e8000601020740800120040002) else (if c < 175 then 0x41004068001409018000803030082e050180c00022d00008000b0102803018180e00 else (if c < 176 then 0x840160a01808061b0c0480800018081400090c81c090b8086806010001e23030280408 else 0x40342e01008ec3401068640400058000200000040a270f8340c02000400205028300202)))) else (if c < 182 then (if c < 179 then (if c < 178 then 0x10041c00038302e3a00800041603058022300028100b000245a05000042e00030002a07 else 0x5880000d0b82c001b0000c0404000200806028080c0408800a6022c03412090286c0007) else (if c < 180 then 0x1008120a048140608038cc16040007c304b0000000140b02c4406008000600020142806 else (if c < 181 then 0x10300a02050140808028044252040041c0500880240806038001f0f808020a02010140c else 0xf84c1c0100004bc020000c021109014260e0008410001801c00000f0101402040040001))) else (if c < 184 then (if c < 183 then 0x500400000380000072404010000f8000c020103814060707c120104044021f040044c10 else 0x300c420b0105400010085c0000078042e000700c140d048100007000040a0301800780a) else (if c < 185 then 0x18280a0909800160e0682c001d030ac00020300400120300c02120681c0800008000411 else (if c < 186 then 0x18080005008205a050a0141200030145a08060902003028300800038000004038580800 else 0x2800220204038220c200081a2600024080a07024640e098a800030b8f80200070740003)))))) else (if c < 206 then (if c < 196 then (if c < 191 then (if c < 189 then (if c < 188 then 0x204472071f80006010b8180e0003004160b0002c18070100830050780c040b0f82c0808 else 0x11000402504874340017860060a07010020207068b2000409c0209051001049058000e07) else (if c < 190 then 0x40f8000b008040052008180013000000000280000431070000e070802c0601009740001 else 0x1d0040206000380c2104870020c0505400270a03400000501c54000e000000e028004a13)) else (if c < 193 then (if c < 192 then 0x80044050700400010001c3a05248283c030600004001480008070880002080001c0201 else 0x581c020002c06000000428002a000140f1881c78030180c521101800060c008001a0c) else (if c < 194 then 0x3c28040801016160082040080d004221a1d8980e10000001a0c0d8040e0e028180e00 else (if c < 195 then 0x800801070481a05100180a0b0e80c002d0f074000b0886402060180c0e180580c0c00 else 0x602c3203030143016028202200001086e060b044261e0307426000382c02230f8000c0e)))) else (if c < 201 then (if c < 198 then (if c < 197 then 0x2818281f00028000d01950041d040000405088140806018602e1807010001e020243208 else 0xf800022a01000000f0200000040000420030380816161601c000800008002d018683000) else (if c < 199 then 0xf87c00040308800140a01c06180500016000006c1c0f020080a1e00010180605030320b else (if c < 200 then 0x2303c0e01000003c070501468110a0407c07000100809010140609000d8022d000342202 else 0x3084102e000000016008180a000285c26081200002110d0000410020605812030240000))) else (if c < 203 then (if c < 202 then 0x484c7615240386e000680c04020481c66120888c0600040100c120004c1e08000091619 else 0x8000605048a8260f028c004000002004060b09c0202050240e063005c1c00050600008) else (if c < 204 then 0x383c5a08038000e020207c060700010000c030000403008041802040044e19000040031 else (if c < 205 then 0x68000600070304400028a0480b20018060f0481400140816c0010050f8021218004302f else 0x41c00058701c202580004081f0403005070504a070500424060002c1619010000204))))) else (if c < 215 then (if c < 210 then (if c < 208 then (if c < 207 then 0x98886a00008000800000540e060c07800070a83c040c2b804020901800020606808361e else 0x110f41a1f1d0040209020340c1907828047d020081c2301864040e0303c060d00028040d) else (if c < 209 then 0x480c00000186000101482c020e02890121a0000800040380c160b0c040322f06810a60c else 0x283c2200028003600008140825048305a35000240201018002e2800010060e050480601)) else (if c < 212 then (if c < 211 then 0x41e4080900000081205028000d00854c212018182e150a84804010001c1400000080632 else 0x108000000001600c0006040000d0483c1e4a01000241200068120c0e00c0e01010203c03) else (if c < 213 then 0x20004601088540004038f002020480c081204014180000000020001814000d048140400 else (if c < 214 then 0x10d0260133008020f180200400070281a0b0080044011d8000c020105806000b000320c else 0x28081005078641400000200201038500008040640201078c0000400018401a0e8a8125c)))) else (if c < 220 then (if c < 217 then (if c < 216 then 0x800952100006000e01c0004008105e010f040122f1282468030200c1c03000040c00 else 0x2010000202884420000880140800024060000004001300028161a0c9800a09040101405) else (if c < 218 then 0x4044100a010542404011380012041600e0707800140304008020902800260203810083e else (if c < 219 then 0x6c1a0604008080d0002404050b000100600000080001800020103040200c048100c01 else 0x1180c0205000007c040d014000000034000d1c0100604000000c20190704214028200200))) else (if c < 222 then (if c < 221 then 0x2800000011e02c040703008cc090282014311380856041100406011d0084a00010080600 else 0xb004000c8480005000180400000701c240900004340000004010300c161e09000040e) else (if c < 223 then 0x1b80c180e008682c21018100a000182838090000c18171688c480c05818220205814040a else (if c < 224 then 0x180204059d454060504c0a060600004011e8540a020080412050201c0013058581611 else 0xb044100304010280d02000000401800000200024060f0c05408040381c2009038080814))))))) else (if c < 263 then (if c < 244 then (if c < 234 then (if c < 229 then (if c < 227 then (if c < 226 then 0x501c4e00010001a000000410190100c263b00048001c178444e05070000045130002029 else 0x901a0c88044021a828101523848260d1b01c261f0381026000004c0203000281422) else (if c < 228 then 0x68ac04140901818170483c7200078000c000007434540105838020e8240058070142a09 else 0x800c1a11068d826020000002120e8000c1314810002d000184805010741006018100016)) else (if c < 231 then (if c < 230 then 0x28080600128000c110200c041d02804060e0002c2a1a038c8080f0100080050d8001408 else 0x313c14070081000030080802320082800020081c08000700432140180c0007160305c0d) else (if c < 232 then 0x78040202058001830008000c020001c00090d8000800030180a0f038201c69000000000 else (if c < 233 then 0x4850240602028020a00010081d0380c00030102802010000c0c00068881c080285c6e00 else 0x1082818070002402001883000282a0003c0025014020a020301606030481608028940017)))) else (if c < 239 then (if c < 236 then (if c < 235 then 0x108988002010440213000041a133102000061100808040083c041c280a80210178080400 else 0x18087c240c00c223d0080018001a0d80607098343e04020002e05020040617070405401) else (if c < 237 then 0x3000041c180206c04030942e0012020520300004280001800000402000021d0d0d82200 else (if c < 238 then 0x90600e2804070380b088100012070100e570307c8218230603e02330100001000581400 else 0x87c0203020f82e610092002070085422000183400000f8a8181e02010020d090389e2c))) else (if c < 241 then (if c < 240 then 0x4806110680c0000058100206040380e021289004000580000130b85c04020b80c7a0b else 0x700c1e0b0600004140102c021e0183c0000068001014020200005000341a06000840c03) else (if c < 242 then 0x104c8215080212e010083400060103000000100c68050a8042a02000081e03140142600 else (if c < 243 then 0x18500402000700005068441a0100828060208000184b3881c0204070080a1d0a01c0610 else 0x9008001a0502c0c0a0c860002f000380640038000c300b80c0418058000c01018380a23))))) else (if c < 253 then (if c < 248 then (if c < 246 then (if c < 245 then 0x300c0e1a040081e05020106e3a230186000018581a01071404c08000a424010b800240c else 0x5800340a11800021b0480018131381c0402000100206038088e020b02824150884c001f) else (if c < 247 then 0x48b05c010203c0213090286a1c01098bc020001c001f0086c14060383c0603020100236 else 0x858120004018020b0706018370610800000000c240d000001000028000c1d040c80000)) else (if c < 250 then (if c < 249 then 0x1701004101480c000102a240e070c80000001706800050c8580c0c018000a19168144c06 else 0xac88261780c0601180001405208184c4f0000004030e828020d0a82408060002c8227) else (if c < 251 then 0x50080a390083c0008000101e04028ac0220080084e170103406240006c0602038006005 else (if c < 252 then 0x18000203020280c03030000029008042e01030cc7a3a0c8444205078284003140100a06 else 0x28305602000004c0a06800082a0000414371f8480c09008f40a011081c00171303c8027)))) else (if c < 258 then (if c < 255 then (if c < 254 then 0x21898004f0302c140a078186e04080200011098401c1814010500202010000800004042e else 0x4012040104406490081404440780450000a844300c081e00a0000008000b030180400) else (if c < 256 then 0x81426260281400070a8388003020040011048086403158c420080a000201b000582401 else (if c < 257 then 0x60801c31008315007000006c07038080a0202018a0023380c160400008040504828000e else 0x178241a030d830220103008000a010103e16238e4a4070001c8003028080e21010580204))) else (if c < 260 then (if c < 259 then 0xc460a0102014050084c00050080c06001c828261b010f430420a85c140e090381820 else 0x58000a1f03948141d0b8000402498280025101103400030003400048001a1102854020d) else (if c < 261 then 0x30546605010080006350109202000a80c2a0081092040e00048060000406000010c3826 else (if c < 262 then 0x8c48a10008ac6c22000001603030005004008049c01008280002048083202010180800 else 0xe87c040321804040e1f0000e000183824090382462500004808280380c0011008080201)))))) else (if c < 282 then (if c < 272 then (if c < 267 then (if c < 265 then (if c < 264 then 0x28008022000340000008cc10040d0e004260287c64190601c260c0a0200241088102e05 else 0x201808053904c0e03000c01000178858a000e02c10030000800040202c1c16008381400) else (if c < 266 then 0xf0247a2b5581c32480214c4600378180240010000a01020781a15042e02205028d0020e else 0x794402040f0904c210d05096091801c100d140600c2a01838020000004aa32048000001)) else (if c < 269 then (if c < 268 then 0x381c1e090e0180c0d07028962b000701608188004e1300021304c1609472070a000002e else 0x180002170081000048041855058346029009200c0100014001942844a002018b0ca15) else (if c < 270 then 0x18818100003834a2140000452042b010000c00014a406108080018010140210168000222 else (if c < 271 then 0x28b46c08118180201190180004008081607028241c0d0e028224d000741801000100201 else 0x3010023d0601c14191007010160380c0200050dc040002000725940058021904014142a)))) else (if c < 277 then (if c < 274 then (if c < 273 then 0x18240c4211910000e0106ca42700808a61900008100200010440b0f8481e001e8383e0e else 0x238005e00061806c03040100000138182e440801402020606c0000018340e0504810140b) else (if c < 275 then 0x100841006118103000000801c030f0003a3700028000102008222a04040140a028000a08 else (if c < 276 then 0x28204c02814040f0285c2c301381816031005c1e300e8042202000a014030c898020d else 0x1882c2e000115006231a004000e06804b8010181888010280862130309016270181c981b))) else (if c < 279 then (if c < 278 then 0x48000007018006c30010340005050043c190100800010580c1229000001014230000400 else 0x484408220101424310d8d046000189818050083806010c8605a23038181e16130003214) else (if c < 280 then 0x4e83810061400c001e148280a02000186e1d160387c0625004142300044001e0181c0004 else (if c < 281 then 0x285008070e80814061d84c6e1907010280b0008012000e8640a0e02018400c05890001e else 0x10a40a000007032012b804060a040280006088000800000140a2e2e8300c2d000201401))))) else (if c < 291 then (if c < 286 then (if c < 284 then (if c < 283 then 0x40244603000180000078a03e00090240006050180e0b02818c4280b8400e6700000020f else 0xa2c1613020582a160e85466000aa400e060b0102e07018001c05030a42e01030101868) else (if c < 285 then 0x901432080a03c0414058582c130080c1000000080c0a0c87442020200032021b198002a else 0xd814000f1380c0c0908008000501000121003024000c0c8805202010280207100780408)) else (if c < 288 then (if c < 287 then 0x303000141f858040f0000800000381056082301456090a9b00a160080000060d0180000 else 0x814ae0302850480e0209c0a01080a40400118240600010cc320a0085c0e16018381007) else (if c < 289 then 0xc00016140200010020f004241d06050000000020c20a190081410081e8020d0203c0217 else (if c < 290 then 0x8000a030201c000008811b03d008f8120403838200001800240a0c080ce250e8400017 else 0x14000e11828080d0a018080d000002e030000800000480402010080c0e11238040c00)))) else (if c < 296 then (if c < 293 then (if c < 292 then 0xb040040522000020b00800040004024ba000180002162a8045e03050000221028141401 else 0x90400e041400020180002822190c05c3a000780000171582009021a800020e0f810e621) else (if c < 294 then 0xd90800000180c380314068340402808120000034021b010080e06030004a001e084064e else (if c < 295 then 0x5c0804040343e0e0a168422e03a503e0800164000200ab8b22a060480046050f41608 else 0xc000180000050081004ae1b03400020687c46101005824040e000000029868002d))) else (if c < 298 then (if c < 297 then 0x39c49c3203004320904894360000028203c12850060000000003302aac02260086c2a01 else 0x649c140d0140a0203034920a001040407081205c0c0082c08012f8250e01048248e12) else (if c < 299 then 0x48409c0200004c011048787a5e560600004010a0000106824f40f23054400d098ac060f else (if c < 300 then 0x128546202100002601070c80c170b84848007c804042b080580e1c050e0ac011e0093205 else 0xd0001c601603804043f000100601))))))))) >>> (9*(i%32))) &&& 0x1ff
def leafT (i : Nat) := let c := i/32; ((if c < 509 then (if c < 254 then (if c < 127 then (if c < 63 then (if c < 31 then (if c < 15 then (if c < 7 then (if c < 3 then (if c < 1 then 0x6040820a04004060808302080820658003020c40302041000204181 else (if c < 2 then 0xc185060c0840e04101020c18006140060404181020c1830014181 else 0x2081840e040820c04181060c18202040010414101040c0810008081)) else (if c < 5 then (if c < 4 then 0x60c18604000850000083060c0870204083001c0820608183060c002 else 0xc0810a0408302041870204181061410206002030a0c0830604083) else (if c < 6 then 0x20c08102040810610101020428002000810404183000c0810608082 else 0x2040810204181061418404081810220080001418500180820000283))) else (if c < 11 then (if c < 9 then (if c < 8 then 0x60c0030208181020008c02081810604301000c18106001830204001 else 0xc0810200181040430002040010608003040410106081810214085) else (if c < 10 then 0x2080850204181060408600143800204080060c10036040800404185 else 0x80830a0408102040010610081060c0010604a010014281021c083)) else (if c < 13 then (if c < 12 then 0x208003020c083000018600040020a18101040410102180810404283 else 0xc0c083020c081020c083020418102042811204081020c1030204102) else (if c < 14 then 0xc101020c00306040810204083020c183022428200000830c04187 else 0x60c081080c10102bc08306040810400185080828106000850404083)))) else (if c < 23 then (if c < 19 then (if c < 17 then (if c < 16 then 0x20c1810604081003c08002000000a0010306040810214181060c101 else 0x2000830c04106020408002040030204284041418306001810420005) else (if c < 18 then 0x61408006040830a0c180020c102040c30206040820204081020c083 else 0x21008102001030804081020c181060018206140820604181080c085)) else (if c < 21 then (if c < 20 then 0x20c083000c185020408302000820204104021c18306000810408081 else 0x20c182000418102040830210281020408102041010604083040c301) else (if c < 22 then 0x6901810404101022818100040000214080020808202001000004101 else 0x604081020c007020c284020c10308040810c0c08004041810604081))) else (if c < 27 then (if c < 25 then (if c < 24 then 0x608081061418c02082850600103000408104041030204e01000c081 else 0x60418402040011e0408102040830004102000c30402040830c04080) else (if c < 26 then 0x40c0830a1400202041820804005060c2800004001000c1830808001 else 0x20c0870804181060c08706041010204283020808002940800204083)) else (if c < 29 then (if c < 28 then 0x4081030600182020850706101030608181020410502041000204180 else 0x20c18102000820804082021c10006040810204083000c085040c082) else (if c < 30 then 0xa001810204083020408202040030200086020808106080810404084 else 0x600081020400204200800214083021410106001810a1c2800208105))))) else (if c < 47 then (if c < 39 then (if c < 35 then (if c < 33 then (if c < 32 then 0x2141830a04081060418108000000608101020400302040830220083 else 0x61c003100c0830a041810a04701020c18202001030408083000c082) else (if c < 34 then 0x2040810018003020018302140810204181040400102001830204083 else 0x4081060c08106040830208300020028106080810c040820610182)) else (if c < 37 then (if c < 36 then 0x4043010204104100c18100141830204183020408114140830ae0183 else 0x42850604100020418102040810608083021430502040011404082) else (if c < 38 then 0x40c1020404103060808300002810604005060c00306080810a10081 else 0x204082000c0820604081020c105020408106140030208082021408a))) else (if c < 43 then (if c < 41 then (if c < 40 then 0x400081060c182020c18102041850e0c082060c20100040850e08081 else 0xa0c1000a000030204001060028102040830604085020c0010604201) else (if c < 42 then 0x20818602141010c0428104040000008081020408204100830204081 else 0x2001822200183060400506040030010080061c18100000811004183)) else (if c < 45 then (if c < 44 then 0x3020004080020008002083810204003020410202041000204201 else 0x80c081040c081060808306000830204a810210104020c385020c080) else (if c < 46 then 0x20c081040c100020008100040810608082020400302041800a0c083 else 0x204081060c082020c0820a0c1850204081060018000042810404103)))) else (if c < 55 then (if c < 51 then (if c < 49 then (if c < 48 then 0x204181000828306182810a0c1810010082120c002060c3010200106 else 0x40808106041810400107020c181040c001060c082383c1030204182) else (if c < 50 then 0x6040830c040810200001060c18102000840a0008900081010604085 else 0x214300060c2810204007020e40302181800408001040c1850a00084)) else (if c < 53 then (if c < 52 then 0x4283020408100041050200182020c201000808306102000204085 else 0x20008302040020e14001020c0010204182060c28106040020200003) else (if c < 54 then 0x614001060c181040c002020c2820404081000c1010408083040c083 else 0x204081020c082020418304040840004081120c00106041830204081))) else (if c < 59 then (if c < 57 then (if c < 56 then 0x60c1020a2010100040850200081020810102002810630183040c182 else 0x208083040018302041000a101810600182120808302080810c0c180) else (if c < 58 then 0x60c0810e041010a04080020018102141020a080850604080060c081 else 0x4081810610183000400002040840c040800208285040c1810604401)) else (if c < 61 then (if c < 60 then 0x2080810208181020c1050204183020808302180810004101020c080 else 0x80808106000830600302040808c0604080040828200040800204181) else (if c < 62 then 0x2080070000083000418102000010604101020408202040810c08100 else 0x1408104080810204083022408100040810a0c00304041800a0c083)))))) else (if c < 95 then (if c < 79 then (if c < 71 then (if c < 67 then (if c < 65 then (if c < 64 then 0xa08102040000302080cb0404100040818c080d68506080810204184 else 0x830102501850404002040c181020c00302000810204181000c283) else (if c < 66 then 0x208283060c00104080010400003020418302041810c040800a0c183 else 0x20408202041020200081020c1020604083000810208140840004081)) else (if c < 69 then (if c < 68 then 0x60408302040bb02080800a10103020c083040c081020c1050204101 else 0x204081040c003021c1830a04002020c00104040830204001020c180) else (if c < 70 then 0x180c3810a10083020400106080830204203000c18302141800a04082 else 0x600082020c1800000182060418106041010400003020c1980204082))) else (if c < 75 then (if c < 73 then (if c < 72 then 0x6040820c044830404003080400106080800604181040c0011010185 else 0x20c081020438500042140204181020c0820204184040c1010e14280) else (if c < 74 then 0x600081041c681040018104040010400302080828302041820204103 else 0x20408102041810a0c18306040800004205020408104080830604181)) else (if c < 77 then (if c < 76 then 0x2081810201d81040400106042011004083000418106000821004181 else 0x2141050200083040400102146030204102020c0830a001830204081) else (if c < 78 then 0x2001810c040810800001020c1012a00083040c0820c040830200005 else 0x21408300040800604101022408002040830204083000c105020c381)))) else (if c < 87 then (if c < 83 then (if c < 81 then (if c < 80 then 0x4000040c0830604183060c1830a08182020808106080810604082 else 0xc041810218005040428006001030004186020408102040030204084) else (if c < 82 then 0x204183020c182040418102081850614186050c182020c081040c183 else 0x20c082021000102041010204083020c08e060028004046010614182)) else (if c < 85 then (if c < 84 then 0x40830a0408510081020400181020c181020c00602001850028083 else 0x40c081020408002041830404181061418006141830808185020c103) else (if c < 86 then 0x20c08104083030c08100061408100080820600081040c080020c085 else 0x80810204001040800302040040608081020408300040850014182))) else (if c < 91 then (if c < 89 then (if c < 88 then 0x40408102042820204080040c006040c000060c18102040020214081 else 0x2080820208082041408602040060620180021408102040810204180) else (if c < 90 then 0x4080050604581020818002083010604001020408104040820200007 else 0x4040810204184020c081040c0010604186020c28d04042800408281)) else (if c < 93 then (if c < 92 then 0x200100060c001060808106041830604100040c00002080010604184 else 0xa04081060c083020c004040808100040800604101060c1800014182) else (if c < 94 then 0x41810214080061818102080020004004000c0830600001001c185 else 0xa1818506040010a0c0820204182060c082040c081020c183020c382))))) else (if c < 111 then (if c < 103 then (if c < 99 then (if c < 97 then (if c < 96 then 0xc18106040810c04000020c2810604082020800102041810208002 else 0xa040810204081060c0830204281060410202040810608002060c080) else (if c < 98 then 0x20c083020408104040810404081020c082060c0850408281060010c else 0xa30100020c0810a040850a04081021418108040820004301080c083)) else (if c < 101 then (if c < 100 then 0x180810a0c001060408302041800608103020408002e4083060c081 else 0x40c080060c105022010006000830204302020808500080830204181) else (if c < 102 then 0x20018004181030204081060c0850210103020c38106002030408081 else 0x2181850a041810200184020410302000810a0800a0204202060c303))) else (if c < 107 then (if c < 105 then (if c < 104 then 0xa040030408081020c1030608281060418200040830a380850004080 else 0x2040811014181061c0030a200030604200040408102041020404101) else (if c < 106 then 0x182020c101040808204040820a0c0010008087060c0820014083 else 0x2081060218080020c0800804082020c081001018a060c001020c282)) else (if c < 109 then (if c < 108 then 0x40c11b020018604082810404181020c187040c1820008101000c101 else 0x4300810204101060400102040810208082020c102020c0030204181) else (if c < 110 then 0x810102040830204385060808302042030200181080c001000c180 else 0x20c1820614182060c28202041810c00181020018106001000608105)))) else (if c < 119 then (if c < 115 then (if c < 113 then (if c < 112 then 0x800083000408306041810204182020c081020410006042800204080 else 0x200080020808102042810204007060c18006040800608103020c183) else (if c < 114 then 0x2000830604081020c18102001850604084060c08102040830008081 else 0x2040840a040820a08181020410a020c08206041050a040810010082)) else (if c < 117 then (if c < 116 then 0x408102000010604105060c083080801b0a0418102041810004080 else 0x80408306040830404101020c0850404083021818100140830608081) else (if c < 118 then 0xa18181020400002041810a040830204081020c18002001810c0c189 else 0x21010102041020204081060008702040810a1800100040810208001))) else (if c < 123 then (if c < 121 then (if c < 120 then 0x18106084830204181020c10e06000800604003020c1000604002 else 0xa381850400101020c281020c08306040800404081060c1820428085) else (if c < 122 then 0x2141830a0c184040810010140830600283060018100042830a08186 else 0x20418002080010004002000c082040418102040830618083020c080)) else (if c < 125 then (if c < 124 then 0x400081020408302041820604082000408200041010604383040c181 else 0x6140811804085020408106040810404081020418300142000210001) else (if c < 126 then 0x20c0870020082020c0020404088020c101020c0810a041810204181 else 0x6082010204082060408102040820404003020808300580850604101))))))) else (if c < 190 then (if c < 158 then (if c < 142 then (if c < 134 then (if c < 130 then (if c < 128 then 0xa1c08202040a9060408608040800204100020000204000050a0c301 else (if c < 129 then 0x404088060400502040850408182040c08106001020a0c0810200101 else 0x60810104041020204081060410202104811c180830c041820614282)) else (if c < 132 then (if c < 131 then 0x2040821e0c280060018b0404185020018102040860c083810604203 else 0x40418102041010a180010a04183060418302040850600083060c183) else (if c < 133 then 0x600081000c083021418102040810000083000408002140810404083 else 0x404285020c181000400006040861808181040818106041830a08081))) else (if c < 138 then (if c < 136 then (if c < 135 then 0x2141040a20081020408000040810604201040808304042810608081 else 0x2080000404180080c08302080810214081020408106100810204101) else (if c < 137 then 0x60408544001830204303040c0800204183060c08502040810204083 else 0x204183060408300040830208182080c080000818502080810804081)) else (if c < 140 then (if c < 139 then 0x187020c181020c0800e0c183021418108140851c040800204101 else 0x60828300040010000081020c001020c183060c0820208100040c181) else (if c < 141 then 0x800083020409b02080850610181060c181040c0830a181810604181 else 0x604083020c081020018100080020604180020808102040810614381)))) else (if c < 150 then (if c < 146 then (if c < 144 then (if c < 143 then 0xc1400100002000220083000c281040400500080810e0c083000c401 else 0x20c0820400006020010304080810a08001060008106143810004103) else (if c < 145 then 0x408081000c203020810102041830604101040818106080810004005 else 0x20c00206041016a04083000c10306041820414000021c0030200182)) else (if c < 148 then (if c < 147 then 0x40c601080418206040810604081020c380060018102040810608083 else 0x81810204182020408202100010404000060410206101830204082) else (if c < 149 then 0x2041830004004060468000140810604086020c08106080020604082 else 0x8102080810402101040808202040010414081060c2830204085))) else (if c < 154 then (if c < 152 then (if c < 151 then 0x20c0817e14003020408100041820004081060c101020c0830404183 else 0x60009c0804083020448302000810804081060418206040860208081) else (if c < 153 then 0x20818002140800a0c08302041000208083020c18202040810204502 else 0x60c08306000010a0c085040c18404081030404102020c1010804002)) else (if c < 156 then (if c < 155 then 0x2080810208101040c081021810202041820604081040c182060c082 else 0x4081020408102100810410403000000306040850c040810404180) else (if c < 157 then 0x210302020418202001030608081020c081000008006502840200881 else 0x4000060c08106040860604103020c1010c0c18102041020604080))))) else (if c < 174 then (if c < 166 then (if c < 162 then (if c < 160 then (if c < 159 then 0x2040010204183060c083020010102041030204283020c1810a00083 else 0x40808100200820200182020c282060408104040810204003060c103) else (if c < 161 then 0x60c080060c10106041870608081000c1000c04181060cb030204083 else 0x2043850404083020008302040810008117060410104040830204080)) else (if c < 164 then (if c < 163 then 0x20870104041000608101060c082000818500201810208a010404087 else 0x60008202025020c0c18304041010208382020408202041820204106) else (if c < 165 then 0x208202020c101060c0810a04181060000302040830600082040c083 else 0x20418106040800604181060c0810604281000c10106040820404181))) else (if c < 170 then (if c < 168 then (if c < 167 then 0x604081000000502140810214180060810206042000a18280080c282 else 0x208081020c08102040810204081040010102101830c04083040c202) else (if c < 169 then 0x4080810404001021820102040830404080020410102041010604000 else 0x6080810804085000438600040810614081020c000020c101020c081)) else (if c < 172 then (if c < 171 then 0x40408106040000204181020c40106001030408081060c1850604081 else 0x20400200140830204100180c1810a00001020000502080050008181) else (if c < 173 then 0x10041830604001020c2800604083020408200141810c04103060c183 else 0x40428300040810004087040c003000c00100000830e040010008183)))) else (if c < 182 then (if c < 178 then (if c < 176 then (if c < 175 then 0x20c10106041800404081000c182021400302040830a000850604087 else 0x60818106103010204081000c0810408083040008206040850204003) else (if c < 177 then 0x604181020408306000800a0c083020c381020418506004030400080 else 0xa201850204084062010302042010404081060410202040830e04001)) else (if c < 180 then (if c < 179 then 0x2040820204016020c0030a000010418101060c2820a040050604103 else 0x4041850004182060408102081010004103080c10118003800208082) else (if c < 181 then 0x6040800e08083020c0010208287080018702040010208181060c081 else 0x20c280020420206043821e0c30006001820618180040c083040c186))) else (if c < 186 then (if c < 184 then (if c < 183 then 0x204105060828a060408306000830604081040018100040820408282 else 0x20418110141810200081020c3010610005020800102040030a08101) else (if c < 185 then 0x20c1810204083020c183060428304041810c04002060c3000204100 else 0x604181060c183060c18706000010604003000c10002041010618083)) else (if c < 188 then (if c < 187 then 0xa00000020c0820200103000408300041010608006020c2810c04105 else 0x204081020c0800410203020048606040800c04180041c080020c181) else (if c < 189 then 0x20018102140811004182060c083040018104140800a04182020c102 else 0x20c081180808102002010408085020c082380418100041831004703)))))) else (if c < 222 then (if c < 206 then (if c < 198 then (if c < 194 then (if c < 192 then (if c < 191 then 0x400181060428102040810400101000c0830204101040c1810004183 else 0xc040890204081000808308040830c04201000c18100081830204085) else (if c < 193 then 0x60c0820214100060c083020808106041050600183061c0020a0c083 else 0x4040870204301041420104041870204100020418106040050204081)) else (if c < 196 then (if c < 195 then 0x120400106000810200183021800100040810a0418102001030204081 else 0xa000810204081040000104081000200081060408102041810008103) else (if c < 197 then 0x21c101040c083020018102040850208181080418002081810204001 else 0x20408302000020c0418508041810410081060c00002041830218180))) else (if c < 202 then (if c < 200 then (if c < 199 then 0x40810210082040c081020c1030420083020008304082830210081 else 0x60c084000c103063810102040810604403020c08102080810004281) else (if c < 201 then 0x41030214101080c00506001050214281020c0010200081040c001 else 0x20c1840204000040c0810604185020c011060408304040851404080)) else (if c < 204 then (if c < 203 then 0x60c083060c283060518204081800404283040c08002041810208083 else 0x60c08002080810a0818104040830408382020c10114040830210180) else (if c < 205 then 0xc0010004185061430302003010204083020c080031c08e080c081 else 0x2040830200303060c0000604000060c0830600005020008a0414081)))) else (if c < 214 then (if c < 210 then (if c < 208 then (if c < 207 then 0x214181040418102180810a0408102000810a0400102101050208102 else 0x204182060010008040810204081020c283020c08202040830004185) else (if c < 209 then 0x200083020c081060408302040010204081020408106041810004181 else 0xa0c083060c080020418300040820008081020400102081830e0c003)) else (if c < 212 then (if c < 211 then 0x60408302082810204100040418306042850a04080020c1810200002 else 0x404081000c08202000830214085020418106040860e080830204081) else (if c < 213 then 0x2042810a1418102040830204081061018302040060004301020c282 else 0x418183020c08c0200301060c183020c087061408302140820218181))) else (if c < 218 then (if c < 216 then (if c < 215 then 0x60c0810400081020c18706080830a0c1010200103060c0010204081 else 0x80400302041810a34183060c1811810181020c000020c0830404085) else (if c < 217 then 0xa040010008103020c0020608181040c300060400200081830204001 else 0x6080830614083020c1820e04083060c2810218083060c08c0604181)) else (if c < 220 then (if c < 219 then 0x210083020428202040830208080040c0880404001020c0810a04301 else 0xa04185060c0810a0418800040830010183060418104080800a0c080) else (if c < 221 then 0x208182021c001061408506040820204085060c10536000030604081 else 0x208000020c1810614081020c081020008202080810a040c6001c081))))) else (if c < 238 then (if c < 230 then (if c < 226 then (if c < 224 then (if c < 223 then 0x2040810004081060c18300141013404083020410304041800604082 else 0x418080041428504080810008183060c002020c181020c0010608183) else (if c < 225 then 0x4081000c18404000830004181040418306040810628081060c081 else 0x20c20102041820204181020c181080c000041020302040800408085)) else (if c < 228 then (if c < 227 then 0x20c0020608081020c283040818100082810a1c18602041010400001 else 0x408083040c1830a0408302141020a0c180000808600080010004083) else (if c < 229 then 0x60410000141840404283040c101020c2810604080000c4820404083 else 0x21c08106041810a0c08106041810204183020418302086030214181))) else (if c < 234 then (if c < 232 then (if c < 231 then 0x40800006042030204082020418102081030408102020c006020c181 else 0x204101020c10102140010c0c1830a04181020008206100830200281) else (if c < 233 then 0x204082060c005020408106041830804701000008300040830a00081 else 0xa041010204003040410202081830204003020010000081000400103)) else (if c < 236 then (if c < 235 then 0x6040810404181020408204040801e04101040c18302080030804183 else 0x400080060c0810c0c0800008082060c381040408002140010608104) else (if c < 237 then 0x4101040c08202040810a040020014001040408104082810e04088 else 0x20c00102041810e00000020c0030404281020870304041890208081)))) else (if c < 246 then (if c < 242 then (if c < 240 then (if c < 239 then 0x60018102040810200003040c202020400012042810204003060c182 else 0x600103020c0850014181020808600141810e0c10002080070c0c18e) else (if c < 241 then 0x400102020c080000c18004040030208101060408302181810400081 else 0x400185000418502301800008181060810302041020000081040c180)) else (if c < 244 then (if c < 243 then 0x2001820a040000a0010304480850208102020c00202041010414181 else 0x20c0800204181000c28406140820200081041408104001010604001) else (if c < 245 then 0x20c0800804183020c0810604101060008002240800000086020c082 else 0x40410106041800804081020808002141810204081020c2020404083))) else (if c < 250 then (if c < 248 then (if c < 247 then 0x6040000204181000800302041840804282020408300000850218080 else 0xe0c283060008306041070c080810808080060c181020c1830204081) else (if c < 249 then 0x40c085040c18102041030014107020c18306000810408283040c081 else 0x4041000a081010a001830404083020c405000810302041800200083)) else (if c < 252 then (if c < 251 then 0x6040810604087040400a12080810200081020c181020c1820804103 else 0x10080020c080060c181020c0810404104000400100040810208081) else (if c < 253 then 0x60c1880604182040808306041010a04081040410102001830208083 else 0x6081830200185040808106082800204007020c10102141820208102)))))))) else (if c < 381 then (if c < 317 then (if c < 285 then (if c < 269 then (if c < 261 then (if c < 257 then (if c < 255 then 0x80c000020408202041810200082060c00002040820004003080c10c else (if c < 256 then 0xa002820c042832200101060018002300830010081060c080020c103 else 0x600082060548106050820604182020c381060818006040810218102)) else (if c < 259 then (if c < 258 then 0x20c1810004180000c1800604281001010302040850a0c1030420081 else 0x608183020448300040810c1418202081830404082020c0850204084) else (if c < 260 then 0x20830102041850e0428102040010404181020c18302041800a0c083 else 0x1000201000c1810208083020418202140030214107020c1820608083))) else (if c < 265 then (if c < 263 then (if c < 262 then 0x2041810204100020c0800604000021c4030e04080020c0840c0c182 else 0x20c0030200103020018306044030204081080c10000000820404085) else (if c < 264 then 0x6041010408103020430008001830208003040c1810c180816604082 else 0x200201020c081060c18102140030008081080418306401820418181)) else (if c < 267 then (if c < 266 then 0xc0c283080c0830404082021800104181010004001000c0820404282 else 0x404005040c183101c101020c100060c081020c18300041810208081) else (if c < 268 then 0x6002830c0c08102140860404205020418302040850004083020c183 else 0x21008308000810600301020c08302001810208080000c083020c181)))) else (if c < 277 then (if c < 273 then (if c < 271 then (if c < 270 then 0x40c30204080800e0c19502082820204083040c08204041810408081 else 0x20c083060c081040418102042810200080020408e0204081000c081) else (if c < 272 then 0x1c0c1820a00182060418106181830a0c180020810104000800e0c103 else 0x208180060c083061818302001090a040810a0430102040800204189)) else (if c < 275 then (if c < 274 then 0x600185080410506080810604103060c080000418104140010a04081 else 0xc083020408306042810208081020c085021410108140830604081) else (if c < 276 then 0x41010600181020c08202040810e040010a08000060c0820604081 else 0x20408002041010a0c70008080050004101060418102000810004281))) else (if c < 281 then (if c < 279 then (if c < 278 then 0x604005020c081020c080020008106086830414105060c0800208001 else 0x41010604081064c0830604080060c081020408102041810208301) else (if c < 280 then 0x604081060c08302040030204181060408104040810a040840004303 else 0xc14082000c1040210181360c0000600081060c00306040810204301)) else (if c < 283 then (if c < 282 then 0x2001830210197020c084020c1810600101020458104080010204001 else 0x20c185040c0820204083021028102000820204283020c103020c003) else (if c < 284 then 0x60c00106040820a0800100041850604081020c18006041810604000 else 0x204083061418104043020a001830204180060c083100c0830404083))))) else (if c < 301 then (if c < 293 then (if c < 289 then (if c < 287 then (if c < 286 then 0x2001800200080060418100040010608081020c4010204081041c080 else 0x20408106000810208180060c60106041020a1408106080010204283) else (if c < 288 then 0x60028102082080204181040c1010204003060808304140830604282 else 0x6041880a1408206001830a0c2010400181301418102000810204183)) else (if c < 291 then (if c < 290 then 0x20c001080418002001810200281000410106041830204083040c281 else 0x20408302080820608181060c281020418102140ab02040830014080) else (if c < 292 then 0x2040820c0c083020838110040050408281040010102081030600082 else 0xa0c181020410002002000604085000c18804040000214180040c201))) else (if c < 297 then (if c < 295 then (if c < 294 then 0x4041817800082020408102002810208185022018302080800e04205 else 0x2040010404083000810304000010a00083060c0820204001060c080) else (if c < 296 then 0x200180020008106003010204081020c1020a0408306200820604083 else 0x40c0830604100040400206000010204109020018102042010220181)) else (if c < 299 then (if c < 298 then 0x40408306000811e101800608080020c1070208101063c0840604182 else 0x804101020c0830204083060c101020408102040810c000810214081) else (if c < 300 then 0x20808002040010204101020c1850204081020800502041820000183 else 0x20c08104041010404083060430102080820c0010206000810200003)))) else (if c < 309 then (if c < 305 then (if c < 303 then (if c < 302 then 0x6081800404081040c880060c180080400306041830000081060c081 else 0x100408000001800404180020c1830a043000404083060c0830604381) else (if c < 304 then 0xa140060814081020400102082810608101040c08206041830a04101 else 0x800101020c0800404183020418304040030608081001c082000c003)) else (if c < 307 then (if c < 306 then 0x40c282081818208041810620081040c1830408101021018106041bb else 0x6040810208101020c40e020c283020400002080870c043020608181) else (if c < 308 then 0xa10205061c083060c08102041030404083020408c040c0030200181 else 0x60408106080811800080020418b04040810204083000c2810404086))) else (if c < 313 then (if c < 311 then (if c < 310 then 0xe141830408083060800102081010208102020c08000040810610081 else 0x6080820a0010202040810204081060408106200820a180820204087) else (if c < 312 then 0x40c10138000850200083041808002040820408086040c0830408201 else 0xa1808000140800608181000008104081c2080c101020c1810a10104)) else (if c < 315 then (if c < 314 then 0x204083020410302081020014000020c00100042800a04081020c182 else 0x804081021418502040840404603000c28302081820a08003020c085) else (if c < 316 then 0x4001820204000100c0010204001021c2830204103020c2810208181 else 0x20800100084020008186020c2000204082080420406041030204102)))))) else (if c < 349 then (if c < 333 then (if c < 325 then (if c < 321 then (if c < 319 then (if c < 318 then 0x20c1840600081040810504040830214101020c180060c1800208082 else 0xa0400006042850200002063c2840600080060c00006000811804182) else (if c < 320 then 0x4180080c180020808306080000400082020000300000810004283 else 0x2081010218882040400002040850408183000818102041010404101)) else (if c < 323 then (if c < 322 then 0x6040030204183040c0840a0400302041810604181060c0810600100 else 0x204083020418202080830e0418100080850404101060c0830004087) else (if c < 324 then 0x80408102043810c0408808180820604083000c0800400081020c080 else 0x204086021c1030400281040c10302101030604001020c2810604182))) else (if c < 329 then (if c < 327 then (if c < 326 then 0x20c28104040820400085020c4810200081022018200040010a10081 else 0x81000c081040c1010208000060c182021020302140850614005) else (if c < 328 then 0x60400106041820c18182020820002141830a1c08606041070a0c081 else 0x404081020c00100040810a0818006141860c04001020c0060404081)) else (if c < 331 then (if c < 330 then 0x4042830208280020418102080810204081020c0810a04083060c085 else 0xa08186040c1000018181000c00102082810a04103060c0010614081) else (if c < 332 then 0x60408102041830a04100020c38300141810a04203020c001040c180 else 0x208081040c089021c00500081010208083020c08206041850210001)))) else (if c < 341 then (if c < 337 then (if c < 335 then (if c < 334 then 0x60428102081830a040020250081060408304040800004001020c180 else 0xc182041c1050204083020c083020010e0004081020c081040c083) else (if c < 336 then 0x400081021408508081810a140800494002020c18502041810200083 else 0x60c183100008006081010204081000c19c041418102001830200081)) else (if c < 339 then (if c < 338 then 0x20c2810604082020808104041810604183060c08106040810608082 else 0x600081060c10102180810200080000c001020828102040000004281) else (if c < 340 then 0x204083000c0030004182020018306041810008100020c1030608003 else 0x4143050204003060c08100100812a04102040008002080810a18082))) else (if c < 345 then (if c < 343 then (if c < 342 then 0x2040000204083020018000040820818106040418102041830604101 else 0x40c08006040810208381060808106040850220181080c085020c002) else (if c < 344 then 0x604083020c18006081850a0c080020c085020018102000830a0c181 else 0x4040010204082060408306002810200101041018602140810200282)) else (if c < 347 then (if c < 346 then 0x818306040810a001820404080020818302040840004181020c181 else 0x20c081026c103060430302041830204181000418104041010204183) else (if c < 348 then 0x40c1820200002100818104000800a04485040c0800c0c4010208001 else 0x2040830200083021018102041020608081020c1000a040070014081))))) else (if c < 365 then (if c < 357 then (if c < 353 then (if c < 351 then (if c < 350 then 0x1408006041800004981060808502041810604083060c0830e0c103 else 0x60c081060c38504180010e00083040c101060410004040830204001) else (if c < 352 then 0x2081810a041810624281020018104001030a0408302441840208282 else 0x40810204103020420102041051a0c002021400302140830404001)) else (if c < 355 then (if c < 354 then 0x20008104040030200081020c1800208087000418104040024008086 else 0x40850204083020408002080810204101020408310040830204081) else (if c < 356 then 0x81c2850004086021408102040800604103020c08506080880218281 else 0x8041850604080020c081020408000041010804181020c2050a0c081))) else (if c < 361 then (if c < 359 then (if c < 358 then 0x8040820404182020418006041010604481060c1800e080810208185 else 0x41408504001010a04183020c08c080c085060c08106140810a04081) else (if c < 360 then 0xa04081020c08312000810004181041418102040810004383040c000 else 0x204280020c101040c183020c101060c084060410300040830200181)) else (if c < 363 then (if c < 362 then 0x20818004000850a0c103060c08502200830204081020c0810200083 else 0x608081020408202041814404182000c0830208183020c3830230081) else (if c < 364 then 0x604301000c181000c082060408100081050204085060c0810208281 else 0x20808102040831c0c0860204101040418106181020600103020c081)))) else (if c < 373 then (if c < 369 then (if c < 367 then (if c < 366 then 0x6040060a0800302141802204181040c080020828302040810204282 else 0xc000830604006020c18106001010004005024c08102080839404082) else (if c < 368 then 0x4041830a0c081061008106000830610081021418102041010000400 else 0xa080850404081040c00202082820200282020808300081830808185)) else (if c < 371 then (if c < 370 then 0x20408302301820a0410106040820610081061808302041820414301 else 0x40020300080810604288020808302080800c0408102041051408282) else (if c < 372 then 0x60408000004010204087020800302040810808081020c1010604083 else 0x21418102082820008101020c0810200180000c08504000850604085))) else (if c < 377 then (if c < 375 then (if c < 374 then 0x2000830204082040428702040810a1020102041800200183080c084 else 0x20c084020c08302081010004102080c183021440308040830014083) else (if c < 376 then 0x4081060c08302001850a040850414201060800006080800220183 else 0x20c1802804003020c201020c1830614083060c08802041020810114)) else (if c < 379 then (if c < 378 then 0x141810600280020800102180810404181020c0830400084020c085 else 0x2000050204101000028400140800208301040c0830004181120c102) else (if c < 380 then 0x2140000214180060808208501811804001040c182040c082000c180 else 0x400d0214181020c08102040800004180043020504001820604081))))))) else (if c < 445 then (if c < 413 then (if c < 397 then (if c < 389 then (if c < 385 then (if c < 383 then (if c < 382 then 0x2080810a1409d1004085060418102081000208081060c0810608083 else 0x283810a0c2810004081020c18106080060204084020c083060c181) else (if c < 384 then 0x604081001c0010204180060008606040a6040000002040800400002 else 0x808402000820604085020c103060c083020400206141830e0c281)) else (if c < 387 then (if c < 386 then 0x4180810200102180808304000010a0008208700010804404020c103 else 0x204181060428304000040204100040820302000010204281040800c) else (if c < 388 then 0x361418302040820004181020008202040810014281020c005060c181 else 0x2b4083060c295060c0810214283020c70d0a0c081020c1810604003))) else (if c < 393 then (if c < 391 then (if c < 390 then 0x40c1010404001021408b06000810214281060410306040810214002 else 0xc041060204084060c0810c041830204105020808204040810004082) else (if c < 392 then 0x6080800004181000c705080c003040c0830c0808302040830014183 else 0x1050083020c08002301010c0c100000418308081850a041830210100)) else (if c < 395 then (if c < 394 then 0x2001010604182000c1850414185020c0810a040820018102020c086 else 0x20c30002041830208280060c1820200080020c18302040800200080) else (if c < 396 then 0x21410106000810218203020c101060408100040810404081000c280 else 0x4041830614082000418102140830454181060c083020c0820600181)))) else (if c < 405 then (if c < 401 then (if c < 399 then (if c < 398 then 0x2041830c0808104001000400402060c084020c08202040830a04285 else 0x4041810008103045810306040851c04081020400108140830608001) else (if c < 400 then 0x20418302040870a0808102141840204184040400100040030498101 else 0x819b02040810004003020808306040830a080810410181020c101)) else (if c < 403 then (if c < 402 then 0x41010600186020008202081820204081002000204040810004105 else 0x2080800204203020c1810a0c181000c18006101830204085020c080) else (if c < 404 then 0x2041810204181020408608001810a04181060c20002141810208087 else 0x8103060008300040a404041010210181020408304000840204108))) else (if c < 409 then (if c < 407 then (if c < 406 then 0x40c081000408004041850e04182021808506041810c001020604281 else 0x20c2810614102060408504040870208284060400302200830210203) else (if c < 408 then 0x214081020c001060c18208042020600181020408302041810404180 else 0x20808106080810204181020c006020c1030c0c08302000820a74181)) else (if c < 411 then (if c < 410 then 0x40c1010204601021c181060c1830600081021c102000c181020c083 else 0x60408102041060a0410200040800e04081020410104080810208381) else (if c < 412 then 0x4000010a0c185040c203020410202041010008081040c10502040bb else 0x21410100041800208081060c003061408006041010208001020c082))))) else (if c < 429 then (if c < 421 then (if c < 417 then (if c < 415 then (if c < 414 then 0x40800404303060c18302001030004001040008100080810208081 else 0x6040830204181020c081040400106041820e0408206e00810200083) else (if c < 416 then 0x60c281023c0020604007020c182000008100081030404183060c081 else 0x60c1000204080020c11c020000206041071804400006cd810214082)) else (if c < 419 then (if c < 418 then 0x60c187020408502042810204082060c1050214181020c0830614080 else 0x40c1810208280020818202081010604083020c08006140830608183) else (if c < 420 then 0xc0830404083060800502140810200083040400106242051014102 else 0x20800300040820604003060c18206040000638180020c0870604101))) else (if c < 425 then (if c < 423 then (if c < 422 then 0x20c003020c280060c0820204003020008502081810014080020c201 else 0xa040820e000810004080020418104081a6020418202040810204081) else (if c < 424 then 0xc041810210081020c18102041810004181040008102001820200081 else 0x142050004101040400302041810200181060c18400040000604083)) else (if c < 427 then (if c < 426 then 0x404081020c2020a380800204081040c080081418002040850c04180 else 0x8183000430302040800208181060418110042817a001030604081) else (if c < 428 then 0xc082020c0800404181020400308080800004001021c1010214101 else 0x1830210001062408100040810a040830408181000c081060c083)))) else (if c < 437 then (if c < 433 then (if c < 431 then (if c < 430 then 0x20c183060c081020c10104001830204081020c183060c1870a0c081 else 0x60c1030204181000c00100201850218085000c105060c0830000104) else (if c < 432 then 0x604085020c101020c08000102830604081060c08510081810e00101 else 0x60c0830200181061c08102140830204103040418002000c90200081)) else (if c < 435 then (if c < 434 then 0xc040800614083060c000060418200041820408081060c1840204282 else 0x40810302000010004081040c005020c080020810100080830604001) else (if c < 436 then 0x20c2030600083020c0810a042830a0c183020418104041010600301 else 0x4001810404083000c1800204081040c082021418102040810604103))) else (if c < 441 then (if c < 439 then (if c < 438 then 0x20408306040850c0c083060c2800404005000c081580c1810204180 else 0x200001020418106001010204102040408304042030208182060c282) else (if c < 440 then 0x614180060400304040830200081020c081040c183040c083060c007 else 0x604081021418304040810404083020408302041010414181060c001)) else (if c < 443 then (if c < 442 then 0x20c181001c081040408106043000208282021809e061c0850204080 else 0x208002060c082060c20104040810600400020018506181810004001) else (if c < 444 then 0x20419504041830604003020c0050a04081020c2810600283020c083 else 0xa0c0810c00180020408102000810604001020c8820a0c0860000081)))))) else (if c < 477 then (if c < 461 then (if c < 453 then (if c < 449 then (if c < 447 then (if c < 446 then 0x6042830a080010204083021408a040c001020408302180000200002 else 0x20408100040810204087040c081020800706141010204605040c181) else (if c < 448 then 0x20c08306040830c10003040c08732002030204105060c0030e0c181 else 0x40028102081030604401021410104140800204182020c1830204003)) else (if c < 451 then (if c < 450 then 0x410088020c181000c28102002030600082060c201020c2810404183 else 0x60c08102180810a0c00002000820204080000810302040010a04205) else (if c < 452 then 0x414081020c1010204086040018302100831e0408004142810608081 else 0xa0c086020c1010e0408106140810824182060408104002810204181))) else (if c < 457 then (if c < 455 then (if c < 454 then 0x800182060408028042810204207020c001020c08306041810214082 else 0x2141820204080020408202080810214080040410306041810608082) else (if c < 456 then 0x41830414003020810c06040820c0c0811a0c1010004182061c181 else 0x80030e0808502081030a040810a0c001060c18206041830200181)) else (if c < 459 then (if c < 458 then 0x6041020008183000409b000c7830410083020808304000870204002 else 0x204081020c1830204080020c4800c000810204181020c0010204080) else (if c < 460 then 0x2041820204082020c1810200083021010204080830600003020c184 else 0x20c08202040810604101000c0860000103020c10106080830604082)))) else (if c < 469 then (if c < 465 then (if c < 463 then (if c < 462 then 0x6080810214082020c181020808200000840208181060c0030a04001 else 0x400083040408102040000410282020410202041820610081021c083) else (if c < 464 then 0x20c0850004001060818202041810208001000c0820000182020c081 else 0x20c0810204082060c080041410304040830604183040c0830204081)) else (if c < 467 then (if c < 466 then 0x604181060c2820204081020418302041830604080060c0820208002 else 0x1e04082020400110040810000083020c081020018102001010800080) else (if c < 468 then 0x20c18104040810c080810a080810000181060c0812c0c2020c04081 else 0x20c0811604183040408302080830604181020028300001060014081))) else (if c < 473 then (if c < 471 then (if c < 470 then 0xa08181060c00306300820610081040408406040800a04001000c081 else 0x8042030208000040808304041850a0c083020c30106040830604083) else (if c < 472 then 0x6040830208081080c00102048820204181020408506081000a08080 else 0x4001810204001020c08212040330a04089060c10302000800200084)) else (if c < 475 then (if c < 474 then 0x214103020c1020204003020408300041050804082080c181041c280 else 0x20808102081000814083002c085060818702040890a101010608081) else (if c < 476 then 0x4100820214381020c100080408306000010a0428506100010400003 else 0x604181041408102040070200102060c0810608081020c081060c181))))) else (if c < 493 then (if c < 485 then (if c < 481 then (if c < 479 then (if c < 478 then 0xe04201020c1820404181060c082020c081020c0810604181060c001 else 0x604301060408102141830404181040c11c000408210041020c04183) else (if c < 480 then 0x60c381000c20306040000a0c1810208103000c08006041040a08280 else 0x20c082040410202040020a081800210201000440e04041810204081)) else (if c < 483 then (if c < 482 then 0x204001060808706141010204000040418502f80810604103061c101 else 0x6080880424103060c301040420006041030218181060c0020604183) else (if c < 484 then 0x604101060c08102040810614281020c18300040010200103060c100 else 0x824083040010000041820204185020c106080420106000810004189))) else (if c < 489 then (if c < 487 then (if c < 486 then 0xc1020204003040c00302080000204085000c0810a0c0840204082 else 0x60008104040850a0c0010404081020c18102081010a00081040c188) else (if c < 488 then 0x6041010204183020470506000820004080060808102041810218081 else 0x214181060c0812824284060c0810004381040438100041010618103)) else (if c < 491 then (if c < 490 then 0x20c007020408106041030c040830410001020c101040c081000c086 else 0xa001800608083000c18106041810400183000c08502041020604101) else (if c < 492 then 0x204006020c1810404103000c0880600182020c08706001870404881 else 0x40418006040830604183020410302040851800181041c0820608183)))) else (if c < 501 then (if c < 497 then (if c < 495 then (if c < 494 then 0x40418802041820200081020c0830204181020c00304040820604180 else 0x2041010600181080808504001810204103060818504000810204205) else (if c < 496 then 0x208081000400108040810a0c0830408181001408104141851004083 else 0x302020c001040008102040810610182040408104000810804001)) else (if c < 499 then (if c < 498 then 0x2040010634182000c002020410100040830200003040c1850604182 else 0x6080830204100060018002040820220081060c18100001030604280) else (if c < 500 then 0x6080810008082060418400000850604301023c18506081031004101 else 0x20c1830204185020418306141030a0c181020810104000030a04081))) else (if c < 505 then (if c < 503 then (if c < 502 then 0x604081020818102041810a00083060c280000408304040810a00087 else 0xa00181020c28302041010a0c0800604083060408104541830004280) else (if c < 504 then 0x20c10500002830008081001418306040821e0c08102040820230105 else 0x6041010214083020c183020c081020c1800e0008306001810208183)) else (if c < 507 then (if c < 506 then 0x408102020c081000818302000840204082020418306041800608081 else 0x81010218085020408704002030204001060810402041860a14083) else (if c < 508 then 0x204181060c081021008202042010200081060418206180030400081 else 0x80c08006080810210101020c1800004288021028506140810604181))))))))) else (if c < 764 then (if c < 636 then (if c < 572 then (if c < 540 then (if c < 524 then (if c < 516 then (if c < 512 then (if c < 510 then 0x60c081020c285020410400041810804001060018206000800600081 else (if c < 511 then 0x20c000060808302040800208081020c00102140010010182240c481 else 0x60c085021c1850014181061018102041830a1408206141830404081)) else (if c < 514 then (if c < 513 then 0x4100810604081020028706080820c0c683020408102041810408081 else 0x60d9030604085020420006001000600081060c1010204081060c181) else (if c < 515 then 0x4380830204181060400206041050008083020418106041830204003 else 0x60810106081810a0c1810214087020c2810a140850604085040c101))) else (if c < 520 then (if c < 518 then (if c < 517 then 0x804081020400104003850604085020c081040808102100810204080 else 0x604181020c08206001810404285060408500001810004081020c082) else (if c < 519 then 0x60408106080830208280000418102040010614080000c0810604083 else 0x20c0010a04081000800e02080010404080040c081000c1840214082)) else (if c < 522 then (if c < 521 then 0x20400106080800a080050414181060c085040c403060c1020204301 else 0xc140810204183020860302040830010100060c001022c0800004101) else (if c < 523 then 0x2080820204081060408302083030a31e00020408102080820000081 else 0x6040810400080060c50502082840600280041018106041030608283)))) else (if c < 532 then (if c < 528 then (if c < 526 then (if c < 525 then 0x2000830210284020c183060010302000810604180060c1850204100 else 0x820200180020408002001010404288020418006041810204081) else (if c < 527 then 0xc081121000102001810a0428108040040204086060c09a0a0c182 else 0x20c0000604080040800300080830200101020c00102040010604181)) else (if c < 530 then (if c < 529 then 0x6081830604083021408206041810000081080450104182850004003 else 0x6140860208181060c08004000830004101021808306001030c08183) else (if c < 531 then 0x20c202000c0010208103120c0010a0c001020800302040050204185 else 0x604104000c08102041030608083020c403001018100040840604100))) else (if c < 536 then (if c < 534 then (if c < 533 then 0x6042810404003020c08004001020e0c1830218102020009a0010082 else 0x604083020418306100820238101060410206040810408182020c082) else (if c < 535 then 0x600081040880104041830204a81060408102081010204005000c083 else 0x1000c18304040030e0c001000c181021400300241810618206)) else (if c < 538 then (if c < 537 then 0x410206001010214084040c006020c18104000810604080000c083 else 0xc041030004081020c001000c183020c001061c188060c0030614103) else (if c < 539 then 0x404101000ddb60204081680000206040851204001040c1031004001 else 0xc18102081820a0c0010010082060818206080810204083000c081))))) else (if c < 556 then (if c < 548 then (if c < 544 then (if c < 542 then (if c < 541 then 0x40810306040810608181021c1020404083040c00c04000000404084 else 0x60408506040830a0408102001010204085060420100141070004102) else (if c < 543 then 0x1c1050620401060c181020c0810400005040410102041820604403 else 0x40c283000428e040c100020c3030604102000840310081020608080)) else (if c < 546 then (if c < 545 then 0x4040830600281061418306080820410085001408102080800004106 else 0x40818302284010200182020c10106080830a0008302000810014183) else (if c < 547 then 0x220102020810106040010604185000c08006040830a0c0830204002 else 0xc283020c08108540850404183060c081060418502081031804181))) else (if c < 552 then (if c < 550 then (if c < 549 then 0x20c18102000830604002000c00102041810604181000c181040008a else 0x4040000204080060c181020c085020c080001428802042010208183) else (if c < 551 then 0xa041020404181020c0820610180020c18100001830a0c0840c04081 else 0x208003060800106041810600083060c1000204181061c0010a04201)) else (if c < 554 then (if c < 553 then 0xa0c00102040820604181060c1810268181060c102040c0801c04183 else 0x20c00100082030204081060c0810204081061030300042810204085) else (if c < 555 then 0x20c1030604200060478506040010204103060808102000010804083 else 0x21c1060204103080c10704141000408082040808000041830204082)))) else (if c < 564 then (if c < 560 then (if c < 558 then (if c < 557 then 0x20c1820a0018102083030000080060418106040830404101000c080 else 0x20c08306140040608082023c101020010108000810804005040430e) else (if c < 559 then 0x20408004141030004085000008000041810a140010a0c0810404082 else 0x20408006001070604007020c20102001810604081060c0810204081)) else (if c < 562 then (if c < 561 then 0x204181060c1850214085020c1810c0c182021400104040810204081 else 0x808b06001020400081060c006020810c020018302041810000080) else (if c < 563 then 0xc00083060408104040020604103061808306040810a001800604083 else 0x60c181001410102082840604001060c103020c103020c0820014002))) else (if c < 568 then (if c < 566 then (if c < 565 then 0x2000810204084060018202300810604081020c08102080830004082 else 0x60c00106141810604081060408102102810a0008006186820608083) else (if c < 567 then 0xc2810604081020c001020408100100810a0400502181830014409 else 0x20408304001800228183000c081280c081061408102100800604082)) else (if c < 570 then (if c < 569 then 0x414301060c1810404d8102001830a0c085060008206043010a0c106 else 0x10040810014186020c1810208181000418106040830a0c283060c401) else (if c < 571 then 0x2200810250101020408300043010408103020418706040010604283 else 0x60c001060c30106201080404085020c183020408106080810a00082)))))) else (if c < 604 then (if c < 588 then (if c < 580 then (if c < 576 then (if c < 574 then (if c < 573 then 0x20418106000810a0000606040840414101060818206141810a04005 else 0x200202121418102000000404180000400202040820214100060c083) else (if c < 575 then 0x40810204280061808302040830204081040028206041010200283 else 0x20c006020c087040008500041010204181020c002040c001060c083)) else (if c < 578 then (if c < 577 then 0x204000001408302040820200080021419b02041800604281060c181 else 0x80c1810218085021c00306041810410182000420102000010a08200) else (if c < 579 then 0x1830404283021c18006001010204181020418002040010204084 else 0x2040840008081020410102002810414081020c00104142800814085))) else (if c < 584 then (if c < 582 then (if c < 581 then 0x80800604001020818304081010c0808102040010a041810004002 else 0x20008204041000a0c002000c08208042830c080010a041000414181) else (if c < 583 then 0xa081800200083060008002040830414180060018302040820600205 else 0x200085060408102040810604100040c0000618084020c0000600183)) else (if c < 586 then (if c < 585 then 0x40810a0c0800604285028c1830800381020408206080830204003 else 0x60c0010000182020c2030618080020808002041800a0c1000200283) else (if c < 587 then 0x20428102041810204081060c181040c103000410304041810214083 else 0x6040810a14181020410300041800204085040408102041010008085)))) else (if c < 596 then (if c < 592 then (if c < 590 then (if c < 589 then 0x20808102081840204286041410102041060c0400302040830200080 else 0x40c080020c181060c18304082830014085040c083000c183020418c) else (if c < 591 then 0x6000810a04085020c182060418d02081880204103060c0830a0c103 else 0x60810202081af0c20181020c280020808306000810e080810608082)) else (if c < 594 then (if c < 593 then 0x214103020818302041030404701020c181020818302140810404083 else 0x2040830604082020408102004010208082020c087025c0960004081) else (if c < 595 then 0x61418302086020004001021408300041800204080020c1890c04001 else 0x120c083020818106040840a00183060c1810600180000c103080c084))) else (if c < 600 then (if c < 598 then (if c < 597 then 0xc0c082020408206041800a140810c042830604201020d3010418103 else 0x20408302040830400283060c0810604183020008304081020a04101) else (if c < 599 then 0x804203020c083020c083000c10300081820404d850218401060c083 else 0x408004040c181041800106040840a0c08004040030604188080c187)) else (if c < 602 then (if c < 601 then 0x20010106000810c00180000008106001830204182020c080020c002 else 0x60408006041030200081061408402000040200d8306043030204000) else (if c < 603 then 0x4041010c08185020c080040c08002000810a141810204081000c001 else 0x408084000410354001810a140810610103020c0830234083020c101))))) else (if c < 620 then (if c < 612 then (if c < 608 then (if c < 606 then (if c < 605 then 0x2040820004201060c10000040830204081020c003040c2810208183 else 0x604083060c08106040810404100040418302040810404181020c080) else (if c < 607 then 0x100c0000624103020c08202001850a040840a102810208081020c181 else 0x20c08202082010214203020c183021018102042020204081041c082)) else (if c < 610 then (if c < 609 then 0x4042830c001000414102020c183060c18304040910440281040c100 else 0x40c0830204083000418d00041070208083060838006001820804285) else (if c < 611 then 0x4d41810000105080c0830a0c28302040810410002060c0810204185 else 0x2041020204281020c080020c1810204081020800302041820204183))) else (if c < 616 then (if c < 614 then (if c < 613 then 0x804181020c0830404185020c003040818c0204000060c1811204081 else 0x4000010004081060c1810200106060c1830404081040c0810608081) else (if c < 615 then 0x20c1810a00396060c183060c181060c081060018102001010204180 else 0x20c08402081830a18081020c0030a0418104040810a040830604181)) else (if c < 618 then (if c < 617 then 0x604101040818000081810604083000818104141810204385061c181 else 0x208000020c0801c0c003060c1810a0c183000408000040810410081) else (if c < 619 then 0x2040020608081000010804040830600080020808000141800220080 else 0x4006040c2830208083020c183040c185020c00100100030204081)))) else (if c < 628 then (if c < 624 then (if c < 622 then (if c < 621 then 0x6041810404183020c0010a182810008103140c180020c0850208080 else 0x60018306040810404188020400202040810604181060c081020c203) else (if c < 623 then 0x20018302041820a0c18106001830a04080060000002141810208085 else 0xc000060828402081030408082020c081000018304040080408081)) else (if c < 626 then (if c < 625 then 0x20c0810e0c1810404a0106041820a04284020408304040810204081 else 0x20c08106043030a0c18300200810004085060808306040800214082) else (if c < 627 then 0x40c1820038102020018406080830204185020818300001810604403 else 0xc0810204081020418100040010604180000c08302001840604001))) else (if c < 632 then (if c < 630 then (if c < 629 then 0xa201810a0c2060a0828206180010204301001c101041c0850404082 else 0x20c0830600283068c282020c183060418202181820600081020c114) else (if c < 631 then 0x60c1080204183000800106040020208082060c18106040802a04083 else 0x2000010610201020418002082800200080041c0020a000851404081)) else (if c < 634 then (if c < 633 then 0x204201020c10006041010a140050000001060c18102041830404081 else 0x21008102041810e0c08006041030c0c103020c083020c0010204186) else (if c < 635 then 0x204182060c080020838104041830200081020408206000810c0c082 else 0x6081030e040813c180811aa0301020818202140810814101020c401))))))) else (if c < 700 then (if c < 668 then (if c < 652 then (if c < 644 then (if c < 640 then (if c < 638 then (if c < 637 then 0x2101810a00081020418202080810204101020818104040010204182 else 0x63428104041810004183020c002060c1830204083020c1810404304) else (if c < 639 then 0x4283040c0850208083060c082060410302041030a0c0810614103 else 0xa04200020808002001810004083040c0830204083060c0820400182)) else (if c < 642 then (if c < 641 then 0x120c00104041850204083060800004141000a040830604283001c001 else 0x604103020408302140820200081080c301020400302041830608180) else (if c < 643 then 0x604183040408102080800208183020c2800c14008080c084000c181 else 0x41020004082020408200080030208002000c10102080030604081))) else (if c < 648 then (if c < 646 then (if c < 645 then 0x4045830204180000c082021028202040030a14287069c0800610002 else 0x6101841a040030404005020c083000418302041010018083060c200) else (if c < 647 then 0x20408500041820204202020c1010204000020c1010608180020c081 else 0x404081001408206040840408080020420100040810404101060c183)) else (if c < 650 then (if c < 649 then 0x20c1010204280061c08104101800a14083020400302041810804181 else 0x20408106000830c04086021410106040830604083020c106060c182) else (if c < 651 then 0xc0830204101020018302040910008283060409000041810814283 else 0x200183000428106040820200081020c101060420206001000404102)))) else (if c < 660 then (if c < 656 then (if c < 654 then (if c < 653 then 0x2040030404102020c0800604082040410c04040810604003020c083 else 0x20c003020428406040010414182020018502040820a08183020419b) else (if c < 655 then 0xc082040c203020c00228042010204002020c18202040010608203 else 0x60408106301830204100120c1030208081020c08102000040200080)) else (if c < 658 then (if c < 657 then 0x20c181000c0c20214083060c185020400504180810a040810204101 else 0x6081010204201020400106041820404281020409f04001030a04180) else (if c < 659 then 0x208082060408308041830c0c1810204083061410102040830614080 else 0x60e5810204081020c08602081010404186020418000040830200082))) else (if c < 664 then (if c < 662 then (if c < 661 then 0x208083100408306041010414181020418302080850a040030a04100 else 0x6100820604081000820506080800604101060400500041030204101) else (if c < 663 then 0x2041810604081020c081080c0810204085020c0030200086020c603 else 0x20408004040830208080060808100040850e0008e0204001040c082)) else (if c < 666 then (if c < 665 then 0x20010200042810220284020408100043020a0810300080800a04002 else 0xc08506040810e0418302101030e040830604101100c0810004182) else (if c < 667 then 0x2140840608300022008104046030a0c1040020001080c081120c183 else 0x61008302041830408001020020306080810a0c08106040800608001))))) else (if c < 684 then (if c < 676 then (if c < 672 then (if c < 670 then (if c < 669 then 0x214181060c08a060c18206080840004100022000406000010400082 else 0x428302041180200203000c103020c18102043030208181000c083) else (if c < 671 then 0x183040810102040820404102000c183021408202041810604083 else 0x42830604080040430206086030004487021c18106040810604082)) else (if c < 674 then (if c < 673 then 0x2080810614185040c083060c2040204002060008102100830204083 else 0x900408102042810c1c0810c04081020018108080830210182060c203) else (if c < 675 then 0x6081800608081040408106040810400002020400302040810004083 else 0x610180020808006040830a0818602040810408183100c0830204002))) else (if c < 680 then (if c < 678 then (if c < 677 then 0x2080860404083000c08304044840414003060c081021c100060c083 else 0x20c1030210189060428404242810204181021400104047010404181) else (if c < 679 then 0xa140030008182000c080140c0820404080000408102040800a0c081 else 0x608102021418310080830204282060c082020408004101820404082)) else (if c < 682 then (if c < 681 then 0xe1418106040810608383021808106080810208182020c0800604480 else 0x20808502181890204102080408302000810600081020c0830204283) else (if c < 683 then 0x10040880608081060c2830a040820620001020418002001850804182 else 0x404002000c081001c0810404103020410206040810014001040c281)))) else (if c < 692 then (if c < 688 then (if c < 686 then (if c < 685 then 0x4041010204001020c0810604185000c180021008106042850204009 else 0x20c0810404085060c18002041810408181020818102080850214001) else (if c < 687 then 0x2040920200204060c08406100850600204020408102000830604181 else 0x20818308083010a380810a04085060c1800208083020c1010204283)) else (if c < 690 then (if c < 689 then 0x604101040418106001830208180060c1010a040810418181060c103 else 0x20418106041820200081000c0820204088041818306080810400100) else (if c < 691 then 0x204080080c101040c181060c281020808300041830c04081040c203 else 0xa0c201060408102a408102041810a0808208041810a0c0820200081))) else (if c < 696 then (if c < 694 then (if c < 693 then 0x2040830204282020c083040410104e018100040030a0c0830604302 else 0x4081830400002040c0010610201061818206000810600182040c081) else (if c < 695 then 0x40418100040800808083020408202100810218081000c3030600082 else 0x4041810a0c081060408106041811c04083021800270041860208002)) else (if c < 698 then (if c < 697 then 0x42820204003080c18100000810c0c181060408302040810008083 else 0xa0818102041830a0c1820204181020c083020410106043030608081) else (if c < 699 then 0xc4860a0408300040030604082060c080000428102041830e00281 else 0x20c08102043000204083740c083020818302140830208082020c185)))))) else (if c < 732 then (if c < 716 then (if c < 708 then (if c < 704 then (if c < 702 then (if c < 701 then 0x40c183060c18202041810400180020c183020810202000810200184 else 0xc1800604081061c0830604185060408502180010204181020c080) else (if c < 703 then 0x40020604081060c101060c0810a04186020c00102040810a10282 else 0xe0c10104101a900040010204103060c181020c0810204100020c383)) else (if c < 706 then (if c < 705 then 0x2000080604083020c083060c18102082840a001830c0c1810204081 else 0xa04203180c085020c00302101810200083100c0810208083060c081) else (if c < 707 then 0x604280060c001060418102041020c0c080020c1810a040030608083 else 0x60008100040010604104040800206041810400080040c0870254181))) else (if c < 712 then (if c < 710 then (if c < 709 then 0x204081020c301000c0030208083020c281060408200040810404181 else 0x42050a04183060010302100810214181020c00106040810c04082) else (if c < 711 then 0x404105000c0810c1808306100831c04283060410106200870a20101 else 0x21400102041830208080060c3030000102020408102041000a0018c)) else (if c < 714 then (if c < 713 then 0x2041020638103000c002000c1830210183060408302081040a00085 else 0x604082040c1830604083020c1810604081020408102004000208187) else (if c < 715 then 0x20c0830604002000828102040837c0028102041800a04181020c181 else 0x20c08106080810a08083020418104040800a04282000c0810650001)))) else (if c < 724 then (if c < 720 then (if c < 718 then (if c < 717 then 0x220c10304001010000082001418306001830a0c0830204081020c080 else 0x20c08602080810a0408100040800c0c2810004181020c0830214101) else (if c < 719 then 0x20808706040800204281020c0810210181021c1850a740800600281 else 0x80c0830a140810204305020c10102041030004084020c1070404084)) else (if c < 722 then (if c < 721 then 0x2140010604181020808702041010608108060408004041860404081 else 0x20400206041010a300810600006060c181760c083060c1810204185) else (if c < 723 then 0x4040831c0c084020418300080010a0008106040810c08281000c081 else 0x20830006001820a041810204003000c081021c10304041810000083))) else (if c < 728 then (if c < 726 then (if c < 725 then 0x2041880404103020408100042810600082021400102001810604183 else 0x12040030204003040408104142830208003021808506080800400103) else (if c < 727 then 0x4283020c101040c08402000880400083041000302041820808305 else 0xa0c101000c0830a0808006080830e04183060c085020c1030204701)) else (if c < 730 then (if c < 729 then 0x40808108001820004082000c08306041010204083020c0800400180 else 0x6040810620103020c1830404281040c103020c08302040800004081) else (if c < 731 then 0x2040800604101020c181041810236041820208083060c0820604181 else 0x20c0010208081020c1810018101020c085020400204040800408082))))) else (if c < 748 then (if c < 740 then (if c < 736 then (if c < 734 then (if c < 733 then 0xc086020410306081000618083040c08302002830000201040c101 else 0x40c1810208181020c083120c2810604103040430102002810004181) else (if c < 735 then 0x2040820204081000c183021818000040800208101120c081040c181 else 0xc1820604183060408100040810604083020c4010204083021c082)) else (if c < 738 then (if c < 737 then 0x60408102000810e00083020c0820204181021410602001810600a81 else 0x60c001020c083080408102040850204081020418502081030204283) else (if c < 739 then 0x608281040018102041810a14081060818100003b802040840000003 else 0x40008500041800608181060c181020c0810a0010302000030204101))) else (if c < 744 then (if c < 742 then (if c < 741 then 0x604102060408106040810c14080020c201040008200001810204001 else 0x214082060410100047010608083060c0070204082040c1800604081) else (if c < 743 then 0x6040830604083020008202040820404085060808106040800208180 else 0x6082830604281020c18106040030200281020418002080820204001)) else (if c < 746 then (if c < 745 then 0x2080000220105041010102041010210100060c08302080010204103 else 0x4080820a0c18306040850200081020c08402040800a04104083c101) else (if c < 747 then 0x410081040c101080008004041810404080000c0820404082060c081 else 0x2040010a0c280060408100141810c10181021c10302040970208182)))) else (if c < 756 then (if c < 752 then (if c < 750 then (if c < 749 then 0x40c28100301050604483020408106080810204180000c085060c181 else 0x20c081060c10102041810004101000810102100850604e000604082) else (if c < 751 then 0x10002000800204181060c100020c283000c08306040850204086 else 0x6041000014103040018306083810600081020418106040050604180)) else (if c < 754 then (if c < 753 then 0x6040810a04106020c18106202810c040800a002810600181060c300 else 0x6041810204182101400500081820220286020408602080810a0c081) else (if c < 755 then 0x43408106042010208183020c3850200081020418106040830208202 else 0x20c10102041850a0000202001810404001060c10204042890204181))) else (if c < 760 then (if c < 758 then (if c < 757 then 0x21c00206042010004081020808104000810a1008304040830a04081 else 0xc00006040030608082060c0030a04103020c18106041830204083) else (if c < 759 then 0xa0800102040000404080021c0810208181021408302041820204003 else 0x141808306080010204103020c0830210082020018206081810404084)) else (if c < 762 then (if c < 761 then 0x4083010a0c1030608181021408e0604381020810100183810404202 else 0x2180810604082060c10302081020204089020408002043010208081) else (if c < 763 then 0x1c4010204085000408102140800608081060408102042830004283 else 0x180008500180810810382020410202041850210281040c1800204003)))))))) else (if c < 891 then (if c < 827 then (if c < 795 then (if c < 779 then (if c < 771 then (if c < 767 then (if c < 765 then 0x20c285020408402081800204181060c083020418404041030a10103 else (if c < 766 then 0x60408106001030600080000408c0208082020c00100041800600082 else 0x4041810600081060408200040830600082060408306080870014081)) else (if c < 769 then (if c < 768 then 0xc2830414285020c102020c00102040820204085060c0810204081 else 0x20418002040800204783020c101020c082001408300081860a04285) else (if c < 770 then 0x14101020c0000a081b8000c0830204181060818302041820604083 else 0x200103020008602081020404180021018304001810200081020c106))) else (if c < 775 then (if c < 773 then (if c < 772 then 0x410185060c18002140810400182061418306100010c041830208101 else 0x20410104041810a0c0810208083040c203040c28300100810618185) else (if c < 774 then 0x6040830410080000410304081820004000020018600180000200182 else 0x20c081020c1820204181020c0810604003060c00002000030404181)) else (if c < 777 then (if c < 776 then 0x204081020c0840a0c0800410082060800302041030214103040c083 else 0x40820608180000c08100041810404082020400504040010204185) else (if c < 778 then 0x40c083020c083020c1010204030020c085060418000181020204081 else 0x2501820600080061c181000c2010404003020c100000c0070a08080)))) else (if c < 787 then (if c < 783 then (if c < 781 then (if c < 780 then 0x1000281060428302041800014182041000302000840208204020c183 else 0x2302010a08001060c081020408106002810008081060c0800808a02) else (if c < 782 then 0x204083000810102042830610080020c101061808202001810614080 else 0x2041830204082060c20106140810610183020c1010604101060c101)) else (if c < 785 then (if c < 784 then 0x604001080408104040810a0c1810a08101020408002040810408202 else 0xc403020c001060c083000c303000c283020c08102001830604085) else (if c < 786 then 0x40c080020c10202140840204081060c0830204083060c181060c103 else 0xa000830214003060c18502041030404181060418102100820a0c082))) else (if c < 791 then (if c < 789 then (if c < 788 then 0xc090020c182021418304001800200083020428206081020600083 else 0x2001010208202020010202041030204080060410104041820404001) else (if c < 790 then 0x8081830204282060c101060818106001850604081020c082041c202 else 0x80000c40302040820a14087060c080000c2811208083100c180)) else (if c < 793 then (if c < 792 then 0x20020202041830c040050608101080c2800204101040c0810218180 else 0x200082060c482060c0800008183000428e060818206000012000000) else (if c < 794 then 0x60c083020c182060400106041810410083020420200040850a04081 else 0x400181020c181020c281060418302040840204082060c0840604105))))) else (if c < 811 then (if c < 803 then (if c < 799 then (if c < 797 then (if c < 796 then 0x2041810604083021418102040810208181061418200080810404085 else 0x2001010e0408102040840204081001428102080850a0c2010414281) else (if c < 798 then 0x20c10100080030a0c114040c0800a04283060c083020c1810e0c302 else 0x204080020410106040810c041820000081040008006040810c00001)) else (if c < 801 then (if c < 800 then 0x4080021418102002020600086060c18302083830c140830404083 else 0x1c0810218082020c083040420902040020a0408106001810204381) else (if c < 802 then 0x820404081020c3810614082000c181060c0810200281020c181 else 0x100010108040810608101021c101020c00104000810204102040c181))) else (if c < 807 then (if c < 805 then (if c < 804 then 0x40408502080810204101040c3030008181061800104001830208181 else 0xa0400100044010608203020c085021c183020c10106041010604182) else (if c < 806 then 0x63c0810c0c301000410104000850604181060c283020c0810204381 else 0x210182020c3810200080020c08202040820208081020c0830208001)) else (if c < 809 then (if c < 808 then 0x600082060c08006080810204082000c284020808102140830414101 else 0x400381020840100080810804083002008100081820208081020c007) else (if c < 810 then 0x2040800004203000c0820804081001c085060408106000810208103 else 0x20c181060c281020c0810204183020c0830004080020c1810c04183)))) else (if c < 819 then (if c < 815 then (if c < 813 then (if c < 812 then 0x204303020408028040800204002060018100002000610101040c180 else 0x40810c041830404001061408102100010204003080c0830200002) else (if c < 814 then 0x2040830200003040c181060c0830604001020018306040810204084 else 0x60c18102040830a04001020c1810004083020c08302040820008003)) else (if c < 817 then (if c < 816 then 0x4081880218081000408502080810004181020c40502081030204281 else 0x10182000c08402000830200181021c08306a008304082840200181) else (if c < 818 then 0x2041010208181020018102043810004081060408412143850204201 else 0x604083000c283020810306041020208081100410106040820a00283))) else (if c < 823 then (if c < 821 then (if c < 820 then 0x4080820608101020408106040880400083001810902142820608280 else 0x604181080c181000408102183010404202080418102140810608082) else (if c < 822 then 0x2101830004081020c101020c003021c181060c0910204a81020c101 else 0x40400502040830200181020c003020818204040820208185020c294)) else (if c < 825 then (if c < 824 then 0x7100810a04181060440100040810200107040408102040860604183 else 0x418104080830c0c180000c08006080850e0010502041030004081) else (if c < 826 then 0x181830204081020c18104081820604003060008306141010200008 else 0x208283000c0800400101040400202040010600083020c181060c083)))))) else (if c < 859 then (if c < 843 then (if c < 835 then (if c < 831 then (if c < 829 then (if c < 828 then 0x2041830204081000c20202001000214081020408502041810a04187 else 0x6080830604080000800102101810604081041408102040820414103) else (if c < 830 then 0x60418302000030208081060c001040418106041810400081021c107 else 0x214184000408502080010e0418206080830a0c10108140830204080)) else (if c < 833 then (if c < 832 then 0xc2830604080060c18202080800604081060c1801c1c1030404083 else 0x608083060c1810608083020c0800204181020408306082850414003) else (if c < 834 then 0x20c181000008202140830800083060c001040018202082030604081 else 0x408106040830604080020c0880200101020c08102040020004181))) else (if c < 839 then (if c < 837 then (if c < 836 then 0xc284021418102003050408000041c08102041010a000810204082 else 0x204081020c1810200181020418202060010608680060c1810204182) else (if c < 838 then 0x40c482020008302200810e00183020c08104040030a0c101040c082 else 0x4041810404183001408102041830414103040c101020c1830200081)) else (if c < 841 then (if c < 840 then 0xa0000108041830000101040c101000c2860608183020c1820204007 else 0x4083030014082060410702002810204082061808800081810004104) else (if c < 842 then 0x408101000c083040c085000c1010014101060808000040860200283 else 0x2040030c0c20206140830208081081408302040020a041010604085)))) else (if c < 851 then (if c < 847 then (if c < 845 then (if c < 844 then 0x2081830214083020c00702000020604080060408502702820000101 else 0x2041820404003040c08306040800218102060c001000c1820c08081) else (if c < 846 then 0x20c0810200082020c18102101800e00180020470104041810208003 else 0xa04085060c0830600001100c0830610183000c18102040810604184)) else (if c < 849 then (if c < 848 then 0x21048302101810200002040008104080010208100120c1800a04301 else 0xa0008d0200101020408202040010008083021408106042810430080) else (if c < 850 then 0x4101120c083060010102043030c04081020808104141810608184 else 0x40c1030218081040018006040030404103020808402041820410081))) else (if c < 855 then (if c < 853 then (if c < 852 then 0x8081810408084080c1880604081000c100060408202044060004282 else 0xc0c182020c185040c0080608181060c08106042010204283040c083) else (if c < 854 then 0x6040810a0c081020010100140800204083020c080020c1830414006 else 0x6041010a04283020400502042040604083060808102140810a00188)) else (if c < 857 then (if c < 856 then 0x20818206041830a0410604003060200083020418306043830404082 else 0x20c081020c081020000102001810208081060428102001010404081) else (if c < 858 then 0x40800202040810604105061408002000810604103020c103080c101 else 0x204082020c1810a0c1010004081020c00102043830a080800604380))))) else (if c < 875 then (if c < 867 then (if c < 863 then (if c < 861 then (if c < 860 then 0x604101060c080280810006101020208081020c18002043010004103 else 0x404080060c1010a0008102041860604101060818002042830240183) else (if c < 862 then 0x6000830600181000c3030404183060410002040830a000810604106 else 0x20c1000204083060408506002840204101080410306080850214283)) else (if c < 865 then (if c < 864 then 0x20000106100820a0c3050208103020418302041010604180020c003 else 0x20800206040810204181080430330081820200182020c2810204302) else (if c < 866 then 0x8040810604087060c00100200810204181060008202001850004080 else 0xa001810004081020c2830004102020008302040835c200830604000))) else (if c < 871 then (if c < 869 then (if c < 868 then 0x604081040c0830204103060c081020c08d2200081060c1020804103 else 0x40c08102040812e080830208181000c0830200083020c0000404081) else (if c < 870 then 0x20c081020408302040830604082060c1810a0808102040800804182 else 0x20408302080010404083020c080020c0830a0408306142810404001)) else (if c < 873 then (if c < 872 then 0x614184000c4030400085060c0810204001020408302040840204003 else 0x20c08102040020a08088020c003080c281000408100041830a18181) else (if c < 874 then 0x40c0a10600003020c081041c201040c083020400102200810a08103 else 0x6040810410083021818306040830400080060400302001010214181)))) else (if c < 883 then (if c < 879 then (if c < 877 then (if c < 876 then 0x204085060400102041800a040810a0c0830204081000c1830604103 else 0x2000860404083060c183000c1830c0c183060418200141830004081) else (if c < 878 then 0x818002020c186020418808040810200101021010102041830e04081 else 0xa141820a04081000c101060008104082830a0c08306040811410082)) else (if c < 881 then (if c < 880 then 0x2008002040810204282020c08300141010200081020c7810408081 else 0xa14186020410302040810a1408500041850c00183060c0010004081) else (if c < 882 then 0x40408306141010608184060408006040830400003020c0800614203 else 0xa181817a0c0000604083060c0810204102000408102042810c30103))) else (if c < 887 then (if c < 885 then (if c < 884 then 0x40810c0418106042800c04285040c38302041810a040010614001 else 0x60808102000810a14080020430102041800800081040c0000204084) else (if c < 886 then 0x8081240c0860608281040c0850614083060400100180030604085 else 0x40830604183040c281020c1830a0c0880408081020c1820400303)) else (if c < 889 then (if c < 888 then 0x604183020808102041800600303020c103000c2820608201000c086 else 0x204381080c1830008081021c20506080830600001040c1010404082) else (if c < 890 then 0x20c081040818100041820004003080c18106080800204381060c182 else 0x8080800414083060018202041810604081061410102082830a0c081))))))) else (if c < 955 then (if c < 923 then (if c < 907 then (if c < 899 then (if c < 895 then (if c < 893 then (if c < 892 then 0x408180060008104002830208103040c18302041811014182000c181 else 0x2041030208000020c0820404005020c083060018104000830804002) else (if c < 894 then 0x60408002080810a08400040c0010200081020418302041030804082 else 0x2002840004182040c080021c0800004081020418102080810608002)) else (if c < 897 then (if c < 896 then 0x604181020c10002042830614201060420102001030610081000c081 else 0x2000820204181060c20008140830604004020418202040830408086) else (if c < 898 then 0x60c2010204100020028006041830808081020c1000608081020c080 else 0x4083000818206140810608081000c1010604286060c0810200481))) else (if c < 903 then (if c < 901 then (if c < 900 then 0x2040040004183000440102440810e0c083020408302042850408102 else 0x20408504001810a0400302040800a08083020800204000800604182) else (if c < 902 then 0x6041830604001060818102080810614182060818602041810404101 else 0x204186061c0810604081020c18000380810200105000c3030004201)) else (if c < 905 then (if c < 904 then 0x80408202043880a1c303080c0030404083020418102041010218001 else 0x2141810404283020820206080820610182020c28102141830604081) else (if c < 906 then 0x200102060c083080008102043861e04082040408002100030400083 else 0x204085020c1000a0820102040810208083020c103080c2830608382)))) else (if c < 915 then (if c < 911 then (if c < 909 then (if c < 908 then 0x61408104042810004083020c1010204083040008302041810c04002 else 0x20c101081008002080810214203040c003080408002141810230001) else (if c < 910 then 0xa180810204181020c182080408012040030204c00020c0810204182 else 0xa0400206040821004283061408006094050204181020c1830608081)) else (if c < 913 then (if c < 912 then 0x60c0800604102060810106081810608080020418004140830210100 else 0x2000050204381000400404180810804181060c081020c083060c001) else (if c < 914 then 0x4140810414083000c1010804181081418302142810a10080040c001 else 0x60c08304001010e0c08106080820004283020810106000010208082))) else (if c < 919 then (if c < 917 then (if c < 916 then 0x20c18202081010204082020c0810a0c08200040830c081b6020c18d else 0x200003020808302001020204083040c081020400204086030004180) else (if c < 918 then 0x810a0401102040810204089060c180060c083040c3000204180 else 0x3608001020c181041c1820204003020c0830a0c10108081820204103)) else (if c < 921 then (if c < 920 then 0x6102860e0408302081800804084020c081020c18102081020204081 else 0x2041010204080020408102001820020081080c08102102810408001) else (if c < 922 then 0x20410102040820604381041018502080801c0418000042833804083 else 0x41850004080020c0000004083060c081020418000040810610102))))) else (if c < 939 then (if c < 931 then (if c < 927 then (if c < 925 then (if c < 924 then 0x4203040c0030a04081020c2020204081040410102007830008283 else 0x204081020c081020c0810404083061408102141810204080060c181) else (if c < 926 then 0x60010102141030618181020c30502000020c0410104001010604083 else 0xa0c00106040810a14280061410002040810408105060c0820204101)) else (if c < 929 then (if c < 928 then 0x10081020c1010a081810200081040c181060808304040810208085 else 0x204281040c083060c0810210081020c282060408102041800208103) else (if c < 930 then 0x204083020410004041800454201060c183061008202040810204082 else 0x20c1810400182000c0830a0c285020818200701010200081020c281))) else (if c < 935 then (if c < 933 then (if c < 932 then 0x80418302081810614083120c08002040810a040810208083000c081 else 0x60c08004040830600083020c080060c0810610181020c1030408108) else (if c < 934 then 0x6040010614182020c003020c08302042810404083060c181020c103 else 0x204181000c083060c18102001050604080022c0810410182020c181)) else (if c < 937 then (if c < 936 then 0x20c1010600000060c08100180020004081060408102040811e0c085 else 0xc2830a042021004281020c1850204383020c081080c0810404001) else (if c < 938 then 0x20c083020c00204041840a1c4810a04083020840706040810808181 else 0xa08081122408202081830a0c0830e0c1820204080060c0830200001)))) else (if c < 947 then (if c < 943 then (if c < 941 then (if c < 940 then 0x4082801008001060c0810a0828306080810604082040c180040c083 else 0x20c181000c185020800102040810404181020c0000a0c102060c101) else (if c < 942 then 0x4181820c1050004100060c08306044010a0c68300041810204181 else 0x60c08108001833804085040c08000080010004081061c0860804083)) else (if c < 945 then (if c < 944 then 0x400181000c0070204181060460106001830808101020c1840208181 else 0x604283040c0010608083072428002041010004000060c0800208081) else (if c < 946 then 0x40c28306041820014101020418202081800204081060c0030014180 else 0x204081000808104140810414081086428306000010204081020c080))) else (if c < 951 then (if c < 949 then (if c < 948 then 0x2040830604083020808102082810600180020c0010208081060c103 else 0x608101060c0810a141830204181020408102041010e040810614184) else (if c < 950 then 0x418302080810404100000808302006140204185020c100000c101 else 0x200102061c08606040830204181020c083060c080040c0830200185)) else (if c < 953 then (if c < 952 then 0x608100020c082061c181021408102040010a042830204083060ce03 else 0x2040810414083061418304041830414181040808206040820a0c18c) else (if c < 954 then 0x141810a0c080040c1830408180040010102081800200201020c303 else 0x204001020c0830a0828102080860a0c08006080030414081020c104)))))) else (if c < 987 then (if c < 971 then (if c < 963 then (if c < 959 then (if c < 957 then (if c < 956 then 0x2041910204182020000102158820604182061808302000820404086 else 0x21818102041010204181020c1850e0c081020c283020c1810214083) else (if c < 958 then 0x20c182021c2830e04087000c183020c3010a041810204c830614083 else 0x60408302041800204183020c2810204101020018302001810204201)) else (if c < 961 then (if c < 960 then 0x204080001408206140830218082060c0810c0418108041030204081 else 0x20400202040802a0438102041000204003001818006081030600102) else (if c < 962 then 0x6081850204081040030002041831044187020c08304180000604381 else 0x20400102140830614285020c1800a0808206042010008081060c180))) else (if c < 967 then (if c < 965 then (if c < 964 then 0x60c08602041830a0010306140830808180020418104200050604183 else 0x40410004041020204101000808202040050610180040c003021c282) else (if c < 966 then 0x20818000040800404083020c0850204005021410506140010004281 else 0x60c38106002830214283020c1820a04083020c08006040800204080)) else (if c < 969 then (if c < 968 then 0x208080101c0000404085020410100141830618083020408d0a0c101 else 0x4187000408000140830608180020410102046020204083020c001) else (if c < 970 then 0x8086010604181040c000020c0030208181020010102040030208081 else 0x404081020418302040820404083020c2820204103060c181020c081)))) else (if c < 979 then (if c < 975 then (if c < 973 then (if c < 972 then 0x40c0010a0800302040850000081040c0040604301020c0040a0c084 else 0x60c1820004183040c083020c18202000810604081020c003040c181) else (if c < 974 then 0x204083020c087020408002003020208301020c08302001030204181 else 0x20018002080810008084060418102040830018083020c1820204180)) else (if c < 977 then (if c < 976 then 0x8185040c006020018504000850404084020c18102082010404080 else 0x408502040800a08185060c183060c08004041050214003020c001) else (if c < 978 then 0x240c28002082810200083060c30006301800404100021c081020c081 else 0x40410104040810008182020c08102040020a0c00106040830200001))) else (if c < 983 then (if c < 981 then (if c < 980 then 0x20c2810210101040408206000010a00004100418304180810604003 else 0xa0408206040810204101020c1830208081100818304040060814082) else (if c < 982 then 0x404082020c10106041800604282020c1830204101060c1020404301 else 0x6041010204081020c0840608083040c08202080020604485020c102)) else (if c < 985 then (if c < 984 then 0x20c0820204081060408d00040810a04080020008104141800214383 else 0x60c1850604180040008502080830c0c181060808008040810610081) else (if c < 986 then 0x60c0030604100040808002040810208081040428100040020604202 else 0x2180800a0c18106040810604203020c082021408304181830600280))))) else (if c < 1003 then (if c < 995 then (if c < 991 then (if c < 989 then (if c < 988 then 0x40c080020c081060c281021c0800204e000604383020c0030204081 else 0xc00348140800408082020c00502041010a0800402000000604280) else (if c < 990 then 0x204203040c1830c040810a0018a0204101021018002040830604101 else 0x2080800208181020400306040030600125020028302040000600086)) else (if c < 993 then (if c < 992 then 0x8301020428106180010610101021410004042830404280060cd80 else 0x20c082000c1810a04103060c005100400302042810200081040c180) else (if c < 994 then 0x1010a00183021418200001800604101060408102002810a00184 else 0x180c1830004080060400308040830028081040810102040810204083))) else (if c < 999 then (if c < 997 then (if c < 996 then 0xc080870018081040400100442010a0008506041850410303021c082 else 0x40c0830a0810006047030200183060c180000420302000010814083) else (if c < 998 then 0x20c20100041811c080010608100020418302040810a001030008181 else 0x20c183060c083020410306000830404086060c08100040020004081)) else (if c < 1001 then (if c < 1000 then 0x20c181020c1000608181020c18304040810204081040c6010404101 else 0x20408104040830204183000c1010c041840a0418204040820a0c081) else (if c < 1002 then 0x60c280040818004000800608284020c401060c101060c1830004182 else 0x604003060c083020408302040810200087060018104040880414085)))) else (if c < 1011 then (if c < 1007 then (if c < 1005 then (if c < 1004 then 0x4dc001020c1820208082020408006081830618103020c1010204081 else 0x204085047c102021410306140810214281060408102040830604181) else (if c < 1006 then 0x404203020c083040418102040810204080020410306180840204080 else 0xc1400306041030a040800008180020c081060c0800e042810204081)) else (if c < 1009 then (if c < 1008 then 0x2040850604100020020306000832a0418502040810204003060c081 else 0xc00080021408006040820a04103020418202082810808103040c183) else (if c < 1010 then 0x610300120c2800a0c101040c0850a0408006081860a14a030608080 else 0x20400106040810604001020010104200810a00083020c105020c085))) else (if c < 1015 then (if c < 1013 then (if c < 1012 then 0x4083040c083020c1810610083000c201020408206041070464081 else 0x604082060c003040418102041820010001020c081060c1830a04083) else (if c < 1014 then 0x140c081040c0820a1410102040010004080080818202001000204185 else 0x6001820204103029420102041810a080800608083020c186020c205)) else (if c < 1017 then (if c < 1016 then 0x2000830208085060408506181830014183001408306041818a18082 else 0x40c1010200081000418200040000604083020418100201010204184) else (if c < 1018 then 0x20400302041010a002010604181040418006043830e041820608081 else 0x4200)))))))))) >>> (7*(i%32))) &&& 0x7f
def leafChoice (h : Nat) := leafT (((h/9613)+leafD (h%9613)*(h%65521+1))%32579)
def internalD (i : Nat) := let c := i/32; ((if c < 16 then (if c < 8 then (if c < 4 then (if c < 2 then (if c < 1 then 0x14000c010001050a04021901060b05050b060201010016020400070c08261d else 0x1040a0e070702040a020002000b050b0002011504070b04030202000c060004) else (if c < 3 then 0x403191808060708041a020d010309000415020100010701010000000601000f else 0x201020701000404040800060003000b0c070b031f0602022504000501012b)) else (if c < 6 then (if c < 5 then 0x10a001100160e0a100402020806030c0326000e01000104020009080d030a01 else 0x2040402190008090e0303000505100a030115040e040202020100091105) else (if c < 7 then 0x601000a0301020c2203000e04080307040400010300000103190a0007050b00 else 0x4000500060705010200004f02010a010500011105000009190001000707030b))) else (if c < 12 then (if c < 10 then (if c < 9 then 0x104000506000812011904000d011a00031b1617163c160a010518002105090a else 0x70202010106080101000f01160f09011f02170207110a100106000200010101) else (if c < 11 then 0xb16000a000000061901002503000300011a001a000101000201100e03020102 else 0x20506040726060002371b011f0d060103040a231f0a0103090c1600092a0545)) else (if c < 14 then (if c < 13 then 0x1754041611230d011401060912011a010b000508460600000b12030c140e09 else 0x44210a0e0c010e02000406000000111000030e0007030611000c030805111902) else (if c < 15 then 0xe1d03040004040116020b442f05000a00021b010000081703001b03010e090d else 0x30404060906090607010f0600000512160311101d000100020102110205000f)))) else (if c < 24 then (if c < 20 then (if c < 18 then (if c < 17 then 0x90605070c18160209020105090e270300001414000522030e02090b41080800 else 0x604000100230701001700150625040003030215030202070e0001130306003b) else (if c < 19 then 0xc000208020300050901012e00010d0413150d0102000133141203000c040300 else 0xc273d0311110301080003000200020b0227311406050007110400020c020501)) else (if c < 22 then (if c < 21 then 0x13050c0e12023b070014630c0d00050b01000a2703060f0b1906001e3902030b else 0x1040e000500501501000020070e0900010429010210120f050b040302000c01) else (if c < 23 then 0xa0100052d060000020200211a0c08042c08050302000900054a16082505190b else 0x724060f00011e79020101000206330f00050f01111f0503090f021203020014))) else (if c < 28 then (if c < 26 then (if c < 25 then 0x40b040610010201271c021019030517003f241f0c02002f6306040101080105 else 0x62b030202022600004c0009040f0e00020105050707010a132a0a1a4301031f) else (if c < 27 then 0x20050005020600510100021b2c210e08044b2c0b100507010111050323002308 else 0x190004180921000200081c03000a07350014130f1f030806030906000c007f00)) else (if c < 30 then (if c < 29 then 0x2905000207170321061d1c0507090c131d0201000d0819020c06001a01081e08 else 0xe1c02022d0000034f041e05044d03ad020d141d050e022f1565050800000000) else (if c < 31 then 0xb1107090c090100091a100b000306030100050c0010120d0c06000c251f010b else 0x26b2f04043a030600041e0d001048022539710a3a))))) >>> (8*(i%32))) &&& 0xff
def internalT (i : Nat) := let c := i/32; ((if c < 54 then (if c < 27 then (if c < 13 then (if c < 6 then (if c < 3 then (if c < 1 then 0x1a1a83220800017c5482816ca80641c90000028b8c05d6ed50ea7c95027c0026e2c89305781602494c00180 else (if c < 2 then 0xbb21c653d46aa0fd83a554e2a90d0123000f48365180e22f42cc0b0f63d06e86433b30d771e408822d17000 else 0x1129021283972c8f4000350002f44f928093304958f90000302600011e74a01a080f505cab8ca0d0b8a6b000)) else (if c < 4 then 0x472000783ec114000000ea4e88f4cd0568c20008f85a0282587da5e00013a6a0bb172a595a06c00e60941815 else (if c < 5 then 0x4a8ec0472d3000000001b3328bbc910cc5462880149a0460f08088d21859e500001ca555090f203e2a549008 else 0x3970ac000ab1380005687e20865c004ed3020001ca3300056d782530807b4411f06681ec3b1611d407806ab3))) else (if c < 9 then (if c < 7 then 0x31a00d9d8f833a000f58af6d00681b938804090073e2048338002500e63206684400092cd907913a164e51f8 else (if c < 8 then 0x1a40c5a30ff510c8060b3e7720285a80a6b642c5d0001cccbc62cf222e1b0e2ab001e0c80e9974a40001e077 else 0xa0118033ac3ff36c0024a720001b38b02520007728e662bfe0c04813c04d57b9d03ab28358e011ea3979800)) else (if c < 11 then (if c < 10 then 0x1403bdedbe920c0028d8004b0351a50a83420a80380513438491000500581be9e04821a00b20f02a5746e006 else 0x10c351571162387bc8c193042088004746ec0555180038e00ccc0e82430690819e070000008491ec3447e010) else (if c < 12 then 0xaa51c0002e63b03fb949643b817a4202e6448e81124621d589c124c1f5db8090000007847f22a35d118e7 else 0x8c637c00442198750322690ec614051206e8614338532289584e08e04a944042440184f8051508f744940a43)))) else (if c < 20 then (if c < 16 then (if c < 14 then 0x468360170942384e8000876b01d4420417d52dc188851020020700016664a7d11f4582c8dd3350a6bd07100b else (if c < 15 then 0x398384062c445a3c4000df47c1828a86910c1d4000fa07f26c0180034431e589f1086354a738f0aab34d0910 else 0x2fc91cee8d600017c810000f341c5eabe87a1a84d8a44b83bd17cd2222424ee0002969e8e781f254001770e2)) else (if c < 18 then (if c < 17 then 0x2ac469a444f2965511886953a5400925902401999b1d5f21e0b900f0002f8d18e13b8118199fd7fe00000094 else 0x11942a1601c61a932929909409fe8ce2363ee21977000999f8c6a544a3c458580000007180418400107220) else (if c < 19 then 0x48a6303200000803c0c2d11b8448568003e47016809c4402147f2831842e8000d64fc1705fb8e000875a795f else 0x130320f18dd3849d86bca20440000050a974ba01821844f14c32a161700021c08a596a4c000470008c8b2000))) else (if c < 23 then (if c < 21 then 0x426f400e3bd0d28fc4b99c30006c7a8893846d48180013d1619e1050ce248f9916a08fc8040003f6bd0398a1 else (if c < 22 then 0x639cf0003089f4e80be1a400289a5a82815a1da0b2de418120cc0e65362b11702250c0b3b81b52642685d else 0x1705bc000071822aa2da010d21dc3d32456a2406d067000a781eacf05c0640488a61e4744990e3f23c00236d)) else (if c < 25 then (if c < 24 then 0x99a00018000000468ec82f152bb43128400a18c0b8001e42503997428ccc84d15290ac481a2b37e8001eb8e2 else 0x818dc1df0372b292d2ea551a0210172af23069a28802022041631ba0c8264001b8000424078295b23c4488f3) else (if c < 26 then 0x6a32c630a40000014fa4187e49059a370000028d02119ce24108261552987d8880b4001528133f405d60b5e else 0x14081ac0047291b78001fa6a1032875849f9233e4115070010793665fc000bf7b8fbd7507835437cf69db))))) else (if c < 40 then (if c < 33 then (if c < 30 then (if c < 28 then 0x3c1e68130993a44d1d65154157ac270a719e5d8e56970c405055618155448001860f512b6689aa7001285 else (if c < 29 then 0x1d053c000c16165606480343906c001c54285f6368c734800043000072621938cd8030585825b3de7ec4308e else 0x3fc3d2118000769400051032c1b94cbb616a760019e15a441c000c11886945b9191a60009748e05025088481)) else (if c < 31 then 0x1e61680714849c1b95e01a7c22c18b90122c37c261bc4183967389a1a80a10580035c989b5a645e204d363e5 else (if c < 32 then 0x21238c0000024009d8c17d52e1345893b202001670990002e85ece14f435a082fd9ea4703d88b92af38002d5 else 0x1641621601e32207a3805c06cc943690f0462cc3300098a4287927974a3b47f8a7178f243e81e12038048516))) else (if c < 36 then (if c < 34 then 0x1162f82829021c8141b09c1fc5e14fbf50013b16404d0564080a17259087ca086f000004000eb0bcaec1d0b1 else (if c < 35 then 0x9aec4003c30000010a8de0866c40000051b25d6f17b8783f0003a91d632c47034000829018362309826bcb6 else 0x537338b12301b45b400000230a247d28b7f05ec0582346a00a0f0770b8e18000bd0dc0985996c1f239011019)) else (if c < 38 then (if c < 37 then 0xa220d58101923142500004042e800890ac4885233a000b81ecb160011b0868811a20186ba223208a800000 else 0x540450f19302e658101d015034c693fb24c2984b8317384789f0002800010f0ae00025555ac027408603800) else (if c < 39 then 0x60c3c00061b2b4f980b0c2b34000000aa00011056186cda2c8ff492108b98015185e8498005ac0d84f0ee else 0xfc3dc5593720ea28000d5002db8fc8d905e690b8415160af01401512a254858b205e362910f80b634c52a1c)))) else (if c < 47 then (if c < 43 then (if c < 41 then 0x4740022392100a46a7f85f3dc06836c7d904c687fc7c06b104750298cc0fceb2ea722bdc392727d614926032 else (if c < 42 then 0x1160016c0001bc0002facc10ee825c8fd5ca00a270000000005904e094b255104840c0d01087700000106800 else 0x35a9a472003150adc6c0b67a2a19f30d7966a140004013603800030000634cc8003324d5188ad1cf2fcdf43e)) else (if c < 45 then (if c < 44 then 0x1e218c158053f1150c58001ec2ada387623633945cea23e3625e33f0a935616abd07e5984b3931a71c88cac2 else 0x1f213875074200379d997c5e4109730652ea7783d322000948000005390345b8f712a26c76b1b5b680061053) else (if c < 46 then 0x66b7c0009b49a0e42bc30840ae5bf11a0361fc7a8737aa3b02c0000ea608560e227a078cf84713e264158ac else 0x3020001a1e6000068001e91b805c50b2e090310798045a88ddf38f2122450a610f9fa0008506e180b8c028d2))) else (if c < 50 then (if c < 48 then 0x600098ccc1294801dad0008002379b539c5d8060014dc1c5ca8005180000004136c3a4cfcb4000a6832cda else (if c < 49 then 0x1ba494960d246826c61a465c8e02358b55581ec161710d6095328a11e8610060330b26c8a30302a65e5c94e5 else 0x20e57a49bfa2d0e643589728b2f8890005cc2d4f90ce0004bc0c43758a3c4461ff02828d33cf9294001be000)) else (if c < 52 then (if c < 51 then 0x98ed408b813a38ae06434c00cf1d360822106511aac91a02d184800104124189380942466982c000ca483b14 else 0x6e6258001475ba4100929040a00027a804ee3117daf870adc4fb8d01bd3d82ea7830e398220fb06a0013b0bf) else (if c < 53 then 0x552adc772970004c0000520002b4d58070002644280400027a908920381d9410398be638918000033299e87e else 0x34e09450800418399bbc0a52484c1312900030a8586f0a424e758450140006ca270994749e04154c06c680ac)))))) else (if c < 81 then (if c < 67 then (if c < 60 then (if c < 57 then (if c < 55 then 0x5d87380faab95432d350c91e810e003198b80a4000003880d5a710c2582144e8c228e88c0008c0006c120000 else (if c < 56 then 0x289ae8882140809a8fd212a507ba001d200000127808eac5b0b689434c7681858e1500045038c12c5ca79 else 0x5261180000015c998f12e24de3304c037236fc0892713dc3a4500bb0100b8c403a4352ac002cc106000ec1bf)) else (if c < 58 then 0x1f00c60006249387f0ecaba3b8e41aa5fc4f9740d8059608ed3bf2a40008f0040249f87d2bce1000000 else (if c < 59 then 0x4da4500000196ad8cdc00056122d881e2000c20929f053aee94400f11093c0480000070c2f0e064243cb8863 else 0x19e0002b8a75f8750310002a20c1704ac8a41289050d0b62cc1d04f1fa1b66cb874ff0c8762ac46cb10532b6))) else (if c < 63 then (if c < 61 then 0x562000559114bc7542207294e3443a84b0fab3816a6b031370b500020c2e40f8000f33788c84700096800802 else (if c < 62 then 0x49000081000436000208450f6b749b0155a2151554110a2bc0210bb09f389e425f6501f14d00019200007adc else 0x1c2d847e0c61ca1bc7ca1722a54421800a032c16e2b20b06b5eece61c05506214f74ec54004c954a4b497000)) else (if c < 65 then (if c < 64 then 0x5d26d0000168721046e9a868800073adf26e4d9312780000ec83287a3c0f0000f5074d14ecb0a13a211e282f else 0x2b63bdb93985d0000838003c62480008520438d220000c2315eb0628242ddcd02b2be04d720b006c23677838) else (if c < 66 then 0x5b48fc510637b4049c6b4100043803ab22681d2720f8244c086390a5766bca48000d02e44010288052813c8f else 0x3d40a82709025027610800000ce41b02754e0005e0e21d04cc4e0a51f08a03c2d98fd0e80003824233da8900)))) else (if c < 74 then (if c < 70 then (if c < 68 then 0xae9630ba012b79489fc0003299c029248144161b44ea5997f313178001c44601c6374740009388c1b6000 else (if c < 69 then 0x2cba64e8d41f4b848680004f230c80150960006080885d018600003a400048bd8224ab45709f74c3a5b1428 else 0x52c000001af282238b5a51058548db8000c08592b88d12e5d40006f4fabb0ed86c284314343e30282181d01c)) else (if c < 72 then (if c < 71 then 0x1906988f0f356c36467800168074d609607c0003300086a04086239106000002247bc0010d1487ece281383b else 0x692f300001d9fc001ac8030207b06b9d52ee0f473a8d0ae000108af7940ac289400785c11935a07e36084286) else (if c < 73 then 0xe2001c180863c72c5c130352da8f413b010130a708392534130a601da1941411537a16cdb0004ea5300003f else 0x3aebc596cd100058c000fc99e3bcef85041cfdceeb5402024a3b0f51543bc1f1396c8c105a0005b144404c5e))) else (if c < 77 then (if c < 75 then 0x3f400cbc0d514f20c004d89ee434d817c24a0ac7b1860e2030000338e71884129e08d07e151b16020046785d else (if c < 76 then 0x93c0844131b50d08405b4d52582702c04c9221103284c1c1048bc0640743e0a500011c0c25f9e29ae0e809 else 0x988258460006ae3401bae31180810c08869aa04ab82902881c6d91d0f00026f849452108720a20b64a8e680c)) else (if c < 79 then (if c < 78 then 0x9300001686154927c1e8a8900ebc3347a28aaf9538d452acdc7507253232c000cf1802b01100015c0c26405a else 0x5ec068000005548bd960001040e0c322501a1885fada4e6e30204f405a8555a0a65862a40880e0008502182a) else (if c < 80 then 0x94a0001701b23c08d36a54096000350804061140011b000000003650000f0b491d0008d9ab256172c153d89e else 0x638fa05796200000055a1295c000908fc106000f29d105a0444390c1000015310331859cd48e531f3b8a6bfe))))) else (if c < 94 then (if c < 87 then (if c < 84 then (if c < 82 then 0xa20d40e2bf606000000023ce7f8000f61b899e228000af28ce507e3441e5131cc000d7d6901a81132c8780e else (if c < 83 then 0x20aa6d344480000013d862000118fa8f10ee0184aaf24ae81c003068d229204b7b100700953d30bc4f223014 else 0x61c42c5a1321083ec498d600005cb192b93c5108c8a516eed165c794200005883100005420ab80005ba0783a)) else (if c < 85 then 0x23c5b0002d31ce090b286602f1a08345a102d4cb40615ae02d1dae705e90d2e8006f40765c1be1942812e000 else (if c < 86 then 0xc220075a4700066c000003ee09c9387c68013cf20000002a48b01e51e924f02ed0dd2bd158b402461e19cc2 else 0xfa00ce78a35303000005c2088a482b6044c000fa05a0324b03886d20601c000250d6fcc33ab900045000131))) else (if c < 90 then (if c < 88 then 0x7dc180000c30001bc16c2f748a448182c04a2842a86301a4fc34adb0ba50c390db08a0003f892188b1429cfc else (if c < 89 then 0x4480010205f0a443851cc078840026c578dc810dc9ea7449651c0c5226f1848a28000b50aa8250529341f2a8 else 0x42200003b5c2ac44cd29d30002986d8c6330000e40cd1cc1d40205220015d6780005426a220003b40f906aca)) else (if c < 92 then (if c < 91 then 0x7372456b07401e000572583ca8f81c27716c7a4f385e54312c63a3b528a09c59fd00a001e584800928449824 else 0x7c25c001581ea596798000b03681922c17ceb400113070000c7a4a2f40cc480002480e4383b237f22802159) else (if c < 93 then 0x3bc2fe121335869c83a08a1e0bbc0307c80ada4000721d63844481f25e98c0c8686ea8f25ea2105c0000006a else 0xde0b515c1924c8e08330001002784502d1d5108d125060c7487c1700005d8a00e067077000a12bac00161)))) else (if c < 101 then (if c < 97 then (if c < 95 then 0x840d0539420000083f00d55aeed341b90cc0000683b20aa80a2124376e8ccd00007c8ac824861026488aae7 else (if c < 96 then 0x778f3c0599e00015214ab51be0018f81c2b800104819062804619539bb47c66a0a75048c0d9ae00ed0c24000 else 0x106001421a3913220004e073f43c9a1eb1f4165380004549f000105000140c49fc0001d24692b0011e016800)) else (if c < 99 then (if c < 98 then 0x6547180006b5427857288d404230002110000f5540f416a7c42f15a07a11e26049146100059a7000b862ac36 else 0xcc03d0053901128c8d52080d0de0065eaae84480b06e128fa00e3cc66c730a30009fcd60001ee20436802) else (if c < 100 then 0x57e7447421ba068e8090079d07346f1c90acb1ce18e43764f4ca822000170700704c62e83fa4f2dc3b056219 else 0xa2cac7f0bc0002f8880a55aa3d87c803022001bfb110f46280a0c700019c0717e000c994a80000047d4c02a))) else (if c < 104 then (if c < 102 then 0x2d69d014202108d090c8401323dd0fbc24840005338214e0f0f40a27f221c550d65e6000e38cc4663f80d8d9 else (if c < 103 then 0x1436c0e39745c44d168db2220c80018a1fa00096ba10022607f0ca000990659391a2281381da3ec16686010 else 0x42e2bc0f83b2007b00004b000444900370002c85c26111e001bc8f248b4380c20f1631900006564606454222)) else (if c < 106 then (if c < 105 then 0x7f83e00023c2db2424a02322e4988098b0009bc000ff041450478cd0487128315d3a6af6718a449c5a624a73 else 0x36e000fb0d900d3ec4c0b71546f4632d73ea098028b1026e04cabdf75c4352d8bb2385d83015a6011c4d00f3) else (if c < 107 then 0x7826a856bed77ed484c08d3ae000000700003e88806004001075d0898c000004f88ba5240017983200406baa else 0xec13a3717d00078040413000))))))) >>> (11*(i%32))) &&& 0x7ff
def internalChoice (h : Nat) := internalT (((h/1013)+internalD (h%1013)*(h%65521+1))%3433)
def cert0 : FixedPair := ⟨x1,x6,⟨(false,17),[((false,17),0),((false,10),2),((false,21),1),((true,170),3)]⟩,⟨(false,34),[((false,34),0),((true,113),2),((true,231),1),((true,234),3)]⟩,(0x4000000000000000000000000000000000000000000,0x220400),(0x48000000000000000000000000000020000000000000000000000000000,0x400000000)⟩
def cert1 : FixedPair := ⟨x0,x5,⟨(false,4),[((false,4),2),((false,44),1),((true,116),3)]⟩,⟨(false,57),[((false,57),0),((true,183),2),((true,243),1),((true,245),3)]⟩,(0x100000000000000000000000000000,0x100000000010),(0x28000000000000008000000000000000000000000000000000000000000000,0x200000000000000)⟩
def cert2 : FixedPair := ⟨x3,x4,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert3 : FixedPair := ⟨x5,x6,⟨(false,0),[((false,0),0),((false,89),2),((false,147),1),((true,199),3)]⟩,⟨(false,2),[((false,2),0),((true,93),2),((true,150),1),((true,214),3)]⟩,(0x80000000000000000000000000000000000000000000000000,0x8000000000000020000000000000000000001),(0x400000000000000040000000000000200000000000000000000000,0x4)⟩
def cert4 : FixedPair := ⟨x1,x2,⟨(false,7),[((false,7),2),((false,3),1),((true,6),3)]⟩,⟨(false,4),[((false,4),0),((true,45),2),((true,51),1),((true,59),3)]⟩,(0x40,0x88),(0x808200000000000,0x10)⟩
def cert5 : FixedPair := ⟨x0,x2,⟨(false,1),[((false,1),2),((false,3),1),((true,0),3)]⟩,⟨(false,10),[((false,10),0),((true,22),2),((true,29),1),((true,36),3)]⟩,(0x1,0xa),(0x1020400000,0x400)⟩
def cert6 : FixedPair := ⟨x1,x4,⟨(false,89),[((false,89),0),((false,11),2),((false,44),1),((true,121),3)]⟩,⟨(false,34),[((false,34),0),((true,113),2),((true,137),1),((true,140),3)]⟩,(0x2000000000000000000000000000000,0x20000000000100000000800),(0x120000020000000000000000000000000000,0x400000000)⟩
def cert7 : FixedPair := ⟨x0,x3,⟨(false,147),[((false,147),0),((false,5),2),((false,21),1),((true,165),3)]⟩,⟨(false,57),[((false,57),0),((true,183),2),((true,194),1),((true,196),3)]⟩,(0x200000000000000000000000000000000000000000,0x8000000000000000000000000000000200020),(0x14008000000000000000000000000000000000000000000000,0x200000000000000)⟩
def cert8 : FixedPair := ⟨x1,x6,⟨(false,1),[((false,1),0),((false,2),2),((false,5),1),((true,150),3)]⟩,⟨(false,44),[((false,44),0),((true,121),2),((true,236),1),((true,241),3)]⟩,(0x40000000000000000000000000000000000000,0x26),(0x2100000000000000000000000000002000000000000000000000000000000,0x100000000000)⟩
def cert9 : FixedPair := ⟨x0,x2,⟨(false,11),[((false,11),0),((true,93),2),((true,100),1),((true,107),3)]⟩,⟨(false,147),[((false,147),0),((false,5),2),((false,154),1),((true,156),3)]⟩,(0x810200000000000000000000000,0x800),(0x1000000000000000000000000000000000000000,0x408000000000000000000000000000000000020)⟩
def cert10 : FixedPair := ⟨w23,x4,⟨(false,89),[((false,89),0),((false,11),2),((false,44),1),((true,121),3)]⟩,⟨(false,34),[((false,34),0),((true,113),2),((true,137),1),((true,140),3)]⟩,(0x2000000000000000000000000000000,0x20000000000100000000800),(0x120000020000000000000000000000000000,0x400000000)⟩
def cert11 : FixedPair := ⟨x0,x5,⟨(false,0),[((false,0),0),((false,1),2),((false,89),1),((true,85),3)]⟩,⟨(false,21),[((false,21),0),((true,165),2),((true,224),1),((true,228),3)]⟩,(0x2000000000000000000000,0x20000000000000000000003),(0x1100000000000000200000000000000000000000000000000000000000,0x200000)⟩
def cert12 : FixedPair := ⟨x0,x3,⟨(false,0),[((false,0),0),((false,1),2),((false,17),1),((true,14),3)]⟩,⟨(false,44),[((false,44),0),((true,116),2),((true,130),1),((true,134),3)]⟩,(0x4000,0x20003),(0x4400100000000000000000000000000000,0x100000000000)⟩
def cert13 : FixedPair := ⟨x1,x2,⟨(false,17),[((false,17),0),((false,10),2),((false,25),1),((true,29),3)]⟩,⟨(false,5),[((false,5),0),((true,150),2),((true,156),1),((true,164),3)]⟩,(0x20000000,0x2020400),(0x101040000000000000000000000000000000000000,0x20)⟩
def cert14 : FixedPair := ⟨x1,x4,⟨(false,7),[((false,7),2),((false,41),1),((true,37),3)]⟩,⟨(false,21),[((false,21),0),((true,170),2),((true,187),1),((true,192),3)]⟩,(0x2000000000,0x20000000080),(0x1080004000000000000000000000000000000000000000000,0x200000)⟩
def cert15 : FixedPair := ⟨w9,x4,⟨(false,0),[((false,0),2),((false,17),0),((false,41),3),((true,60),1)]⟩,⟨(false,2),[((false,2),2),((true,22),0),((true,45),3),((true,75),1)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert16 : FixedPair := ⟨w7,x2,⟨(false,0),[((false,0),2),((false,1),0),((false,3),3),((true,0),1)]⟩,⟨(false,10),[((false,10),2),((true,22),0),((true,29),3),((true,36),1)]⟩,(0x1,0xb),(0x1020400000,0x400)⟩
def cert17 : FixedPair := ⟨w7,x5,⟨(false,0),[((false,0),2),((false,1),0),((false,89),3),((true,85),1)]⟩,⟨(false,154),[((false,154),2),((true,156),0),((true,215),3),((true,221),1)]⟩,(0x2000000000000000000000,0x20000000000000000000003),(0x20800000000000001000000000000000000000000000000000000000,0x400000000000000000000000000000000000000)⟩
def cert18 : FixedPair := ⟨w8,x0,⟨(false,0),[((false,0),2),((false,1),3),((false,3),0),((true,0),1)]⟩,⟨(false,10),[((false,10),2),((true,22),3),((true,29),0),((true,36),1)]⟩,(0x1,0xb),(0x1020400000,0x400)⟩
def cert19 : FixedPair := ⟨x4,w480,⟨(false,0),[((false,0),0),((false,7),1),((false,41),2),((true,37),3)]⟩,⟨(false,25),[((false,25),0),((true,29),1),((true,76),2),((true,83),3)]⟩,(0x2000000000,0x20000000081),(0x810000000000020000000,0x2000000)⟩
def cert20 : FixedPair := ⟨x3,w479,⟨(false,0),[((false,0),0),((false,1),1),((false,17),2),((true,14),3)]⟩,⟨(false,49),[((false,49),0),((true,51),1),((true,76),2),((true,82),3)]⟩,(0x4000,0x20003),(0x410000008000000000000,0x2000000000000)⟩
def cert21 : FixedPair := ⟨w23,x3,⟨(false,147),[((false,147),0),((false,5),2),((false,21),1),((true,165),3)]⟩,⟨(false,57),[((false,57),0),((true,183),2),((true,194),1),((true,196),3)]⟩,(0x200000000000000000000000000000000000000000,0x8000000000000000000000000000000200020),(0x14008000000000000000000000000000000000000000000000,0x200000000000000)⟩
def cert22 : FixedPair := ⟨x5,w294,⟨(false,0),[((false,0),0),((false,89),2),((false,147),1),((true,199),3)]⟩,⟨(false,2),[((false,2),0),((true,93),2),((true,150),1),((true,214),3)]⟩,(0x80000000000000000000000000000000000000000000000000,0x8000000000000020000000000000000000001),(0x400000000000000040000000000000200000000000000000000000,0x4)⟩
def cert23 : FixedPair := ⟨x3,w306,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert24 : FixedPair := ⟨w235,x6,⟨(false,0),[((false,0),0),((false,89),2),((false,147),1),((true,199),3)]⟩,⟨(false,2),[((false,2),0),((true,93),2),((true,150),1),((true,214),3)]⟩,(0x80000000000000000000000000000000000000000000000000,0x8000000000000020000000000000000000001),(0x400000000000000040000000000000200000000000000000000000,0x4)⟩
def cert25 : FixedPair := ⟨w249,x4,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert26 : FixedPair := ⟨w386,x6,⟨(false,0),[((false,0),0),((false,7),2),((false,147),1),((true,142),3)]⟩,⟨(false,96),[((false,96),0),((true,100),2),((true,215),1),((true,222),3)]⟩,(0x400000000000000000000000000000000000,0x8000000000000000000000000000000000081),(0x40800000000000000000000000000010000000000000000000000000,0x1000000000000000000000000)⟩
def cert27 : FixedPair := ⟨w385,x5,⟨(false,0),[((false,0),0),((false,1),2),((false,89),1),((true,85),3)]⟩,⟨(false,154),[((false,154),0),((true,156),2),((true,215),1),((true,221),3)]⟩,(0x2000000000000000000000,0x20000000000000000000003),(0x20800000000000001000000000000000000000000000000000000000,0x400000000000000000000000000000000000000)⟩
def cert28 : FixedPair := ⟨w693,x4,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert29 : FixedPair := ⟨x0,w697,⟨(false,0),[((false,0),0),((false,1),2),((false,89),1),((true,85),3)]⟩,⟨(false,154),[((false,154),0),((true,156),2),((true,215),1),((true,221),3)]⟩,(0x2000000000000000000000,0x20000000000000000000003),(0x20800000000000001000000000000000000000000000000000000000,0x400000000000000000000000000000000000000)⟩
def cert30 : FixedPair := ⟨w76,x6,⟨(false,17),[((false,17),0),((false,10),2),((false,21),1),((true,170),3)]⟩,⟨(false,34),[((false,34),0),((true,113),2),((true,231),1),((true,234),3)]⟩,(0x4000000000000000000000000000000000000000000,0x220400),(0x48000000000000000000000000000020000000000000000000000000000,0x400000000)⟩
def cert31 : FixedPair := ⟨w76,x4,⟨(false,89),[((false,89),0),((false,11),2),((false,44),1),((true,121),3)]⟩,⟨(false,34),[((false,34),0),((true,113),2),((true,137),1),((true,140),3)]⟩,(0x2000000000000000000000000000000,0x20000000000100000000800),(0x120000020000000000000000000000000000,0x400000000)⟩
def cert32 : FixedPair := ⟨x0,x5,⟨(false,7),[((false,7),0),((false,2),2),((false,11),1),((true,93),3)]⟩,⟨(false,35),[((false,35),0),((true,176),2),((true,231),1),((true,233),3)]⟩,(0x200000000000000000000000,0x884),(0x28000000000000100000000000000000000000000000000000000000000,0x800000000)⟩
def cert33 : FixedPair := ⟨x1,x4,⟨(false,1),[((false,1),0),((false,2),2),((false,4),1),((true,45),3)]⟩,⟨(false,25),[((false,25),0),((true,29),2),((true,76),1),((true,83),3)]⟩,(0x200000000000,0x16),(0x810000000000020000000,0x2000000)⟩
def cert34 : FixedPair := ⟨x3,w250,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert35 : FixedPair := ⟨x5,w237,⟨(false,0),[((false,0),0),((false,89),2),((false,147),1),((true,199),3)]⟩,⟨(false,2),[((false,2),0),((true,93),2),((true,150),1),((true,214),3)]⟩,(0x80000000000000000000000000000000000000000000000000,0x8000000000000020000000000000000000001),(0x400000000000000040000000000000200000000000000000000000,0x4)⟩
def cert36 : FixedPair := ⟨x2,w386,⟨(false,0),[((false,0),0),((false,7),1),((false,3),2),((true,6),3)]⟩,⟨(false,4),[((false,4),0),((true,45),1),((true,51),2),((true,59),3)]⟩,(0x40,0x89),(0x808200000000000,0x10)⟩
def cert37 : FixedPair := ⟨x2,w480,⟨(false,0),[((false,0),0),((false,7),1),((false,3),2),((true,6),3)]⟩,⟨(false,4),[((false,4),0),((true,45),1),((true,51),2),((true,59),3)]⟩,(0x40,0x89),(0x808200000000000,0x10)⟩
def cert38 : FixedPair := ⟨w2476,x2,⟨(false,0),[((false,0),0),((false,7),2),((false,3),1),((true,6),3)]⟩,⟨(false,4),[((false,4),0),((true,45),2),((true,51),1),((true,59),3)]⟩,(0x40,0x89),(0x808200000000000,0x10)⟩
def cert39 : FixedPair := ⟨w744,x3,⟨(false,0),[((false,0),0),((false,17),1),((false,41),2),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),1),((true,45),2),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert40 : FixedPair := ⟨x1,w483,⟨(false,0),[((false,0),0),((false,7),2),((false,41),1),((true,37),3)]⟩,⟨(false,25),[((false,25),0),((true,29),2),((true,76),1),((true,83),3)]⟩,(0x2000000000,0x20000000081),(0x810000000000020000000,0x2000000)⟩
def cert41 : FixedPair := ⟨x5,w245,⟨(false,0),[((false,0),0),((false,89),2),((false,147),1),((true,199),3)]⟩,⟨(false,2),[((false,2),0),((true,93),2),((true,150),1),((true,214),3)]⟩,(0x80000000000000000000000000000000000000000000000000,0x8000000000000020000000000000000000001),(0x400000000000000040000000000000200000000000000000000000,0x4)⟩
def cert42 : FixedPair := ⟨x3,x4,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1)]⟩,⟨(true,60),[((true,60),3),((false,147),0),((false,21),2),((false,181),1)]⟩,(0x200000400000,0x4),(0x1000000000000000,0x2000000008000000000000000000000000000000200000)⟩
def cert43 : FixedPair := ⟨w284,x6,⟨(false,0),[((false,0),0),((false,89),2),((false,147),1),((true,199),3)]⟩,⟨(false,2),[((false,2),0),((true,93),2),((true,150),1),((true,214),3)]⟩,(0x80000000000000000000000000000000000000000000000000,0x8000000000000020000000000000000000001),(0x400000000000000040000000000000200000000000000000000000,0x4)⟩
def cert44 : FixedPair := ⟨w292,x6,⟨(false,0),[((false,0),0),((false,89),2),((false,147),1),((true,199),3)]⟩,⟨(false,2),[((false,2),0),((true,93),2),((true,150),1),((true,214),3)]⟩,(0x80000000000000000000000000000000000000000000000000,0x8000000000000020000000000000000000001),(0x400000000000000040000000000000200000000000000000000000,0x4)⟩
def cert45 : FixedPair := ⟨x3,x4,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1)]⟩,⟨(true,60),[((true,60),3),((false,89),0),((false,110),2),((false,44),1)]⟩,(0x200000400000,0x4),(0x1000000000000000,0x4000020000000000100000000000)⟩
def cert46 : FixedPair := ⟨x3,w189,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert47 : FixedPair := ⟨x3,w257,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert48 : FixedPair := ⟨x3,w483,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert49 : FixedPair := ⟨w298,x4,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert50 : FixedPair := ⟨w305,x4,⟨(false,0),[((false,0),0),((false,17),2),((false,41),1),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),2),((true,45),1),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert51 : FixedPair := ⟨x4,w482,⟨(false,0),[((false,0),0),((false,17),1),((false,41),2),((true,60),3)]⟩,⟨(false,2),[((false,2),0),((true,22),1),((true,45),2),((true,75),3)]⟩,(0x1000000000000000,0x20000020001),(0x8000000200000400000,0x4)⟩
def cert52 : FixedPair := ⟨x0,w41,⟨(false,41),[((false,41),0),((false,4),2),((true,85),3),((false,44),1)]⟩,⟨(false,57),[((false,57),0),((true,183),2),((true,221),3),((true,243),1)]⟩,(0x2000000000000000000000,0x120000000010),(0x8000020000000008000000000000000000000000000000000000000000000,0x200000000000000)⟩
def cert53 : FixedPair := ⟨x0,w37,⟨(false,147),[((false,147),0),((false,5),2),((false,21),1),((true,165),3)]⟩,⟨(false,57),[((false,57),0),((true,183),2),((true,194),1),((true,196),3)]⟩,(0x200000000000000000000000000000000000000000,0x8000000000000000000000000000000200020),(0x14008000000000000000000000000000000000000000000000,0x200000000000000)⟩
def cert54 : FixedPair := ⟨w221,x4,⟨(false,0),[((false,0),0),((false,7),2),((false,41),1),((true,37),3)]⟩,⟨(false,25),[((false,25),0),((true,29),2),((true,76),1),((true,83),3)]⟩,(0x2000000000,0x20000000081),(0x810000000000020000000,0x2000000)⟩
def cert55 : FixedPair := ⟨w23,x6,⟨(false,17),[((false,17),0),((false,10),2),((false,21),1),((true,170),3)]⟩,⟨(false,34),[((false,34),0),((true,113),2),((true,231),1),((true,234),3)]⟩,(0x4000000000000000000000000000000000000000000,0x220400),(0x48000000000000000000000000000020000000000000000000000000000,0x400000000)⟩
def cert56 : FixedPair := ⟨w2105,x2,⟨(false,0),[((false,0),0),((false,1),2),((false,3),1),((true,0),3)]⟩,⟨(false,10),[((false,10),0),((true,22),2),((true,29),1),((true,36),3)]⟩,(0x1,0xb),(0x1020400000,0x400)⟩
def cert57 : FixedPair := ⟨w270,x3,⟨(false,0),[((false,0),0),((false,1),2),((false,17),1),((true,14),3)]⟩,⟨(false,49),[((false,49),0),((true,51),2),((true,76),1),((true,82),3)]⟩,(0x4000,0x20003),(0x410000008000000000000,0x2000000000000)⟩
def cert58 : FixedPair := ⟨w23,x5,⟨(false,41),[((false,41),0),((false,4),2),((false,44),1),((true,116),3)]⟩,⟨(false,57),[((false,57),0),((true,183),2),((true,243),1),((true,245),3)]⟩,(0x100000000000000000000000000000,0x120000000010),(0x28000000000000008000000000000000000000000000000000000000000000,0x200000000000000)⟩
def cert59 : FixedPair := ⟨x2,w385,⟨(false,0),[((false,0),0),((false,1),1),((false,3),2),((true,0),3)]⟩,⟨(false,10),[((false,10),0),((true,22),1),((true,29),2),((true,36),3)]⟩,(0x1,0xb),(0x1020400000,0x400)⟩
def cert60 : FixedPair := ⟨x2,w479,⟨(false,0),[((false,0),0),((false,1),1),((false,3),2),((true,0),3)]⟩,⟨(false,10),[((false,10),0),((true,22),1),((true,29),2),((true,36),3)]⟩,(0x1,0xb),(0x1020400000,0x400)⟩
def cert61 : FixedPair := ⟨w8,x1,⟨(false,0),[((false,0),2),((false,7),3),((false,3),0),((true,6),1)]⟩,⟨(false,4),[((false,4),2),((true,45),3),((true,51),0),((true,59),1)]⟩,(0x40,0x89),(0x808200000000000,0x10)⟩
def cert62 : FixedPair := ⟨w5670,x4,⟨(false,0),[((false,0),0),((false,7),2),((false,41),1),((true,37),3)]⟩,⟨(false,25),[((false,25),0),((true,29),2),((true,76),1),((true,83),3)]⟩,(0x2000000000,0x20000000081),(0x810000000000020000000,0x2000000)⟩
def cert63 : FixedPair := ⟨x1,w748,⟨(false,0),[((false,0),0),((false,7),2),((false,147),1),((true,142),3)]⟩,⟨(false,96),[((false,96),0),((true,100),2),((true,215),1),((true,222),3)]⟩,(0x400000000000000000000000000000000000,0x8000000000000000000000000000000000081),(0x40800000000000000000000000000010000000000000000000000000,0x1000000000000000000000000)⟩
def cert64 : FixedPair := ⟨x0,w2108,⟨(false,1),[((false,1),2),((false,41),0),((true,85),3),((false,44),1)]⟩,⟨(true,156),[((true,156),2),((false,57),0),((true,221),3),((true,243),1)]⟩,(0x2000000000000000000000,0x120000000002),(0x8000020000000000000001000000000000000000000000000000000000000,0x200000000000000)⟩
def cert65 : FixedPair := ⟨x0,w389,⟨(false,0),[((false,0),0),((false,1),2),((false,89),1),((true,85),3)]⟩,⟨(false,154),[((false,154),0),((true,156),2),((true,215),1),((true,221),3)]⟩,(0x2000000000000000000000,0x20000000000000000000003),(0x20800000000000001000000000000000000000000000000000000000,0x400000000000000000000000000000000000000)⟩
def cert66 : FixedPair := ⟨x0,w2107,⟨(false,1),[((false,1),2),((true,14),3),((false,147),0),((false,21),1)]⟩,⟨(true,51),[((true,51),2),((true,82),3),((false,57),0),((true,194),1)]⟩,(0x4000,0x8000000000000000000000000000000200002),(0x4000000000000000000000000000400000008000000000000,0x200000000000000)⟩
def cert67 : FixedPair := ⟨x0,w387,⟨(false,0),[((false,0),0),((false,1),2),((false,3),1),((true,0),3)]⟩,⟨(false,10),[((false,10),0),((true,22),2),((true,29),1),((true,36),3)]⟩,(0x1,0xb),(0x1020400000,0x400)⟩
def cert68 : FixedPair := ⟨w5681,x3,⟨(false,0),[((false,0),0),((false,1),2),((false,17),1),((true,14),3)]⟩,⟨(false,49),[((false,49),0),((true,51),2),((true,76),1),((true,82),3)]⟩,(0x4000,0x20003),(0x410000008000000000000,0x2000000000000)⟩
def cert69 : FixedPair := ⟨w23,w29,⟨(true,37),[((true,37),3),((false,89),0),((false,11),2),((false,44),1)]⟩,⟨(true,83),[((true,83),3),((false,34),0),((true,113),2),((true,137),1)]⟩,(0x2000000000,0x20000000000100000000800),(0x20000020000000800000000000000000000,0x400000000)⟩
def cert70 : FixedPair := ⟨w23,w37,⟨(true,14),[((true,14),3),((false,147),0),((false,5),2),((false,21),1)]⟩,⟨(true,82),[((true,82),3),((false,57),0),((true,183),2),((true,194),1)]⟩,(0x4000,0x8000000000000000000000000000000200020),(0x4008000000000000000000000000400000000000000000000,0x200000000000000)⟩
def cert71 : FixedPair := ⟨x1,w1381,⟨(false,0),[((false,0),0),((false,7),2),((false,147),1),((true,142),3)]⟩,⟨(false,96),[((false,96),0),((true,100),2),((true,215),1),((true,222),3)]⟩,(0x400000000000000000000000000000000000,0x8000000000000000000000000000000000081),(0x40800000000000000000000000000010000000000000000000000000,0x1000000000000000000000000)⟩
def cert72 : FixedPair := ⟨x0,w1376,⟨(false,0),[((false,0),0),((false,1),2),((false,89),1),((true,85),3)]⟩,⟨(false,154),[((false,154),0),((true,156),2),((true,215),1),((true,221),3)]⟩,(0x2000000000000000000000,0x20000000000000000000003),(0x20800000000000001000000000000000000000000000000000000000,0x400000000000000000000000000000000000000)⟩
def cert73 : FixedPair := ⟨x1,w1391,⟨(false,0),[((false,0),0),((false,7),2),((false,41),1),((true,37),3)]⟩,⟨(false,25),[((false,25),0),((true,29),2),((true,76),1),((true,83),3)]⟩,(0x2000000000,0x20000000081),(0x810000000000020000000,0x2000000)⟩
def cert74 : FixedPair := ⟨x0,w1385,⟨(false,0),[((false,0),0),((false,1),2),((false,17),1),((true,14),3)]⟩,⟨(false,49),[((false,49),0),((true,51),2),((true,76),1),((true,82),3)]⟩,(0x4000,0x20003),(0x410000008000000000000,0x2000000000000)⟩
def fixedEntry (i : Nat) : FixedPair := (if i < 37 then (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then cert0 else cert1) else (if i < 3 then cert2 else cert3)) else (if i < 6 then (if i < 5 then cert4 else cert5) else (if i < 7 then cert6 else (if i < 8 then cert7 else cert8)))) else (if i < 13 then (if i < 11 then (if i < 10 then cert9 else cert10) else (if i < 12 then cert11 else cert12)) else (if i < 15 then (if i < 14 then cert13 else cert14) else (if i < 16 then cert15 else (if i < 17 then cert16 else cert17))))) else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then cert18 else cert19) else (if i < 21 then cert20 else cert21)) else (if i < 24 then (if i < 23 then cert22 else cert23) else (if i < 25 then cert24 else (if i < 26 then cert25 else cert26)))) else (if i < 32 then (if i < 29 then (if i < 28 then cert27 else cert28) else (if i < 30 then cert29 else (if i < 31 then cert30 else cert31))) else (if i < 34 then (if i < 33 then cert32 else cert33) else (if i < 35 then cert34 else (if i < 36 then cert35 else cert36)))))) else (if i < 56 then (if i < 46 then (if i < 41 then (if i < 39 then (if i < 38 then cert37 else cert38) else (if i < 40 then cert39 else cert40)) else (if i < 43 then (if i < 42 then cert41 else cert42) else (if i < 44 then cert43 else (if i < 45 then cert44 else cert45)))) else (if i < 51 then (if i < 48 then (if i < 47 then cert46 else cert47) else (if i < 49 then cert48 else (if i < 50 then cert49 else cert50))) else (if i < 53 then (if i < 52 then cert51 else cert52) else (if i < 54 then cert53 else (if i < 55 then cert54 else cert55))))) else (if i < 65 then (if i < 60 then (if i < 58 then (if i < 57 then cert56 else cert57) else (if i < 59 then cert58 else cert59)) else (if i < 62 then (if i < 61 then cert60 else cert61) else (if i < 63 then cert62 else (if i < 64 then cert63 else cert64)))) else (if i < 70 then (if i < 67 then (if i < 66 then cert65 else cert66) else (if i < 68 then cert67 else (if i < 69 then cert68 else cert69))) else (if i < 72 then (if i < 71 then cert70 else cert71) else (if i < 73 then cert72 else (if i < 74 then cert73 else cert74)))))))
def book : Book where
  count := 75
  entry := fixedEntry
  choose k t v := let i := leafChoice (stateKey k t v); if i=0 then 75 else i-1
set_option maxRecDepth 30000 in
theorem checkedBook : span (fun i => decide (book.entry i).intrinsic) 75 0 = true := by decide +kernel
theorem goodBook : book.Valid := by
  intro i hi
  apply of_decide_eq_true
  exact span_range checkedBook i (by omega) (by simpa [book] using hi)

def front (z : Nat) := ((List.range 7).filter (fun i => z.testBit i)).map atom7 ++ (words 13 11 (z >>> 7)).map (fun i => s (i+6))
def table_10_0 (i : Nat) := let c := i/32; (0x3fbfeffff >>> (9*(i%32))) &&& 0x1ff
def table_10_1 (i : Nat) := let c := i/32; (0x1fdfcffbddffefff >>> (9*(i%32))) &&& 0x1ff
def table_10_2 (i : Nat) := let c := i/32; (0x1fdfcffbddffefff >>> (9*(i%32))) &&& 0x1ff
def table_10_3 (i : Nat) := let c := i/32; (0x3fbfaf7f7 >>> (9*(i%32))) &&& 0x1ff
def table_10_4 (i : Nat) := let c := i/32; (0 >>> (1*(i%32))) &&& 0x1
def count10 (t : Nat) := if t < 5 then (if t < 2 then (if t < 1 then 4 else 7) else (if t < 3 then 7 else (if t < 4 then 4 else 0))) else 0
def front10 (t i : Nat) := (if t < 2 then (if t < 1 then table_10_0 i else table_10_1 i) else (if t < 3 then table_10_2 i else (if t < 4 then table_10_3 i else table_10_4 i)))
def L10 : Layer where
  count := count10
  state t i := front (front10 t i)
  pick t v := (internalChoice (stateKey 10 t v))-1
def table_9_0 (i : Nat) := let c := i/32; ((if c < 4 then (if c < 2 then (if c < 1 then 0x30003fe58007fca000ff92001ff20003fe0c003fe9000ff830017f0000efe38007fc00033f8c001ff0000afe28007fc00023f88001ff00006fe18007fc00013f84001ff00053ff4c003fe9800bfd3001ff00054ff50003fea000bfd4001ff00055ff54003fea800bfd5001ff else 0x32003fe34007fdc000ffaf001ff52003fe84007fcb800ff8b001ff6c003fed0007fd3800ff9f001ff2a003fec8007fd8000ffae001ff3a003fe4c007fc4800ffac001ff54003fea0007fd3000ff91001ff0e003fe90007fd1000ffa0001ff3c003fe70007fc2800ff9a001ff) else (if c < 3 then 0x34002fe60005fcb000bf940017f24002fe40005fc10007fd20017f00044ff10005fc0010bfc20017f00040ff00005fc000fbfbe0017f0003cfef0005fc000ebfba0017f72003fedc007fd9800ffad001ff4a003fe6c007fc7800ff80001ff6a003fec4007fd5800ffa3001ff else 0x46002fe64005fe1800bfb80017f5e002fea4005fd0800bf970017f82002fed8005fda000bfa70017f3e002fe54005fdf800bfb20017f60002feb8005fce800bf930017f58002fea8005fd4000bfa60017f22002fef4005fd2000bfa20017f40002fe78005fce000bfbb0017f)) else (if c < 6 then (if c < 5 then 0x38001fe68003fcc0007f96000ff28001fe48003fc80007f800287fa0001fe0009dfe70007f800267f98001fe00095fe50007f800247f90001fe0008dfe30007f800297fa4001fee4005fdb800bfb30017f5a002fe94005fcd800bfc50017f00002fed4005fd8800bfab0017f else 0x56001fe8c003fcc8007fcf000ff70001febc003fd48007fa1000ff2e001ff34003fdb0007fb4000ff4e001fe7c003fca8007fcb000ff64001fec0003fd70007f9d000ff26001ff24003fd60007faa000ff50001fe98003fc88007fc7000ff48001fe88003fd00007f9e000ff) else (if c < 7 then 0x9fe00059fc000abf800147f00026fe00023fc0011ff8001eff00007fe00049fc0008bf800107f0001efe00039fc000eff80002ff0001afe00031fc0005bf8000a7f00012fe00021fdc8007fb7000ff66001feb4003fd28007f9b000ffa2001fe00003fda8007fb1000ff else (if c < 8 then 0x45fe0001ffc00003f8001aff00031fe00057fc0008ff8000cff0004ffe00087fc00037f8001c7f0002ffe00053fc00087f8000bff0004dfe00083fc0002ff8001b7f00034fe0004ffc0007ff8000aff0004bfe0007ffc000cbf800187f0002efe0003bfc0004ff80024ff else 0x73fc000dff80019ff0002dfe0004bfc0006ff80028ff)))) >>> (27*(i%32))) &&& 0x7ffffff
def table_9_1 (i : Nat) := let c := i/32; ((if c < 5 then (if c < 2 then (if c < 1 then 0x53ff4c003ba98007f53000efa6002d74c005ee9800b7d3001e7a6003ef4c007bc00152f8002a7fa8001bd50003faa0006fd40015ba8002f7500057ea000ebd4001f7a8003be000abfc00155fd5000feaa0017d54002fea800bdd50013baa0027f54007dea800dbd5001bf else 0x40003ee78007dce000fb85001f734003ee60007dcb000fb94001f724003ee40007dc18007b03000fe06001ef48007d69000fed2001f706002e60c005ec1800bb800077f1c003ee00019fc6000fb800057f14003ee00011fc4000fb800037f0c003ee00009fc2000fb80029ef) else (if c < 3 then 0x6a003eec4007dd5800fba3001f732003ee34007ddc000fbaf001f752003ee84007dcb800fb8b001f76c003eed0007dd3800fb9f001f72a003ee00007fd9000fbb0001f75c003ee74007dc9800fb89001f758003eea8007dd4000fba6001f722003ee1c007dd2000fba2001f7 else (if c < 4 then 0x34002f660005ecb000bd940017b24002f640005ec10007d02000fe04001f748005e69000bed20017b00044ff10005ec0010bfc20017b00040ff00005ec000fbfbe0017b0003cfef0005ec000ebfba0017b72003eedc007dd9800fbad001f74a003ee6c007dc7800fb80001f7 else 0x32002f70c005edc000bdaf0017b52002f684005ecb800bdc10017b6c002f6d0005ed3800bd9f0017b2a002f6fc005ed9000bdb00017b5c002f674005ec9800bd800017f58002f6a8005ed4000bda60017b22002f6f4005ed2000bda20017b40002f678005ece000bdbb0017b))) else (if c < 7 then (if c < 6 then 0x28001fc48003f880007f000287fa0001fc0009dfe70007f000267f98001fc00095fe50007f000247f90001fc0008dfe30007f000297d00052ff48003f290007f52000fd72002f6dc005ed9800bdad0017b4a002f66c005ee2800bd800017b6a002f6c4005ed5800bda30017b else 0x5e001fca4003f908007f17000fe9a001fcd8003f9a0007f27000fe3e001fc54003fa58007f32000fe60001fcb8003f8e8007f13000fe92001fcb0003f950007f28000fe4c001fc44003fa38007f24000fe44001fc80003f8f0007f1c000fe00001fe68003f8c0007f16000fe) else (if c < 8 then 0x11fe0008ffc000f7f80003ff00024fe00045fc00083f8000f7f0001cfe00077fc00017f8000d7f00018fe0002dfc00053f800097f00010fee4003f9b8007f33000fe5a001fc94003f8d8007f51000fe00001fcd4003f988007f2b000fe46001fc64003fa78007f38000fe else (if c < 9 then 0x2bfe00047fc00067f80027ff00043fe0001bfc000e3f80017ff00029fe00043fc0005ff80026ff00041fe00017fc000dbf8001a7f00027fe0003ffc00057f80025ff0003ffe00065fc000c3f800177f0001dfe00027fc00127f80004ff0002cfe00055fc000a3f800137f else 0x39fe0006ffc000cff80016ff00025fe00037fc00147f80022ff0000ffe00001fc000d7f80018ff)))) >>> (27*(i%32))) &&& 0x7ffffff
def table_9_2 (i : Nat) := let c := i/32; (0x1fc00007f000297da4001f800005ec10007d520017900003ee0c003da9000fa830017300053df4c003ba9800b5d3001e700054bf500037aa000add4001d7000557f54002faa8009dd5001b7 >>> (27*(i%32))) &&& 0x7ffffff
def count9 (t : Nat) := if t < 3 then (if t < 1 then 263 else (if t < 2 then 300 else 23)) else 0
def front9 (t i : Nat) := (if t < 1 then table_9_0 i else (if t < 2 then table_9_1 i else table_9_2 i))
def L9 : Layer where
  count := count9
  state t i := front (front9 t i)
  pick t v := (internalChoice (stateKey 9 t v))-1
def table_8_0 (i : Nat) := let c := i/32; ((if c < 21 then (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0x7efe000000f9fc0000022bf80000194ff00000088fe000000f5fc00000cabf8000002a7f00000074fe000000e5fc000001c3f800000377f0000006cfe000000d5fc000001e3f80000195ff00000076fe000000d1fc00000cb3f8000002aff00000062fe000000c1fc0000017bf8000002e7f0000005afe000000b1fc0000019bf80000196ff00000064fe000000adfc00000cbbf80000197ff else 0xa3fe00000143fc000004dff800210037d00022006fa0001c00df40000001bf8001e0037d0000009dfe00000137fc00000267f8000004bff0002e004fc00014009f800128013f800000027f00028004fc00000129fc0000024bf800000487f0000008efe00000119fc00000327f8000005dff000000b9fe0000064ffc00000ca3f80000029ff00000086fe00000109fc0000020bf800000407f) else (if c < 3 then 0x1fffe000003e5fc000007aff800000f27f0006a00cbe0008c0197c000c8032f8000d0065f0000000cfe000e00197c00180032f800000597f000001c9fe00000383fc000006e7f800170056f0001600ade00000015fc0017002b7800000567f000000aafe000002e3fc0000059ff8002d0047b00052008f60004c011ec00048023d800a20046f00000008fe00098011ec000e0023d80000052ff else (if c < 4 then 0x25a003be004780077c008b000ef8010e001df001ca003be003740077c00c0800df80120001bf002200037e003d8006fc0077800df800e7001bf001be0037e00000007fc00f8000df80210001df00414003be0065c007bc00de000fb80138001fb0025e003f600000451fc0000088bf8000010bff00000211fe00000417fc005b803b7800370073f0003600e7e0003c01cfc0000003bf800320073f else 0x234003fc00420007f800ed000fe8017c001fd001e2003fa00380007f4006b800fe801db001fb00350003f600628007ec00be800fd8012a001fb00236003f6003c8007ec0070800fd801dc001f700256003ee00490007dc008e000fb8010a001f7001e6003ee00364007dc00ee800f78012c001ef00218003de003ec007bc007a000f7800e3001ef001b6003de002dc007bc0051000f78017f001df))) else (if c < 7 then (if c < 6 then 0x247fe0000048bfc0000090ff8000013dff00078011fa000f4079f4000000f3f8003c018ff0007801cfa0000047ffc000008f7f8000011dff00000239fe000e8023f8001d80ebf0003a01bff0000003afe000e8025f8000008dbf8000011a7f00000232fe00000461fc000008bbf8000012eff0000025bfe000000f7fc000001a7f8000002bff003b2003fc005ec007f9b008800ff00129001fe else 0x880387e00110058fc00000a7ff8000014f7f0000029dfe00000539fc0021008ef8004200cdf00086042be00000085fc002100e2f800420155f00000254fe00000529fc00000a4ff800001497f00080021de0010002fbc002081037800000207f0008002ede00100051bc0000093bf800001267f00000288fe0000050ffc001f007fb8003e00af70007e03eee0000007dfc001f00bbb8003e01377) else (if c < 8 then 0x25a002be004780057c008b000af8010e0015f001ca002be003740057c00c08009f801200013f002200027e003d8004fc00778009f800e70013f001be0027e00000005fc00f80009f8029a0013f00420002be00a900057c00cb800b7802810016f00378002ee00a34005dc009c000bd80000154ff000002a8fe0000054ffc00000a9bf80000152ff000880257e00110036fc00228111f800000227f else (if c < 9 then 0x2f6002fc004a4005f8008d000bf001080017e003b4002fa005f0005f40078800be800e00017d001ae002fa0076c005ec00d4000bd8018a0017b002fa002f6004a8005ec008d800bd800f20017b001c2002f600770005dc0095800bb801240017700238002ee00428005dc0079800bb800d900177003ba002de004b0005bc0086000b7800fb0016f001e8002de0038c005bc006d800b78017f0015f else 0x8c023fa0011803ff400230077e800470237d0055e046ee00acc08d7c0000011bf80046018ff0008c010fa00000569fc00000acbf800001587f000002aefe00000559fc00000973f8000005e7f00000324fe0000064bfc00000c9bf800000297f000000c7fe0000018bfc0000030ff80000060ff000000bffe0000017bfc00000aabf8000005d7f00000089fe000000effc00000197f801d90017e)))) else (if c < 15 then (if c < 12 then (if c < 11 then 0x30cfe00b20099ec002600df78004c01aef0009802fde00130053bc002681337800000267f00098020de0013002dbc00000b33f800001657f00000302fe00000603fc002500c7b8004a013f70009604aee00000095fc00250053b80000162ff000002c3fe00000583fc00000bd7f80048015fb00090027f600124091ec00000123f800480097b000002bdfe00000577fc00000ae7f8000015bff else 0x32e001de006f0003dc009c0007d802e6000bf005c4001de00890003fc00000c8ff800001917f00000321fe00000641fc00000c7ff802d50287b000a00397e0014006efc002800cdf80050016bf000a20507e000000a1fc00280091f8005000d3f00000319fe00000631fc00000c5ff8000018b7f0009c031be001380577c0027813af800000277f0009c018be000005a5fc00000c3bf80000186ff) else (if c < 13 then 0x214001ee003cc003dc006c8007b802af000f7003ba001dfb8084003bc0096000778010c000ef001f6001de003d0003bc007180077800db000ef002fe001be004b40037c008f0006f80116000df0021c001be003940037c006e8006f802b3000df003020017fb8094002fc00900005f80110000bf001ec0017e003bc002fc00738005f800df000bf003a0001fe00000003fc00f80005f80210000df else (if c < 14 then 0xcefe00000199fc00000aaff8000012f7f000000cafe00000117fc000001e7f80000033ff003b2001fc005ec003f800948007f0011a000fe00210001fc00768003f400be0007e800f1000fd001c0001fa0035c003f400ed8007d801a8000fb00314001f6005f4003ec00950007d8011b000fb001e4001f600384003ec016a8007d802c8000fb003b8001ee004ac003dc00920007b8011c000f7 else 0x14fe000b8029dc0000039bf800000727f000000e2fe000002e5fc0000035bf8000007fff0000015ffe0035c025f40016804bd800290097b001b2012ee0036c025bc006e804af800df0093f00000012fe00070025ec0000037bf8000006e7f000000dafe000001b1fc0000097ff800001327f00000272fe00000197fc000003f7f800000977f00000010fe000001a9fc0000034bf800000687f))) else (if c < 18 then (if c < 16 then 0x1f9fe000003e7fc000007b3f8000014b7f000001defe003c4031f400790063d800f300c77001e8018de0008c0317c007b0061f8000000c7f00070018be000001ebfc00000747f800000e57f000001c2fe00000517fc000006cbf800ef00b3f00000016fe000001ddfc000003b3f800000ceff00000195fe000004fffc00700053e800e100a7b0003e014ee0038c029bc00728052f800e700a3f else (if c < 17 then 0x249fe000004c3fc000009a3f80000120ff00000260fe000004cdfc000008e3f80000002ff000000b4fe000001effc00000417f800000577f000000f0fe00000207fc0000029ff800000747f00000101fe0000013ffc0000025bf8000003eff0000006bfe000000b3fc000008a7f80000111ff0000021dfe00000431fc0000084bf800001507f00000206fe003ec035bc0000006bf800001007f else 0x22c01ebe0000003dfc0000045ff8000008aff00000113fe000002d1fc00000bb3f80000083ff0000012ff60000025ffc0097801fd800000b07f0005601cf60009c039ec00248073d8010a00e770021801cde004380397c00880071f8000000e7f0000010ffe0000021bfc0000042ff80000084ff000000befe00000077fc0000095bf80000131ff0000026cfe000004a1fc0000098bf800001357f)) else (if c < 19 then 0x24fe000e0048fc00000807f800000fd7f000001f4fe000003cbfc00000c43f8000014bff000001dffe00490045dc0000008bf800000937f000001d2fe00000397fc000006ebf80000182ff0000028cfe00000367fc008d8083d8011c0107700040017de00080017bc008f0082f801200103f00000020fe000b8041bc0000047ff8000008eff0000019efe0000031bfc00000be7f800001407f else (if c < 20 then 0x242fe000004ddfc000009cff80000117ff00000007fe0000016bfc000004a3f8000009aff000000affe00000243fc000004cff800000547f00000119fe00000263fc00000283f80000046ff0000007ffe000000dbfc0000016ff800001157f00000224fe0000043dfc00000867f800001067f0000031afe00000543fc0000081ff8012a0127b00256024ee004b0049bc00968092f8002400dbf else 0x270011f60011c06ffc0000011ff8000016a7f000002ddfe000005cdfc00000b99f802e6023bf000002cefe000005b9fc00000b93f80000163ff000002dbfe000005c5bc00000b8bf802e2023ef000002bffe000005b5fc00000b83f8000015b7f000002d9fe000005bdfc000000f7f8000012bff00000271fe000004f3fc00000947f800001387f00000277fe00000495fc000009bff8000013aff))))) else (if c < 31 then (if c < 26 then (if c < 23 then (if c < 22 then 0x150fe0000029dfc0000065bf800000c77f000002fafe0000004dfc00000523f800000a37f00000144fe000004cbfc000003fbf80037008ff00066011fe00000023fc001a8047f80031008ff000000f8fe00000253fc00000503f80000078ff00000122fe0000027dfc000003a7f8000008d7f0000013cfe000001c1fc00000447f8000009d7f000000d7fe00000211fc000004e3d8000009c7f else 0x152fe000002c7fc000002a7f800000a57f00000161fe00000131fc0000023ff80000040ff0000006ffe000000bbfc000008aff80000112ff0000021ffe00000427fc00000837f8000018dff00000208fe00000059fc0000080bf800000fdff000001edfe000003cdfc00000c47f800000f07f0000002afe000002affc0000074ff800000e1ff000001bbfe0000060dfc000006d3f800000147f) else (if c < 24 then 0x16ffe000001e5fc0000054ff800000b6ff000000eafe00000297fc000005aff80000070ff00000142fe000002d3fc00000337f8004901bff00000049fe000005abfc00000baff80000179ff000002cffe000005d5fc00000bc7f800001647f000002e9fe000005dffc00000b03f800001747f000002edfe0000055bfc00000303f80000004ff000000b6fe000002b3fc00000597f800000587f else (if c < 25 then 0x6202eee000b804fdc002580bbb800370176f0005c029de005fc05d7c00c080b9f800000177f00000180fe000002fdfc000004e7f8000016fff00000130fe0000003bfc00188077f800000957f0000015bfe000002f3fc0000048ff800000aa7f00000177fe00000237fc00000533f800000baff00000112fe00000287fc000005cff800000807f0006e013fe00000027fc000003e7f800000ad7f else 0x281fe00a0407fbc000008ebf80000118ff00000083fe000000e3fc0000017ff800001167f00000226fe00000435fc00000853f800001077f0000031cfe00000545fc000000cbf80000101ff000001f5fe000003ddfc0000079ff800001897f00000298fe00000061fc0000061bf800000e67f000001c4fe00000379dc00de005fb800000de7f00000307fe0000051bdc01468107b80000146ff))) else (if c < 28 then (if c < 27 then 0xf3fe00000305fc00000647f80000075ff0000017bfe0000031ffc00000367f80000067ff00096025fe00000097fc00000b5bf8000017c7f000002fffe000005a1fc00000bdff8000017eff000002c9fe000005edfc00000beff8000015c7f000002affe00000185fc000000fff8000012c7f0000027efe0000050bfc0000094bf8000013eff00000283fe00000497fc000009f3f80000140ef else 0x15cfe00000315fc0000068ff800000aaff00000184fe00000343fc00000537f800000beff0000019ffe00000277fc00000b87f8000013a7f0003e01bfe0000003ffc000004aff800000c4ff0000019bfe00000249fc0000060ff800000ccff0000011cfe000002f9fc0000065f7800000cbff0032e01fde00000215fc0000099ff8002500aff00000015fe000001f5fc00000623f800000c9ff) else (if c < 29 then 0x1acfe0000036ffc000002c7f800000d2ff000001b5fe00000145fc0000026bf80000048ff00000073fe000000c3fc000008b7f800001107f0000021bfe0000042bfc0000083ff8000018eff000002a3fe00000413fc000000dbf800000fe7f000001f6fe000003dffc000007a3f80000189ff00000299fe000003c3fc000000d3f800000d57f00000174fe000002d5fc00000bbbf80000013ff else (if c < 30 then 0xfbfe0000035bfc000006fff8000007a7f000001a6fe0000037bfc0000038ff8000006dff000000d1fe0000009bfc00000b5ff800001827f0000030afe000005a3fc00000c0ff800001847f000002c2fe00000575fc00000ac7f800000627f00000041fe000004b3fc00000a2bf800001487f00000253fe00000513fc00000a3bf800001227f0000023cfe00000467fc0000002ff8000005bff else 0x1d4fe000002edfc000005b3f800001787f00000162fe00000053fc00000577f800000d7ff000001cffe000002adfc000006a3f800000e6ff00000145fe0000027bfc00000b8ff8000013b7f00000132fe00000043fc00108067f8004f010ff0000012cfe0000035dfc0000071ff80000092ff000001a7fe0000038bfc00000453f800000867f00000269fe00000205fc0000005ff8002300bff)))) else (if c < 36 then (if c < 33 then (if c < 32 then 0x63fe0000044ffc00000887f8000010e7f00000216fe008400377c00000842f800001087f0000031efe00a9008b7c00000a92f800001527f0041400fbe000004157c0000082bf80038018df0007002bbe0013c0717c001c00ddf80038016bf00000038fe00000341fc00000663f800000c87f000002fcfe00000505fc000000bff800000c5ff000001b0fe000003adfc00000617f800000d4ff else 0xedfe000001cbfc00000377f80000069ff0000004ffe000005b1fc00000c3ff8000018a7f000002cbfe00000589fc00000af3f80000159ff000000c6fe00000087fc0000096bf8000014aff0000029afe00a68086fc00000a69f80000126ff00000246fe0000047dfc000008d7f80000006ff000000b8fe000003b1fc0000078bf80000055ff000000a4fe00000139fc0000024ff80000042ff) else (if c < 34 then 0x1dcfe000003fbfc000005fff800000bc7f0000016efe000005e5fc00000593f80000015ff0000015efe000003b7fc000007dff800000a7ff00000147fe0000027ffc00000b97f8000013c7f00000134fe00000047fc000004b7f800000ed7f000001f0fe007c0046fc000007c1f8000008f7f00000116fe0000021dfc000009aff800000827f00000019fe000001f9fc00000767f800000f4ff else (if c < 35 then 0x255fe0000049ffc00000923f800001207f00000237fe0000001ffc000002cff80000056ff000000a6fe0000013dfc00000257f80000043ff00000075fe00000001fc00000757f800000e77f000001c6fe0000037dfc00000c27f80000147ff000001b6fe0000006bfc000006c7f800000eeff00000204fe00000345fc0000066bf800000c97f000002fefe00000509fc000000c7f800000c67f else 0x170fe000005e9fc0000059bf80000016ff00000158fe000002a3fc00000527f800000a0ff000002e7fe000004f5fc000004dbf80000012ff00000127fe00000241fc00000463f800000887f0000026dfe0000020dfc0000006ff8000007b7f000000effe000001cffc0000037ff8000006aff00000051fe000005a7fc00000b37f800001637f000002befe0000056bfc00000323f80000022ff))) else (if c < 39 then (if c < 37 then 0xe77e000001befc0028806df80045016bf0006600f7e0000040bfc000007fbf800000fc7f000001f1fe000003d5fc00000c57f8000014dff000001e3fe00000073fc0000075ff800000e87f000001c8fe00000381fc00000c2ff80000148ff000001b8fe0000006ffc000006aff800000d27f0000019cfe00000329fc00000c03f800001437f00000033fe0000030ffc00000607f800000bd7f else (if c < 38 then 0xa2de000d40637c000005fef80039011df0006a023be000c40477c0015808ef80000096df0000011ebe0000022d7c0000043af8003100cdf00056019be000001cb7c00000376f8004f011df0009e019be000005677c002180aef80031006df0006e0337e00000302fc001b8095f8002d012bf000001207e00000220fc001c806df8003700dbf0006601b7e000b4036fc000003d9f80000077bf else 0x124ee00000239dc0000042bb8003100af70004e015ee000001e7dc00000367b8004b00ff700096015ee0000055fdc001f809fb8003701aef000001ddde00774071bc001b8087780029010ef0000012cde00000219bc001b805f78003500bef0005e017de000a402fbc000003ef78000007a6f000000e3de000001b7bc0026805f780041014ef0006e00bde000bc017bc0014802f78000005bef)) else (if c < 40 then 0x3b6038f6000ac053ec000006a3d801a801a7b0005a027f6000a404fec0000062bd800000befb00314032f6005f405dec00168077d8002900efb0000012af600000237ec0015804fd80027009fb000000f2f6000001c3ec002480b7d80049014fb00092013f6000005abec00000b23d80027004fb00066031ee000003b9dc00ee00e3b8003300ff70006201fee000bc03fdc0013807fb80000095f7 else (if c < 41 then 0x3b2038fc0005c02bf8000005eff0017b0177e00036011fc0005c023f800098047f00000094fe0000011afc00000211f800948093f0011a0107e0021001cfc000ec027f8000a8017f00025011fd000001dafa00768071f40010807fe800000be7d002f802efa0008c023f4000f8047e8001d008fd000000f1fa000001c1f40000035fe80047008fd0007a01dfa0007c00ff4001680afd800000edfb else 0xd8067f000000ecfe)))))) >>> (39*(i%32))) &&& 0x7fffffffff
def table_8_1 (i : Nat) := let c := i/32; ((if c < 5 then (if c < 2 then (if c < 1 then 0x540295da8052000dc000540015ba8002000daa80520015900054001d7a8003000d6a8052001d5a80030015300054029cfa8053000cea80530014ba8053001c70000002abf00055000be000550293daa052000bc000550013baa002000baaa0520013900055001b7aa003000b6aa052001b5aa0030013300055029afaa053000aeaa0530012baa053001a70005502a1faa0540009eaa0540011baa05400197 else 0x110001b7000f6001b7000ef001b7000e7001b7000df001b700000001f7001f0001b700210001d70020a001d700197001e700138001f30012f001f300003000f600052001f5a4003000f4000030017306002000f2a400300171000000dcf700000029ef00053000ee000530296da6052000ec000530016ba6002000eaa60520016900053001e7a6003000e6a6052001e5a6003001630000002a5f00054000de) else (if c < 3 then 0x108001f6001da001f50017c001f5000f1001f5000e0001f5000d7001f5001db001f3001a8001f30018a001f30017d001f30012a001f30011b001f3000f2001f3000e1001f3001dd001e70012c001e70010c001e7000fb001e7000f4001e7000e3001e7000db001e7000b7001e7000a2001e70017f001d70012d001d70011e001d700116001d70010e001d7000e5001d7000dd001d700181001b700120001b7 else (if c < 4 then 0xdb0016b0017f0015b0012d0015b0011e0015b001160015b0010e0015b000e50015b000dd0015b001810013b001200013b001100013b000f60013b000ef0013b000e70013b000df0013b000000017b001f00013b0029a0013b002100015b002a40015b001970016b002810016b001bc001730028d0017300002000fa0005200179a4002000f80000013dfb001d9001f60017b001f600129001f60011a001f6 else 0x1f0000be00210000de00197000ee001bc000f600138000fa002e6000be002e2000ee000000297d00052000fc001d90017a0017b0017a001290017a0011a0017a001080017a001da001790017c00179000f100179000e000179000d700179001dc001730012b0017300124001730011c001730010a00173000f300173000d900173001dd0016b0012c0016b0010c0016b000fb0016b000f40016b000e30016b))) else (if c < 7 then (if c < 6 then 0x2c8000fa001dc000f60012b000f600124000f60011c000f60010a000f6000f3000f6000d9000f6002af000f6001dd000ee0012c000ee0010c000ee000fb000ee000f4000ee000e3000ee000db000ee0017f000de0012d000de0011e000de00116000de0010e000de000e5000de000dd000de002b3000de00181000be00120000be00110000be000f6000be000ef000be000e7000be000df000be00000000fe else 0xcbef00000140ef000000de7700000146f70000009c7b000001733f000001716f00000138fb00000137fb000000947700000090f70000008cf700000083f700000097fb000001317b000001307b00000078770000006b77001da000fc0017c000fc000f1000fc000e0000fc000d7000fc001db000fa001a8000fa0018a000fa0017d000fa0012a000fa0011b000fa000f2000fa000e1000fa002d5000fa) else (if c < 8 then 0x6cf700000157f7000000eeef000000966f000000866f0000007def0000007a6f00000071ef0000006def0000005bef000000516f000000bfdf00000096df0000008f5f0000008b5f000000875f00000072df0000006edf00000159df000000c0bf000000903f000000883f0000007b3f00000077bf00000073bf0000006fbf000000007f000000f83f0000014d3f000001085f000001525f000001055f else (if c < 9 then 0x94fe0000008d7e000000847e0000016efe0000016dfe0000016cfe000000ed7d000000be7d00000078fd000000707d0000006bfd000000edfb0000014afb000000d47b00000144fb000000c57b000000befb0000013f7b0000013e7b000000957b0000008dfb000000797b00000070fb0000016afb000001647b000000ee77000000ec7700000095f700000092770000008e77000000857700000079f7 else 0xecfe00000187fe000000bdfe0000017b7e)))) >>> (40*(i%32))) &&& 0xffffffffff
def count8 (t : Nat) := if t < 2 then (if t < 1 then 1314 else 292) else 0
def front8 (t i : Nat) := (if t < 1 then table_8_0 i else table_8_1 i)
def L8 : Layer where
  count := count8
  state t i := front (front8 t i)
  pick t v := (internalChoice (stateKey 8 t v))-1
def table_7_0 (i : Nat) := let c := i/32; ((if c < 12 then (if c < 6 then (if c < 3 then (if c < 1 then 0x51a040ce005ec07dd800be00fba8019701f670050203ece00420079f0009c00f3c800d701d7c0027003af400000b78fc000016eaf801d90065e003b400cba007740193c00f80030f8017b0056e0037800ace00000b71ec00001693d801080047a00218008d600440010ec000016dbe800002da7e001c6004dc006f0009d800001197d800002006f000003feee000007f9ec00000febe800001fc7e else (if c < 2 then 0x1ba048b60000112df400002233e8000043c7d000007677e00000ecb7c00001d8f7800003b0f70000075bbe00000ea6fc00001d46f8000039fdf0000073dde00000e9fdc00001d17b8000039df70000074df600000e73ec00001d7ff000003a5fe00000737fc00764088f800ed0111e802100221f005480443e007640857800ed010ae801f00211f005340423e005ec081b800be01036801bc02067 else 0x220012760000113cfc00002272f8000044d6f00000898ee00001128fc0000224af800004486f0000088a7e00001100fc041a0007d8083d000fd0025405076004ac0a0dc009601417800fb0282f0025a0503e003c809d6c0079813ab8000043f6f00000874de0046c099ac008e013338011e0264f0024004c5e003bc098bc000021f3b800e102573001ca04aae0000111dec000021ebd800d902473)) else (if c < 4 then 0xaae1387600000271ec041c0b99d800001733f00000cb27e020dc5c5ac00000b8b7802e61712f00000c89de0000107bf40000568fe80224008fd0000156cfa008400487c00de0083380552097eb0000012ff6000017a7ec00002f0bd800d900e73001ba01cb60000155d7c00002aabb80000a527e003f2011fc007680317400f80060f8017c00a750032e014ce00001407ec000027bfd8010c0096b else (if c < 5 then 0x14c6ee00002979dc00004c93b8000097877000012e6ee00002555dc00de00df3801bc014e7003780e3ce015683795c02ad86f1b800000de770051a029ce0000051bdc000047ffb800008e3f700000fefde0039405d5c009000b97800007b83f00000f6cde00002ab7ec00005543d80000a26fb0000143ff6000025dfec00004b83d800008927b00000d37f601550271cc02aa84e358055609c5b else 0x1552be00002a7d7c000054eaf8021001b9f0042002d3e008401ec7c00000842f802a40169f000002a4be000029f37c0000082af80000a72df000012ee7e00002b23bc00005617780000aacef000014a1de00002925bc0000512b7800008b5ef00001125de00002246fc0000447f78000088c6f00abc1979e0157c32ebc0000065f78000086bef00000281de00002013bc000056a7b80000ad0f7))) else (if c < 9 then (if c < 7 then 0x4b57e0000095efc00001289f8000024ebf000004977e000007e4fc00000f95f800001e03f00000000fe00002998fc000052f5f80000a513f000014937e000028f8fc00005141f80000a25bf000014467e00002882fc000007c1f80000a113f0000029a7e00002770fc00004e39f80000ad55f000015a2be00002b3d7c0000563af80000ac35f00001576be00002add7c0000557af80000aab5f else (if c < 8 then 0xac37e0000157cfc00002ae1f800004da3f000009ac7e00001348fc000003d9f800004c03f000009787e000001defc00002551f800004a7bf000000e77e00001266fc000024b9f8000006fbf000009097e00001208fc000023f9f80000461bf000008be7e00001170fc000022c5f800003d63f0000077d7e00000ee0fc00001c4df8000030bbf000005fe7e00000bd6fc00001799f800002f03f else 0x7aabe000005677c00001e1af800003bddf00000775be00000edd7c014d00acf8000030adf00000607be00000bf97c000017daf800002ef5f000004bebe000009677c000012b6f8000024adf0000038dbe0000070d7c00000daef800002afbf000010a17e00000ab6fc00000605f800007bf3f00000d4c7e000019eafc0000155df800005a1bf000001207e00001634fc00002bb9f800000883f)) else (if c < 10 then 0xb48be000016837c00002ccaf8012008f1f0000011ebe0000163d7c00002c4ef800005825f00000116be000015ef7c00002bb2f8000056f5f0022010e3e0000021d7c00002b1ef8000055e5f00000ab6be0000129b7c00738394f80000072df00000937be000012597c006f8374f8000006edf0000090dbe000012057c000023f2f80000463df000008bcbe0000116d7c000022bef801f00279f else (if c < 11 then 0x53fde002dc036bc000002df7800002856f000000a2de000009a9bc0000133f78000025eef000004abde0000094bbc00001283780000249ef0000047ade00000abd7c00003e52f800002ad5f0030217f3e000002ff7c00003e0af800006a55f00000cddbe00000aad7c007b008cf8000041b5f00000badbe0000174d7c00002e5ef8012d00d9f0000012dbe007c00627c00f800acf801f00969f else 0x9a2de003d00473c007b03d178000007a6f00000984de00001297bc0072838e7800e7071af000000e3de0000126dbc000024c778000048c6f001ba0db9e0037c1b6bc0000036f7800004866f00000907de000011f5bc0000231b780000460ef000008b4de0000115bbc00001fab7800003c2ef0000076cde00000e1fbc000019577800003036f000005eede00000bd3bc00001773780120005af)))) else (if c < 18 then (if c < 15 then (if c < 13 then 0x13a7de00000ac9bc000007777805690f82f00ac82109e00001f41bc0000366378000068eef00000555de00001811bc00002e9378012d0964f0025801b5e00000259bc009600e17800005a76f00000af6de00000aa5bc008704327801100862f0000010cde0000158dbc00002b0778000055a6f00000a43de0047802f3c0090005d7800004f66f000009dade000013a5bc000003ef7800004d56f else (if c < 14 then 0x1b60d9ce003741b35c006f8365b8000006cf70000090bee0000120ddc00002403b80000462f7000008c0ee00001175dc000022afb80197025e7000007e9ee00acc55f5c00000abfb800003c2770000077fee00000ef3dc00001dabb8000032a7700502027ce00000c0bdc00001803b800002fd77000005e8ee0000089fdc00001103b80000212f7003ba0319e005fc06f3c000015a7780000a06ef else 0xb6fee000016c1dc00000493b800005a6f700000b3fee00001661dc008e005f38011c005e70023c11cae00480238dc00000473b8000058ef700000b18ee0065c0639c00cb809f38019708e6700000adaee004302159c0087042ab80110085370000010aee0000158bdc00002b03b8000055d77000009a0ee003d01e79c0079808eb800f6079b7000000f3ee003cc0715c0000260fb800004a977)) else (if c < 16 then 0x71ef600000e03ec00001427d800002747b000004bcf600000963ec0000127fd801dd0ee6700000568ee00604062dc00004ddfb800002b1f7003b80376e000003b9dc02b407c1b805631085700001173ee00001b2fdc0000341fb800002aa77001c601fce0039403f5c0073807db800005daf700000835ee00001745dc00002e4fb8012c095e70025a12bae004ac036dc000004afb800005bff7 else (if c < 17 then 0x1ec0f276000001e5ec007900e2d800004c17b00000951f60038403fcc007183875800e5070db001ce0e176000001c3ec007080bb98000049afb00000930f600001255ec00002313d8000045ffb000008b9f600001165ec00860127580110024bb003a0049f60000104bec00000b57d800003f47b000002c8f600000f99ec00001f1fd800003d9fb000007a8f600000f07ec00001de3d80000396fb else 0x30217d76000002fbec00003e07d800007be7b00aba197d601564379cee014809f18000041c7b00000837f600001069ec009584ab98012c0956b0025a12ab6004a8036ec000004abd8012a01c3b00000b4cf600470237cc008d805f58011b005eb0023c11bb600480236ec0000046fd8011b0176b00000b1cf60000162fec00002bd7d800005757b000009a8f6003cc1e5cc007a03cb5800f2011db))) else (if c < 21 then (if c < 19 then 0x3ba1dbd600430057ac006e80b6d80000a42fb00000567f6000027d7ec008800add800009c1fb00000562f6000003b7ec02b387c1d805621085be005a02b3600002501ec006e80a6d800008ca7b00001189f6000022ffec000006a3d800008b97b00001106f600000abbec000041f3d8000082cfb00218027d60044004eec00003f93d800007e8fb0000018af600001f3fec00001567d8017f0bedb else (if c < 20 then 0x1c60e0da003941c17400738381e800000707d00000934fa0000125ff4000024a7e800d7016f9001ae029f2003641afd4006d835f6800dd06bdd001be0d77a000001aff40000242be80000482fd000008fffa000011f1f4009c035fc800003f3fd000007a7fa00000ca7f400001867e80000309fd000005e7fa00000bb5f400001423e8000024f7d00000491fa007703b7cc006c80b79800d9014f3 else 0x3b404fba00000ac3f400ed00dde801da016bd000001dafa007c03b4f402b08842e800008b8fd00000f9efa00000ab1f400be00df68017c014ed002fe17cba006042f8f4000005f3e800007c07d00000f7bfa0065c2f9b402ac06f3a800006cb7d00000d48fa0000134df40000267be800f2078f9001e60f1ea003d01e3b4007b03c5e80000078fd00000981fa000012a1f400002527e800e107079)) else (if c < 22 then 0x210027f400420093e800850423b0010c0846e0021c108bc00440210f800000423f000005627e00000abffc00001573f800002acbf001380847a003b20247c005ec041b80000194bf0000031b7e00000612fc00000c09f8000017e7f00000283fe000004bbfc00000961f8000012a7f001db0ed79002fa17cf2007703b5d400be00c7a8017c013f5002f804bea007743b5b400ed00c6e801da015dd else (if c < 23 then 0x55cfc0157032fb800003e77f0017b01bee002f6029dc005fc2f77800c085edf000000bdfe00000f7ffc00001ef5f800de05efb000006cafe00000d47fc00001067f800002e83f0012a094fa00256129ec004b0253b8009684a6f00000094fe00000b4bfc0000167bf8008d846bd0011c08d760023c11abc00480234f80000046bf0000058dfe00000b16fc000015e9f800002ba7f00108015fa else 0x1da0ecfc002f817bf91805c023f1f00d8047e001db0ecfa002fa17bf4007703b3d800bd80c7b0017b013f6002f604bec007743b3b800ec80c6f001d9015de003b204fbc00000acdf802b307c1f001d901bbe003b202d7c000003b3f801080766f000008b87e))))) >>> (39*(i%32))) &&& 0x7fffffffff
def table_7_1 (i : Nat) := let c := i/32; (0 >>> (1*(i%32))) &&& 0x1
def count7 (t : Nat) := if t < 2 then (if t < 1 then 757 else 0) else 0
def front7 (t i : Nat) := (if t < 1 then table_7_0 i else table_7_1 i)
def L7 : Layer where
  count := count7
  state t i := front (front7 t i)
  pick t v := (internalChoice (stateKey 7 t v))-1
def table_6_0 (i : Nat) := let c := i/32; ((if c < 1 then 0x5f01cb54001da079d5001590ac334005690ed2d0015841ec740055f0be2d0020d0023e40055506be900155c1aee4005552aa6300155caa8cc0010c06ce30004401b2cc005562aacb0004301bb2c005572ab1b0004401ba6c002100951b0006f02378c001f00791b00065c1c38c005642b1c70015a4ad09c0055b2ad17000002c3d9c00197072c70007c01e65c0055f2af0f0008402583c00000b0f9f0006f02409c0083d024f9 else (if c < 2 then 0x15642f7cbb202d0159a0015883b368005672b33a001574ab9a8001d90953a0005ec237a8005630ecd60015a0accd80055c08e660015682f758005692b32e000764258b8005660969e001578ab9380055f2ae2e0005ec240b8009a8008fa001550211c8005560845a001564ab1c6f8029013e1001588ac367b402d0159900159c3b4e40055d0be690007681e5640017c070f100158cac35400558071e5001568ab1540055b2ac35 else 0x2f6029013e2)) >>> (42*(i%32))) &&& 0x3ffffffffff
def count6 (t : Nat) := if t < 1 then 65 else 0
def front6 (t i : Nat) := table_6_0 i
def L6 : Layer where
  count := count6
  state t i := front (front6 t i)
  pick t v := (internalChoice (stateKey 6 t v))-1
def table_5_0 (i : Nat) := let c := i/32; (0 >>> (1*(i%32))) &&& 0x1
def count5 (t : Nat) := if t < 1 then 0 else 0
def front5 (t i : Nat) := table_5_0 i
def L5 : Layer where
  count := count5
  state t i := front (front5 t i)
  pick t v := (internalChoice (stateKey 5 t v))-1
def pass5 (t i : Nat) := bookPass emptyLayer book 4 t (L5.state t i)
private theorem done_5_0 (i : Nat) (hi : i<0) : pass5 0 i=true := by omega
theorem good5 : L5.Valid 5 := by
  intro t i hi
  have ht : t < 1 := by
    by_contra hx
    simp [L5,count5,hx] at hi
  have hc : pass5 t i = true := by
    interval_cases t
    · exact done_5_0 i hi
  exact bookPass_ok (emptyLayer_ok 4) goodBook hc
def pass6 (t i : Nat) := bookPass L5 book 5 t (L6.state t i)
private theorem blk_6_0_0 : span (pass6 0) 8 0=true := by decide +kernel
private theorem blk_6_0_8 : span (pass6 0) 8 8=true := by decide +kernel
private theorem blk_6_0_16 : span (pass6 0) 8 16=true := by decide +kernel
private theorem blk_6_0_24 : span (pass6 0) 8 24=true := by decide +kernel
private theorem blk_6_0_32 : span (pass6 0) 8 32=true := by decide +kernel
private theorem blk_6_0_40 : span (pass6 0) 8 40=true := by decide +kernel
private theorem blk_6_0_48 : span (pass6 0) 8 48=true := by decide +kernel
private theorem blk_6_0_56 : span (pass6 0) 8 56=true := by decide +kernel
private theorem blk_6_0_64 : span (pass6 0) 1 64=true := by decide +kernel
private theorem done_6_0 (i : Nat) (hi : i<65) : pass6 0 i=true := (if h : i < 32 then (if h : i < 16 then (if h : i < 8 then span_range blk_6_0_0 i (by omega) (by omega) else span_range blk_6_0_8 i (by omega) (by omega)) else (if h : i < 24 then span_range blk_6_0_16 i (by omega) (by omega) else span_range blk_6_0_24 i (by omega) (by omega))) else (if h : i < 48 then (if h : i < 40 then span_range blk_6_0_32 i (by omega) (by omega) else span_range blk_6_0_40 i (by omega) (by omega)) else (if h : i < 56 then span_range blk_6_0_48 i (by omega) (by omega) else (if h : i < 64 then span_range blk_6_0_56 i (by omega) (by omega) else span_range blk_6_0_64 i (by omega) (by omega)))))
theorem good6 : L6.Valid 6 := by
  intro t i hi
  have ht : t < 1 := by
    by_contra hx
    simp [L6,count6,hx] at hi
  have hc : pass6 t i = true := by
    interval_cases t
    · exact done_6_0 i hi
  exact bookPass_ok good5 goodBook hc
def pass7 (t i : Nat) := bookPass L6 book 6 t (L7.state t i)
private theorem blk_7_0_0 : span (pass7 0) 8 0=true := by decide +kernel
private theorem blk_7_0_8 : span (pass7 0) 8 8=true := by decide +kernel
private theorem blk_7_0_16 : span (pass7 0) 8 16=true := by decide +kernel
private theorem blk_7_0_24 : span (pass7 0) 8 24=true := by decide +kernel
private theorem blk_7_0_32 : span (pass7 0) 8 32=true := by decide +kernel
private theorem blk_7_0_40 : span (pass7 0) 8 40=true := by decide +kernel
private theorem blk_7_0_48 : span (pass7 0) 8 48=true := by decide +kernel
private theorem blk_7_0_56 : span (pass7 0) 8 56=true := by decide +kernel
private theorem blk_7_0_64 : span (pass7 0) 8 64=true := by decide +kernel
private theorem blk_7_0_72 : span (pass7 0) 8 72=true := by decide +kernel
private theorem blk_7_0_80 : span (pass7 0) 8 80=true := by decide +kernel
private theorem blk_7_0_88 : span (pass7 0) 8 88=true := by decide +kernel
private theorem blk_7_0_96 : span (pass7 0) 8 96=true := by decide +kernel
private theorem blk_7_0_104 : span (pass7 0) 8 104=true := by decide +kernel
private theorem blk_7_0_112 : span (pass7 0) 8 112=true := by decide +kernel
private theorem blk_7_0_120 : span (pass7 0) 8 120=true := by decide +kernel
private theorem blk_7_0_128 : span (pass7 0) 8 128=true := by decide +kernel
private theorem blk_7_0_136 : span (pass7 0) 8 136=true := by decide +kernel
private theorem blk_7_0_144 : span (pass7 0) 8 144=true := by decide +kernel
private theorem blk_7_0_152 : span (pass7 0) 8 152=true := by decide +kernel
private theorem blk_7_0_160 : span (pass7 0) 8 160=true := by decide +kernel
private theorem blk_7_0_168 : span (pass7 0) 8 168=true := by decide +kernel
private theorem blk_7_0_176 : span (pass7 0) 8 176=true := by decide +kernel
private theorem blk_7_0_184 : span (pass7 0) 8 184=true := by decide +kernel
private theorem blk_7_0_192 : span (pass7 0) 8 192=true := by decide +kernel
private theorem blk_7_0_200 : span (pass7 0) 8 200=true := by decide +kernel
private theorem blk_7_0_208 : span (pass7 0) 8 208=true := by decide +kernel
private theorem blk_7_0_216 : span (pass7 0) 8 216=true := by decide +kernel
private theorem blk_7_0_224 : span (pass7 0) 8 224=true := by decide +kernel
private theorem blk_7_0_232 : span (pass7 0) 8 232=true := by decide +kernel
private theorem blk_7_0_240 : span (pass7 0) 8 240=true := by decide +kernel
private theorem blk_7_0_248 : span (pass7 0) 8 248=true := by decide +kernel
private theorem blk_7_0_256 : span (pass7 0) 8 256=true := by decide +kernel
private theorem blk_7_0_264 : span (pass7 0) 8 264=true := by decide +kernel
private theorem blk_7_0_272 : span (pass7 0) 8 272=true := by decide +kernel
private theorem blk_7_0_280 : span (pass7 0) 8 280=true := by decide +kernel
private theorem blk_7_0_288 : span (pass7 0) 8 288=true := by decide +kernel
private theorem blk_7_0_296 : span (pass7 0) 8 296=true := by decide +kernel
private theorem blk_7_0_304 : span (pass7 0) 8 304=true := by decide +kernel
private theorem blk_7_0_312 : span (pass7 0) 8 312=true := by decide +kernel
private theorem blk_7_0_320 : span (pass7 0) 8 320=true := by decide +kernel
private theorem blk_7_0_328 : span (pass7 0) 8 328=true := by decide +kernel
private theorem blk_7_0_336 : span (pass7 0) 8 336=true := by decide +kernel
private theorem blk_7_0_344 : span (pass7 0) 8 344=true := by decide +kernel
private theorem blk_7_0_352 : span (pass7 0) 8 352=true := by decide +kernel
private theorem blk_7_0_360 : span (pass7 0) 8 360=true := by decide +kernel
private theorem blk_7_0_368 : span (pass7 0) 8 368=true := by decide +kernel
private theorem blk_7_0_376 : span (pass7 0) 8 376=true := by decide +kernel
private theorem blk_7_0_384 : span (pass7 0) 8 384=true := by decide +kernel
private theorem blk_7_0_392 : span (pass7 0) 8 392=true := by decide +kernel
private theorem blk_7_0_400 : span (pass7 0) 8 400=true := by decide +kernel
private theorem blk_7_0_408 : span (pass7 0) 8 408=true := by decide +kernel
private theorem blk_7_0_416 : span (pass7 0) 8 416=true := by decide +kernel
private theorem blk_7_0_424 : span (pass7 0) 8 424=true := by decide +kernel
private theorem blk_7_0_432 : span (pass7 0) 8 432=true := by decide +kernel
private theorem blk_7_0_440 : span (pass7 0) 8 440=true := by decide +kernel
private theorem blk_7_0_448 : span (pass7 0) 8 448=true := by decide +kernel
private theorem blk_7_0_456 : span (pass7 0) 8 456=true := by decide +kernel
private theorem blk_7_0_464 : span (pass7 0) 8 464=true := by decide +kernel
private theorem blk_7_0_472 : span (pass7 0) 8 472=true := by decide +kernel
private theorem blk_7_0_480 : span (pass7 0) 8 480=true := by decide +kernel
private theorem blk_7_0_488 : span (pass7 0) 8 488=true := by decide +kernel
private theorem blk_7_0_496 : span (pass7 0) 8 496=true := by decide +kernel
private theorem blk_7_0_504 : span (pass7 0) 8 504=true := by decide +kernel
private theorem blk_7_0_512 : span (pass7 0) 8 512=true := by decide +kernel
private theorem blk_7_0_520 : span (pass7 0) 8 520=true := by decide +kernel
private theorem blk_7_0_528 : span (pass7 0) 8 528=true := by decide +kernel
private theorem blk_7_0_536 : span (pass7 0) 8 536=true := by decide +kernel
private theorem blk_7_0_544 : span (pass7 0) 8 544=true := by decide +kernel
private theorem blk_7_0_552 : span (pass7 0) 8 552=true := by decide +kernel
private theorem blk_7_0_560 : span (pass7 0) 8 560=true := by decide +kernel
private theorem blk_7_0_568 : span (pass7 0) 8 568=true := by decide +kernel
private theorem blk_7_0_576 : span (pass7 0) 8 576=true := by decide +kernel
private theorem blk_7_0_584 : span (pass7 0) 8 584=true := by decide +kernel
private theorem blk_7_0_592 : span (pass7 0) 8 592=true := by decide +kernel
private theorem blk_7_0_600 : span (pass7 0) 8 600=true := by decide +kernel
private theorem blk_7_0_608 : span (pass7 0) 8 608=true := by decide +kernel
private theorem blk_7_0_616 : span (pass7 0) 8 616=true := by decide +kernel
private theorem blk_7_0_624 : span (pass7 0) 8 624=true := by decide +kernel
private theorem blk_7_0_632 : span (pass7 0) 8 632=true := by decide +kernel
private theorem blk_7_0_640 : span (pass7 0) 8 640=true := by decide +kernel
private theorem blk_7_0_648 : span (pass7 0) 8 648=true := by decide +kernel
private theorem blk_7_0_656 : span (pass7 0) 8 656=true := by decide +kernel
private theorem blk_7_0_664 : span (pass7 0) 8 664=true := by decide +kernel
private theorem blk_7_0_672 : span (pass7 0) 8 672=true := by decide +kernel
private theorem blk_7_0_680 : span (pass7 0) 8 680=true := by decide +kernel
private theorem blk_7_0_688 : span (pass7 0) 8 688=true := by decide +kernel
private theorem blk_7_0_696 : span (pass7 0) 8 696=true := by decide +kernel
private theorem blk_7_0_704 : span (pass7 0) 8 704=true := by decide +kernel
private theorem blk_7_0_712 : span (pass7 0) 8 712=true := by decide +kernel
private theorem blk_7_0_720 : span (pass7 0) 8 720=true := by decide +kernel
private theorem blk_7_0_728 : span (pass7 0) 8 728=true := by decide +kernel
private theorem blk_7_0_736 : span (pass7 0) 8 736=true := by decide +kernel
private theorem blk_7_0_744 : span (pass7 0) 8 744=true := by decide +kernel
private theorem blk_7_0_752 : span (pass7 0) 5 752=true := by decide +kernel
private theorem done_7_0 (i : Nat) (hi : i<757) : pass7 0 i=true := (if h : i < 376 then (if h : i < 184 then (if h : i < 88 then (if h : i < 40 then (if h : i < 16 then (if h : i < 8 then span_range blk_7_0_0 i (by omega) (by omega) else span_range blk_7_0_8 i (by omega) (by omega)) else (if h : i < 24 then span_range blk_7_0_16 i (by omega) (by omega) else (if h : i < 32 then span_range blk_7_0_24 i (by omega) (by omega) else span_range blk_7_0_32 i (by omega) (by omega)))) else (if h : i < 64 then (if h : i < 48 then span_range blk_7_0_40 i (by omega) (by omega) else (if h : i < 56 then span_range blk_7_0_48 i (by omega) (by omega) else span_range blk_7_0_56 i (by omega) (by omega))) else (if h : i < 72 then span_range blk_7_0_64 i (by omega) (by omega) else (if h : i < 80 then span_range blk_7_0_72 i (by omega) (by omega) else span_range blk_7_0_80 i (by omega) (by omega))))) else (if h : i < 136 then (if h : i < 112 then (if h : i < 96 then span_range blk_7_0_88 i (by omega) (by omega) else (if h : i < 104 then span_range blk_7_0_96 i (by omega) (by omega) else span_range blk_7_0_104 i (by omega) (by omega))) else (if h : i < 120 then span_range blk_7_0_112 i (by omega) (by omega) else (if h : i < 128 then span_range blk_7_0_120 i (by omega) (by omega) else span_range blk_7_0_128 i (by omega) (by omega)))) else (if h : i < 160 then (if h : i < 144 then span_range blk_7_0_136 i (by omega) (by omega) else (if h : i < 152 then span_range blk_7_0_144 i (by omega) (by omega) else span_range blk_7_0_152 i (by omega) (by omega))) else (if h : i < 168 then span_range blk_7_0_160 i (by omega) (by omega) else (if h : i < 176 then span_range blk_7_0_168 i (by omega) (by omega) else span_range blk_7_0_176 i (by omega) (by omega)))))) else (if h : i < 280 then (if h : i < 232 then (if h : i < 208 then (if h : i < 192 then span_range blk_7_0_184 i (by omega) (by omega) else (if h : i < 200 then span_range blk_7_0_192 i (by omega) (by omega) else span_range blk_7_0_200 i (by omega) (by omega))) else (if h : i < 216 then span_range blk_7_0_208 i (by omega) (by omega) else (if h : i < 224 then span_range blk_7_0_216 i (by omega) (by omega) else span_range blk_7_0_224 i (by omega) (by omega)))) else (if h : i < 256 then (if h : i < 240 then span_range blk_7_0_232 i (by omega) (by omega) else (if h : i < 248 then span_range blk_7_0_240 i (by omega) (by omega) else span_range blk_7_0_248 i (by omega) (by omega))) else (if h : i < 264 then span_range blk_7_0_256 i (by omega) (by omega) else (if h : i < 272 then span_range blk_7_0_264 i (by omega) (by omega) else span_range blk_7_0_272 i (by omega) (by omega))))) else (if h : i < 328 then (if h : i < 304 then (if h : i < 288 then span_range blk_7_0_280 i (by omega) (by omega) else (if h : i < 296 then span_range blk_7_0_288 i (by omega) (by omega) else span_range blk_7_0_296 i (by omega) (by omega))) else (if h : i < 312 then span_range blk_7_0_304 i (by omega) (by omega) else (if h : i < 320 then span_range blk_7_0_312 i (by omega) (by omega) else span_range blk_7_0_320 i (by omega) (by omega)))) else (if h : i < 352 then (if h : i < 336 then span_range blk_7_0_328 i (by omega) (by omega) else (if h : i < 344 then span_range blk_7_0_336 i (by omega) (by omega) else span_range blk_7_0_344 i (by omega) (by omega))) else (if h : i < 360 then span_range blk_7_0_352 i (by omega) (by omega) else (if h : i < 368 then span_range blk_7_0_360 i (by omega) (by omega) else span_range blk_7_0_368 i (by omega) (by omega))))))) else (if h : i < 568 then (if h : i < 472 then (if h : i < 424 then (if h : i < 400 then (if h : i < 384 then span_range blk_7_0_376 i (by omega) (by omega) else (if h : i < 392 then span_range blk_7_0_384 i (by omega) (by omega) else span_range blk_7_0_392 i (by omega) (by omega))) else (if h : i < 408 then span_range blk_7_0_400 i (by omega) (by omega) else (if h : i < 416 then span_range blk_7_0_408 i (by omega) (by omega) else span_range blk_7_0_416 i (by omega) (by omega)))) else (if h : i < 448 then (if h : i < 432 then span_range blk_7_0_424 i (by omega) (by omega) else (if h : i < 440 then span_range blk_7_0_432 i (by omega) (by omega) else span_range blk_7_0_440 i (by omega) (by omega))) else (if h : i < 456 then span_range blk_7_0_448 i (by omega) (by omega) else (if h : i < 464 then span_range blk_7_0_456 i (by omega) (by omega) else span_range blk_7_0_464 i (by omega) (by omega))))) else (if h : i < 520 then (if h : i < 496 then (if h : i < 480 then span_range blk_7_0_472 i (by omega) (by omega) else (if h : i < 488 then span_range blk_7_0_480 i (by omega) (by omega) else span_range blk_7_0_488 i (by omega) (by omega))) else (if h : i < 504 then span_range blk_7_0_496 i (by omega) (by omega) else (if h : i < 512 then span_range blk_7_0_504 i (by omega) (by omega) else span_range blk_7_0_512 i (by omega) (by omega)))) else (if h : i < 544 then (if h : i < 528 then span_range blk_7_0_520 i (by omega) (by omega) else (if h : i < 536 then span_range blk_7_0_528 i (by omega) (by omega) else span_range blk_7_0_536 i (by omega) (by omega))) else (if h : i < 552 then span_range blk_7_0_544 i (by omega) (by omega) else (if h : i < 560 then span_range blk_7_0_552 i (by omega) (by omega) else span_range blk_7_0_560 i (by omega) (by omega)))))) else (if h : i < 664 then (if h : i < 616 then (if h : i < 592 then (if h : i < 576 then span_range blk_7_0_568 i (by omega) (by omega) else (if h : i < 584 then span_range blk_7_0_576 i (by omega) (by omega) else span_range blk_7_0_584 i (by omega) (by omega))) else (if h : i < 600 then span_range blk_7_0_592 i (by omega) (by omega) else (if h : i < 608 then span_range blk_7_0_600 i (by omega) (by omega) else span_range blk_7_0_608 i (by omega) (by omega)))) else (if h : i < 640 then (if h : i < 624 then span_range blk_7_0_616 i (by omega) (by omega) else (if h : i < 632 then span_range blk_7_0_624 i (by omega) (by omega) else span_range blk_7_0_632 i (by omega) (by omega))) else (if h : i < 648 then span_range blk_7_0_640 i (by omega) (by omega) else (if h : i < 656 then span_range blk_7_0_648 i (by omega) (by omega) else span_range blk_7_0_656 i (by omega) (by omega))))) else (if h : i < 712 then (if h : i < 688 then (if h : i < 672 then span_range blk_7_0_664 i (by omega) (by omega) else (if h : i < 680 then span_range blk_7_0_672 i (by omega) (by omega) else span_range blk_7_0_680 i (by omega) (by omega))) else (if h : i < 696 then span_range blk_7_0_688 i (by omega) (by omega) else (if h : i < 704 then span_range blk_7_0_696 i (by omega) (by omega) else span_range blk_7_0_704 i (by omega) (by omega)))) else (if h : i < 736 then (if h : i < 720 then span_range blk_7_0_712 i (by omega) (by omega) else (if h : i < 728 then span_range blk_7_0_720 i (by omega) (by omega) else span_range blk_7_0_728 i (by omega) (by omega))) else (if h : i < 744 then span_range blk_7_0_736 i (by omega) (by omega) else (if h : i < 752 then span_range blk_7_0_744 i (by omega) (by omega) else span_range blk_7_0_752 i (by omega) (by omega))))))))
private theorem done_7_1 (i : Nat) (hi : i<0) : pass7 1 i=true := by omega
theorem good7 : L7.Valid 7 := by
  intro t i hi
  have ht : t < 2 := by
    by_contra hx
    simp [L7,count7,hx] at hi
  have hc : pass7 t i = true := by
    interval_cases t
    · exact done_7_0 i hi
    · exact done_7_1 i hi
  exact bookPass_ok good6 goodBook hc
def pass8 (t i : Nat) := bookPass L7 book 7 t (L8.state t i)
private theorem blk_8_0_0 : span (pass8 0) 8 0=true := by decide +kernel
private theorem blk_8_0_8 : span (pass8 0) 8 8=true := by decide +kernel
private theorem blk_8_0_16 : span (pass8 0) 8 16=true := by decide +kernel
private theorem blk_8_0_24 : span (pass8 0) 8 24=true := by decide +kernel
private theorem blk_8_0_32 : span (pass8 0) 8 32=true := by decide +kernel
private theorem blk_8_0_40 : span (pass8 0) 8 40=true := by decide +kernel
private theorem blk_8_0_48 : span (pass8 0) 8 48=true := by decide +kernel
private theorem blk_8_0_56 : span (pass8 0) 8 56=true := by decide +kernel
private theorem blk_8_0_64 : span (pass8 0) 8 64=true := by decide +kernel
private theorem blk_8_0_72 : span (pass8 0) 8 72=true := by decide +kernel
private theorem blk_8_0_80 : span (pass8 0) 8 80=true := by decide +kernel
private theorem blk_8_0_88 : span (pass8 0) 8 88=true := by decide +kernel
private theorem blk_8_0_96 : span (pass8 0) 8 96=true := by decide +kernel
private theorem blk_8_0_104 : span (pass8 0) 8 104=true := by decide +kernel
private theorem blk_8_0_112 : span (pass8 0) 8 112=true := by decide +kernel
private theorem blk_8_0_120 : span (pass8 0) 8 120=true := by decide +kernel
private theorem blk_8_0_128 : span (pass8 0) 8 128=true := by decide +kernel
private theorem blk_8_0_136 : span (pass8 0) 8 136=true := by decide +kernel
private theorem blk_8_0_144 : span (pass8 0) 8 144=true := by decide +kernel
private theorem blk_8_0_152 : span (pass8 0) 8 152=true := by decide +kernel
private theorem blk_8_0_160 : span (pass8 0) 8 160=true := by decide +kernel
private theorem blk_8_0_168 : span (pass8 0) 8 168=true := by decide +kernel
private theorem blk_8_0_176 : span (pass8 0) 8 176=true := by decide +kernel
private theorem blk_8_0_184 : span (pass8 0) 8 184=true := by decide +kernel
private theorem blk_8_0_192 : span (pass8 0) 8 192=true := by decide +kernel
private theorem blk_8_0_200 : span (pass8 0) 8 200=true := by decide +kernel
private theorem blk_8_0_208 : span (pass8 0) 8 208=true := by decide +kernel
private theorem blk_8_0_216 : span (pass8 0) 8 216=true := by decide +kernel
private theorem blk_8_0_224 : span (pass8 0) 8 224=true := by decide +kernel
private theorem blk_8_0_232 : span (pass8 0) 8 232=true := by decide +kernel
private theorem blk_8_0_240 : span (pass8 0) 8 240=true := by decide +kernel
private theorem blk_8_0_248 : span (pass8 0) 8 248=true := by decide +kernel
private theorem blk_8_0_256 : span (pass8 0) 8 256=true := by decide +kernel
private theorem blk_8_0_264 : span (pass8 0) 8 264=true := by decide +kernel
private theorem blk_8_0_272 : span (pass8 0) 8 272=true := by decide +kernel
private theorem blk_8_0_280 : span (pass8 0) 8 280=true := by decide +kernel
private theorem blk_8_0_288 : span (pass8 0) 8 288=true := by decide +kernel
private theorem blk_8_0_296 : span (pass8 0) 8 296=true := by decide +kernel
private theorem blk_8_0_304 : span (pass8 0) 8 304=true := by decide +kernel
private theorem blk_8_0_312 : span (pass8 0) 8 312=true := by decide +kernel
private theorem blk_8_0_320 : span (pass8 0) 8 320=true := by decide +kernel
private theorem blk_8_0_328 : span (pass8 0) 8 328=true := by decide +kernel
private theorem blk_8_0_336 : span (pass8 0) 8 336=true := by decide +kernel
private theorem blk_8_0_344 : span (pass8 0) 8 344=true := by decide +kernel
private theorem blk_8_0_352 : span (pass8 0) 8 352=true := by decide +kernel
private theorem blk_8_0_360 : span (pass8 0) 8 360=true := by decide +kernel
private theorem blk_8_0_368 : span (pass8 0) 8 368=true := by decide +kernel
private theorem blk_8_0_376 : span (pass8 0) 8 376=true := by decide +kernel
private theorem blk_8_0_384 : span (pass8 0) 8 384=true := by decide +kernel
private theorem blk_8_0_392 : span (pass8 0) 8 392=true := by decide +kernel
private theorem blk_8_0_400 : span (pass8 0) 8 400=true := by decide +kernel
private theorem blk_8_0_408 : span (pass8 0) 8 408=true := by decide +kernel
private theorem blk_8_0_416 : span (pass8 0) 8 416=true := by decide +kernel
private theorem blk_8_0_424 : span (pass8 0) 8 424=true := by decide +kernel
private theorem blk_8_0_432 : span (pass8 0) 8 432=true := by decide +kernel
private theorem blk_8_0_440 : span (pass8 0) 8 440=true := by decide +kernel
private theorem blk_8_0_448 : span (pass8 0) 8 448=true := by decide +kernel
private theorem blk_8_0_456 : span (pass8 0) 8 456=true := by decide +kernel
private theorem blk_8_0_464 : span (pass8 0) 8 464=true := by decide +kernel
private theorem blk_8_0_472 : span (pass8 0) 8 472=true := by decide +kernel
private theorem blk_8_0_480 : span (pass8 0) 8 480=true := by decide +kernel
private theorem blk_8_0_488 : span (pass8 0) 8 488=true := by decide +kernel
private theorem blk_8_0_496 : span (pass8 0) 8 496=true := by decide +kernel
private theorem blk_8_0_504 : span (pass8 0) 8 504=true := by decide +kernel
private theorem blk_8_0_512 : span (pass8 0) 8 512=true := by decide +kernel
private theorem blk_8_0_520 : span (pass8 0) 8 520=true := by decide +kernel
private theorem blk_8_0_528 : span (pass8 0) 8 528=true := by decide +kernel
private theorem blk_8_0_536 : span (pass8 0) 8 536=true := by decide +kernel
private theorem blk_8_0_544 : span (pass8 0) 8 544=true := by decide +kernel
private theorem blk_8_0_552 : span (pass8 0) 8 552=true := by decide +kernel
private theorem blk_8_0_560 : span (pass8 0) 8 560=true := by decide +kernel
private theorem blk_8_0_568 : span (pass8 0) 8 568=true := by decide +kernel
private theorem blk_8_0_576 : span (pass8 0) 8 576=true := by decide +kernel
private theorem blk_8_0_584 : span (pass8 0) 8 584=true := by decide +kernel
private theorem blk_8_0_592 : span (pass8 0) 8 592=true := by decide +kernel
private theorem blk_8_0_600 : span (pass8 0) 8 600=true := by decide +kernel
private theorem blk_8_0_608 : span (pass8 0) 8 608=true := by decide +kernel
private theorem blk_8_0_616 : span (pass8 0) 8 616=true := by decide +kernel
private theorem blk_8_0_624 : span (pass8 0) 8 624=true := by decide +kernel
private theorem blk_8_0_632 : span (pass8 0) 8 632=true := by decide +kernel
private theorem blk_8_0_640 : span (pass8 0) 8 640=true := by decide +kernel
private theorem blk_8_0_648 : span (pass8 0) 8 648=true := by decide +kernel
private theorem blk_8_0_656 : span (pass8 0) 8 656=true := by decide +kernel
private theorem blk_8_0_664 : span (pass8 0) 8 664=true := by decide +kernel
private theorem blk_8_0_672 : span (pass8 0) 8 672=true := by decide +kernel
private theorem blk_8_0_680 : span (pass8 0) 8 680=true := by decide +kernel
private theorem blk_8_0_688 : span (pass8 0) 8 688=true := by decide +kernel
private theorem blk_8_0_696 : span (pass8 0) 8 696=true := by decide +kernel
private theorem blk_8_0_704 : span (pass8 0) 8 704=true := by decide +kernel
private theorem blk_8_0_712 : span (pass8 0) 8 712=true := by decide +kernel
private theorem blk_8_0_720 : span (pass8 0) 8 720=true := by decide +kernel
private theorem blk_8_0_728 : span (pass8 0) 8 728=true := by decide +kernel
private theorem blk_8_0_736 : span (pass8 0) 8 736=true := by decide +kernel
private theorem blk_8_0_744 : span (pass8 0) 8 744=true := by decide +kernel
private theorem blk_8_0_752 : span (pass8 0) 8 752=true := by decide +kernel
private theorem blk_8_0_760 : span (pass8 0) 8 760=true := by decide +kernel
private theorem blk_8_0_768 : span (pass8 0) 8 768=true := by decide +kernel
private theorem blk_8_0_776 : span (pass8 0) 8 776=true := by decide +kernel
private theorem blk_8_0_784 : span (pass8 0) 8 784=true := by decide +kernel
private theorem blk_8_0_792 : span (pass8 0) 8 792=true := by decide +kernel
private theorem blk_8_0_800 : span (pass8 0) 8 800=true := by decide +kernel
private theorem blk_8_0_808 : span (pass8 0) 8 808=true := by decide +kernel
private theorem blk_8_0_816 : span (pass8 0) 8 816=true := by decide +kernel
private theorem blk_8_0_824 : span (pass8 0) 8 824=true := by decide +kernel
private theorem blk_8_0_832 : span (pass8 0) 8 832=true := by decide +kernel
private theorem blk_8_0_840 : span (pass8 0) 8 840=true := by decide +kernel
private theorem blk_8_0_848 : span (pass8 0) 8 848=true := by decide +kernel
private theorem blk_8_0_856 : span (pass8 0) 8 856=true := by decide +kernel
private theorem blk_8_0_864 : span (pass8 0) 8 864=true := by decide +kernel
private theorem blk_8_0_872 : span (pass8 0) 8 872=true := by decide +kernel
private theorem blk_8_0_880 : span (pass8 0) 8 880=true := by decide +kernel
private theorem blk_8_0_888 : span (pass8 0) 8 888=true := by decide +kernel
private theorem blk_8_0_896 : span (pass8 0) 8 896=true := by decide +kernel
private theorem blk_8_0_904 : span (pass8 0) 8 904=true := by decide +kernel
private theorem blk_8_0_912 : span (pass8 0) 8 912=true := by decide +kernel
private theorem blk_8_0_920 : span (pass8 0) 8 920=true := by decide +kernel
private theorem blk_8_0_928 : span (pass8 0) 8 928=true := by decide +kernel
private theorem blk_8_0_936 : span (pass8 0) 8 936=true := by decide +kernel
private theorem blk_8_0_944 : span (pass8 0) 8 944=true := by decide +kernel
private theorem blk_8_0_952 : span (pass8 0) 8 952=true := by decide +kernel
private theorem blk_8_0_960 : span (pass8 0) 8 960=true := by decide +kernel
private theorem blk_8_0_968 : span (pass8 0) 8 968=true := by decide +kernel
private theorem blk_8_0_976 : span (pass8 0) 8 976=true := by decide +kernel
private theorem blk_8_0_984 : span (pass8 0) 8 984=true := by decide +kernel
private theorem blk_8_0_992 : span (pass8 0) 8 992=true := by decide +kernel
private theorem blk_8_0_1000 : span (pass8 0) 8 1000=true := by decide +kernel
private theorem blk_8_0_1008 : span (pass8 0) 8 1008=true := by decide +kernel
private theorem blk_8_0_1016 : span (pass8 0) 8 1016=true := by decide +kernel
private theorem blk_8_0_1024 : span (pass8 0) 8 1024=true := by decide +kernel
private theorem blk_8_0_1032 : span (pass8 0) 8 1032=true := by decide +kernel
private theorem blk_8_0_1040 : span (pass8 0) 8 1040=true := by decide +kernel
private theorem blk_8_0_1048 : span (pass8 0) 8 1048=true := by decide +kernel
private theorem blk_8_0_1056 : span (pass8 0) 8 1056=true := by decide +kernel
private theorem blk_8_0_1064 : span (pass8 0) 8 1064=true := by decide +kernel
private theorem blk_8_0_1072 : span (pass8 0) 8 1072=true := by decide +kernel
private theorem blk_8_0_1080 : span (pass8 0) 8 1080=true := by decide +kernel
private theorem blk_8_0_1088 : span (pass8 0) 8 1088=true := by decide +kernel
private theorem blk_8_0_1096 : span (pass8 0) 8 1096=true := by decide +kernel
private theorem blk_8_0_1104 : span (pass8 0) 8 1104=true := by decide +kernel
private theorem blk_8_0_1112 : span (pass8 0) 8 1112=true := by decide +kernel
private theorem blk_8_0_1120 : span (pass8 0) 8 1120=true := by decide +kernel
private theorem blk_8_0_1128 : span (pass8 0) 8 1128=true := by decide +kernel
private theorem blk_8_0_1136 : span (pass8 0) 8 1136=true := by decide +kernel
private theorem blk_8_0_1144 : span (pass8 0) 8 1144=true := by decide +kernel
private theorem blk_8_0_1152 : span (pass8 0) 8 1152=true := by decide +kernel
private theorem blk_8_0_1160 : span (pass8 0) 8 1160=true := by decide +kernel
private theorem blk_8_0_1168 : span (pass8 0) 8 1168=true := by decide +kernel
private theorem blk_8_0_1176 : span (pass8 0) 8 1176=true := by decide +kernel
private theorem blk_8_0_1184 : span (pass8 0) 8 1184=true := by decide +kernel
private theorem blk_8_0_1192 : span (pass8 0) 8 1192=true := by decide +kernel
private theorem blk_8_0_1200 : span (pass8 0) 8 1200=true := by decide +kernel
private theorem blk_8_0_1208 : span (pass8 0) 8 1208=true := by decide +kernel
private theorem blk_8_0_1216 : span (pass8 0) 8 1216=true := by decide +kernel
private theorem blk_8_0_1224 : span (pass8 0) 8 1224=true := by decide +kernel
private theorem blk_8_0_1232 : span (pass8 0) 8 1232=true := by decide +kernel
private theorem blk_8_0_1240 : span (pass8 0) 8 1240=true := by decide +kernel
private theorem blk_8_0_1248 : span (pass8 0) 8 1248=true := by decide +kernel
private theorem blk_8_0_1256 : span (pass8 0) 8 1256=true := by decide +kernel
private theorem blk_8_0_1264 : span (pass8 0) 8 1264=true := by decide +kernel
private theorem blk_8_0_1272 : span (pass8 0) 8 1272=true := by decide +kernel
private theorem blk_8_0_1280 : span (pass8 0) 8 1280=true := by decide +kernel
private theorem blk_8_0_1288 : span (pass8 0) 8 1288=true := by decide +kernel
private theorem blk_8_0_1296 : span (pass8 0) 8 1296=true := by decide +kernel
private theorem blk_8_0_1304 : span (pass8 0) 8 1304=true := by decide +kernel
private theorem blk_8_0_1312 : span (pass8 0) 2 1312=true := by decide +kernel
private theorem done_8_0 (i : Nat) (hi : i<1314) : pass8 0 i=true := (if h : i < 656 then (if h : i < 328 then (if h : i < 160 then (if h : i < 80 then (if h : i < 40 then (if h : i < 16 then (if h : i < 8 then span_range blk_8_0_0 i (by omega) (by omega) else span_range blk_8_0_8 i (by omega) (by omega)) else (if h : i < 24 then span_range blk_8_0_16 i (by omega) (by omega) else (if h : i < 32 then span_range blk_8_0_24 i (by omega) (by omega) else span_range blk_8_0_32 i (by omega) (by omega)))) else (if h : i < 56 then (if h : i < 48 then span_range blk_8_0_40 i (by omega) (by omega) else span_range blk_8_0_48 i (by omega) (by omega)) else (if h : i < 64 then span_range blk_8_0_56 i (by omega) (by omega) else (if h : i < 72 then span_range blk_8_0_64 i (by omega) (by omega) else span_range blk_8_0_72 i (by omega) (by omega))))) else (if h : i < 120 then (if h : i < 96 then (if h : i < 88 then span_range blk_8_0_80 i (by omega) (by omega) else span_range blk_8_0_88 i (by omega) (by omega)) else (if h : i < 104 then span_range blk_8_0_96 i (by omega) (by omega) else (if h : i < 112 then span_range blk_8_0_104 i (by omega) (by omega) else span_range blk_8_0_112 i (by omega) (by omega)))) else (if h : i < 136 then (if h : i < 128 then span_range blk_8_0_120 i (by omega) (by omega) else span_range blk_8_0_128 i (by omega) (by omega)) else (if h : i < 144 then span_range blk_8_0_136 i (by omega) (by omega) else (if h : i < 152 then span_range blk_8_0_144 i (by omega) (by omega) else span_range blk_8_0_152 i (by omega) (by omega)))))) else (if h : i < 240 then (if h : i < 200 then (if h : i < 176 then (if h : i < 168 then span_range blk_8_0_160 i (by omega) (by omega) else span_range blk_8_0_168 i (by omega) (by omega)) else (if h : i < 184 then span_range blk_8_0_176 i (by omega) (by omega) else (if h : i < 192 then span_range blk_8_0_184 i (by omega) (by omega) else span_range blk_8_0_192 i (by omega) (by omega)))) else (if h : i < 216 then (if h : i < 208 then span_range blk_8_0_200 i (by omega) (by omega) else span_range blk_8_0_208 i (by omega) (by omega)) else (if h : i < 224 then span_range blk_8_0_216 i (by omega) (by omega) else (if h : i < 232 then span_range blk_8_0_224 i (by omega) (by omega) else span_range blk_8_0_232 i (by omega) (by omega))))) else (if h : i < 280 then (if h : i < 256 then (if h : i < 248 then span_range blk_8_0_240 i (by omega) (by omega) else span_range blk_8_0_248 i (by omega) (by omega)) else (if h : i < 264 then span_range blk_8_0_256 i (by omega) (by omega) else (if h : i < 272 then span_range blk_8_0_264 i (by omega) (by omega) else span_range blk_8_0_272 i (by omega) (by omega)))) else (if h : i < 304 then (if h : i < 288 then span_range blk_8_0_280 i (by omega) (by omega) else (if h : i < 296 then span_range blk_8_0_288 i (by omega) (by omega) else span_range blk_8_0_296 i (by omega) (by omega))) else (if h : i < 312 then span_range blk_8_0_304 i (by omega) (by omega) else (if h : i < 320 then span_range blk_8_0_312 i (by omega) (by omega) else span_range blk_8_0_320 i (by omega) (by omega))))))) else (if h : i < 488 then (if h : i < 408 then (if h : i < 368 then (if h : i < 344 then (if h : i < 336 then span_range blk_8_0_328 i (by omega) (by omega) else span_range blk_8_0_336 i (by omega) (by omega)) else (if h : i < 352 then span_range blk_8_0_344 i (by omega) (by omega) else (if h : i < 360 then span_range blk_8_0_352 i (by omega) (by omega) else span_range blk_8_0_360 i (by omega) (by omega)))) else (if h : i < 384 then (if h : i < 376 then span_range blk_8_0_368 i (by omega) (by omega) else span_range blk_8_0_376 i (by omega) (by omega)) else (if h : i < 392 then span_range blk_8_0_384 i (by omega) (by omega) else (if h : i < 400 then span_range blk_8_0_392 i (by omega) (by omega) else span_range blk_8_0_400 i (by omega) (by omega))))) else (if h : i < 448 then (if h : i < 424 then (if h : i < 416 then span_range blk_8_0_408 i (by omega) (by omega) else span_range blk_8_0_416 i (by omega) (by omega)) else (if h : i < 432 then span_range blk_8_0_424 i (by omega) (by omega) else (if h : i < 440 then span_range blk_8_0_432 i (by omega) (by omega) else span_range blk_8_0_440 i (by omega) (by omega)))) else (if h : i < 464 then (if h : i < 456 then span_range blk_8_0_448 i (by omega) (by omega) else span_range blk_8_0_456 i (by omega) (by omega)) else (if h : i < 472 then span_range blk_8_0_464 i (by omega) (by omega) else (if h : i < 480 then span_range blk_8_0_472 i (by omega) (by omega) else span_range blk_8_0_480 i (by omega) (by omega)))))) else (if h : i < 568 then (if h : i < 528 then (if h : i < 504 then (if h : i < 496 then span_range blk_8_0_488 i (by omega) (by omega) else span_range blk_8_0_496 i (by omega) (by omega)) else (if h : i < 512 then span_range blk_8_0_504 i (by omega) (by omega) else (if h : i < 520 then span_range blk_8_0_512 i (by omega) (by omega) else span_range blk_8_0_520 i (by omega) (by omega)))) else (if h : i < 544 then (if h : i < 536 then span_range blk_8_0_528 i (by omega) (by omega) else span_range blk_8_0_536 i (by omega) (by omega)) else (if h : i < 552 then span_range blk_8_0_544 i (by omega) (by omega) else (if h : i < 560 then span_range blk_8_0_552 i (by omega) (by omega) else span_range blk_8_0_560 i (by omega) (by omega))))) else (if h : i < 608 then (if h : i < 584 then (if h : i < 576 then span_range blk_8_0_568 i (by omega) (by omega) else span_range blk_8_0_576 i (by omega) (by omega)) else (if h : i < 592 then span_range blk_8_0_584 i (by omega) (by omega) else (if h : i < 600 then span_range blk_8_0_592 i (by omega) (by omega) else span_range blk_8_0_600 i (by omega) (by omega)))) else (if h : i < 632 then (if h : i < 616 then span_range blk_8_0_608 i (by omega) (by omega) else (if h : i < 624 then span_range blk_8_0_616 i (by omega) (by omega) else span_range blk_8_0_624 i (by omega) (by omega))) else (if h : i < 640 then span_range blk_8_0_632 i (by omega) (by omega) else (if h : i < 648 then span_range blk_8_0_640 i (by omega) (by omega) else span_range blk_8_0_648 i (by omega) (by omega)))))))) else (if h : i < 984 then (if h : i < 816 then (if h : i < 736 then (if h : i < 696 then (if h : i < 672 then (if h : i < 664 then span_range blk_8_0_656 i (by omega) (by omega) else span_range blk_8_0_664 i (by omega) (by omega)) else (if h : i < 680 then span_range blk_8_0_672 i (by omega) (by omega) else (if h : i < 688 then span_range blk_8_0_680 i (by omega) (by omega) else span_range blk_8_0_688 i (by omega) (by omega)))) else (if h : i < 712 then (if h : i < 704 then span_range blk_8_0_696 i (by omega) (by omega) else span_range blk_8_0_704 i (by omega) (by omega)) else (if h : i < 720 then span_range blk_8_0_712 i (by omega) (by omega) else (if h : i < 728 then span_range blk_8_0_720 i (by omega) (by omega) else span_range blk_8_0_728 i (by omega) (by omega))))) else (if h : i < 776 then (if h : i < 752 then (if h : i < 744 then span_range blk_8_0_736 i (by omega) (by omega) else span_range blk_8_0_744 i (by omega) (by omega)) else (if h : i < 760 then span_range blk_8_0_752 i (by omega) (by omega) else (if h : i < 768 then span_range blk_8_0_760 i (by omega) (by omega) else span_range blk_8_0_768 i (by omega) (by omega)))) else (if h : i < 792 then (if h : i < 784 then span_range blk_8_0_776 i (by omega) (by omega) else span_range blk_8_0_784 i (by omega) (by omega)) else (if h : i < 800 then span_range blk_8_0_792 i (by omega) (by omega) else (if h : i < 808 then span_range blk_8_0_800 i (by omega) (by omega) else span_range blk_8_0_808 i (by omega) (by omega)))))) else (if h : i < 896 then (if h : i < 856 then (if h : i < 832 then (if h : i < 824 then span_range blk_8_0_816 i (by omega) (by omega) else span_range blk_8_0_824 i (by omega) (by omega)) else (if h : i < 840 then span_range blk_8_0_832 i (by omega) (by omega) else (if h : i < 848 then span_range blk_8_0_840 i (by omega) (by omega) else span_range blk_8_0_848 i (by omega) (by omega)))) else (if h : i < 872 then (if h : i < 864 then span_range blk_8_0_856 i (by omega) (by omega) else span_range blk_8_0_864 i (by omega) (by omega)) else (if h : i < 880 then span_range blk_8_0_872 i (by omega) (by omega) else (if h : i < 888 then span_range blk_8_0_880 i (by omega) (by omega) else span_range blk_8_0_888 i (by omega) (by omega))))) else (if h : i < 936 then (if h : i < 912 then (if h : i < 904 then span_range blk_8_0_896 i (by omega) (by omega) else span_range blk_8_0_904 i (by omega) (by omega)) else (if h : i < 920 then span_range blk_8_0_912 i (by omega) (by omega) else (if h : i < 928 then span_range blk_8_0_920 i (by omega) (by omega) else span_range blk_8_0_928 i (by omega) (by omega)))) else (if h : i < 960 then (if h : i < 944 then span_range blk_8_0_936 i (by omega) (by omega) else (if h : i < 952 then span_range blk_8_0_944 i (by omega) (by omega) else span_range blk_8_0_952 i (by omega) (by omega))) else (if h : i < 968 then span_range blk_8_0_960 i (by omega) (by omega) else (if h : i < 976 then span_range blk_8_0_968 i (by omega) (by omega) else span_range blk_8_0_976 i (by omega) (by omega))))))) else (if h : i < 1152 then (if h : i < 1064 then (if h : i < 1024 then (if h : i < 1000 then (if h : i < 992 then span_range blk_8_0_984 i (by omega) (by omega) else span_range blk_8_0_992 i (by omega) (by omega)) else (if h : i < 1008 then span_range blk_8_0_1000 i (by omega) (by omega) else (if h : i < 1016 then span_range blk_8_0_1008 i (by omega) (by omega) else span_range blk_8_0_1016 i (by omega) (by omega)))) else (if h : i < 1040 then (if h : i < 1032 then span_range blk_8_0_1024 i (by omega) (by omega) else span_range blk_8_0_1032 i (by omega) (by omega)) else (if h : i < 1048 then span_range blk_8_0_1040 i (by omega) (by omega) else (if h : i < 1056 then span_range blk_8_0_1048 i (by omega) (by omega) else span_range blk_8_0_1056 i (by omega) (by omega))))) else (if h : i < 1104 then (if h : i < 1080 then (if h : i < 1072 then span_range blk_8_0_1064 i (by omega) (by omega) else span_range blk_8_0_1072 i (by omega) (by omega)) else (if h : i < 1088 then span_range blk_8_0_1080 i (by omega) (by omega) else (if h : i < 1096 then span_range blk_8_0_1088 i (by omega) (by omega) else span_range blk_8_0_1096 i (by omega) (by omega)))) else (if h : i < 1128 then (if h : i < 1112 then span_range blk_8_0_1104 i (by omega) (by omega) else (if h : i < 1120 then span_range blk_8_0_1112 i (by omega) (by omega) else span_range blk_8_0_1120 i (by omega) (by omega))) else (if h : i < 1136 then span_range blk_8_0_1128 i (by omega) (by omega) else (if h : i < 1144 then span_range blk_8_0_1136 i (by omega) (by omega) else span_range blk_8_0_1144 i (by omega) (by omega)))))) else (if h : i < 1232 then (if h : i < 1192 then (if h : i < 1168 then (if h : i < 1160 then span_range blk_8_0_1152 i (by omega) (by omega) else span_range blk_8_0_1160 i (by omega) (by omega)) else (if h : i < 1176 then span_range blk_8_0_1168 i (by omega) (by omega) else (if h : i < 1184 then span_range blk_8_0_1176 i (by omega) (by omega) else span_range blk_8_0_1184 i (by omega) (by omega)))) else (if h : i < 1208 then (if h : i < 1200 then span_range blk_8_0_1192 i (by omega) (by omega) else span_range blk_8_0_1200 i (by omega) (by omega)) else (if h : i < 1216 then span_range blk_8_0_1208 i (by omega) (by omega) else (if h : i < 1224 then span_range blk_8_0_1216 i (by omega) (by omega) else span_range blk_8_0_1224 i (by omega) (by omega))))) else (if h : i < 1272 then (if h : i < 1248 then (if h : i < 1240 then span_range blk_8_0_1232 i (by omega) (by omega) else span_range blk_8_0_1240 i (by omega) (by omega)) else (if h : i < 1256 then span_range blk_8_0_1248 i (by omega) (by omega) else (if h : i < 1264 then span_range blk_8_0_1256 i (by omega) (by omega) else span_range blk_8_0_1264 i (by omega) (by omega)))) else (if h : i < 1296 then (if h : i < 1280 then span_range blk_8_0_1272 i (by omega) (by omega) else (if h : i < 1288 then span_range blk_8_0_1280 i (by omega) (by omega) else span_range blk_8_0_1288 i (by omega) (by omega))) else (if h : i < 1304 then span_range blk_8_0_1296 i (by omega) (by omega) else (if h : i < 1312 then span_range blk_8_0_1304 i (by omega) (by omega) else span_range blk_8_0_1312 i (by omega) (by omega)))))))))
private theorem blk_8_1_0 : span (pass8 1) 8 0=true := by decide +kernel
private theorem blk_8_1_8 : span (pass8 1) 8 8=true := by decide +kernel
private theorem blk_8_1_16 : span (pass8 1) 8 16=true := by decide +kernel
private theorem blk_8_1_24 : span (pass8 1) 8 24=true := by decide +kernel
private theorem blk_8_1_32 : span (pass8 1) 8 32=true := by decide +kernel
private theorem blk_8_1_40 : span (pass8 1) 8 40=true := by decide +kernel
private theorem blk_8_1_48 : span (pass8 1) 8 48=true := by decide +kernel
private theorem blk_8_1_56 : span (pass8 1) 8 56=true := by decide +kernel
private theorem blk_8_1_64 : span (pass8 1) 8 64=true := by decide +kernel
private theorem blk_8_1_72 : span (pass8 1) 8 72=true := by decide +kernel
private theorem blk_8_1_80 : span (pass8 1) 8 80=true := by decide +kernel
private theorem blk_8_1_88 : span (pass8 1) 8 88=true := by decide +kernel
private theorem blk_8_1_96 : span (pass8 1) 8 96=true := by decide +kernel
private theorem blk_8_1_104 : span (pass8 1) 8 104=true := by decide +kernel
private theorem blk_8_1_112 : span (pass8 1) 8 112=true := by decide +kernel
private theorem blk_8_1_120 : span (pass8 1) 8 120=true := by decide +kernel
private theorem blk_8_1_128 : span (pass8 1) 8 128=true := by decide +kernel
private theorem blk_8_1_136 : span (pass8 1) 8 136=true := by decide +kernel
private theorem blk_8_1_144 : span (pass8 1) 8 144=true := by decide +kernel
private theorem blk_8_1_152 : span (pass8 1) 8 152=true := by decide +kernel
private theorem blk_8_1_160 : span (pass8 1) 8 160=true := by decide +kernel
private theorem blk_8_1_168 : span (pass8 1) 8 168=true := by decide +kernel
private theorem blk_8_1_176 : span (pass8 1) 8 176=true := by decide +kernel
private theorem blk_8_1_184 : span (pass8 1) 8 184=true := by decide +kernel
private theorem blk_8_1_192 : span (pass8 1) 8 192=true := by decide +kernel
private theorem blk_8_1_200 : span (pass8 1) 8 200=true := by decide +kernel
private theorem blk_8_1_208 : span (pass8 1) 8 208=true := by decide +kernel
private theorem blk_8_1_216 : span (pass8 1) 8 216=true := by decide +kernel
private theorem blk_8_1_224 : span (pass8 1) 8 224=true := by decide +kernel
private theorem blk_8_1_232 : span (pass8 1) 8 232=true := by decide +kernel
private theorem blk_8_1_240 : span (pass8 1) 8 240=true := by decide +kernel
private theorem blk_8_1_248 : span (pass8 1) 8 248=true := by decide +kernel
private theorem blk_8_1_256 : span (pass8 1) 8 256=true := by decide +kernel
private theorem blk_8_1_264 : span (pass8 1) 8 264=true := by decide +kernel
private theorem blk_8_1_272 : span (pass8 1) 8 272=true := by decide +kernel
private theorem blk_8_1_280 : span (pass8 1) 8 280=true := by decide +kernel
private theorem blk_8_1_288 : span (pass8 1) 4 288=true := by decide +kernel
private theorem done_8_1 (i : Nat) (hi : i<292) : pass8 1 i=true := (if h : i < 144 then (if h : i < 72 then (if h : i < 32 then (if h : i < 16 then (if h : i < 8 then span_range blk_8_1_0 i (by omega) (by omega) else span_range blk_8_1_8 i (by omega) (by omega)) else (if h : i < 24 then span_range blk_8_1_16 i (by omega) (by omega) else span_range blk_8_1_24 i (by omega) (by omega))) else (if h : i < 48 then (if h : i < 40 then span_range blk_8_1_32 i (by omega) (by omega) else span_range blk_8_1_40 i (by omega) (by omega)) else (if h : i < 56 then span_range blk_8_1_48 i (by omega) (by omega) else (if h : i < 64 then span_range blk_8_1_56 i (by omega) (by omega) else span_range blk_8_1_64 i (by omega) (by omega))))) else (if h : i < 104 then (if h : i < 88 then (if h : i < 80 then span_range blk_8_1_72 i (by omega) (by omega) else span_range blk_8_1_80 i (by omega) (by omega)) else (if h : i < 96 then span_range blk_8_1_88 i (by omega) (by omega) else span_range blk_8_1_96 i (by omega) (by omega))) else (if h : i < 120 then (if h : i < 112 then span_range blk_8_1_104 i (by omega) (by omega) else span_range blk_8_1_112 i (by omega) (by omega)) else (if h : i < 128 then span_range blk_8_1_120 i (by omega) (by omega) else (if h : i < 136 then span_range blk_8_1_128 i (by omega) (by omega) else span_range blk_8_1_136 i (by omega) (by omega)))))) else (if h : i < 216 then (if h : i < 176 then (if h : i < 160 then (if h : i < 152 then span_range blk_8_1_144 i (by omega) (by omega) else span_range blk_8_1_152 i (by omega) (by omega)) else (if h : i < 168 then span_range blk_8_1_160 i (by omega) (by omega) else span_range blk_8_1_168 i (by omega) (by omega))) else (if h : i < 192 then (if h : i < 184 then span_range blk_8_1_176 i (by omega) (by omega) else span_range blk_8_1_184 i (by omega) (by omega)) else (if h : i < 200 then span_range blk_8_1_192 i (by omega) (by omega) else (if h : i < 208 then span_range blk_8_1_200 i (by omega) (by omega) else span_range blk_8_1_208 i (by omega) (by omega))))) else (if h : i < 256 then (if h : i < 232 then (if h : i < 224 then span_range blk_8_1_216 i (by omega) (by omega) else span_range blk_8_1_224 i (by omega) (by omega)) else (if h : i < 240 then span_range blk_8_1_232 i (by omega) (by omega) else (if h : i < 248 then span_range blk_8_1_240 i (by omega) (by omega) else span_range blk_8_1_248 i (by omega) (by omega)))) else (if h : i < 272 then (if h : i < 264 then span_range blk_8_1_256 i (by omega) (by omega) else span_range blk_8_1_264 i (by omega) (by omega)) else (if h : i < 280 then span_range blk_8_1_272 i (by omega) (by omega) else (if h : i < 288 then span_range blk_8_1_280 i (by omega) (by omega) else span_range blk_8_1_288 i (by omega) (by omega)))))))
theorem good8 : L8.Valid 8 := by
  intro t i hi
  have ht : t < 2 := by
    by_contra hx
    simp [L8,count8,hx] at hi
  have hc : pass8 t i = true := by
    interval_cases t
    · exact done_8_0 i hi
    · exact done_8_1 i hi
  exact bookPass_ok good7 goodBook hc
def pass9 (t i : Nat) := bookPass L8 book 8 t (L9.state t i)
private theorem blk_9_0_0 : span (pass9 0) 8 0=true := by decide +kernel
private theorem blk_9_0_8 : span (pass9 0) 8 8=true := by decide +kernel
private theorem blk_9_0_16 : span (pass9 0) 8 16=true := by decide +kernel
private theorem blk_9_0_24 : span (pass9 0) 8 24=true := by decide +kernel
private theorem blk_9_0_32 : span (pass9 0) 8 32=true := by decide +kernel
private theorem blk_9_0_40 : span (pass9 0) 8 40=true := by decide +kernel
private theorem blk_9_0_48 : span (pass9 0) 8 48=true := by decide +kernel
private theorem blk_9_0_56 : span (pass9 0) 8 56=true := by decide +kernel
private theorem blk_9_0_64 : span (pass9 0) 8 64=true := by decide +kernel
private theorem blk_9_0_72 : span (pass9 0) 8 72=true := by decide +kernel
private theorem blk_9_0_80 : span (pass9 0) 8 80=true := by decide +kernel
private theorem blk_9_0_88 : span (pass9 0) 8 88=true := by decide +kernel
private theorem blk_9_0_96 : span (pass9 0) 8 96=true := by decide +kernel
private theorem blk_9_0_104 : span (pass9 0) 8 104=true := by decide +kernel
private theorem blk_9_0_112 : span (pass9 0) 8 112=true := by decide +kernel
private theorem blk_9_0_120 : span (pass9 0) 8 120=true := by decide +kernel
private theorem blk_9_0_128 : span (pass9 0) 8 128=true := by decide +kernel
private theorem blk_9_0_136 : span (pass9 0) 8 136=true := by decide +kernel
private theorem blk_9_0_144 : span (pass9 0) 8 144=true := by decide +kernel
private theorem blk_9_0_152 : span (pass9 0) 8 152=true := by decide +kernel
private theorem blk_9_0_160 : span (pass9 0) 8 160=true := by decide +kernel
private theorem blk_9_0_168 : span (pass9 0) 8 168=true := by decide +kernel
private theorem blk_9_0_176 : span (pass9 0) 8 176=true := by decide +kernel
private theorem blk_9_0_184 : span (pass9 0) 8 184=true := by decide +kernel
private theorem blk_9_0_192 : span (pass9 0) 8 192=true := by decide +kernel
private theorem blk_9_0_200 : span (pass9 0) 8 200=true := by decide +kernel
private theorem blk_9_0_208 : span (pass9 0) 8 208=true := by decide +kernel
private theorem blk_9_0_216 : span (pass9 0) 8 216=true := by decide +kernel
private theorem blk_9_0_224 : span (pass9 0) 8 224=true := by decide +kernel
private theorem blk_9_0_232 : span (pass9 0) 8 232=true := by decide +kernel
private theorem blk_9_0_240 : span (pass9 0) 8 240=true := by decide +kernel
private theorem blk_9_0_248 : span (pass9 0) 8 248=true := by decide +kernel
private theorem blk_9_0_256 : span (pass9 0) 7 256=true := by decide +kernel
private theorem done_9_0 (i : Nat) (hi : i<263) : pass9 0 i=true := (if h : i < 128 then (if h : i < 64 then (if h : i < 32 then (if h : i < 16 then (if h : i < 8 then span_range blk_9_0_0 i (by omega) (by omega) else span_range blk_9_0_8 i (by omega) (by omega)) else (if h : i < 24 then span_range blk_9_0_16 i (by omega) (by omega) else span_range blk_9_0_24 i (by omega) (by omega))) else (if h : i < 48 then (if h : i < 40 then span_range blk_9_0_32 i (by omega) (by omega) else span_range blk_9_0_40 i (by omega) (by omega)) else (if h : i < 56 then span_range blk_9_0_48 i (by omega) (by omega) else span_range blk_9_0_56 i (by omega) (by omega)))) else (if h : i < 96 then (if h : i < 80 then (if h : i < 72 then span_range blk_9_0_64 i (by omega) (by omega) else span_range blk_9_0_72 i (by omega) (by omega)) else (if h : i < 88 then span_range blk_9_0_80 i (by omega) (by omega) else span_range blk_9_0_88 i (by omega) (by omega))) else (if h : i < 112 then (if h : i < 104 then span_range blk_9_0_96 i (by omega) (by omega) else span_range blk_9_0_104 i (by omega) (by omega)) else (if h : i < 120 then span_range blk_9_0_112 i (by omega) (by omega) else span_range blk_9_0_120 i (by omega) (by omega))))) else (if h : i < 192 then (if h : i < 160 then (if h : i < 144 then (if h : i < 136 then span_range blk_9_0_128 i (by omega) (by omega) else span_range blk_9_0_136 i (by omega) (by omega)) else (if h : i < 152 then span_range blk_9_0_144 i (by omega) (by omega) else span_range blk_9_0_152 i (by omega) (by omega))) else (if h : i < 176 then (if h : i < 168 then span_range blk_9_0_160 i (by omega) (by omega) else span_range blk_9_0_168 i (by omega) (by omega)) else (if h : i < 184 then span_range blk_9_0_176 i (by omega) (by omega) else span_range blk_9_0_184 i (by omega) (by omega)))) else (if h : i < 224 then (if h : i < 208 then (if h : i < 200 then span_range blk_9_0_192 i (by omega) (by omega) else span_range blk_9_0_200 i (by omega) (by omega)) else (if h : i < 216 then span_range blk_9_0_208 i (by omega) (by omega) else span_range blk_9_0_216 i (by omega) (by omega))) else (if h : i < 240 then (if h : i < 232 then span_range blk_9_0_224 i (by omega) (by omega) else span_range blk_9_0_232 i (by omega) (by omega)) else (if h : i < 248 then span_range blk_9_0_240 i (by omega) (by omega) else (if h : i < 256 then span_range blk_9_0_248 i (by omega) (by omega) else span_range blk_9_0_256 i (by omega) (by omega)))))))
private theorem blk_9_1_0 : span (pass9 1) 8 0=true := by decide +kernel
private theorem blk_9_1_8 : span (pass9 1) 8 8=true := by decide +kernel
private theorem blk_9_1_16 : span (pass9 1) 8 16=true := by decide +kernel
private theorem blk_9_1_24 : span (pass9 1) 8 24=true := by decide +kernel
private theorem blk_9_1_32 : span (pass9 1) 8 32=true := by decide +kernel
private theorem blk_9_1_40 : span (pass9 1) 8 40=true := by decide +kernel
private theorem blk_9_1_48 : span (pass9 1) 8 48=true := by decide +kernel
private theorem blk_9_1_56 : span (pass9 1) 8 56=true := by decide +kernel
private theorem blk_9_1_64 : span (pass9 1) 8 64=true := by decide +kernel
private theorem blk_9_1_72 : span (pass9 1) 8 72=true := by decide +kernel
private theorem blk_9_1_80 : span (pass9 1) 8 80=true := by decide +kernel
private theorem blk_9_1_88 : span (pass9 1) 8 88=true := by decide +kernel
private theorem blk_9_1_96 : span (pass9 1) 8 96=true := by decide +kernel
private theorem blk_9_1_104 : span (pass9 1) 8 104=true := by decide +kernel
private theorem blk_9_1_112 : span (pass9 1) 8 112=true := by decide +kernel
private theorem blk_9_1_120 : span (pass9 1) 8 120=true := by decide +kernel
private theorem blk_9_1_128 : span (pass9 1) 8 128=true := by decide +kernel
private theorem blk_9_1_136 : span (pass9 1) 8 136=true := by decide +kernel
private theorem blk_9_1_144 : span (pass9 1) 8 144=true := by decide +kernel
private theorem blk_9_1_152 : span (pass9 1) 8 152=true := by decide +kernel
private theorem blk_9_1_160 : span (pass9 1) 8 160=true := by decide +kernel
private theorem blk_9_1_168 : span (pass9 1) 8 168=true := by decide +kernel
private theorem blk_9_1_176 : span (pass9 1) 8 176=true := by decide +kernel
private theorem blk_9_1_184 : span (pass9 1) 8 184=true := by decide +kernel
private theorem blk_9_1_192 : span (pass9 1) 8 192=true := by decide +kernel
private theorem blk_9_1_200 : span (pass9 1) 8 200=true := by decide +kernel
private theorem blk_9_1_208 : span (pass9 1) 8 208=true := by decide +kernel
private theorem blk_9_1_216 : span (pass9 1) 8 216=true := by decide +kernel
private theorem blk_9_1_224 : span (pass9 1) 8 224=true := by decide +kernel
private theorem blk_9_1_232 : span (pass9 1) 8 232=true := by decide +kernel
private theorem blk_9_1_240 : span (pass9 1) 8 240=true := by decide +kernel
private theorem blk_9_1_248 : span (pass9 1) 8 248=true := by decide +kernel
private theorem blk_9_1_256 : span (pass9 1) 8 256=true := by decide +kernel
private theorem blk_9_1_264 : span (pass9 1) 8 264=true := by decide +kernel
private theorem blk_9_1_272 : span (pass9 1) 8 272=true := by decide +kernel
private theorem blk_9_1_280 : span (pass9 1) 8 280=true := by decide +kernel
private theorem blk_9_1_288 : span (pass9 1) 8 288=true := by decide +kernel
private theorem blk_9_1_296 : span (pass9 1) 4 296=true := by decide +kernel
private theorem done_9_1 (i : Nat) (hi : i<300) : pass9 1 i=true := (if h : i < 152 then (if h : i < 72 then (if h : i < 32 then (if h : i < 16 then (if h : i < 8 then span_range blk_9_1_0 i (by omega) (by omega) else span_range blk_9_1_8 i (by omega) (by omega)) else (if h : i < 24 then span_range blk_9_1_16 i (by omega) (by omega) else span_range blk_9_1_24 i (by omega) (by omega))) else (if h : i < 48 then (if h : i < 40 then span_range blk_9_1_32 i (by omega) (by omega) else span_range blk_9_1_40 i (by omega) (by omega)) else (if h : i < 56 then span_range blk_9_1_48 i (by omega) (by omega) else (if h : i < 64 then span_range blk_9_1_56 i (by omega) (by omega) else span_range blk_9_1_64 i (by omega) (by omega))))) else (if h : i < 112 then (if h : i < 88 then (if h : i < 80 then span_range blk_9_1_72 i (by omega) (by omega) else span_range blk_9_1_80 i (by omega) (by omega)) else (if h : i < 96 then span_range blk_9_1_88 i (by omega) (by omega) else (if h : i < 104 then span_range blk_9_1_96 i (by omega) (by omega) else span_range blk_9_1_104 i (by omega) (by omega)))) else (if h : i < 128 then (if h : i < 120 then span_range blk_9_1_112 i (by omega) (by omega) else span_range blk_9_1_120 i (by omega) (by omega)) else (if h : i < 136 then span_range blk_9_1_128 i (by omega) (by omega) else (if h : i < 144 then span_range blk_9_1_136 i (by omega) (by omega) else span_range blk_9_1_144 i (by omega) (by omega)))))) else (if h : i < 224 then (if h : i < 184 then (if h : i < 168 then (if h : i < 160 then span_range blk_9_1_152 i (by omega) (by omega) else span_range blk_9_1_160 i (by omega) (by omega)) else (if h : i < 176 then span_range blk_9_1_168 i (by omega) (by omega) else span_range blk_9_1_176 i (by omega) (by omega))) else (if h : i < 200 then (if h : i < 192 then span_range blk_9_1_184 i (by omega) (by omega) else span_range blk_9_1_192 i (by omega) (by omega)) else (if h : i < 208 then span_range blk_9_1_200 i (by omega) (by omega) else (if h : i < 216 then span_range blk_9_1_208 i (by omega) (by omega) else span_range blk_9_1_216 i (by omega) (by omega))))) else (if h : i < 264 then (if h : i < 240 then (if h : i < 232 then span_range blk_9_1_224 i (by omega) (by omega) else span_range blk_9_1_232 i (by omega) (by omega)) else (if h : i < 248 then span_range blk_9_1_240 i (by omega) (by omega) else (if h : i < 256 then span_range blk_9_1_248 i (by omega) (by omega) else span_range blk_9_1_256 i (by omega) (by omega)))) else (if h : i < 280 then (if h : i < 272 then span_range blk_9_1_264 i (by omega) (by omega) else span_range blk_9_1_272 i (by omega) (by omega)) else (if h : i < 288 then span_range blk_9_1_280 i (by omega) (by omega) else (if h : i < 296 then span_range blk_9_1_288 i (by omega) (by omega) else span_range blk_9_1_296 i (by omega) (by omega)))))))
private theorem blk_9_2_0 : span (pass9 2) 8 0=true := by decide +kernel
private theorem blk_9_2_8 : span (pass9 2) 8 8=true := by decide +kernel
private theorem blk_9_2_16 : span (pass9 2) 7 16=true := by decide +kernel
private theorem done_9_2 (i : Nat) (hi : i<23) : pass9 2 i=true := (if h : i < 8 then span_range blk_9_2_0 i (by omega) (by omega) else (if h : i < 16 then span_range blk_9_2_8 i (by omega) (by omega) else span_range blk_9_2_16 i (by omega) (by omega)))
theorem good9 : L9.Valid 9 := by
  intro t i hi
  have ht : t < 3 := by
    by_contra hx
    simp [L9,count9,hx] at hi
  have hc : pass9 t i = true := by
    interval_cases t
    · exact done_9_0 i hi
    · exact done_9_1 i hi
    · exact done_9_2 i hi
  exact bookPass_ok good8 goodBook hc
def pass10 (t i : Nat) := bookPass L9 book 9 t (L10.state t i)
private theorem blk_10_0_0 : span (pass10 0) 4 0=true := by decide +kernel
private theorem done_10_0 (i : Nat) (hi : i<4) : pass10 0 i=true := span_range blk_10_0_0 i (by omega) (by omega)
private theorem blk_10_1_0 : span (pass10 1) 7 0=true := by decide +kernel
private theorem done_10_1 (i : Nat) (hi : i<7) : pass10 1 i=true := span_range blk_10_1_0 i (by omega) (by omega)
private theorem blk_10_2_0 : span (pass10 2) 7 0=true := by decide +kernel
private theorem done_10_2 (i : Nat) (hi : i<7) : pass10 2 i=true := span_range blk_10_2_0 i (by omega) (by omega)
private theorem blk_10_3_0 : span (pass10 3) 4 0=true := by decide +kernel
private theorem done_10_3 (i : Nat) (hi : i<4) : pass10 3 i=true := span_range blk_10_3_0 i (by omega) (by omega)
private theorem done_10_4 (i : Nat) (hi : i<0) : pass10 4 i=true := by omega
theorem good10 : L10.Valid 10 := by
  intro t i hi
  have ht : t < 5 := by
    by_contra hx
    simp [L10,count10,hx] at hi
  have hc : pass10 t i = true := by
    interval_cases t
    · exact done_10_0 i hi
    · exact done_10_1 i hi
    · exact done_10_2 i hi
    · exact done_10_3 i hi
    · exact done_10_4 i hi
  exact bookPass_ok good9 goodBook hc
theorem root_0 : bookRoot 0 L10 book=true := by decide +kernel
theorem lower_0 (C : Circuit) (h : C.size≤10) (f : PEqualNP.MetaComplexity.FanInTwo C) : ¬∀ x : Fin 7 → Bool, C.eval (List.ofFn x ++ [!(x (0:Fin 7))]) = theta x := exclusion_from_book 0 L10 book good10 goodBook root_0 C h f
theorem root_2 : bookRoot 2 L10 book=true := by decide +kernel
theorem lower_2 (C : Circuit) (h : C.size≤10) (f : PEqualNP.MetaComplexity.FanInTwo C) : ¬∀ x : Fin 7 → Bool, C.eval (List.ofFn x ++ [!(x (2:Fin 7))]) = theta x := exclusion_from_book 2 L10 book good10 goodBook root_2 C h f
theorem root_3 : bookRoot 3 L10 book=true := by decide +kernel
theorem lower_3 (C : Circuit) (h : C.size≤10) (f : PEqualNP.MetaComplexity.FanInTwo C) : ¬∀ x : Fin 7 → Bool, C.eval (List.ofFn x ++ [!(x (3:Fin 7))]) = theta x := exclusion_from_book 3 L10 book good10 goodBook root_3 C h f
end CoThetaWholeBase.CertifiedData
