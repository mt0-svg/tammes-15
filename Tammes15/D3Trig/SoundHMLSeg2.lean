import Tammes15.D3Trig.Prog.HML
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHML_seg2 (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (hb_H4 : H4 < 2 ^ 64) (v23 : ℕ) (v47 : ℕ) (v52 : ℕ) (v60 : ℕ) (v69 : ℕ) (v72 : ℕ) (v73 : ℕ) (v100 : ℕ) (v107 : ℕ) (v116 : ℕ) (v135 : ℕ) (v138 : ℕ) (v139 : ℕ) (v166 : ℕ) (v173 : ℕ) (v272 : ℕ) (v397 : ℕ) (v403 : ℕ) (v408 : ℕ) (v416 : ℕ) (v418 : ℕ) (v421 : ℕ) (v422 : ℕ) (v438 : ℕ) (v440 : ℕ) (v722 : ℕ) (v764 : ℕ) (v766 : ℕ) (v778 : ℕ) (v784 : ℕ) (v788 : ℕ) (v794 : ℕ) (v798 : ℕ) (v804 : ℕ) (v808 : ℕ) (v816 : ℕ) (v819 : ℕ) (v820 : ℕ) (v823 : ℕ) (v844 : ℕ) (v847 : ℕ) (v848 : ℕ) (v870 : ℕ) (v871 : ℕ) (v1216 : ℕ) (t1218 : ℕ × ℕ) (v1232 : ℕ) (v1233 : ℕ) (t1234 : ℕ × ℕ) (v1245 : ℕ) (h_v23 : R 1 0 0 1 v23 v23) (h_v47 : R 1 0 0 1 v47 v47) (h_v52 : R 1 0 4611686018427387900 4611686018695823359 v52 v52) (h_v60 : R 1 0 4611686018427387908 4611686018695823367 v60 v60) (h_v69 : R 1 0 0 1 v69 v69) (h_v72 : R 1 0 0 1 v72 v72) (h_v73 : R 1 0 0 1 v73 v73) (h_v100 : R 1 0 4611686018158952441 4611686018695823359 v100 v100) (h_v107 : R 1 0 4611686018158952449 4611686018695823367 v107 v107) (h_v116 : R 1 0 4611686018158952441 4611686018695823359 v116 v116) (h_v135 : R 1 0 0 1 v135 v135) (h_v138 : R 1 0 0 1 v138 v138) (h_v139 : R 1 0 0 1 v139 v139) (h_v166 : R 1 0 0 1 v166 v166) (h_v173 : R 1 0 0 1 v173 v173) (h_v272 : R 1 0 4611686018158952449 4611686018695823367 v272 v272) (h_v397 : R 1 0 4611686017353646081 4611686019501129727 v397 v397) (h_v403 : R 1 0 0 1 v403 v403) (h_v408 : R 1 0 4611686018427387900 4611686018695823359 v408 v408) (h_v416 : R 1 0 4611686018427387908 4611686018695823367 v416 v416) (h_v418 : R 1 0 0 1 v418 v418) (h_v421 : R 1 0 0 1 v421 v421) (h_v422 : R 1 0 0 1 v422 v422) (h_v438 : R 1 0 4611686018427387899 4611686018695823374 v438 v438) (h_v440 : R 1 0 4611686018427387900 4611686018695823375 v440 v440) (h_v722 : R 1 0 4611686017353646081 4611686019501129727 v722 v722) (h_v764 : R 1 0 4611686018427387899 4611686018695823374 v764 v764) (h_v766 : R 1 0 4611686018427387900 4611686018695823375 v766 v766) (h_v778 : R 1 0 0 1 v778 v778) (h_v784 : R 1 0 4611686018158952386 4611686018695823360 v784 v784) (h_v788 : R 1 0 4611686018158952392 4611686018695823360 v788 v788) (h_v794 : R 1 0 4611686018158952386 4611686018695823360 v794 v794) (h_v798 : R 1 0 4611686018158952392 4611686018695823360 v798 v798) (h_v804 : R 1 0 4611686018158952386 4611686018695823360 v804 v804) (h_v808 : R 1 0 4611686018158952392 4611686018695823360 v808 v808) (h_v816 : R 1 0 0 1 v816 v816) (h_v819 : R 1 0 0 1 v819 v819) (h_v820 : R 1 0 0 1 v820 v820) (h_v823 : R 1 0 0 1 v823 v823) (h_v844 : R 1 0 0 1 v844 v844) (h_v847 : R 1 0 0 1 v847 v847) (h_v848 : R 1 0 0 1 v848 v848) (h_v870 : R 1 0 0 1 v870 v870) (h_v871 : R 1 0 0 1 v871 v871) (h_v1216 : R 1 0 0 1 v1216 v1216) (h_t1218_1 : R 1 0 4611686018427387904 4611686018695823363 t1218.1 t1218.1) (h_t1218_2 : R 1 0 4611686018158952445 4611686018695823363 t1218.2 t1218.2) (h_v1232 : R 1 0 0 1 v1232 v1232) (h_v1233 : R 1 0 4611686018427387904 4611686019501129727 v1233 v1233) (h_t1234_1 : R 1 0 4611686018427387904 4611686018695823363 t1234.1 t1234.1) (h_t1234_2 : R 1 0 4611686018158952445 4611686018695823363 t1234.2 t1234.2) (h_v1245 : R 1 0 0 1 v1245 v1245) :
    let OFFr := Nat.mul 1 4611686018427387904
    let v3 := ix 1 F1 32
    let v5 := ix 1 F2 32
    let v9 := Nat.mul 1 4611686019270702761
    let v15 := Nat.mul 1 4611686019270702760
    let v19 := Nat.mul 1 4611686018427387903
    let v28 := Nat.mul 1 4611686018427387900
    let v31 := Nat.mul 1 4611686018427387908
    let v33 := Nat.mul 1 4611686018695823360
    let v36 := Nat.mul 1 4611686018849045334
    let v38 := Nat.mul 1 4611686018849045331
    let v61 := Nat.mul 1 4611686018427387904
    let v95 := Nat.mul 1 4611686018158952448
    let v98 := Nat.mul 1 4611686019270702759
    let v105 := Nat.mul 1 4611686018427387905
    let v940 := Nat.mul 1 4683743612465315840
    let v967 := Nat.mul 1 4647714815446351872
    let v1234 := hxa 1 H2 32
    let v1246 := psel (pmask v1245) v1234 v9
    let v1247 := psel (pmask v778) v1233 v61
    let v1248 := psel (pmask v778) v1246 v9
    let v1249 := Nat.land v778 v1216
    let v1252 := Nat.sub 1 v1249
    let v1253 := Nat.land v820 v848
    let v1254 := Nat.sub 1 v1253
    let v1255 := Nat.lor v823 v1254
    let v1256 := Nat.land v816 v848
    let v1257 := Nat.lor v847 v1256
    let v1258 := psel (pmask v1257) v808 v804
    let v1259 := Nat.land v820 v844
    let v1260 := Nat.lor v819 v1259
    let v1261 := psel (pmask v1260) v798 v794
    let v1262 := Nat.land v819 v848
    let v1263 := Nat.lor v847 v1262
    let v1264 := psel (pmask v1263) v804 v808
    let v1265 := Nat.land v820 v847
    let v1266 := Nat.lor v819 v1265
    let v1267 := psel (pmask v1266) v794 v798
    let v1268 := smx 30 1 v1261 v1258
    let v1269 := srdF 1 v1268
    let v1270 := smx 30 1 v1267 v1264
    let v1271 := srdC 1 v1270
    let v1272 := Nat.sub (Nat.add v784 OFFr) v1271
    let v1273 := Nat.sub (Nat.add v788 OFFr) v1269
    let v1274 := plt 1 v61 v1272
    let v1275 := plt 1 v1273 v61
    let v1276 := psel (pmask v870) v440 v438
    let v1277 := psel (pmask v871) v438 v440
    let v1278 := psel (pmask v871) v440 v438
    let v1279 := psel (pmask v870) v438 v440
    let v1280 := psel (pmask v1274) v766 v764
    let v1281 := psel (pmask v1275) v764 v766
    let v1282 := psel (pmask v1275) v766 v764
    let v1283 := psel (pmask v1274) v764 v766
    let v1289 := smx 29 1 v1277 v1277
    let v1290 := srdC 1 v1289
    let v1291 := Nat.sub (Nat.add v1290 v1290) OFFr
    let v1292 := Nat.sub (Nat.add v33 OFFr) v1291
    let v1293 := plt 1 v1292 v95
    let v1294 := psel (pmask v1293) v95 v1292
    let v1295 := smx 29 1 v1276 v1276
    let v1296 := srdF 1 v1295
    let v1297 := Nat.sub (Nat.add v1296 v1296) OFFr
    let v1298 := Nat.sub (Nat.add v33 OFFr) v1297
    let v1299 := smx 29 1 v1281 v1281
    let v1300 := srdC 1 v1299
    let v1301 := Nat.sub (Nat.add v1300 v1300) OFFr
    let v1302 := Nat.sub (Nat.add v33 OFFr) v1301
    let v1303 := plt 1 v1302 v95
    let v1304 := psel (pmask v1303) v95 v1302
    let v1305 := smx 29 1 v1280 v1280
    let v1306 := srdF 1 v1305
    let v1307 := Nat.sub (Nat.add v1306 v1306) OFFr
    let v1308 := Nat.sub (Nat.add v33 OFFr) v1307
    let v1309 := plt 1 v1294 v61
    let v1310 := Nat.sub 1 v1309
    let v1311 := plt 1 v61 v1298
    let v1312 := Nat.sub 1 v1311
    let v1313 := Nat.land v1309 v1312
    let v1314 := Nat.land v1309 v1311
    let v1315 := plt 1 v1304 v61
    let v1316 := Nat.sub 1 v1315
    let v1317 := plt 1 v61 v1308
    let v1318 := Nat.sub 1 v1317
    let v1319 := Nat.land v1315 v1318
    let v1320 := Nat.land v1315 v1317
    let v1321 := Nat.land v1314 v1320
    let v1322 := Nat.sub 1 v1321
    let v1323 := Nat.lor v823 v1322
    let v1324 := Nat.land v1310 v1320
    let v1325 := Nat.lor v1319 v1324
    let v1326 := psel (pmask v1325) v1298 v1294
    let v1327 := Nat.land v1314 v1316
    let v1328 := Nat.lor v1313 v1327
    let v1329 := psel (pmask v1328) v1308 v1304
    let v1336 := smx 30 1 v1329 v1326
    let v1337 := srdF 1 v1336
    let v1341 := Nat.sub (Nat.add v808 OFFr) v1337
    let v1342 := Nat.sub (Nat.add v940 OFFr) v1295
    let v1343 := psqrt 1 v1342
    let v1344 := Nat.sub (Nat.add v105 v1343) OFFr
    let v1345 := smx 29 1 v1343 v1276
    let v1346 := srdF 1 v1345
    let v1347 := Nat.sub (Nat.add v1346 v1346) OFFr
    let v1348 := smx 29 1 v1344 v1276
    let v1349 := srdC 1 v1348
    let v1350 := Nat.sub (Nat.add v1349 v1349) OFFr
    let v1351 := plt 1 v1350 v33
    let v1352 := psel (pmask v1351) v1350 v33
    let v1353 := Nat.sub (Nat.add v940 OFFr) v1289
    let v1354 := psqrt 1 v1353
    let v1355 := Nat.sub (Nat.add v105 v1354) OFFr
    let v1356 := smx 29 1 v1354 v1277
    let v1357 := srdF 1 v1356
    let v1358 := Nat.sub (Nat.add v1357 v1357) OFFr
    let v1359 := smx 29 1 v1355 v1277
    let v1360 := srdC 1 v1359
    let v1361 := Nat.sub (Nat.add v1360 v1360) OFFr
    let v1362 := plt 1 v1361 v33
    let v1363 := psel (pmask v1362) v1361 v33
    let v1364 := plt 1 v1347 v1358
    let v1365 := psel (pmask v1364) v1347 v1358
    let v1366 := plt 1 v1352 v1363
    let v1367 := psel (pmask v1366) v1363 v1352
    let v1368 := plt 1 v967 v1295
    let v1369 := Nat.sub 1 v1368
    let v1370 := plt 1 v1289 v967
    let v1371 := Nat.sub 1 v1370
    let v1372 := Nat.land v1369 v1371
    let v1373 := psel (pmask v1372) v33 v1367
    let v1374 := Nat.sub (Nat.add v940 OFFr) v1305
    let v1375 := psqrt 1 v1374
    let v1376 := Nat.sub (Nat.add v105 v1375) OFFr
    let v1377 := smx 29 1 v1375 v1280
    let v1378 := srdF 1 v1377
    let v1379 := Nat.sub (Nat.add v1378 v1378) OFFr
    let v1380 := smx 29 1 v1376 v1280
    let v1381 := srdC 1 v1380
    let v1382 := Nat.sub (Nat.add v1381 v1381) OFFr
    let v1383 := plt 1 v1382 v33
    let v1384 := psel (pmask v1383) v1382 v33
    let v1385 := Nat.sub (Nat.add v940 OFFr) v1299
    let v1386 := psqrt 1 v1385
    let v1387 := Nat.sub (Nat.add v105 v1386) OFFr
    let v1388 := smx 29 1 v1386 v1281
    let v1389 := srdF 1 v1388
    let v1390 := Nat.sub (Nat.add v1389 v1389) OFFr
    let v1391 := smx 29 1 v1387 v1281
    let v1392 := srdC 1 v1391
    let v1393 := Nat.sub (Nat.add v1392 v1392) OFFr
    let v1394 := plt 1 v1393 v33
    let v1395 := psel (pmask v1394) v1393 v33
    let v1396 := plt 1 v1379 v1390
    let v1397 := psel (pmask v1396) v1379 v1390
    let v1398 := plt 1 v1384 v1395
    let v1399 := psel (pmask v1398) v1395 v1384
    let v1400 := plt 1 v967 v1305
    let v1401 := Nat.sub 1 v1400
    let v1402 := plt 1 v1299 v967
    let v1403 := Nat.sub 1 v1402
    let v1404 := Nat.land v1401 v1403
    let v1405 := psel (pmask v1404) v33 v1399
    let v1406 := plt 1 v1365 v61
    let v1407 := Nat.sub 1 v1406
    let v1408 := plt 1 v61 v1373
    let v1409 := Nat.sub 1 v1408
    let v1410 := Nat.land v1406 v1409
    let v1411 := Nat.land v1406 v1408
    let v1412 := plt 1 v1397 v61
    let v1413 := Nat.sub 1 v1412
    let v1414 := plt 1 v61 v1405
    let v1415 := Nat.sub 1 v1414
    let v1416 := Nat.land v1412 v1415
    let v1417 := Nat.land v1412 v1414
    let v1418 := Nat.land v1411 v1417
    let v1419 := Nat.sub 1 v1418
    let v1420 := Nat.lor v823 v1419
    let v1421 := Nat.land v1407 v1417
    let v1422 := Nat.lor v1416 v1421
    let v1423 := psel (pmask v1422) v1373 v1365
    let v1424 := Nat.land v1411 v1413
    let v1425 := Nat.lor v1410 v1424
    let v1426 := psel (pmask v1425) v1405 v1397
    let v1427 := Nat.land v1410 v1417
    let v1428 := Nat.lor v1416 v1427
    let v1429 := psel (pmask v1428) v1365 v1373
    let v1430 := Nat.land v1411 v1416
    let v1431 := Nat.lor v1410 v1430
    let v1432 := psel (pmask v1431) v1397 v1405
    let v1433 := smx 29 1 v1426 v1423
    let v1434 := srdF 1 v1433
    let v1435 := smx 29 1 v1432 v1429
    let v1436 := srdC 1 v1435
    let v1437 := plt 1 v61 v1434
    let v1438 := Nat.sub 1 v1437
    let v1441 := plt 1 v1341 v61
    let v1442 := psel (pmask v1441) v1436 v1434
    let v1443 := Nat.sub (Nat.add v61 OFFr) v1442
    let v1444 := plt 1 v1341 v1443
    let v1445 := Nat.land v1437 v1444
    let v1446 := plt 1 v1341 v1442
    let v1447 := Nat.sub 1 v1446
    let v1448 := Nat.lor v1438 v1447
    let v1449 := psel (pmask v1448) v33 v1341
    let v1450 := psel (pmask v1448) v33 v1442
    let v1454 := smx 29 1 v1279 v1279
    let v1455 := srdC 1 v1454
    let v1456 := Nat.sub (Nat.add v1455 v1455) OFFr
    let v1457 := Nat.sub (Nat.add v33 OFFr) v1456
    let v1458 := plt 1 v1457 v95
    let v1459 := psel (pmask v1458) v95 v1457
    let v1460 := smx 29 1 v1278 v1278
    let v1461 := srdF 1 v1460
    let v1462 := Nat.sub (Nat.add v1461 v1461) OFFr
    let v1463 := Nat.sub (Nat.add v33 OFFr) v1462
    let v1464 := smx 29 1 v1283 v1283
    let v1465 := srdC 1 v1464
    let v1466 := Nat.sub (Nat.add v1465 v1465) OFFr
    let v1467 := Nat.sub (Nat.add v33 OFFr) v1466
    let v1468 := plt 1 v1467 v95
    let v1469 := psel (pmask v1468) v95 v1467
    let v1470 := smx 29 1 v1282 v1282
    let v1471 := srdF 1 v1470
    let v1472 := Nat.sub (Nat.add v1471 v1471) OFFr
    let v1473 := Nat.sub (Nat.add v33 OFFr) v1472
    let v1474 := plt 1 v1459 v61
    let v1476 := plt 1 v61 v1463
    let v1477 := Nat.sub 1 v1476
    let v1478 := Nat.land v1474 v1477
    let v1479 := Nat.land v1474 v1476
    let v1480 := plt 1 v1469 v61
    let v1482 := plt 1 v61 v1473
    let v1483 := Nat.sub 1 v1482
    let v1484 := Nat.land v1480 v1483
    let v1485 := Nat.land v1480 v1482
    let v1486 := Nat.land v1479 v1485
    let v1487 := Nat.sub 1 v1486
    let v1488 := Nat.lor v823 v1487
    let v1495 := Nat.land v1478 v1485
    let v1496 := Nat.lor v1484 v1495
    let v1497 := psel (pmask v1496) v1459 v1463
    let v1498 := Nat.land v1479 v1484
    let v1499 := Nat.lor v1478 v1498
    let v1500 := psel (pmask v1499) v1469 v1473
    let v1503 := smx 30 1 v1500 v1497
    let v1504 := srdC 1 v1503
    let v1505 := Nat.sub (Nat.add v804 OFFr) v1504
    let v1507 := Nat.sub (Nat.add v940 OFFr) v1460
    let v1508 := psqrt 1 v1507
    let v1509 := Nat.sub (Nat.add v105 v1508) OFFr
    let v1510 := smx 29 1 v1508 v1278
    let v1511 := srdF 1 v1510
    let v1512 := Nat.sub (Nat.add v1511 v1511) OFFr
    let v1513 := smx 29 1 v1509 v1278
    let v1514 := srdC 1 v1513
    let v1515 := Nat.sub (Nat.add v1514 v1514) OFFr
    let v1516 := plt 1 v1515 v33
    let v1517 := psel (pmask v1516) v1515 v33
    let v1518 := Nat.sub (Nat.add v940 OFFr) v1454
    let v1519 := psqrt 1 v1518
    let v1520 := Nat.sub (Nat.add v105 v1519) OFFr
    let v1521 := smx 29 1 v1519 v1279
    let v1522 := srdF 1 v1521
    let v1523 := Nat.sub (Nat.add v1522 v1522) OFFr
    let v1524 := smx 29 1 v1520 v1279
    let v1525 := srdC 1 v1524
    let v1526 := Nat.sub (Nat.add v1525 v1525) OFFr
    let v1527 := plt 1 v1526 v33
    let v1528 := psel (pmask v1527) v1526 v33
    let v1529 := plt 1 v1512 v1523
    let v1530 := psel (pmask v1529) v1512 v1523
    let v1531 := plt 1 v1517 v1528
    let v1532 := psel (pmask v1531) v1528 v1517
    let v1533 := plt 1 v967 v1460
    let v1534 := Nat.sub 1 v1533
    let v1535 := plt 1 v1454 v967
    let v1536 := Nat.sub 1 v1535
    let v1537 := Nat.land v1534 v1536
    let v1538 := psel (pmask v1537) v33 v1532
    let v1539 := Nat.sub (Nat.add v940 OFFr) v1470
    let v1540 := psqrt 1 v1539
    let v1541 := Nat.sub (Nat.add v105 v1540) OFFr
    let v1542 := smx 29 1 v1540 v1282
    let v1543 := srdF 1 v1542
    let v1544 := Nat.sub (Nat.add v1543 v1543) OFFr
    let v1545 := smx 29 1 v1541 v1282
    let v1546 := srdC 1 v1545
    let v1547 := Nat.sub (Nat.add v1546 v1546) OFFr
    let v1548 := plt 1 v1547 v33
    let v1549 := psel (pmask v1548) v1547 v33
    let v1550 := Nat.sub (Nat.add v940 OFFr) v1464
    let v1551 := psqrt 1 v1550
    let v1552 := Nat.sub (Nat.add v105 v1551) OFFr
    let v1553 := smx 29 1 v1551 v1283
    let v1554 := srdF 1 v1553
    let v1555 := Nat.sub (Nat.add v1554 v1554) OFFr
    let v1556 := smx 29 1 v1552 v1283
    let v1557 := srdC 1 v1556
    let v1558 := Nat.sub (Nat.add v1557 v1557) OFFr
    let v1559 := plt 1 v1558 v33
    let v1560 := psel (pmask v1559) v1558 v33
    let v1561 := plt 1 v1544 v1555
    let v1562 := psel (pmask v1561) v1544 v1555
    let v1563 := plt 1 v1549 v1560
    let v1564 := psel (pmask v1563) v1560 v1549
    let v1565 := plt 1 v967 v1470
    let v1566 := Nat.sub 1 v1565
    let v1567 := plt 1 v1464 v967
    let v1568 := Nat.sub 1 v1567
    let v1569 := Nat.land v1566 v1568
    let v1570 := psel (pmask v1569) v33 v1564
    let v1571 := plt 1 v1530 v61
    let v1572 := Nat.sub 1 v1571
    let v1573 := plt 1 v61 v1538
    let v1574 := Nat.sub 1 v1573
    let v1575 := Nat.land v1571 v1574
    let v1576 := Nat.land v1571 v1573
    let v1577 := plt 1 v1562 v61
    let v1578 := Nat.sub 1 v1577
    let v1579 := plt 1 v61 v1570
    let v1580 := Nat.sub 1 v1579
    let v1581 := Nat.land v1577 v1580
    let v1582 := Nat.land v1577 v1579
    let v1583 := Nat.land v1576 v1582
    let v1584 := Nat.sub 1 v1583
    let v1585 := Nat.lor v823 v1584
    let v1586 := Nat.land v1572 v1582
    let v1587 := Nat.lor v1581 v1586
    let v1588 := psel (pmask v1587) v1538 v1530
    let v1589 := Nat.land v1576 v1578
    let v1590 := Nat.lor v1575 v1589
    let v1591 := psel (pmask v1590) v1570 v1562
    let v1592 := Nat.land v1575 v1582
    let v1593 := Nat.lor v1581 v1592
    let v1594 := psel (pmask v1593) v1530 v1538
    let v1595 := Nat.land v1576 v1581
    let v1596 := Nat.lor v1575 v1595
    let v1597 := psel (pmask v1596) v1562 v1570
    let v1598 := smx 29 1 v1591 v1588
    let v1599 := srdF 1 v1598
    let v1600 := smx 29 1 v1597 v1594
    let v1601 := srdC 1 v1600
    let v1602 := plt 1 v61 v1599
    let v1603 := Nat.sub 1 v1602
    let v1604 := plt 1 v1505 v61
    let v1605 := psel (pmask v1604) v1599 v1601
    let v1608 := plt 1 v1605 v1505
    let v1609 := Nat.land v1602 v1608
    let v1610 := Nat.sub (Nat.add v61 OFFr) v1605
    let v1611 := plt 1 v1610 v1505
    let v1612 := Nat.sub 1 v1611
    let v1613 := Nat.lor v1603 v1612
    let v1614 := psel (pmask v1613) v95 v1505
    let v1615 := psel (pmask v1613) v33 v1605
    let v1616 := Nat.lor v1445 v1609
    let v1618 := hxa 1 H3 0
    let v1619 := plt 1 v61 v1618
    let v1620 := Nat.sub 1 v1619
    let t1618 := sc28u 1 v1618
    let v1622 := Nat.sub (Nat.add v28 t1618.2) OFFr
    let v1623 := plt 1 v1622 v95
    let v1624 := psel (pmask v1623) v95 v1622
    let v1625 := sshl 1 v1449
    let v1626 := smx 29 1 v1624 v1450
    let v1627 := plt 1 v1626 v1625
    let v1628 := Nat.sub 1 v1627
    let v1629 := plt 1 v15 v1618
    let v1630 := Nat.sub 1 v1629
    let v1631 := Nat.land v1628 v1630
    let v1632 := Nat.lor v1620 v1631
    let v1633 := psel (pmask v1632) v1618 v61
    let v1634 := hxa 1 H3 32
    let v1635 := plt 1 v1634 v9
    let v1636 := Nat.sub 1 v1635
    let t1634 := sc28u 1 v1634
    let v1638 := Nat.sub (Nat.add v31 t1634.2) OFFr
    let v1639 := plt 1 v1638 v33
    let v1640 := psel (pmask v1639) v1638 v33
    let v1641 := sshl 1 v1614
    let v1642 := smx 29 1 v1640 v1615
    let v1643 := plt 1 v1641 v1642
    let v1644 := Nat.sub 1 v1643
    let v1645 := Nat.lor v1636 v1644
    let v1646 := psel (pmask v1645) v1634 v9
    let v1647 := psel (pmask v778) v1633 v61
    let v1648 := psel (pmask v778) v1646 v9
    let v1649 := Nat.land v778 v1616
    let v1652 := Nat.sub 1 v1649
    let v1654 := Nat.sub (Nat.add v397 v1248) OFFr
    let v1656 := Nat.sub (Nat.add v722 v1648) OFFr
    let v1657 := plt 1 v3 v9
    let v1658 := plt 1 v1654 v9
    let v1659 := Nat.land v1657 v1658
    let v1661 := Nat.lor v23 v1659
    let v1662 := Nat.lor v47 v1659
    let v1663 := Nat.land v73 v139
    let v1664 := Nat.sub 1 v1663
    let v1665 := Nat.lor v1659 v1664
    let v1666 := Nat.land v73 v135
    let v1667 := Nat.lor v72 v1666
    let v1668 := psel (pmask v1667) v107 v100
    let v1669 := Nat.land v69 v139
    let v1670 := Nat.lor v138 v1669
    let v1671 := psel (pmask v1670) v60 v52
    let v1678 := smx 29 1 v1671 v1668
    let v1679 := srdF 1 v1678
    let v1682 := plt 1 v19 v1247
    let v1683 := plt 1 v9 v1248
    let v1684 := Nat.sub 1 v1683
    let v1685 := Nat.land v1682 v1684
    let v1686 := Nat.lor v1659 v1685
    let v1687 := psel (pmask v1245) t1234.2 v95
    let v1688 := psel (pmask v778) v1687 v95
    let v1689 := Nat.sub (Nat.add v28 v1688) OFFr
    let v1690 := plt 1 v1689 v95
    let v1691 := psel (pmask v1690) v95 v1689
    let v1692 := plt 1 v98 v1248
    let v1693 := psel (pmask v1692) v95 v1691
    let v1694 := psel (pmask v1232) t1218.2 v33
    let v1695 := psel (pmask v778) v1694 v33
    let v1696 := Nat.sub (Nat.add v31 v1695) OFFr
    let v1697 := plt 1 v1696 v33
    let v1698 := psel (pmask v1697) v1696 v33
    let v1699 := plt 1 v1247 v105
    let v1700 := psel (pmask v1699) v33 v1698
    let v1702 := psel (pmask v1232) t1218.1 v61
    let v1703 := psel (pmask v778) v1702 v61
    let v1705 := psel (pmask v1245) t1234.1 v61
    let v1706 := psel (pmask v778) v1705 v61
    let v1707 := plt 1 v1703 v1706
    let v1708 := psel (pmask v1707) v1703 v1706
    let v1709 := Nat.sub (Nat.add v28 v1708) OFFr
    let v1710 := psel (pmask v1707) v1706 v1703
    let v1711 := Nat.sub (Nat.add v31 v1710) OFFr
    let v1712 := plt 1 v1711 v33
    let v1713 := psel (pmask v1712) v1711 v33
    let v1714 := plt 1 v1247 v36
    let v1715 := plt 1 v38 v1248
    let v1716 := Nat.land v1714 v1715
    let v1717 := psel (pmask v1716) v33 v1713
    let v1718 := plt 1 v61 v1709
    let v1719 := Nat.sub 1 v1718
    let v1720 := plt 1 v1693 v61
    let v1721 := psel (pmask v1720) v1709 v1717
    let v1722 := plt 1 v1700 v61
    let v1723 := psel (pmask v1722) v1717 v1709
    let v1724 := Nat.lor v47 v1719
    let v1725 := Nat.lor v1659 v1724
    let v1726 := Nat.sub 1 v1720
    let v1727 := plt 1 v61 v1700
    let v1728 := Nat.sub 1 v1727
    let v1729 := Nat.land v1720 v1728
    let v1730 := Nat.land v1720 v1727
    let v1731 := plt 1 v61 v272
    let v1732 := Nat.sub 1 v1731
    let v1733 := Nat.land v166 v1732
    let v1734 := Nat.land v166 v1731
    let v1735 := Nat.land v1730 v1734
    let v1736 := Nat.sub 1 v1735
    let v1737 := Nat.lor v1719 v1736
    let v1738 := Nat.lor v1659 v1737
    let v1739 := Nat.land v1726 v1734
    let v1740 := Nat.lor v1733 v1739
    let v1741 := psel (pmask v1740) v1700 v1693
    let v1742 := psel (pmask v1740) v1723 v1721
    let v1743 := Nat.land v173 v1730
    let v1744 := Nat.lor v1729 v1743
    let v1745 := psel (pmask v1744) v272 v116
    let v1746 := Nat.sub (Nat.add v61 OFFr) v1679
    let v1747 := smx 29 1 v1746 v1742
    let v1748 := smx 29 1 v1745 v1741
    let v1749 := plt 1 v1747 v1748
    let v1750 := Nat.land v1718 v1749
    let v1751 := Nat.lor v1659 v1750
    let v1752 := plt 1 v5 v9
    let v1753 := plt 1 v1656 v9
    let v1754 := Nat.land v1752 v1753
    let v1756 := Nat.lor v23 v1754
    let v1757 := Nat.lor v403 v1754
    let v1758 := Nat.land v139 v422
    let v1759 := Nat.sub 1 v1758
    let v1760 := Nat.lor v1754 v1759
    let v1761 := Nat.land v135 v422
    let v1762 := Nat.lor v421 v1761
    let v1763 := psel (pmask v1762) v107 v100
    let v1764 := Nat.land v139 v418
    let v1765 := Nat.lor v138 v1764
    let v1766 := psel (pmask v1765) v416 v408
    let v1773 := smx 29 1 v1766 v1763
    let v1774 := srdF 1 v1773
    let v1777 := plt 1 v19 v1647
    let v1778 := plt 1 v9 v1648
    let v1779 := Nat.sub 1 v1778
    let v1780 := Nat.land v1777 v1779
    let v1781 := Nat.lor v1754 v1780
    let v1782 := psel (pmask v1645) t1634.2 v95
    let v1783 := psel (pmask v778) v1782 v95
    let v1784 := Nat.sub (Nat.add v28 v1783) OFFr
    let v1785 := plt 1 v1784 v95
    let v1786 := psel (pmask v1785) v95 v1784
    let v1787 := plt 1 v98 v1648
    let v1788 := psel (pmask v1787) v95 v1786
    let v1789 := psel (pmask v1632) t1618.2 v33
    let v1790 := psel (pmask v778) v1789 v33
    let v1791 := Nat.sub (Nat.add v31 v1790) OFFr
    let v1792 := plt 1 v1791 v33
    let v1793 := psel (pmask v1792) v1791 v33
    let v1794 := plt 1 v1647 v105
    let v1795 := psel (pmask v1794) v33 v1793
    let v1797 := psel (pmask v1632) t1618.1 v61
    let v1798 := psel (pmask v778) v1797 v61
    let v1800 := psel (pmask v1645) t1634.1 v61
    let v1801 := psel (pmask v778) v1800 v61
    let v1802 := plt 1 v1798 v1801
    let v1803 := psel (pmask v1802) v1798 v1801
    let v1804 := Nat.sub (Nat.add v28 v1803) OFFr
    let v1805 := psel (pmask v1802) v1801 v1798
    let v1806 := Nat.sub (Nat.add v31 v1805) OFFr
    ∀ (P : Prop), ((v1246 = if v1245 = 1 then v1234 else v9) → (v1247 = if v778 = 1 then v1233 else v61) → (v1248 = if v778 = 1 then v1246 else v9) → ((v1249 = 1 ↔ v778 = 1 ∧ v1216 = 1)) → (R 1 0 0 1 v1252 v1252) → ((v1252 = 1 ↔ ¬v1249 = 1)) → ((v1253 = 1 ↔ v820 = 1 ∧ v848 = 1)) → ((v1254 = 1 ↔ ¬v1253 = 1)) → (R 1 0 0 1 v1255 v1255) → ((v1255 = 1 ↔ v823 = 1 ∨ v1254 = 1)) → ((v1256 = 1 ↔ v816 = 1 ∧ v848 = 1)) → ((v1257 = 1 ↔ v847 = 1 ∨ v1256 = 1)) → (v1258 = if v1257 = 1 then v808 else v804) → ((v1259 = 1 ↔ v820 = 1 ∧ v844 = 1)) → ((v1260 = 1 ↔ v819 = 1 ∨ v1259 = 1)) → (v1261 = if v1260 = 1 then v798 else v794) → ((v1262 = 1 ↔ v819 = 1 ∧ v848 = 1)) → ((v1263 = 1 ↔ v847 = 1 ∨ v1262 = 1)) → (v1264 = if v1263 = 1 then v804 else v808) → ((v1265 = 1 ↔ v820 = 1 ∧ v847 = 1)) → ((v1266 = 1 ↔ v819 = 1 ∨ v1265 = 1)) → (v1267 = if v1266 = 1 then v794 else v798) → (sv v1268 = sv v1261 * sv v1258) → (sv v1269 = sv v1268 / 2 ^ 28) → (sv v1270 = sv v1267 * sv v1264) → (sv v1271 = -((-sv v1270) / 2 ^ 28)) → (sv v1272 = sv v784 - sv v1271) → (sv v1273 = sv v788 - sv v1269) → ((v1274 = 1 ↔ sv v61 < sv v1272)) → ((v1275 = 1 ↔ sv v1273 < sv v61)) → (v1276 = if v870 = 1 then v440 else v438) → (v1277 = if v871 = 1 then v438 else v440) → (v1278 = if v871 = 1 then v440 else v438) → (v1279 = if v870 = 1 then v438 else v440) → (v1280 = if v1274 = 1 then v766 else v764) → (v1281 = if v1275 = 1 then v764 else v766) → (v1282 = if v1275 = 1 then v766 else v764) → (v1283 = if v1274 = 1 then v764 else v766) → (sv v1289 = sv v1277 * sv v1277) → (sv v1290 = -((-sv v1289) / 2 ^ 28)) → (sv v1291 = sv v1290 + sv v1290) → (sv v1292 = sv v33 - sv v1291) → ((v1293 = 1 ↔ sv v1292 < sv v95)) → (v1294 = if v1293 = 1 then v95 else v1292) → (sv v1295 = sv v1276 * sv v1276) → (sv v1296 = sv v1295 / 2 ^ 28) → (sv v1297 = sv v1296 + sv v1296) → (sv v1298 = sv v33 - sv v1297) → (sv v1299 = sv v1281 * sv v1281) → (sv v1300 = -((-sv v1299) / 2 ^ 28)) → (sv v1301 = sv v1300 + sv v1300) → (sv v1302 = sv v33 - sv v1301) → ((v1303 = 1 ↔ sv v1302 < sv v95)) → (v1304 = if v1303 = 1 then v95 else v1302) → (sv v1305 = sv v1280 * sv v1280) → (sv v1306 = sv v1305 / 2 ^ 28) → (sv v1307 = sv v1306 + sv v1306) → (sv v1308 = sv v33 - sv v1307) → ((v1309 = 1 ↔ sv v1294 < sv v61)) → ((v1310 = 1 ↔ ¬v1309 = 1)) → ((v1311 = 1 ↔ sv v61 < sv v1298)) → ((v1312 = 1 ↔ ¬v1311 = 1)) → ((v1313 = 1 ↔ v1309 = 1 ∧ v1312 = 1)) → ((v1314 = 1 ↔ v1309 = 1 ∧ v1311 = 1)) → ((v1315 = 1 ↔ sv v1304 < sv v61)) → ((v1316 = 1 ↔ ¬v1315 = 1)) → ((v1317 = 1 ↔ sv v61 < sv v1308)) → ((v1318 = 1 ↔ ¬v1317 = 1)) → ((v1319 = 1 ↔ v1315 = 1 ∧ v1318 = 1)) → ((v1320 = 1 ↔ v1315 = 1 ∧ v1317 = 1)) → ((v1321 = 1 ↔ v1314 = 1 ∧ v1320 = 1)) → ((v1322 = 1 ↔ ¬v1321 = 1)) → (R 1 0 0 1 v1323 v1323) → ((v1323 = 1 ↔ v823 = 1 ∨ v1322 = 1)) → ((v1324 = 1 ↔ v1310 = 1 ∧ v1320 = 1)) → ((v1325 = 1 ↔ v1319 = 1 ∨ v1324 = 1)) → (v1326 = if v1325 = 1 then v1298 else v1294) → ((v1327 = 1 ↔ v1314 = 1 ∧ v1316 = 1)) → ((v1328 = 1 ↔ v1313 = 1 ∨ v1327 = 1)) → (v1329 = if v1328 = 1 then v1308 else v1304) → (sv v1336 = sv v1329 * sv v1326) → (sv v1337 = sv v1336 / 2 ^ 28) → (sv v1341 = sv v808 - sv v1337) → (sv v1342 = sv v940 - sv v1295) → (sv v1343 = ((Nat.sqrt (v1342 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1344 = sv v105 + sv v1343) → (sv v1345 = sv v1343 * sv v1276) → (sv v1346 = sv v1345 / 2 ^ 28) → (sv v1347 = sv v1346 + sv v1346) → (sv v1348 = sv v1344 * sv v1276) → (sv v1349 = -((-sv v1348) / 2 ^ 28)) → (sv v1350 = sv v1349 + sv v1349) → ((v1351 = 1 ↔ sv v1350 < sv v33)) → (v1352 = if v1351 = 1 then v1350 else v33) → (sv v1353 = sv v940 - sv v1289) → (sv v1354 = ((Nat.sqrt (v1353 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1355 = sv v105 + sv v1354) → (sv v1356 = sv v1354 * sv v1277) → (sv v1357 = sv v1356 / 2 ^ 28) → (sv v1358 = sv v1357 + sv v1357) → (sv v1359 = sv v1355 * sv v1277) → (sv v1360 = -((-sv v1359) / 2 ^ 28)) → (sv v1361 = sv v1360 + sv v1360) → ((v1362 = 1 ↔ sv v1361 < sv v33)) → (v1363 = if v1362 = 1 then v1361 else v33) → ((v1364 = 1 ↔ sv v1347 < sv v1358)) → (v1365 = if v1364 = 1 then v1347 else v1358) → ((v1366 = 1 ↔ sv v1352 < sv v1363)) → (v1367 = if v1366 = 1 then v1363 else v1352) → ((v1368 = 1 ↔ sv v967 < sv v1295)) → ((v1369 = 1 ↔ ¬v1368 = 1)) → ((v1370 = 1 ↔ sv v1289 < sv v967)) → ((v1371 = 1 ↔ ¬v1370 = 1)) → ((v1372 = 1 ↔ v1369 = 1 ∧ v1371 = 1)) → (v1373 = if v1372 = 1 then v33 else v1367) → (sv v1374 = sv v940 - sv v1305) → (sv v1375 = ((Nat.sqrt (v1374 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1376 = sv v105 + sv v1375) → (sv v1377 = sv v1375 * sv v1280) → (sv v1378 = sv v1377 / 2 ^ 28) → (sv v1379 = sv v1378 + sv v1378) → (sv v1380 = sv v1376 * sv v1280) → (sv v1381 = -((-sv v1380) / 2 ^ 28)) → (sv v1382 = sv v1381 + sv v1381) → ((v1383 = 1 ↔ sv v1382 < sv v33)) → (v1384 = if v1383 = 1 then v1382 else v33) → (sv v1385 = sv v940 - sv v1299) → (sv v1386 = ((Nat.sqrt (v1385 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1387 = sv v105 + sv v1386) → (sv v1388 = sv v1386 * sv v1281) → (sv v1389 = sv v1388 / 2 ^ 28) → (sv v1390 = sv v1389 + sv v1389) → (sv v1391 = sv v1387 * sv v1281) → (sv v1392 = -((-sv v1391) / 2 ^ 28)) → (sv v1393 = sv v1392 + sv v1392) → ((v1394 = 1 ↔ sv v1393 < sv v33)) → (v1395 = if v1394 = 1 then v1393 else v33) → ((v1396 = 1 ↔ sv v1379 < sv v1390)) → (v1397 = if v1396 = 1 then v1379 else v1390) → ((v1398 = 1 ↔ sv v1384 < sv v1395)) → (v1399 = if v1398 = 1 then v1395 else v1384) → ((v1400 = 1 ↔ sv v967 < sv v1305)) → ((v1401 = 1 ↔ ¬v1400 = 1)) → ((v1402 = 1 ↔ sv v1299 < sv v967)) → ((v1403 = 1 ↔ ¬v1402 = 1)) → ((v1404 = 1 ↔ v1401 = 1 ∧ v1403 = 1)) → (v1405 = if v1404 = 1 then v33 else v1399) → ((v1406 = 1 ↔ sv v1365 < sv v61)) → ((v1407 = 1 ↔ ¬v1406 = 1)) → ((v1408 = 1 ↔ sv v61 < sv v1373)) → ((v1409 = 1 ↔ ¬v1408 = 1)) → ((v1410 = 1 ↔ v1406 = 1 ∧ v1409 = 1)) → ((v1411 = 1 ↔ v1406 = 1 ∧ v1408 = 1)) → ((v1412 = 1 ↔ sv v1397 < sv v61)) → ((v1413 = 1 ↔ ¬v1412 = 1)) → ((v1414 = 1 ↔ sv v61 < sv v1405)) → ((v1415 = 1 ↔ ¬v1414 = 1)) → ((v1416 = 1 ↔ v1412 = 1 ∧ v1415 = 1)) → ((v1417 = 1 ↔ v1412 = 1 ∧ v1414 = 1)) → ((v1418 = 1 ↔ v1411 = 1 ∧ v1417 = 1)) → ((v1419 = 1 ↔ ¬v1418 = 1)) → (R 1 0 0 1 v1420 v1420) → ((v1420 = 1 ↔ v823 = 1 ∨ v1419 = 1)) → ((v1421 = 1 ↔ v1407 = 1 ∧ v1417 = 1)) → ((v1422 = 1 ↔ v1416 = 1 ∨ v1421 = 1)) → (v1423 = if v1422 = 1 then v1373 else v1365) → ((v1424 = 1 ↔ v1411 = 1 ∧ v1413 = 1)) → ((v1425 = 1 ↔ v1410 = 1 ∨ v1424 = 1)) → (v1426 = if v1425 = 1 then v1405 else v1397) → ((v1427 = 1 ↔ v1410 = 1 ∧ v1417 = 1)) → ((v1428 = 1 ↔ v1416 = 1 ∨ v1427 = 1)) → (v1429 = if v1428 = 1 then v1365 else v1373) → ((v1430 = 1 ↔ v1411 = 1 ∧ v1416 = 1)) → ((v1431 = 1 ↔ v1410 = 1 ∨ v1430 = 1)) → (v1432 = if v1431 = 1 then v1397 else v1405) → (sv v1433 = sv v1426 * sv v1423) → (sv v1434 = sv v1433 / 2 ^ 28) → (sv v1435 = sv v1432 * sv v1429) → (sv v1436 = -((-sv v1435) / 2 ^ 28)) → ((v1437 = 1 ↔ sv v61 < sv v1434)) → ((v1438 = 1 ↔ ¬v1437 = 1)) → ((v1441 = 1 ↔ sv v1341 < sv v61)) → (v1442 = if v1441 = 1 then v1436 else v1434) → (sv v1443 = sv v61 - sv v1442) → ((v1444 = 1 ↔ sv v1341 < sv v1443)) → ((v1445 = 1 ↔ v1437 = 1 ∧ v1444 = 1)) → ((v1446 = 1 ↔ sv v1341 < sv v1442)) → ((v1447 = 1 ↔ ¬v1446 = 1)) → ((v1448 = 1 ↔ v1438 = 1 ∨ v1447 = 1)) → (v1449 = if v1448 = 1 then v33 else v1341) → (v1450 = if v1448 = 1 then v33 else v1442) → (sv v1454 = sv v1279 * sv v1279) → (sv v1455 = -((-sv v1454) / 2 ^ 28)) → (sv v1456 = sv v1455 + sv v1455) → (sv v1457 = sv v33 - sv v1456) → ((v1458 = 1 ↔ sv v1457 < sv v95)) → (v1459 = if v1458 = 1 then v95 else v1457) → (sv v1460 = sv v1278 * sv v1278) → (sv v1461 = sv v1460 / 2 ^ 28) → (sv v1462 = sv v1461 + sv v1461) → (sv v1463 = sv v33 - sv v1462) → (sv v1464 = sv v1283 * sv v1283) → (sv v1465 = -((-sv v1464) / 2 ^ 28)) → (sv v1466 = sv v1465 + sv v1465) → (sv v1467 = sv v33 - sv v1466) → ((v1468 = 1 ↔ sv v1467 < sv v95)) → (v1469 = if v1468 = 1 then v95 else v1467) → (sv v1470 = sv v1282 * sv v1282) → (sv v1471 = sv v1470 / 2 ^ 28) → (sv v1472 = sv v1471 + sv v1471) → (sv v1473 = sv v33 - sv v1472) → ((v1474 = 1 ↔ sv v1459 < sv v61)) → ((v1476 = 1 ↔ sv v61 < sv v1463)) → ((v1477 = 1 ↔ ¬v1476 = 1)) → ((v1478 = 1 ↔ v1474 = 1 ∧ v1477 = 1)) → ((v1479 = 1 ↔ v1474 = 1 ∧ v1476 = 1)) → ((v1480 = 1 ↔ sv v1469 < sv v61)) → ((v1482 = 1 ↔ sv v61 < sv v1473)) → ((v1483 = 1 ↔ ¬v1482 = 1)) → ((v1484 = 1 ↔ v1480 = 1 ∧ v1483 = 1)) → ((v1485 = 1 ↔ v1480 = 1 ∧ v1482 = 1)) → ((v1486 = 1 ↔ v1479 = 1 ∧ v1485 = 1)) → ((v1487 = 1 ↔ ¬v1486 = 1)) → (R 1 0 0 1 v1488 v1488) → ((v1488 = 1 ↔ v823 = 1 ∨ v1487 = 1)) → ((v1495 = 1 ↔ v1478 = 1 ∧ v1485 = 1)) → ((v1496 = 1 ↔ v1484 = 1 ∨ v1495 = 1)) → (v1497 = if v1496 = 1 then v1459 else v1463) → ((v1498 = 1 ↔ v1479 = 1 ∧ v1484 = 1)) → ((v1499 = 1 ↔ v1478 = 1 ∨ v1498 = 1)) → (v1500 = if v1499 = 1 then v1469 else v1473) → (sv v1503 = sv v1500 * sv v1497) → (sv v1504 = -((-sv v1503) / 2 ^ 28)) → (sv v1505 = sv v804 - sv v1504) → (sv v1507 = sv v940 - sv v1460) → (sv v1508 = ((Nat.sqrt (v1507 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1509 = sv v105 + sv v1508) → (sv v1510 = sv v1508 * sv v1278) → (sv v1511 = sv v1510 / 2 ^ 28) → (sv v1512 = sv v1511 + sv v1511) → (sv v1513 = sv v1509 * sv v1278) → (sv v1514 = -((-sv v1513) / 2 ^ 28)) → (sv v1515 = sv v1514 + sv v1514) → ((v1516 = 1 ↔ sv v1515 < sv v33)) → (v1517 = if v1516 = 1 then v1515 else v33) → (sv v1518 = sv v940 - sv v1454) → (sv v1519 = ((Nat.sqrt (v1518 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1520 = sv v105 + sv v1519) → (sv v1521 = sv v1519 * sv v1279) → (sv v1522 = sv v1521 / 2 ^ 28) → (sv v1523 = sv v1522 + sv v1522) → (sv v1524 = sv v1520 * sv v1279) → (sv v1525 = -((-sv v1524) / 2 ^ 28)) → (sv v1526 = sv v1525 + sv v1525) → ((v1527 = 1 ↔ sv v1526 < sv v33)) → (v1528 = if v1527 = 1 then v1526 else v33) → ((v1529 = 1 ↔ sv v1512 < sv v1523)) → (v1530 = if v1529 = 1 then v1512 else v1523) → ((v1531 = 1 ↔ sv v1517 < sv v1528)) → (v1532 = if v1531 = 1 then v1528 else v1517) → ((v1533 = 1 ↔ sv v967 < sv v1460)) → ((v1534 = 1 ↔ ¬v1533 = 1)) → ((v1535 = 1 ↔ sv v1454 < sv v967)) → ((v1536 = 1 ↔ ¬v1535 = 1)) → ((v1537 = 1 ↔ v1534 = 1 ∧ v1536 = 1)) → (v1538 = if v1537 = 1 then v33 else v1532) → (sv v1539 = sv v940 - sv v1470) → (sv v1540 = ((Nat.sqrt (v1539 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1541 = sv v105 + sv v1540) → (sv v1542 = sv v1540 * sv v1282) → (sv v1543 = sv v1542 / 2 ^ 28) → (sv v1544 = sv v1543 + sv v1543) → (sv v1545 = sv v1541 * sv v1282) → (sv v1546 = -((-sv v1545) / 2 ^ 28)) → (sv v1547 = sv v1546 + sv v1546) → ((v1548 = 1 ↔ sv v1547 < sv v33)) → (v1549 = if v1548 = 1 then v1547 else v33) → (sv v1550 = sv v940 - sv v1464) → (sv v1551 = ((Nat.sqrt (v1550 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1552 = sv v105 + sv v1551) → (sv v1553 = sv v1551 * sv v1283) → (sv v1554 = sv v1553 / 2 ^ 28) → (sv v1555 = sv v1554 + sv v1554) → (sv v1556 = sv v1552 * sv v1283) → (sv v1557 = -((-sv v1556) / 2 ^ 28)) → (sv v1558 = sv v1557 + sv v1557) → ((v1559 = 1 ↔ sv v1558 < sv v33)) → (v1560 = if v1559 = 1 then v1558 else v33) → ((v1561 = 1 ↔ sv v1544 < sv v1555)) → (v1562 = if v1561 = 1 then v1544 else v1555) → ((v1563 = 1 ↔ sv v1549 < sv v1560)) → (v1564 = if v1563 = 1 then v1560 else v1549) → ((v1565 = 1 ↔ sv v967 < sv v1470)) → ((v1566 = 1 ↔ ¬v1565 = 1)) → ((v1567 = 1 ↔ sv v1464 < sv v967)) → ((v1568 = 1 ↔ ¬v1567 = 1)) → ((v1569 = 1 ↔ v1566 = 1 ∧ v1568 = 1)) → (v1570 = if v1569 = 1 then v33 else v1564) → ((v1571 = 1 ↔ sv v1530 < sv v61)) → ((v1572 = 1 ↔ ¬v1571 = 1)) → ((v1573 = 1 ↔ sv v61 < sv v1538)) → ((v1574 = 1 ↔ ¬v1573 = 1)) → ((v1575 = 1 ↔ v1571 = 1 ∧ v1574 = 1)) → ((v1576 = 1 ↔ v1571 = 1 ∧ v1573 = 1)) → ((v1577 = 1 ↔ sv v1562 < sv v61)) → ((v1578 = 1 ↔ ¬v1577 = 1)) → ((v1579 = 1 ↔ sv v61 < sv v1570)) → ((v1580 = 1 ↔ ¬v1579 = 1)) → ((v1581 = 1 ↔ v1577 = 1 ∧ v1580 = 1)) → ((v1582 = 1 ↔ v1577 = 1 ∧ v1579 = 1)) → ((v1583 = 1 ↔ v1576 = 1 ∧ v1582 = 1)) → ((v1584 = 1 ↔ ¬v1583 = 1)) → (R 1 0 0 1 v1585 v1585) → ((v1585 = 1 ↔ v823 = 1 ∨ v1584 = 1)) → ((v1586 = 1 ↔ v1572 = 1 ∧ v1582 = 1)) → ((v1587 = 1 ↔ v1581 = 1 ∨ v1586 = 1)) → (v1588 = if v1587 = 1 then v1538 else v1530) → ((v1589 = 1 ↔ v1576 = 1 ∧ v1578 = 1)) → ((v1590 = 1 ↔ v1575 = 1 ∨ v1589 = 1)) → (v1591 = if v1590 = 1 then v1570 else v1562) → ((v1592 = 1 ↔ v1575 = 1 ∧ v1582 = 1)) → ((v1593 = 1 ↔ v1581 = 1 ∨ v1592 = 1)) → (v1594 = if v1593 = 1 then v1530 else v1538) → ((v1595 = 1 ↔ v1576 = 1 ∧ v1581 = 1)) → ((v1596 = 1 ↔ v1575 = 1 ∨ v1595 = 1)) → (v1597 = if v1596 = 1 then v1562 else v1570) → (sv v1598 = sv v1591 * sv v1588) → (sv v1599 = sv v1598 / 2 ^ 28) → (sv v1600 = sv v1597 * sv v1594) → (sv v1601 = -((-sv v1600) / 2 ^ 28)) → ((v1602 = 1 ↔ sv v61 < sv v1599)) → ((v1603 = 1 ↔ ¬v1602 = 1)) → ((v1604 = 1 ↔ sv v1505 < sv v61)) → (v1605 = if v1604 = 1 then v1599 else v1601) → ((v1608 = 1 ↔ sv v1605 < sv v1505)) → ((v1609 = 1 ↔ v1602 = 1 ∧ v1608 = 1)) → (sv v1610 = sv v61 - sv v1605) → ((v1611 = 1 ↔ sv v1610 < sv v1505)) → ((v1612 = 1 ↔ ¬v1611 = 1)) → ((v1613 = 1 ↔ v1603 = 1 ∨ v1612 = 1)) → (v1614 = if v1613 = 1 then v95 else v1505) → (v1615 = if v1613 = 1 then v33 else v1605) → ((v1616 = 1 ↔ v1445 = 1 ∨ v1609 = 1)) → (sv v1618 = ((H3 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → ((v1619 = 1 ↔ sv v61 < sv v1618)) → ((v1620 = 1 ↔ ¬v1619 = 1)) → (sv t1618.1 = (sc28pS (scArg v1618)).1) → (sv t1618.2 = (sc28pS (scArg v1618)).2) → (sv v1622 = sv v28 + sv t1618.2) → ((v1623 = 1 ↔ sv v1622 < sv v95)) → (v1624 = if v1623 = 1 then v95 else v1622) → (sv v1625 = sv v1449 * 2 ^ 28) → (sv v1626 = sv v1624 * sv v1450) → ((v1627 = 1 ↔ sv v1626 < sv v1625)) → ((v1628 = 1 ↔ ¬v1627 = 1)) → ((v1629 = 1 ↔ sv v15 < sv v1618)) → ((v1630 = 1 ↔ ¬v1629 = 1)) → ((v1631 = 1 ↔ v1628 = 1 ∧ v1630 = 1)) → ((v1632 = 1 ↔ v1620 = 1 ∨ v1631 = 1)) → (v1633 = if v1632 = 1 then v1618 else v61) → (sv v1634 = ((H3 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ)) → ((v1635 = 1 ↔ sv v1634 < sv v9)) → ((v1636 = 1 ↔ ¬v1635 = 1)) → (sv t1634.1 = (sc28pS (scArg v1634)).1) → (sv t1634.2 = (sc28pS (scArg v1634)).2) → (sv v1638 = sv v31 + sv t1634.2) → ((v1639 = 1 ↔ sv v1638 < sv v33)) → (v1640 = if v1639 = 1 then v1638 else v33) → (sv v1641 = sv v1614 * 2 ^ 28) → (sv v1642 = sv v1640 * sv v1615) → ((v1643 = 1 ↔ sv v1641 < sv v1642)) → ((v1644 = 1 ↔ ¬v1643 = 1)) → ((v1645 = 1 ↔ v1636 = 1 ∨ v1644 = 1)) → (v1646 = if v1645 = 1 then v1634 else v9) → (R 1 0 4611686018427387904 4611686019501129727 v1647 v1647) → (v1647 = if v778 = 1 then v1633 else v61) → (R 1 0 4611686018427387904 4611686019501129727 v1648 v1648) → (v1648 = if v778 = 1 then v1646 else v9) → ((v1649 = 1 ↔ v778 = 1 ∧ v1616 = 1)) → (R 1 0 0 1 v1652 v1652) → ((v1652 = 1 ↔ ¬v1649 = 1)) → (sv v1654 = sv v397 + sv v1248) → (sv v1656 = sv v722 + sv v1648) → ((v1657 = 1 ↔ sv v3 < sv v9)) → ((v1658 = 1 ↔ sv v1654 < sv v9)) → ((v1659 = 1 ↔ v1657 = 1 ∧ v1658 = 1)) → (R 1 0 0 1 v1661 v1661) → ((v1661 = 1 ↔ v23 = 1 ∨ v1659 = 1)) → (R 1 0 0 1 v1662 v1662) → ((v1662 = 1 ↔ v47 = 1 ∨ v1659 = 1)) → ((v1663 = 1 ↔ v73 = 1 ∧ v139 = 1)) → ((v1664 = 1 ↔ ¬v1663 = 1)) → (R 1 0 0 1 v1665 v1665) → ((v1665 = 1 ↔ v1659 = 1 ∨ v1664 = 1)) → ((v1666 = 1 ↔ v73 = 1 ∧ v135 = 1)) → ((v1667 = 1 ↔ v72 = 1 ∨ v1666 = 1)) → (v1668 = if v1667 = 1 then v107 else v100) → ((v1669 = 1 ↔ v69 = 1 ∧ v139 = 1)) → ((v1670 = 1 ↔ v138 = 1 ∨ v1669 = 1)) → (v1671 = if v1670 = 1 then v60 else v52) → (sv v1678 = sv v1671 * sv v1668) → (sv v1679 = sv v1678 / 2 ^ 28) → ((v1682 = 1 ↔ sv v19 < sv v1247)) → ((v1683 = 1 ↔ sv v9 < sv v1248)) → ((v1684 = 1 ↔ ¬v1683 = 1)) → ((v1685 = 1 ↔ v1682 = 1 ∧ v1684 = 1)) → (R 1 0 0 1 v1686 v1686) → ((v1686 = 1 ↔ v1659 = 1 ∨ v1685 = 1)) → (v1687 = if v1245 = 1 then t1234.2 else v95) → (v1688 = if v778 = 1 then v1687 else v95) → (sv v1689 = sv v28 + sv v1688) → ((v1690 = 1 ↔ sv v1689 < sv v95)) → (v1691 = if v1690 = 1 then v95 else v1689) → ((v1692 = 1 ↔ sv v98 < sv v1248)) → (v1693 = if v1692 = 1 then v95 else v1691) → (v1694 = if v1232 = 1 then t1218.2 else v33) → (v1695 = if v778 = 1 then v1694 else v33) → (sv v1696 = sv v31 + sv v1695) → ((v1697 = 1 ↔ sv v1696 < sv v33)) → (v1698 = if v1697 = 1 then v1696 else v33) → ((v1699 = 1 ↔ sv v1247 < sv v105)) → (v1700 = if v1699 = 1 then v33 else v1698) → (v1702 = if v1232 = 1 then t1218.1 else v61) → (v1703 = if v778 = 1 then v1702 else v61) → (v1705 = if v1245 = 1 then t1234.1 else v61) → (v1706 = if v778 = 1 then v1705 else v61) → ((v1707 = 1 ↔ sv v1703 < sv v1706)) → (v1708 = if v1707 = 1 then v1703 else v1706) → (sv v1709 = sv v28 + sv v1708) → (v1710 = if v1707 = 1 then v1706 else v1703) → (sv v1711 = sv v31 + sv v1710) → ((v1712 = 1 ↔ sv v1711 < sv v33)) → (v1713 = if v1712 = 1 then v1711 else v33) → ((v1714 = 1 ↔ sv v1247 < sv v36)) → ((v1715 = 1 ↔ sv v38 < sv v1248)) → ((v1716 = 1 ↔ v1714 = 1 ∧ v1715 = 1)) → (v1717 = if v1716 = 1 then v33 else v1713) → ((v1718 = 1 ↔ sv v61 < sv v1709)) → ((v1719 = 1 ↔ ¬v1718 = 1)) → ((v1720 = 1 ↔ sv v1693 < sv v61)) → (v1721 = if v1720 = 1 then v1709 else v1717) → ((v1722 = 1 ↔ sv v1700 < sv v61)) → (v1723 = if v1722 = 1 then v1717 else v1709) → ((v1724 = 1 ↔ v47 = 1 ∨ v1719 = 1)) → (R 1 0 0 1 v1725 v1725) → ((v1725 = 1 ↔ v1659 = 1 ∨ v1724 = 1)) → ((v1726 = 1 ↔ ¬v1720 = 1)) → ((v1727 = 1 ↔ sv v61 < sv v1700)) → ((v1728 = 1 ↔ ¬v1727 = 1)) → ((v1729 = 1 ↔ v1720 = 1 ∧ v1728 = 1)) → ((v1730 = 1 ↔ v1720 = 1 ∧ v1727 = 1)) → ((v1731 = 1 ↔ sv v61 < sv v272)) → ((v1732 = 1 ↔ ¬v1731 = 1)) → ((v1733 = 1 ↔ v166 = 1 ∧ v1732 = 1)) → ((v1734 = 1 ↔ v166 = 1 ∧ v1731 = 1)) → ((v1735 = 1 ↔ v1730 = 1 ∧ v1734 = 1)) → ((v1736 = 1 ↔ ¬v1735 = 1)) → ((v1737 = 1 ↔ v1719 = 1 ∨ v1736 = 1)) → (R 1 0 0 1 v1738 v1738) → ((v1738 = 1 ↔ v1659 = 1 ∨ v1737 = 1)) → ((v1739 = 1 ↔ v1726 = 1 ∧ v1734 = 1)) → ((v1740 = 1 ↔ v1733 = 1 ∨ v1739 = 1)) → (v1741 = if v1740 = 1 then v1700 else v1693) → (v1742 = if v1740 = 1 then v1723 else v1721) → ((v1743 = 1 ↔ v173 = 1 ∧ v1730 = 1)) → ((v1744 = 1 ↔ v1729 = 1 ∨ v1743 = 1)) → (v1745 = if v1744 = 1 then v272 else v116) → (sv v1746 = sv v61 - sv v1679) → (sv v1747 = sv v1746 * sv v1742) → (sv v1748 = sv v1745 * sv v1741) → ((v1749 = 1 ↔ sv v1747 < sv v1748)) → ((v1750 = 1 ↔ v1718 = 1 ∧ v1749 = 1)) → (R 1 0 0 1 v1751 v1751) → ((v1751 = 1 ↔ v1659 = 1 ∨ v1750 = 1)) → ((v1752 = 1 ↔ sv v5 < sv v9)) → ((v1753 = 1 ↔ sv v1656 < sv v9)) → (R 1 0 0 1 v1754 v1754) → ((v1754 = 1 ↔ v1752 = 1 ∧ v1753 = 1)) → (R 1 0 0 1 v1756 v1756) → ((v1756 = 1 ↔ v23 = 1 ∨ v1754 = 1)) → (R 1 0 0 1 v1757 v1757) → ((v1757 = 1 ↔ v403 = 1 ∨ v1754 = 1)) → ((v1758 = 1 ↔ v139 = 1 ∧ v422 = 1)) → ((v1759 = 1 ↔ ¬v1758 = 1)) → (R 1 0 0 1 v1760 v1760) → ((v1760 = 1 ↔ v1754 = 1 ∨ v1759 = 1)) → ((v1761 = 1 ↔ v135 = 1 ∧ v422 = 1)) → ((v1762 = 1 ↔ v421 = 1 ∨ v1761 = 1)) → (v1763 = if v1762 = 1 then v107 else v100) → ((v1764 = 1 ↔ v139 = 1 ∧ v418 = 1)) → ((v1765 = 1 ↔ v138 = 1 ∨ v1764 = 1)) → (v1766 = if v1765 = 1 then v416 else v408) → (sv v1773 = sv v1766 * sv v1763) → (R 1 0 4611686018158952433 4611686018695823374 v1774 v1774) → (sv v1774 = sv v1773 / 2 ^ 28) → ((v1777 = 1 ↔ sv v19 < sv v1647)) → ((v1778 = 1 ↔ sv v9 < sv v1648)) → ((v1779 = 1 ↔ ¬v1778 = 1)) → ((v1780 = 1 ↔ v1777 = 1 ∧ v1779 = 1)) → (R 1 0 0 1 v1781 v1781) → ((v1781 = 1 ↔ v1754 = 1 ∨ v1780 = 1)) → (v1782 = if v1645 = 1 then t1634.2 else v95) → (v1783 = if v778 = 1 then v1782 else v95) → (sv v1784 = sv v28 + sv v1783) → ((v1785 = 1 ↔ sv v1784 < sv v95)) → (v1786 = if v1785 = 1 then v95 else v1784) → ((v1787 = 1 ↔ sv v98 < sv v1648)) → (R 1 0 4611686018158952441 4611686018695823359 v1788 v1788) → (v1788 = if v1787 = 1 then v95 else v1786) → (v1789 = if v1632 = 1 then t1618.2 else v33) → (v1790 = if v778 = 1 then v1789 else v33) → (sv v1791 = sv v31 + sv v1790) → ((v1792 = 1 ↔ sv v1791 < sv v33)) → (v1793 = if v1792 = 1 then v1791 else v33) → ((v1794 = 1 ↔ sv v1647 < sv v105)) → (R 1 0 4611686018158952449 4611686018695823367 v1795 v1795) → (v1795 = if v1794 = 1 then v33 else v1793) → (v1797 = if v1632 = 1 then t1618.1 else v61) → (v1798 = if v778 = 1 then v1797 else v61) → (v1800 = if v1645 = 1 then t1634.1 else v61) → (v1801 = if v778 = 1 then v1800 else v61) → ((v1802 = 1 ↔ sv v1798 < sv v1801)) → (v1803 = if v1802 = 1 then v1798 else v1801) → (R 1 0 4611686018427387900 4611686018695823359 v1804 v1804) → (sv v1804 = sv v28 + sv v1803) → (v1805 = if v1802 = 1 then v1801 else v1798) → (R 1 0 4611686018427387908 4611686018695823367 v1806 v1806) → (sv v1806 = sv v31 + sv v1805) → P) → P := by
  intro OFFr v3 v5 v9 v15 v19 v28 v31 v33 v36 v38 v61 v95 v98 v105 v940 v967 v1234 v1246 v1247 v1248 v1249 v1252 v1253 v1254 v1255 v1256 v1257 v1258 v1259 v1260 v1261 v1262 v1263 v1264 v1265 v1266 v1267 v1268 v1269 v1270 v1271 v1272 v1273 v1274 v1275 v1276 v1277 v1278 v1279 v1280 v1281 v1282 v1283 v1289 v1290 v1291 v1292 v1293 v1294 v1295 v1296 v1297 v1298 v1299 v1300 v1301 v1302 v1303 v1304 v1305 v1306 v1307 v1308 v1309 v1310 v1311 v1312 v1313 v1314 v1315 v1316 v1317 v1318 v1319 v1320 v1321 v1322 v1323 v1324 v1325 v1326 v1327 v1328 v1329 v1336 v1337 v1341 v1342 v1343 v1344 v1345 v1346 v1347 v1348 v1349 v1350 v1351 v1352 v1353 v1354 v1355 v1356 v1357 v1358 v1359 v1360 v1361 v1362 v1363 v1364 v1365 v1366 v1367 v1368 v1369 v1370 v1371 v1372 v1373 v1374 v1375 v1376 v1377 v1378 v1379 v1380 v1381 v1382 v1383 v1384 v1385 v1386 v1387 v1388 v1389 v1390 v1391 v1392 v1393 v1394 v1395 v1396 v1397 v1398 v1399 v1400 v1401 v1402 v1403 v1404 v1405 v1406 v1407 v1408 v1409 v1410 v1411 v1412 v1413 v1414 v1415 v1416 v1417 v1418 v1419 v1420 v1421 v1422 v1423 v1424 v1425 v1426 v1427 v1428 v1429 v1430 v1431 v1432 v1433 v1434 v1435 v1436 v1437 v1438 v1441 v1442 v1443 v1444 v1445 v1446 v1447 v1448 v1449 v1450 v1454 v1455 v1456 v1457 v1458 v1459 v1460 v1461 v1462 v1463 v1464 v1465 v1466 v1467 v1468 v1469 v1470 v1471 v1472 v1473 v1474 v1476 v1477 v1478 v1479 v1480 v1482 v1483 v1484 v1485 v1486 v1487 v1488 v1495 v1496 v1497 v1498 v1499 v1500 v1503 v1504 v1505 v1507 v1508 v1509 v1510 v1511 v1512 v1513 v1514 v1515 v1516 v1517 v1518 v1519 v1520 v1521 v1522 v1523 v1524 v1525 v1526 v1527 v1528 v1529 v1530 v1531 v1532 v1533 v1534 v1535 v1536 v1537 v1538 v1539 v1540 v1541 v1542 v1543 v1544 v1545 v1546 v1547 v1548 v1549 v1550 v1551 v1552 v1553 v1554 v1555 v1556 v1557 v1558 v1559 v1560 v1561 v1562 v1563 v1564 v1565 v1566 v1567 v1568 v1569 v1570 v1571 v1572 v1573 v1574 v1575 v1576 v1577 v1578 v1579 v1580 v1581 v1582 v1583 v1584 v1585 v1586 v1587 v1588 v1589 v1590 v1591 v1592 v1593 v1594 v1595 v1596 v1597 v1598 v1599 v1600 v1601 v1602 v1603 v1604 v1605 v1608 v1609 v1610 v1611 v1612 v1613 v1614 v1615 v1616 v1618 v1619 v1620 t1618 v1622 v1623 v1624 v1625 v1626 v1627 v1628 v1629 v1630 v1631 v1632 v1633 v1634 v1635 v1636 t1634 v1638 v1639 v1640 v1641 v1642 v1643 v1644 v1645 v1646 v1647 v1648 v1649 v1652 v1654 v1656 v1657 v1658 v1659 v1661 v1662 v1663 v1664 v1665 v1666 v1667 v1668 v1669 v1670 v1671 v1678 v1679 v1682 v1683 v1684 v1685 v1686 v1687 v1688 v1689 v1690 v1691 v1692 v1693 v1694 v1695 v1696 v1697 v1698 v1699 v1700 v1702 v1703 v1705 v1706 v1707 v1708 v1709 v1710 v1711 v1712 v1713 v1714 v1715 v1716 v1717 v1718 v1719 v1720 v1721 v1722 v1723 v1724 v1725 v1726 v1727 v1728 v1729 v1730 v1731 v1732 v1733 v1734 v1735 v1736 v1737 v1738 v1739 v1740 v1741 v1742 v1743 v1744 v1745 v1746 v1747 v1748 v1749 v1750 v1751 v1752 v1753 v1754 v1756 v1757 v1758 v1759 v1760 v1761 v1762 v1763 v1764 v1765 v1766 v1773 v1774 v1777 v1778 v1779 v1780 v1781 v1782 v1783 v1784 v1785 v1786 v1787 v1788 v1789 v1790 v1791 v1792 v1793 v1794 v1795 v1797 v1798 v1800 v1801 v1802 v1803 v1804 v1805 v1806
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v3 : R 1 0 4611686018427387904 4611686087146864624 v3 v3 := (r1_ix hb_F1 32 (of_decide_eq_true rfl))
  have h_v5 : R 1 0 4611686018427387904 4611686087146864624 v5 v5 := (r1_ix hb_F2 32 (of_decide_eq_true rfl))
  have h_v9 : R 1 0 4611686019270702761 4611686019270702761 v9 v9 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have h_v15 : R 1 0 4611686019270702760 4611686019270702760 v15 v15 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
  have h_v19 : R 1 0 4611686018427387903 4611686018427387903 v19 v19 := (r_c hl 4611686018427387903 (of_decide_eq_true rfl))
  have h_v28 : R 1 0 4611686018427387900 4611686018427387900 v28 v28 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have h_v31 : R 1 0 4611686018427387908 4611686018427387908 v31 v31 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have h_v33 : R 1 0 4611686018695823360 4611686018695823360 v33 v33 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have h_v36 : R 1 0 4611686018849045334 4611686018849045334 v36 v36 := (r_c hl 4611686018849045334 (of_decide_eq_true rfl))
  have h_v38 : R 1 0 4611686018849045331 4611686018849045331 v38 v38 := (r_c hl 4611686018849045331 (of_decide_eq_true rfl))
  have h_v61 : R 1 0 4611686018427387904 4611686018427387904 v61 v61 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v95 : R 1 0 4611686018158952448 4611686018158952448 v95 v95 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have h_v98 : R 1 0 4611686019270702759 4611686019270702759 v98 v98 := (r_c hl 4611686019270702759 (of_decide_eq_true rfl))
  have h_v105 : R 1 0 4611686018427387905 4611686018427387905 v105 v105 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have h_v940 : R 1 0 4683743612465315840 4683743612465315840 v940 v940 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have h_v967 : R 1 0 4647714815446351872 4647714815446351872 v967 v967 := (r_c hl 4647714815446351872 (of_decide_eq_true rfl))
  have h_v1234 : R 1 0 4611686018427387904 4611686019501129727 v1234 v1234 := (r1_hxa hb_H2 32 (of_decide_eq_true rfl))
  have h_v1246 : R 1 0 4611686018427387904 4611686019501129727 v1246 v1246 := (r_psel hl h_v1245 h_v1234 h_v9 (of_decide_eq_true rfl))
  have e_v1246 : v1246 = if v1245 = 1 then v1234 else v9 := e_psel h_v1245 h_v1234 h_v9 (of_decide_eq_true rfl)
  have h_v1247 : R 1 0 4611686018427387904 4611686019501129727 v1247 v1247 := (r_psel hl h_v778 h_v1233 h_v61 (of_decide_eq_true rfl))
  have e_v1247 : v1247 = if v778 = 1 then v1233 else v61 := e_psel h_v778 h_v1233 h_v61 (of_decide_eq_true rfl)
  have h_v1248 : R 1 0 4611686018427387904 4611686019501129727 v1248 v1248 := (r_psel hl h_v778 h_v1246 h_v9 (of_decide_eq_true rfl))
  have e_v1248 : v1248 = if v778 = 1 then v1246 else v9 := e_psel h_v778 h_v1246 h_v9 (of_decide_eq_true rfl)
  have h_v1249 : R 1 0 0 1 v1249 v1249 := (r_land hl h_v778 h_v1216 (of_decide_eq_true rfl))
  clear h_v1234 h_v1246
  have e_v1249 : (v1249 = 1 ↔ v778 = 1 ∧ v1216 = 1) := e_land h_v778 h_v1216 (of_decide_eq_true rfl)
  have h_v1252 : R 1 0 0 1 v1252 v1252 := (r_sub hl (r_O hl) h_v1249 (of_decide_eq_true rfl))
  have e_v1252 : (v1252 = 1 ↔ ¬v1249 = 1) := e_not h_v1249 (of_decide_eq_true rfl)
  have h_v1253 : R 1 0 0 1 v1253 v1253 := (r_land hl h_v820 h_v848 (of_decide_eq_true rfl))
  have e_v1253 : (v1253 = 1 ↔ v820 = 1 ∧ v848 = 1) := e_land h_v820 h_v848 (of_decide_eq_true rfl)
  have h_v1254 : R 1 0 0 1 v1254 v1254 := (r_sub hl (r_O hl) h_v1253 (of_decide_eq_true rfl))
  have e_v1254 : (v1254 = 1 ↔ ¬v1253 = 1) := e_not h_v1253 (of_decide_eq_true rfl)
  have h_v1255 : R 1 0 0 1 v1255 v1255 := (r_lor hl h_v823 h_v1254 (of_decide_eq_true rfl))
  have e_v1255 : (v1255 = 1 ↔ v823 = 1 ∨ v1254 = 1) := e_lor h_v823 h_v1254 (of_decide_eq_true rfl)
  have h_v1256 : R 1 0 0 1 v1256 v1256 := (r_land hl h_v816 h_v848 (of_decide_eq_true rfl))
  have e_v1256 : (v1256 = 1 ↔ v816 = 1 ∧ v848 = 1) := e_land h_v816 h_v848 (of_decide_eq_true rfl)
  have h_v1257 : R 1 0 0 1 v1257 v1257 := (r_lor hl h_v847 h_v1256 (of_decide_eq_true rfl))
  have e_v1257 : (v1257 = 1 ↔ v847 = 1 ∨ v1256 = 1) := e_lor h_v847 h_v1256 (of_decide_eq_true rfl)
  have h_v1258 : R 1 0 4611686018158952386 4611686018695823360 v1258 v1258 := (r_psel hl h_v1257 h_v808 h_v804 (of_decide_eq_true rfl))
  have e_v1258 : v1258 = if v1257 = 1 then v808 else v804 := e_psel h_v1257 h_v808 h_v804 (of_decide_eq_true rfl)
  have h_v1259 : R 1 0 0 1 v1259 v1259 := (r_land hl h_v820 h_v844 (of_decide_eq_true rfl))
  have e_v1259 : (v1259 = 1 ↔ v820 = 1 ∧ v844 = 1) := e_land h_v820 h_v844 (of_decide_eq_true rfl)
  have h_v1260 : R 1 0 0 1 v1260 v1260 := (r_lor hl h_v819 h_v1259 (of_decide_eq_true rfl))
  have e_v1260 : (v1260 = 1 ↔ v819 = 1 ∨ v1259 = 1) := e_lor h_v819 h_v1259 (of_decide_eq_true rfl)
  have h_v1261 : R 1 0 4611686018158952386 4611686018695823360 v1261 v1261 := (r_psel hl h_v1260 h_v798 h_v794 (of_decide_eq_true rfl))
  have e_v1261 : v1261 = if v1260 = 1 then v798 else v794 := e_psel h_v1260 h_v798 h_v794 (of_decide_eq_true rfl)
  have h_v1262 : R 1 0 0 1 v1262 v1262 := (r_land hl h_v819 h_v848 (of_decide_eq_true rfl))
  have e_v1262 : (v1262 = 1 ↔ v819 = 1 ∧ v848 = 1) := e_land h_v819 h_v848 (of_decide_eq_true rfl)
  have h_v1263 : R 1 0 0 1 v1263 v1263 := (r_lor hl h_v847 h_v1262 (of_decide_eq_true rfl))
  have e_v1263 : (v1263 = 1 ↔ v847 = 1 ∨ v1262 = 1) := e_lor h_v847 h_v1262 (of_decide_eq_true rfl)
  clear h_v1249 h_v1253 h_v1254 h_v1256 h_v1257 h_v1259 h_v1260 h_v1262
  have h_v1264 : R 1 0 4611686018158952386 4611686018695823360 v1264 v1264 := (r_psel hl h_v1263 h_v804 h_v808 (of_decide_eq_true rfl))
  have e_v1264 : v1264 = if v1263 = 1 then v804 else v808 := e_psel h_v1263 h_v804 h_v808 (of_decide_eq_true rfl)
  have h_v1265 : R 1 0 0 1 v1265 v1265 := (r_land hl h_v820 h_v847 (of_decide_eq_true rfl))
  have e_v1265 : (v1265 = 1 ↔ v820 = 1 ∧ v847 = 1) := e_land h_v820 h_v847 (of_decide_eq_true rfl)
  have h_v1266 : R 1 0 0 1 v1266 v1266 := (r_lor hl h_v819 h_v1265 (of_decide_eq_true rfl))
  have e_v1266 : (v1266 = 1 ↔ v819 = 1 ∨ v1265 = 1) := e_lor h_v819 h_v1265 (of_decide_eq_true rfl)
  have h_v1267 : R 1 0 4611686018158952386 4611686018695823360 v1267 v1267 := (r_psel hl h_v1266 h_v794 h_v798 (of_decide_eq_true rfl))
  have e_v1267 : v1267 = if v1266 = 1 then v794 else v798 := e_psel h_v1266 h_v794 h_v798 (of_decide_eq_true rfl)
  have h_v1268 : R 1 0 4539628407746461696 4683743645751316228 v1268 v1268 := (r_smx hl 30 h_v1261 h_v1258 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1268 : sv v1268 = sv v1261 * sv v1258 := e_smx 30 h_v1261 h_v1258 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1269 : R 1 0 4611686018158952386 4611686018695823484 v1269 v1269 := (r_srdF hl h_v1268 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v1269 : sv v1269 = sv v1268 / 2 ^ 28 := e_srdF h_v1268 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v1270 : R 1 0 4539628407746461696 4683743645751316228 v1270 v1270 := (r_smx hl 30 h_v1267 h_v1264 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1270 : sv v1270 = sv v1267 * sv v1264 := e_smx 30 h_v1267 h_v1264 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1271 : R 1 0 4611686018158952386 4611686018695823485 v1271 v1271 := (r_srdC hl h_v1270 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v1271 : sv v1271 = -((-sv v1270) / 2 ^ 28) := e_srdC h_v1270 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v1272 : R 1 0 4611686017890516805 4611686018964258878 v1272 v1272 := (r_sub hl (r_add hl h_v784 h_OFFr (of_decide_eq_true rfl)) h_v1271 (of_decide_eq_true rfl))
  have e_v1272 : sv v1272 = sv v784 - sv v1271 := e_sub h_v784 h_v1271 (of_decide_eq_true rfl)
  have h_v1273 : R 1 0 4611686017890516812 4611686018964258878 v1273 v1273 := (r_sub hl (r_add hl h_v788 h_OFFr (of_decide_eq_true rfl)) h_v1269 (of_decide_eq_true rfl))
  have e_v1273 : sv v1273 = sv v788 - sv v1269 := e_sub h_v788 h_v1269 (of_decide_eq_true rfl)
  have h_v1274 : R 1 0 0 1 v1274 v1274 := (r_plt hl h_v61 h_v1272 (of_decide_eq_true rfl))
  have e_v1274 : (v1274 = 1 ↔ sv v61 < sv v1272) := e_plt h_v61 h_v1272 (of_decide_eq_true rfl)
  have h_v1275 : R 1 0 0 1 v1275 v1275 := (r_plt hl h_v1273 h_v61 (of_decide_eq_true rfl))
  have e_v1275 : (v1275 = 1 ↔ sv v1273 < sv v61) := e_plt h_v1273 h_v61 (of_decide_eq_true rfl)
  have h_v1276 : R 1 0 4611686018427387899 4611686018695823375 v1276 v1276 := (r_psel hl h_v870 h_v440 h_v438 (of_decide_eq_true rfl))
  clear h_v1258 h_v1261 h_v1263 h_v1264 h_v1265 h_v1266 h_v1267 h_v1268 h_v1269 h_v1270 h_v1271 h_v1272 h_v1273
  have e_v1276 : v1276 = if v870 = 1 then v440 else v438 := e_psel h_v870 h_v440 h_v438 (of_decide_eq_true rfl)
  have h_v1277 : R 1 0 4611686018427387899 4611686018695823375 v1277 v1277 := (r_psel hl h_v871 h_v438 h_v440 (of_decide_eq_true rfl))
  have e_v1277 : v1277 = if v871 = 1 then v438 else v440 := e_psel h_v871 h_v438 h_v440 (of_decide_eq_true rfl)
  have h_v1278 : R 1 0 4611686018427387899 4611686018695823375 v1278 v1278 := (r_psel hl h_v871 h_v440 h_v438 (of_decide_eq_true rfl))
  have e_v1278 : v1278 = if v871 = 1 then v440 else v438 := e_psel h_v871 h_v440 h_v438 (of_decide_eq_true rfl)
  have h_v1279 : R 1 0 4611686018427387899 4611686018695823375 v1279 v1279 := (r_psel hl h_v870 h_v438 h_v440 (of_decide_eq_true rfl))
  have e_v1279 : v1279 = if v870 = 1 then v438 else v440 := e_psel h_v870 h_v438 h_v440 (of_decide_eq_true rfl)
  have h_v1280 : R 1 0 4611686018427387899 4611686018695823375 v1280 v1280 := (r_psel hl h_v1274 h_v766 h_v764 (of_decide_eq_true rfl))
  have e_v1280 : v1280 = if v1274 = 1 then v766 else v764 := e_psel h_v1274 h_v766 h_v764 (of_decide_eq_true rfl)
  have h_v1281 : R 1 0 4611686018427387899 4611686018695823375 v1281 v1281 := (r_psel hl h_v1275 h_v764 h_v766 (of_decide_eq_true rfl))
  have e_v1281 : v1281 = if v1275 = 1 then v764 else v766 := e_psel h_v1275 h_v764 h_v766 (of_decide_eq_true rfl)
  have h_v1282 : R 1 0 4611686018427387899 4611686018695823375 v1282 v1282 := (r_psel hl h_v1275 h_v766 h_v764 (of_decide_eq_true rfl))
  have e_v1282 : v1282 = if v1275 = 1 then v766 else v764 := e_psel h_v1275 h_v766 h_v764 (of_decide_eq_true rfl)
  have h_v1283 : R 1 0 4611686018427387899 4611686018695823375 v1283 v1283 := (r_psel hl h_v1274 h_v764 h_v766 (of_decide_eq_true rfl))
  have e_v1283 : v1283 = if v1274 = 1 then v764 else v766 := e_psel h_v1274 h_v764 h_v766 (of_decide_eq_true rfl)
  have h_v1289 : R 1 0 4611686018427387904 4683743620518379745 v1289 v1289 := (r_smx_sq hl 29 h_v1277 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1289 : sv v1289 = sv v1277 * sv v1277 := e_smx_sq 29 h_v1277 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1290 : R 1 0 4611686018427387904 4611686018695823391 v1290 v1290 := (r_srdC hl h_v1289 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1290 : sv v1290 = -((-sv v1289) / 2 ^ 28) := e_srdC h_v1289 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1291 : R 1 0 4611686018427387904 4611686018964258878 v1291 v1291 := (r_sub hl (r_add hl h_v1290 h_v1290 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1291 : sv v1291 = sv v1290 + sv v1290 := e_add h_v1290 h_v1290 (of_decide_eq_true rfl)
  have h_v1292 : R 1 0 4611686018158952386 4611686018695823360 v1292 v1292 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1291 (of_decide_eq_true rfl))
  have e_v1292 : sv v1292 = sv v33 - sv v1291 := e_sub h_v33 h_v1291 (of_decide_eq_true rfl)
  have h_v1293 : R 1 0 0 1 v1293 v1293 := (r_plt hl h_v1292 h_v95 (of_decide_eq_true rfl))
  have e_v1293 : (v1293 = 1 ↔ sv v1292 < sv v95) := e_plt h_v1292 h_v95 (of_decide_eq_true rfl)
  clear h_v1274 h_v1275 h_v1290 h_v1291
  have h_v1294 : R 1 0 4611686018158952386 4611686018695823360 v1294 v1294 := (r_psel hl h_v1293 h_v95 h_v1292 (of_decide_eq_true rfl))
  have e_v1294 : v1294 = if v1293 = 1 then v95 else v1292 := e_psel h_v1293 h_v95 h_v1292 (of_decide_eq_true rfl)
  have h_v1295 : R 1 0 4611686018427387904 4683743620518379745 v1295 v1295 := (r_smx_sq hl 29 h_v1276 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1295 : sv v1295 = sv v1276 * sv v1276 := e_smx_sq 29 h_v1276 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1296 : R 1 0 4611686018427387904 4611686018695823390 v1296 v1296 := (r_srdF hl h_v1295 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1296 : sv v1296 = sv v1295 / 2 ^ 28 := e_srdF h_v1295 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1297 : R 1 0 4611686018427387904 4611686018964258876 v1297 v1297 := (r_sub hl (r_add hl h_v1296 h_v1296 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1297 : sv v1297 = sv v1296 + sv v1296 := e_add h_v1296 h_v1296 (of_decide_eq_true rfl)
  have h_v1298 : R 1 0 4611686018158952388 4611686018695823360 v1298 v1298 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1297 (of_decide_eq_true rfl))
  have e_v1298 : sv v1298 = sv v33 - sv v1297 := e_sub h_v33 h_v1297 (of_decide_eq_true rfl)
  have h_v1299 : R 1 0 4611686018427387904 4683743620518379745 v1299 v1299 := (r_smx_sq hl 29 h_v1281 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1299 : sv v1299 = sv v1281 * sv v1281 := e_smx_sq 29 h_v1281 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1300 : R 1 0 4611686018427387904 4611686018695823391 v1300 v1300 := (r_srdC hl h_v1299 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1300 : sv v1300 = -((-sv v1299) / 2 ^ 28) := e_srdC h_v1299 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1301 : R 1 0 4611686018427387904 4611686018964258878 v1301 v1301 := (r_sub hl (r_add hl h_v1300 h_v1300 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1301 : sv v1301 = sv v1300 + sv v1300 := e_add h_v1300 h_v1300 (of_decide_eq_true rfl)
  have h_v1302 : R 1 0 4611686018158952386 4611686018695823360 v1302 v1302 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1301 (of_decide_eq_true rfl))
  have e_v1302 : sv v1302 = sv v33 - sv v1301 := e_sub h_v33 h_v1301 (of_decide_eq_true rfl)
  have h_v1303 : R 1 0 0 1 v1303 v1303 := (r_plt hl h_v1302 h_v95 (of_decide_eq_true rfl))
  have e_v1303 : (v1303 = 1 ↔ sv v1302 < sv v95) := e_plt h_v1302 h_v95 (of_decide_eq_true rfl)
  have h_v1304 : R 1 0 4611686018158952386 4611686018695823360 v1304 v1304 := (r_psel hl h_v1303 h_v95 h_v1302 (of_decide_eq_true rfl))
  have e_v1304 : v1304 = if v1303 = 1 then v95 else v1302 := e_psel h_v1303 h_v95 h_v1302 (of_decide_eq_true rfl)
  have h_v1305 : R 1 0 4611686018427387904 4683743620518379745 v1305 v1305 := (r_smx_sq hl 29 h_v1280 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1305 : sv v1305 = sv v1280 * sv v1280 := e_smx_sq 29 h_v1280 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1306 : R 1 0 4611686018427387904 4611686018695823390 v1306 v1306 := (r_srdF hl h_v1305 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  clear h_v1292 h_v1293 h_v1296 h_v1297 h_v1300 h_v1301 h_v1302 h_v1303
  have e_v1306 : sv v1306 = sv v1305 / 2 ^ 28 := e_srdF h_v1305 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1307 : R 1 0 4611686018427387904 4611686018964258876 v1307 v1307 := (r_sub hl (r_add hl h_v1306 h_v1306 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1307 : sv v1307 = sv v1306 + sv v1306 := e_add h_v1306 h_v1306 (of_decide_eq_true rfl)
  have h_v1308 : R 1 0 4611686018158952388 4611686018695823360 v1308 v1308 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1307 (of_decide_eq_true rfl))
  have e_v1308 : sv v1308 = sv v33 - sv v1307 := e_sub h_v33 h_v1307 (of_decide_eq_true rfl)
  have h_v1309 : R 1 0 0 1 v1309 v1309 := (r_plt hl h_v1294 h_v61 (of_decide_eq_true rfl))
  have e_v1309 : (v1309 = 1 ↔ sv v1294 < sv v61) := e_plt h_v1294 h_v61 (of_decide_eq_true rfl)
  have h_v1310 : R 1 0 0 1 v1310 v1310 := (r_sub hl (r_O hl) h_v1309 (of_decide_eq_true rfl))
  have e_v1310 : (v1310 = 1 ↔ ¬v1309 = 1) := e_not h_v1309 (of_decide_eq_true rfl)
  have h_v1311 : R 1 0 0 1 v1311 v1311 := (r_plt hl h_v61 h_v1298 (of_decide_eq_true rfl))
  have e_v1311 : (v1311 = 1 ↔ sv v61 < sv v1298) := e_plt h_v61 h_v1298 (of_decide_eq_true rfl)
  have h_v1312 : R 1 0 0 1 v1312 v1312 := (r_sub hl (r_O hl) h_v1311 (of_decide_eq_true rfl))
  have e_v1312 : (v1312 = 1 ↔ ¬v1311 = 1) := e_not h_v1311 (of_decide_eq_true rfl)
  have h_v1313 : R 1 0 0 1 v1313 v1313 := (r_land hl h_v1309 h_v1312 (of_decide_eq_true rfl))
  have e_v1313 : (v1313 = 1 ↔ v1309 = 1 ∧ v1312 = 1) := e_land h_v1309 h_v1312 (of_decide_eq_true rfl)
  have h_v1314 : R 1 0 0 1 v1314 v1314 := (r_land hl h_v1309 h_v1311 (of_decide_eq_true rfl))
  have e_v1314 : (v1314 = 1 ↔ v1309 = 1 ∧ v1311 = 1) := e_land h_v1309 h_v1311 (of_decide_eq_true rfl)
  have h_v1315 : R 1 0 0 1 v1315 v1315 := (r_plt hl h_v1304 h_v61 (of_decide_eq_true rfl))
  have e_v1315 : (v1315 = 1 ↔ sv v1304 < sv v61) := e_plt h_v1304 h_v61 (of_decide_eq_true rfl)
  have h_v1316 : R 1 0 0 1 v1316 v1316 := (r_sub hl (r_O hl) h_v1315 (of_decide_eq_true rfl))
  have e_v1316 : (v1316 = 1 ↔ ¬v1315 = 1) := e_not h_v1315 (of_decide_eq_true rfl)
  have h_v1317 : R 1 0 0 1 v1317 v1317 := (r_plt hl h_v61 h_v1308 (of_decide_eq_true rfl))
  have e_v1317 : (v1317 = 1 ↔ sv v61 < sv v1308) := e_plt h_v61 h_v1308 (of_decide_eq_true rfl)
  have h_v1318 : R 1 0 0 1 v1318 v1318 := (r_sub hl (r_O hl) h_v1317 (of_decide_eq_true rfl))
  have e_v1318 : (v1318 = 1 ↔ ¬v1317 = 1) := e_not h_v1317 (of_decide_eq_true rfl)
  clear h_v1306 h_v1307 h_v1309 h_v1311 h_v1312
  have h_v1319 : R 1 0 0 1 v1319 v1319 := (r_land hl h_v1315 h_v1318 (of_decide_eq_true rfl))
  have e_v1319 : (v1319 = 1 ↔ v1315 = 1 ∧ v1318 = 1) := e_land h_v1315 h_v1318 (of_decide_eq_true rfl)
  have h_v1320 : R 1 0 0 1 v1320 v1320 := (r_land hl h_v1315 h_v1317 (of_decide_eq_true rfl))
  have e_v1320 : (v1320 = 1 ↔ v1315 = 1 ∧ v1317 = 1) := e_land h_v1315 h_v1317 (of_decide_eq_true rfl)
  have h_v1321 : R 1 0 0 1 v1321 v1321 := (r_land hl h_v1314 h_v1320 (of_decide_eq_true rfl))
  have e_v1321 : (v1321 = 1 ↔ v1314 = 1 ∧ v1320 = 1) := e_land h_v1314 h_v1320 (of_decide_eq_true rfl)
  have h_v1322 : R 1 0 0 1 v1322 v1322 := (r_sub hl (r_O hl) h_v1321 (of_decide_eq_true rfl))
  have e_v1322 : (v1322 = 1 ↔ ¬v1321 = 1) := e_not h_v1321 (of_decide_eq_true rfl)
  have h_v1323 : R 1 0 0 1 v1323 v1323 := (r_lor hl h_v823 h_v1322 (of_decide_eq_true rfl))
  have e_v1323 : (v1323 = 1 ↔ v823 = 1 ∨ v1322 = 1) := e_lor h_v823 h_v1322 (of_decide_eq_true rfl)
  have h_v1324 : R 1 0 0 1 v1324 v1324 := (r_land hl h_v1310 h_v1320 (of_decide_eq_true rfl))
  have e_v1324 : (v1324 = 1 ↔ v1310 = 1 ∧ v1320 = 1) := e_land h_v1310 h_v1320 (of_decide_eq_true rfl)
  have h_v1325 : R 1 0 0 1 v1325 v1325 := (r_lor hl h_v1319 h_v1324 (of_decide_eq_true rfl))
  have e_v1325 : (v1325 = 1 ↔ v1319 = 1 ∨ v1324 = 1) := e_lor h_v1319 h_v1324 (of_decide_eq_true rfl)
  have h_v1326 : R 1 0 4611686018158952386 4611686018695823360 v1326 v1326 := (r_psel hl h_v1325 h_v1298 h_v1294 (of_decide_eq_true rfl))
  have e_v1326 : v1326 = if v1325 = 1 then v1298 else v1294 := e_psel h_v1325 h_v1298 h_v1294 (of_decide_eq_true rfl)
  have h_v1327 : R 1 0 0 1 v1327 v1327 := (r_land hl h_v1314 h_v1316 (of_decide_eq_true rfl))
  have e_v1327 : (v1327 = 1 ↔ v1314 = 1 ∧ v1316 = 1) := e_land h_v1314 h_v1316 (of_decide_eq_true rfl)
  have h_v1328 : R 1 0 0 1 v1328 v1328 := (r_lor hl h_v1313 h_v1327 (of_decide_eq_true rfl))
  have e_v1328 : (v1328 = 1 ↔ v1313 = 1 ∨ v1327 = 1) := e_lor h_v1313 h_v1327 (of_decide_eq_true rfl)
  have h_v1329 : R 1 0 4611686018158952386 4611686018695823360 v1329 v1329 := (r_psel hl h_v1328 h_v1308 h_v1304 (of_decide_eq_true rfl))
  have e_v1329 : v1329 = if v1328 = 1 then v1308 else v1304 := e_psel h_v1328 h_v1308 h_v1304 (of_decide_eq_true rfl)
  have h_v1336 : R 1 0 4539628407746461696 4683743645751316228 v1336 v1336 := (r_smx hl 30 h_v1329 h_v1326 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1336 : sv v1336 = sv v1329 * sv v1326 := e_smx 30 h_v1329 h_v1326 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1337 : R 1 0 4611686018158952386 4611686018695823484 v1337 v1337 := (r_srdF hl h_v1336 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  clear h_v1294 h_v1298 h_v1304 h_v1308 h_v1310 h_v1313 h_v1314 h_v1315 h_v1316 h_v1317 h_v1318 h_v1319 h_v1320 h_v1321 h_v1322 h_v1324 h_v1325 h_v1326 h_v1327 h_v1328 h_v1329
  have e_v1337 : sv v1337 = sv v1336 / 2 ^ 28 := e_srdF h_v1336 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v1341 : R 1 0 4611686017890516812 4611686018964258878 v1341 v1341 := (r_sub hl (r_add hl h_v808 h_OFFr (of_decide_eq_true rfl)) h_v1337 (of_decide_eq_true rfl))
  have e_v1341 : sv v1341 = sv v808 - sv v1337 := e_sub h_v808 h_v1337 (of_decide_eq_true rfl)
  have h_v1342 : R 1 0 4611686010374323999 4683743612465315840 v1342 v1342 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1295 (of_decide_eq_true rfl))
  have e_v1342 : sv v1342 = sv v940 - sv v1295 := e_sub h_v940 h_v1295 (of_decide_eq_true rfl)
  have h_v1343 : R 1 0 4611686018427387904 4611686018695823360 v1343 v1343 := (r_psqrt hl h_v1342 (of_decide_eq_true rfl))
  have e_v1343 : sv v1343 = ((Nat.sqrt (v1342 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1342 (of_decide_eq_true rfl)
  have h_v1344 : R 1 0 4611686018427387905 4611686018695823361 v1344 v1344 := (r_sub hl (r_add hl h_v105 h_v1343 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1344 : sv v1344 = sv v105 + sv v1343 := e_add h_v105 h_v1343 (of_decide_eq_true rfl)
  have pb_v1343_v1276 : PB 1 v1343 v1276 36028797018963968 := pb_sqrt hl h_v1276 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1345 : R 1 0 4611686017085210624 4647714815446351872 v1345 v1345 := (r_smx_pb hl 29 h_v1343 h_v1276 pb_v1343_v1276 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1345 : sv v1345 = sv v1343 * sv v1276 := e_smx_pb 29 h_v1343 h_v1276 pb_v1343_v1276 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1346 : R 1 0 4611686018427387899 4611686018561605632 v1346 v1346 := (r_srdF hl h_v1345 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1346 : sv v1346 = sv v1345 / 2 ^ 28 := e_srdF h_v1345 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1347 : R 1 0 4611686018427387894 4611686018695823360 v1347 v1347 := (r_sub hl (r_add hl h_v1346 h_v1346 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1347 : sv v1347 = sv v1346 + sv v1346 := e_add h_v1346 h_v1346 (of_decide_eq_true rfl)
  have pb_v1344_v1276 : PB 1 v1344 v1276 36028797287399439 := pb_sqrt1 hl h_v1276 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1348 : R 1 0 4611686017085210619 4647714815714787343 v1348 v1348 := (r_smx_pb hl 29 h_v1344 h_v1276 pb_v1344_v1276 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1348 : sv v1348 = sv v1344 * sv v1276 := e_smx_pb 29 h_v1344 h_v1276 pb_v1344_v1276 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1349 : R 1 0 4611686018427387899 4611686018561605634 v1349 v1349 := (r_srdC hl h_v1348 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1349 : sv v1349 = -((-sv v1348) / 2 ^ 28) := e_srdC h_v1348 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1350 : R 1 0 4611686018427387894 4611686018695823364 v1350 v1350 := (r_sub hl (r_add hl h_v1349 h_v1349 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1350 : sv v1350 = sv v1349 + sv v1349 := e_add h_v1349 h_v1349 (of_decide_eq_true rfl)
  have h_v1351 : R 1 0 0 1 v1351 v1351 := (r_plt hl h_v1350 h_v33 (of_decide_eq_true rfl))
  have e_v1351 : (v1351 = 1 ↔ sv v1350 < sv v33) := e_plt h_v1350 h_v33 (of_decide_eq_true rfl)
  clear h_v1276 h_v1336 h_v1337 h_v1342 h_v1343 h_v1344 pb_v1343_v1276 h_v1345 h_v1346 pb_v1344_v1276 h_v1348 h_v1349
  have h_v1352 : R 1 0 4611686018427387894 4611686018695823364 v1352 v1352 := (r_psel hl h_v1351 h_v1350 h_v33 (of_decide_eq_true rfl))
  have e_v1352 : v1352 = if v1351 = 1 then v1350 else v33 := e_psel h_v1351 h_v1350 h_v33 (of_decide_eq_true rfl)
  have h_v1353 : R 1 0 4611686010374323999 4683743612465315840 v1353 v1353 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1289 (of_decide_eq_true rfl))
  have e_v1353 : sv v1353 = sv v940 - sv v1289 := e_sub h_v940 h_v1289 (of_decide_eq_true rfl)
  have h_v1354 : R 1 0 4611686018427387904 4611686018695823360 v1354 v1354 := (r_psqrt hl h_v1353 (of_decide_eq_true rfl))
  have e_v1354 : sv v1354 = ((Nat.sqrt (v1353 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1353 (of_decide_eq_true rfl)
  have h_v1355 : R 1 0 4611686018427387905 4611686018695823361 v1355 v1355 := (r_sub hl (r_add hl h_v105 h_v1354 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1355 : sv v1355 = sv v105 + sv v1354 := e_add h_v105 h_v1354 (of_decide_eq_true rfl)
  have pb_v1354_v1277 : PB 1 v1354 v1277 36028797018963968 := pb_sqrt hl h_v1277 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1356 : R 1 0 4611686017085210624 4647714815446351872 v1356 v1356 := (r_smx_pb hl 29 h_v1354 h_v1277 pb_v1354_v1277 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1356 : sv v1356 = sv v1354 * sv v1277 := e_smx_pb 29 h_v1354 h_v1277 pb_v1354_v1277 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1357 : R 1 0 4611686018427387899 4611686018561605632 v1357 v1357 := (r_srdF hl h_v1356 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1357 : sv v1357 = sv v1356 / 2 ^ 28 := e_srdF h_v1356 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1358 : R 1 0 4611686018427387894 4611686018695823360 v1358 v1358 := (r_sub hl (r_add hl h_v1357 h_v1357 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1358 : sv v1358 = sv v1357 + sv v1357 := e_add h_v1357 h_v1357 (of_decide_eq_true rfl)
  have pb_v1355_v1277 : PB 1 v1355 v1277 36028797287399439 := pb_sqrt1 hl h_v1277 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1359 : R 1 0 4611686017085210619 4647714815714787343 v1359 v1359 := (r_smx_pb hl 29 h_v1355 h_v1277 pb_v1355_v1277 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1359 : sv v1359 = sv v1355 * sv v1277 := e_smx_pb 29 h_v1355 h_v1277 pb_v1355_v1277 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1360 : R 1 0 4611686018427387899 4611686018561605634 v1360 v1360 := (r_srdC hl h_v1359 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1360 : sv v1360 = -((-sv v1359) / 2 ^ 28) := e_srdC h_v1359 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1361 : R 1 0 4611686018427387894 4611686018695823364 v1361 v1361 := (r_sub hl (r_add hl h_v1360 h_v1360 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1361 : sv v1361 = sv v1360 + sv v1360 := e_add h_v1360 h_v1360 (of_decide_eq_true rfl)
  have h_v1362 : R 1 0 0 1 v1362 v1362 := (r_plt hl h_v1361 h_v33 (of_decide_eq_true rfl))
  have e_v1362 : (v1362 = 1 ↔ sv v1361 < sv v33) := e_plt h_v1361 h_v33 (of_decide_eq_true rfl)
  have h_v1363 : R 1 0 4611686018427387894 4611686018695823364 v1363 v1363 := (r_psel hl h_v1362 h_v1361 h_v33 (of_decide_eq_true rfl))
  clear h_v1277 h_v1350 h_v1351 h_v1353 h_v1354 h_v1355 pb_v1354_v1277 h_v1356 h_v1357 pb_v1355_v1277 h_v1359 h_v1360
  have e_v1363 : v1363 = if v1362 = 1 then v1361 else v33 := e_psel h_v1362 h_v1361 h_v33 (of_decide_eq_true rfl)
  have h_v1364 : R 1 0 0 1 v1364 v1364 := (r_plt hl h_v1347 h_v1358 (of_decide_eq_true rfl))
  have e_v1364 : (v1364 = 1 ↔ sv v1347 < sv v1358) := e_plt h_v1347 h_v1358 (of_decide_eq_true rfl)
  have h_v1365 : R 1 0 4611686018427387894 4611686018695823360 v1365 v1365 := (r_psel hl h_v1364 h_v1347 h_v1358 (of_decide_eq_true rfl))
  have e_v1365 : v1365 = if v1364 = 1 then v1347 else v1358 := e_psel h_v1364 h_v1347 h_v1358 (of_decide_eq_true rfl)
  have h_v1366 : R 1 0 0 1 v1366 v1366 := (r_plt hl h_v1352 h_v1363 (of_decide_eq_true rfl))
  have e_v1366 : (v1366 = 1 ↔ sv v1352 < sv v1363) := e_plt h_v1352 h_v1363 (of_decide_eq_true rfl)
  have h_v1367 : R 1 0 4611686018427387894 4611686018695823364 v1367 v1367 := (r_psel hl h_v1366 h_v1363 h_v1352 (of_decide_eq_true rfl))
  have e_v1367 : v1367 = if v1366 = 1 then v1363 else v1352 := e_psel h_v1366 h_v1363 h_v1352 (of_decide_eq_true rfl)
  have h_v1368 : R 1 0 0 1 v1368 v1368 := (r_plt hl h_v967 h_v1295 (of_decide_eq_true rfl))
  have e_v1368 : (v1368 = 1 ↔ sv v967 < sv v1295) := e_plt h_v967 h_v1295 (of_decide_eq_true rfl)
  have h_v1369 : R 1 0 0 1 v1369 v1369 := (r_sub hl (r_O hl) h_v1368 (of_decide_eq_true rfl))
  have e_v1369 : (v1369 = 1 ↔ ¬v1368 = 1) := e_not h_v1368 (of_decide_eq_true rfl)
  have h_v1370 : R 1 0 0 1 v1370 v1370 := (r_plt hl h_v1289 h_v967 (of_decide_eq_true rfl))
  have e_v1370 : (v1370 = 1 ↔ sv v1289 < sv v967) := e_plt h_v1289 h_v967 (of_decide_eq_true rfl)
  have h_v1371 : R 1 0 0 1 v1371 v1371 := (r_sub hl (r_O hl) h_v1370 (of_decide_eq_true rfl))
  have e_v1371 : (v1371 = 1 ↔ ¬v1370 = 1) := e_not h_v1370 (of_decide_eq_true rfl)
  have h_v1372 : R 1 0 0 1 v1372 v1372 := (r_land hl h_v1369 h_v1371 (of_decide_eq_true rfl))
  have e_v1372 : (v1372 = 1 ↔ v1369 = 1 ∧ v1371 = 1) := e_land h_v1369 h_v1371 (of_decide_eq_true rfl)
  have h_v1373 : R 1 0 4611686018427387894 4611686018695823364 v1373 v1373 := (r_psel hl h_v1372 h_v33 h_v1367 (of_decide_eq_true rfl))
  have e_v1373 : v1373 = if v1372 = 1 then v33 else v1367 := e_psel h_v1372 h_v33 h_v1367 (of_decide_eq_true rfl)
  have h_v1374 : R 1 0 4611686010374323999 4683743612465315840 v1374 v1374 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1305 (of_decide_eq_true rfl))
  have e_v1374 : sv v1374 = sv v940 - sv v1305 := e_sub h_v940 h_v1305 (of_decide_eq_true rfl)
  have h_v1375 : R 1 0 4611686018427387904 4611686018695823360 v1375 v1375 := (r_psqrt hl h_v1374 (of_decide_eq_true rfl))
  have e_v1375 : sv v1375 = ((Nat.sqrt (v1374 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1374 (of_decide_eq_true rfl)
  clear h_v1289 h_v1295 h_v1347 h_v1352 h_v1358 h_v1361 h_v1362 h_v1363 h_v1364 h_v1366 h_v1367 h_v1368 h_v1369 h_v1370 h_v1371 h_v1372 h_v1374
  have h_v1376 : R 1 0 4611686018427387905 4611686018695823361 v1376 v1376 := (r_sub hl (r_add hl h_v105 h_v1375 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1376 : sv v1376 = sv v105 + sv v1375 := e_add h_v105 h_v1375 (of_decide_eq_true rfl)
  have pb_v1375_v1280 : PB 1 v1375 v1280 36028797018963968 := pb_sqrt hl h_v1280 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1377 : R 1 0 4611686017085210624 4647714815446351872 v1377 v1377 := (r_smx_pb hl 29 h_v1375 h_v1280 pb_v1375_v1280 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1377 : sv v1377 = sv v1375 * sv v1280 := e_smx_pb 29 h_v1375 h_v1280 pb_v1375_v1280 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1378 : R 1 0 4611686018427387899 4611686018561605632 v1378 v1378 := (r_srdF hl h_v1377 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1378 : sv v1378 = sv v1377 / 2 ^ 28 := e_srdF h_v1377 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1379 : R 1 0 4611686018427387894 4611686018695823360 v1379 v1379 := (r_sub hl (r_add hl h_v1378 h_v1378 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1379 : sv v1379 = sv v1378 + sv v1378 := e_add h_v1378 h_v1378 (of_decide_eq_true rfl)
  have pb_v1376_v1280 : PB 1 v1376 v1280 36028797287399439 := pb_sqrt1 hl h_v1280 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1380 : R 1 0 4611686017085210619 4647714815714787343 v1380 v1380 := (r_smx_pb hl 29 h_v1376 h_v1280 pb_v1376_v1280 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1380 : sv v1380 = sv v1376 * sv v1280 := e_smx_pb 29 h_v1376 h_v1280 pb_v1376_v1280 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1381 : R 1 0 4611686018427387899 4611686018561605634 v1381 v1381 := (r_srdC hl h_v1380 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1381 : sv v1381 = -((-sv v1380) / 2 ^ 28) := e_srdC h_v1380 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1382 : R 1 0 4611686018427387894 4611686018695823364 v1382 v1382 := (r_sub hl (r_add hl h_v1381 h_v1381 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1382 : sv v1382 = sv v1381 + sv v1381 := e_add h_v1381 h_v1381 (of_decide_eq_true rfl)
  have h_v1383 : R 1 0 0 1 v1383 v1383 := (r_plt hl h_v1382 h_v33 (of_decide_eq_true rfl))
  have e_v1383 : (v1383 = 1 ↔ sv v1382 < sv v33) := e_plt h_v1382 h_v33 (of_decide_eq_true rfl)
  have h_v1384 : R 1 0 4611686018427387894 4611686018695823364 v1384 v1384 := (r_psel hl h_v1383 h_v1382 h_v33 (of_decide_eq_true rfl))
  have e_v1384 : v1384 = if v1383 = 1 then v1382 else v33 := e_psel h_v1383 h_v1382 h_v33 (of_decide_eq_true rfl)
  have h_v1385 : R 1 0 4611686010374323999 4683743612465315840 v1385 v1385 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1299 (of_decide_eq_true rfl))
  have e_v1385 : sv v1385 = sv v940 - sv v1299 := e_sub h_v940 h_v1299 (of_decide_eq_true rfl)
  have h_v1386 : R 1 0 4611686018427387904 4611686018695823360 v1386 v1386 := (r_psqrt hl h_v1385 (of_decide_eq_true rfl))
  have e_v1386 : sv v1386 = ((Nat.sqrt (v1385 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1385 (of_decide_eq_true rfl)
  have h_v1387 : R 1 0 4611686018427387905 4611686018695823361 v1387 v1387 := (r_sub hl (r_add hl h_v105 h_v1386 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v1280 h_v1375 h_v1376 pb_v1375_v1280 h_v1377 h_v1378 pb_v1376_v1280 h_v1380 h_v1381 h_v1382 h_v1383 h_v1385
  have e_v1387 : sv v1387 = sv v105 + sv v1386 := e_add h_v105 h_v1386 (of_decide_eq_true rfl)
  have pb_v1386_v1281 : PB 1 v1386 v1281 36028797018963968 := pb_sqrt hl h_v1281 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1388 : R 1 0 4611686017085210624 4647714815446351872 v1388 v1388 := (r_smx_pb hl 29 h_v1386 h_v1281 pb_v1386_v1281 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1388 : sv v1388 = sv v1386 * sv v1281 := e_smx_pb 29 h_v1386 h_v1281 pb_v1386_v1281 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1389 : R 1 0 4611686018427387899 4611686018561605632 v1389 v1389 := (r_srdF hl h_v1388 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1389 : sv v1389 = sv v1388 / 2 ^ 28 := e_srdF h_v1388 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1390 : R 1 0 4611686018427387894 4611686018695823360 v1390 v1390 := (r_sub hl (r_add hl h_v1389 h_v1389 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1390 : sv v1390 = sv v1389 + sv v1389 := e_add h_v1389 h_v1389 (of_decide_eq_true rfl)
  have pb_v1387_v1281 : PB 1 v1387 v1281 36028797287399439 := pb_sqrt1 hl h_v1281 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1391 : R 1 0 4611686017085210619 4647714815714787343 v1391 v1391 := (r_smx_pb hl 29 h_v1387 h_v1281 pb_v1387_v1281 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1391 : sv v1391 = sv v1387 * sv v1281 := e_smx_pb 29 h_v1387 h_v1281 pb_v1387_v1281 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1392 : R 1 0 4611686018427387899 4611686018561605634 v1392 v1392 := (r_srdC hl h_v1391 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1392 : sv v1392 = -((-sv v1391) / 2 ^ 28) := e_srdC h_v1391 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1393 : R 1 0 4611686018427387894 4611686018695823364 v1393 v1393 := (r_sub hl (r_add hl h_v1392 h_v1392 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1393 : sv v1393 = sv v1392 + sv v1392 := e_add h_v1392 h_v1392 (of_decide_eq_true rfl)
  have h_v1394 : R 1 0 0 1 v1394 v1394 := (r_plt hl h_v1393 h_v33 (of_decide_eq_true rfl))
  have e_v1394 : (v1394 = 1 ↔ sv v1393 < sv v33) := e_plt h_v1393 h_v33 (of_decide_eq_true rfl)
  have h_v1395 : R 1 0 4611686018427387894 4611686018695823364 v1395 v1395 := (r_psel hl h_v1394 h_v1393 h_v33 (of_decide_eq_true rfl))
  have e_v1395 : v1395 = if v1394 = 1 then v1393 else v33 := e_psel h_v1394 h_v1393 h_v33 (of_decide_eq_true rfl)
  have h_v1396 : R 1 0 0 1 v1396 v1396 := (r_plt hl h_v1379 h_v1390 (of_decide_eq_true rfl))
  have e_v1396 : (v1396 = 1 ↔ sv v1379 < sv v1390) := e_plt h_v1379 h_v1390 (of_decide_eq_true rfl)
  have h_v1397 : R 1 0 4611686018427387894 4611686018695823360 v1397 v1397 := (r_psel hl h_v1396 h_v1379 h_v1390 (of_decide_eq_true rfl))
  have e_v1397 : v1397 = if v1396 = 1 then v1379 else v1390 := e_psel h_v1396 h_v1379 h_v1390 (of_decide_eq_true rfl)
  have h_v1398 : R 1 0 0 1 v1398 v1398 := (r_plt hl h_v1384 h_v1395 (of_decide_eq_true rfl))
  have e_v1398 : (v1398 = 1 ↔ sv v1384 < sv v1395) := e_plt h_v1384 h_v1395 (of_decide_eq_true rfl)
  clear h_v1281 h_v1379 h_v1386 h_v1387 pb_v1386_v1281 h_v1388 h_v1389 h_v1390 pb_v1387_v1281 h_v1391 h_v1392 h_v1393 h_v1394 h_v1396
  have h_v1399 : R 1 0 4611686018427387894 4611686018695823364 v1399 v1399 := (r_psel hl h_v1398 h_v1395 h_v1384 (of_decide_eq_true rfl))
  have e_v1399 : v1399 = if v1398 = 1 then v1395 else v1384 := e_psel h_v1398 h_v1395 h_v1384 (of_decide_eq_true rfl)
  have h_v1400 : R 1 0 0 1 v1400 v1400 := (r_plt hl h_v967 h_v1305 (of_decide_eq_true rfl))
  have e_v1400 : (v1400 = 1 ↔ sv v967 < sv v1305) := e_plt h_v967 h_v1305 (of_decide_eq_true rfl)
  have h_v1401 : R 1 0 0 1 v1401 v1401 := (r_sub hl (r_O hl) h_v1400 (of_decide_eq_true rfl))
  have e_v1401 : (v1401 = 1 ↔ ¬v1400 = 1) := e_not h_v1400 (of_decide_eq_true rfl)
  have h_v1402 : R 1 0 0 1 v1402 v1402 := (r_plt hl h_v1299 h_v967 (of_decide_eq_true rfl))
  have e_v1402 : (v1402 = 1 ↔ sv v1299 < sv v967) := e_plt h_v1299 h_v967 (of_decide_eq_true rfl)
  have h_v1403 : R 1 0 0 1 v1403 v1403 := (r_sub hl (r_O hl) h_v1402 (of_decide_eq_true rfl))
  have e_v1403 : (v1403 = 1 ↔ ¬v1402 = 1) := e_not h_v1402 (of_decide_eq_true rfl)
  have h_v1404 : R 1 0 0 1 v1404 v1404 := (r_land hl h_v1401 h_v1403 (of_decide_eq_true rfl))
  have e_v1404 : (v1404 = 1 ↔ v1401 = 1 ∧ v1403 = 1) := e_land h_v1401 h_v1403 (of_decide_eq_true rfl)
  have h_v1405 : R 1 0 4611686018427387894 4611686018695823364 v1405 v1405 := (r_psel hl h_v1404 h_v33 h_v1399 (of_decide_eq_true rfl))
  have e_v1405 : v1405 = if v1404 = 1 then v33 else v1399 := e_psel h_v1404 h_v33 h_v1399 (of_decide_eq_true rfl)
  have h_v1406 : R 1 0 0 1 v1406 v1406 := (r_plt hl h_v1365 h_v61 (of_decide_eq_true rfl))
  have e_v1406 : (v1406 = 1 ↔ sv v1365 < sv v61) := e_plt h_v1365 h_v61 (of_decide_eq_true rfl)
  have h_v1407 : R 1 0 0 1 v1407 v1407 := (r_sub hl (r_O hl) h_v1406 (of_decide_eq_true rfl))
  have e_v1407 : (v1407 = 1 ↔ ¬v1406 = 1) := e_not h_v1406 (of_decide_eq_true rfl)
  have h_v1408 : R 1 0 0 1 v1408 v1408 := (r_plt hl h_v61 h_v1373 (of_decide_eq_true rfl))
  have e_v1408 : (v1408 = 1 ↔ sv v61 < sv v1373) := e_plt h_v61 h_v1373 (of_decide_eq_true rfl)
  have h_v1409 : R 1 0 0 1 v1409 v1409 := (r_sub hl (r_O hl) h_v1408 (of_decide_eq_true rfl))
  have e_v1409 : (v1409 = 1 ↔ ¬v1408 = 1) := e_not h_v1408 (of_decide_eq_true rfl)
  have h_v1410 : R 1 0 0 1 v1410 v1410 := (r_land hl h_v1406 h_v1409 (of_decide_eq_true rfl))
  have e_v1410 : (v1410 = 1 ↔ v1406 = 1 ∧ v1409 = 1) := e_land h_v1406 h_v1409 (of_decide_eq_true rfl)
  have h_v1411 : R 1 0 0 1 v1411 v1411 := (r_land hl h_v1406 h_v1408 (of_decide_eq_true rfl))
  clear h_v1299 h_v1305 h_v1384 h_v1395 h_v1398 h_v1399 h_v1400 h_v1401 h_v1402 h_v1403 h_v1404 h_v1409
  have e_v1411 : (v1411 = 1 ↔ v1406 = 1 ∧ v1408 = 1) := e_land h_v1406 h_v1408 (of_decide_eq_true rfl)
  have h_v1412 : R 1 0 0 1 v1412 v1412 := (r_plt hl h_v1397 h_v61 (of_decide_eq_true rfl))
  have e_v1412 : (v1412 = 1 ↔ sv v1397 < sv v61) := e_plt h_v1397 h_v61 (of_decide_eq_true rfl)
  have h_v1413 : R 1 0 0 1 v1413 v1413 := (r_sub hl (r_O hl) h_v1412 (of_decide_eq_true rfl))
  have e_v1413 : (v1413 = 1 ↔ ¬v1412 = 1) := e_not h_v1412 (of_decide_eq_true rfl)
  have h_v1414 : R 1 0 0 1 v1414 v1414 := (r_plt hl h_v61 h_v1405 (of_decide_eq_true rfl))
  have e_v1414 : (v1414 = 1 ↔ sv v61 < sv v1405) := e_plt h_v61 h_v1405 (of_decide_eq_true rfl)
  have h_v1415 : R 1 0 0 1 v1415 v1415 := (r_sub hl (r_O hl) h_v1414 (of_decide_eq_true rfl))
  have e_v1415 : (v1415 = 1 ↔ ¬v1414 = 1) := e_not h_v1414 (of_decide_eq_true rfl)
  have h_v1416 : R 1 0 0 1 v1416 v1416 := (r_land hl h_v1412 h_v1415 (of_decide_eq_true rfl))
  have e_v1416 : (v1416 = 1 ↔ v1412 = 1 ∧ v1415 = 1) := e_land h_v1412 h_v1415 (of_decide_eq_true rfl)
  have h_v1417 : R 1 0 0 1 v1417 v1417 := (r_land hl h_v1412 h_v1414 (of_decide_eq_true rfl))
  have e_v1417 : (v1417 = 1 ↔ v1412 = 1 ∧ v1414 = 1) := e_land h_v1412 h_v1414 (of_decide_eq_true rfl)
  have h_v1418 : R 1 0 0 1 v1418 v1418 := (r_land hl h_v1411 h_v1417 (of_decide_eq_true rfl))
  have e_v1418 : (v1418 = 1 ↔ v1411 = 1 ∧ v1417 = 1) := e_land h_v1411 h_v1417 (of_decide_eq_true rfl)
  have h_v1419 : R 1 0 0 1 v1419 v1419 := (r_sub hl (r_O hl) h_v1418 (of_decide_eq_true rfl))
  have e_v1419 : (v1419 = 1 ↔ ¬v1418 = 1) := e_not h_v1418 (of_decide_eq_true rfl)
  have h_v1420 : R 1 0 0 1 v1420 v1420 := (r_lor hl h_v823 h_v1419 (of_decide_eq_true rfl))
  have e_v1420 : (v1420 = 1 ↔ v823 = 1 ∨ v1419 = 1) := e_lor h_v823 h_v1419 (of_decide_eq_true rfl)
  have h_v1421 : R 1 0 0 1 v1421 v1421 := (r_land hl h_v1407 h_v1417 (of_decide_eq_true rfl))
  have e_v1421 : (v1421 = 1 ↔ v1407 = 1 ∧ v1417 = 1) := e_land h_v1407 h_v1417 (of_decide_eq_true rfl)
  have h_v1422 : R 1 0 0 1 v1422 v1422 := (r_lor hl h_v1416 h_v1421 (of_decide_eq_true rfl))
  have e_v1422 : (v1422 = 1 ↔ v1416 = 1 ∨ v1421 = 1) := e_lor h_v1416 h_v1421 (of_decide_eq_true rfl)
  have h_v1423 : R 1 0 4611686018427387894 4611686018695823364 v1423 v1423 := (r_psel hl h_v1422 h_v1373 h_v1365 (of_decide_eq_true rfl))
  have e_v1423 : v1423 = if v1422 = 1 then v1373 else v1365 := e_psel h_v1422 h_v1373 h_v1365 (of_decide_eq_true rfl)
  clear h_v1406 h_v1407 h_v1408 h_v1412 h_v1414 h_v1415 h_v1418 h_v1419 h_v1421 h_v1422
  have h_v1424 : R 1 0 0 1 v1424 v1424 := (r_land hl h_v1411 h_v1413 (of_decide_eq_true rfl))
  have e_v1424 : (v1424 = 1 ↔ v1411 = 1 ∧ v1413 = 1) := e_land h_v1411 h_v1413 (of_decide_eq_true rfl)
  have h_v1425 : R 1 0 0 1 v1425 v1425 := (r_lor hl h_v1410 h_v1424 (of_decide_eq_true rfl))
  have e_v1425 : (v1425 = 1 ↔ v1410 = 1 ∨ v1424 = 1) := e_lor h_v1410 h_v1424 (of_decide_eq_true rfl)
  have h_v1426 : R 1 0 4611686018427387894 4611686018695823364 v1426 v1426 := (r_psel hl h_v1425 h_v1405 h_v1397 (of_decide_eq_true rfl))
  have e_v1426 : v1426 = if v1425 = 1 then v1405 else v1397 := e_psel h_v1425 h_v1405 h_v1397 (of_decide_eq_true rfl)
  have h_v1427 : R 1 0 0 1 v1427 v1427 := (r_land hl h_v1410 h_v1417 (of_decide_eq_true rfl))
  have e_v1427 : (v1427 = 1 ↔ v1410 = 1 ∧ v1417 = 1) := e_land h_v1410 h_v1417 (of_decide_eq_true rfl)
  have h_v1428 : R 1 0 0 1 v1428 v1428 := (r_lor hl h_v1416 h_v1427 (of_decide_eq_true rfl))
  have e_v1428 : (v1428 = 1 ↔ v1416 = 1 ∨ v1427 = 1) := e_lor h_v1416 h_v1427 (of_decide_eq_true rfl)
  have h_v1429 : R 1 0 4611686018427387894 4611686018695823364 v1429 v1429 := (r_psel hl h_v1428 h_v1365 h_v1373 (of_decide_eq_true rfl))
  have e_v1429 : v1429 = if v1428 = 1 then v1365 else v1373 := e_psel h_v1428 h_v1365 h_v1373 (of_decide_eq_true rfl)
  have h_v1430 : R 1 0 0 1 v1430 v1430 := (r_land hl h_v1411 h_v1416 (of_decide_eq_true rfl))
  have e_v1430 : (v1430 = 1 ↔ v1411 = 1 ∧ v1416 = 1) := e_land h_v1411 h_v1416 (of_decide_eq_true rfl)
  have h_v1431 : R 1 0 0 1 v1431 v1431 := (r_lor hl h_v1410 h_v1430 (of_decide_eq_true rfl))
  have e_v1431 : (v1431 = 1 ↔ v1410 = 1 ∨ v1430 = 1) := e_lor h_v1410 h_v1430 (of_decide_eq_true rfl)
  have h_v1432 : R 1 0 4611686018427387894 4611686018695823364 v1432 v1432 := (r_psel hl h_v1431 h_v1397 h_v1405 (of_decide_eq_true rfl))
  have e_v1432 : v1432 = if v1431 = 1 then v1397 else v1405 := e_psel h_v1431 h_v1397 h_v1405 (of_decide_eq_true rfl)
  have h_v1433 : R 1 0 4611686015743033304 4683743614612799504 v1433 v1433 := (r_smx hl 29 h_v1426 h_v1423 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1433 : sv v1433 = sv v1426 * sv v1423 := e_smx 29 h_v1426 h_v1423 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1434 : R 1 0 4611686018427387893 4611686018695823368 v1434 v1434 := (r_srdF hl h_v1433 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v1434 : sv v1434 = sv v1433 / 2 ^ 28 := e_srdF h_v1433 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1435 : R 1 0 4611686015743033304 4683743614612799504 v1435 v1435 := (r_smx hl 29 h_v1432 h_v1429 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1435 : sv v1435 = sv v1432 * sv v1429 := e_smx 29 h_v1432 h_v1429 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1436 : R 1 0 4611686018427387894 4611686018695823369 v1436 v1436 := (r_srdC hl h_v1435 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  clear h_v1365 h_v1373 h_v1397 h_v1405 h_v1410 h_v1411 h_v1413 h_v1416 h_v1417 h_v1423 h_v1424 h_v1425 h_v1426 h_v1427 h_v1428 h_v1429 h_v1430 h_v1431 h_v1432 h_v1433
  have e_v1436 : sv v1436 = -((-sv v1435) / 2 ^ 28) := e_srdC h_v1435 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1437 : R 1 0 0 1 v1437 v1437 := (r_plt hl h_v61 h_v1434 (of_decide_eq_true rfl))
  have e_v1437 : (v1437 = 1 ↔ sv v61 < sv v1434) := e_plt h_v61 h_v1434 (of_decide_eq_true rfl)
  have h_v1438 : R 1 0 0 1 v1438 v1438 := (r_sub hl (r_O hl) h_v1437 (of_decide_eq_true rfl))
  have e_v1438 : (v1438 = 1 ↔ ¬v1437 = 1) := e_not h_v1437 (of_decide_eq_true rfl)
  have h_v1441 : R 1 0 0 1 v1441 v1441 := (r_plt hl h_v1341 h_v61 (of_decide_eq_true rfl))
  have e_v1441 : (v1441 = 1 ↔ sv v1341 < sv v61) := e_plt h_v1341 h_v61 (of_decide_eq_true rfl)
  have h_v1442 : R 1 0 4611686018427387893 4611686018695823369 v1442 v1442 := (r_psel hl h_v1441 h_v1436 h_v1434 (of_decide_eq_true rfl))
  have e_v1442 : v1442 = if v1441 = 1 then v1436 else v1434 := e_psel h_v1441 h_v1436 h_v1434 (of_decide_eq_true rfl)
  have h_v1443 : R 1 0 4611686018158952439 4611686018427387915 v1443 v1443 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v1442 (of_decide_eq_true rfl))
  have e_v1443 : sv v1443 = sv v61 - sv v1442 := e_sub h_v61 h_v1442 (of_decide_eq_true rfl)
  have h_v1444 : R 1 0 0 1 v1444 v1444 := (r_plt hl h_v1341 h_v1443 (of_decide_eq_true rfl))
  have e_v1444 : (v1444 = 1 ↔ sv v1341 < sv v1443) := e_plt h_v1341 h_v1443 (of_decide_eq_true rfl)
  have h_v1445 : R 1 0 0 1 v1445 v1445 := (r_land hl h_v1437 h_v1444 (of_decide_eq_true rfl))
  have e_v1445 : (v1445 = 1 ↔ v1437 = 1 ∧ v1444 = 1) := e_land h_v1437 h_v1444 (of_decide_eq_true rfl)
  have h_v1446 : R 1 0 0 1 v1446 v1446 := (r_plt hl h_v1341 h_v1442 (of_decide_eq_true rfl))
  have e_v1446 : (v1446 = 1 ↔ sv v1341 < sv v1442) := e_plt h_v1341 h_v1442 (of_decide_eq_true rfl)
  have h_v1447 : R 1 0 0 1 v1447 v1447 := (r_sub hl (r_O hl) h_v1446 (of_decide_eq_true rfl))
  have e_v1447 : (v1447 = 1 ↔ ¬v1446 = 1) := e_not h_v1446 (of_decide_eq_true rfl)
  have h_v1448 : R 1 0 0 1 v1448 v1448 := (r_lor hl h_v1438 h_v1447 (of_decide_eq_true rfl))
  have e_v1448 : (v1448 = 1 ↔ v1438 = 1 ∨ v1447 = 1) := e_lor h_v1438 h_v1447 (of_decide_eq_true rfl)
  have h_v1449 : R 1 0 4611686017890516812 4611686018964258878 v1449 v1449 := (r_psel hl h_v1448 h_v33 h_v1341 (of_decide_eq_true rfl))
  have e_v1449 : v1449 = if v1448 = 1 then v33 else v1341 := e_psel h_v1448 h_v33 h_v1341 (of_decide_eq_true rfl)
  have h_v1450 : R 1 0 4611686018427387893 4611686018695823369 v1450 v1450 := (r_psel hl h_v1448 h_v33 h_v1442 (of_decide_eq_true rfl))
  have e_v1450 : v1450 = if v1448 = 1 then v33 else v1442 := e_psel h_v1448 h_v33 h_v1442 (of_decide_eq_true rfl)
  clear h_v1341 h_v1434 h_v1435 h_v1436 h_v1437 h_v1438 h_v1441 h_v1442 h_v1443 h_v1444 h_v1446 h_v1447 h_v1448
  have h_v1454 : R 1 0 4611686018427387904 4683743620518379745 v1454 v1454 := (r_smx_sq hl 29 h_v1279 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1454 : sv v1454 = sv v1279 * sv v1279 := e_smx_sq 29 h_v1279 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1455 : R 1 0 4611686018427387904 4611686018695823391 v1455 v1455 := (r_srdC hl h_v1454 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1455 : sv v1455 = -((-sv v1454) / 2 ^ 28) := e_srdC h_v1454 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1456 : R 1 0 4611686018427387904 4611686018964258878 v1456 v1456 := (r_sub hl (r_add hl h_v1455 h_v1455 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1456 : sv v1456 = sv v1455 + sv v1455 := e_add h_v1455 h_v1455 (of_decide_eq_true rfl)
  have h_v1457 : R 1 0 4611686018158952386 4611686018695823360 v1457 v1457 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1456 (of_decide_eq_true rfl))
  have e_v1457 : sv v1457 = sv v33 - sv v1456 := e_sub h_v33 h_v1456 (of_decide_eq_true rfl)
  have h_v1458 : R 1 0 0 1 v1458 v1458 := (r_plt hl h_v1457 h_v95 (of_decide_eq_true rfl))
  have e_v1458 : (v1458 = 1 ↔ sv v1457 < sv v95) := e_plt h_v1457 h_v95 (of_decide_eq_true rfl)
  have h_v1459 : R 1 0 4611686018158952386 4611686018695823360 v1459 v1459 := (r_psel hl h_v1458 h_v95 h_v1457 (of_decide_eq_true rfl))
  have e_v1459 : v1459 = if v1458 = 1 then v95 else v1457 := e_psel h_v1458 h_v95 h_v1457 (of_decide_eq_true rfl)
  have h_v1460 : R 1 0 4611686018427387904 4683743620518379745 v1460 v1460 := (r_smx_sq hl 29 h_v1278 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1460 : sv v1460 = sv v1278 * sv v1278 := e_smx_sq 29 h_v1278 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1461 : R 1 0 4611686018427387904 4611686018695823390 v1461 v1461 := (r_srdF hl h_v1460 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1461 : sv v1461 = sv v1460 / 2 ^ 28 := e_srdF h_v1460 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1462 : R 1 0 4611686018427387904 4611686018964258876 v1462 v1462 := (r_sub hl (r_add hl h_v1461 h_v1461 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1462 : sv v1462 = sv v1461 + sv v1461 := e_add h_v1461 h_v1461 (of_decide_eq_true rfl)
  have h_v1463 : R 1 0 4611686018158952388 4611686018695823360 v1463 v1463 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1462 (of_decide_eq_true rfl))
  have e_v1463 : sv v1463 = sv v33 - sv v1462 := e_sub h_v33 h_v1462 (of_decide_eq_true rfl)
  have h_v1464 : R 1 0 4611686018427387904 4683743620518379745 v1464 v1464 := (r_smx_sq hl 29 h_v1283 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1464 : sv v1464 = sv v1283 * sv v1283 := e_smx_sq 29 h_v1283 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1465 : R 1 0 4611686018427387904 4611686018695823391 v1465 v1465 := (r_srdC hl h_v1464 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1465 : sv v1465 = -((-sv v1464) / 2 ^ 28) := e_srdC h_v1464 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1466 : R 1 0 4611686018427387904 4611686018964258878 v1466 v1466 := (r_sub hl (r_add hl h_v1465 h_v1465 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v1455 h_v1456 h_v1457 h_v1458 h_v1461 h_v1462
  have e_v1466 : sv v1466 = sv v1465 + sv v1465 := e_add h_v1465 h_v1465 (of_decide_eq_true rfl)
  have h_v1467 : R 1 0 4611686018158952386 4611686018695823360 v1467 v1467 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1466 (of_decide_eq_true rfl))
  have e_v1467 : sv v1467 = sv v33 - sv v1466 := e_sub h_v33 h_v1466 (of_decide_eq_true rfl)
  have h_v1468 : R 1 0 0 1 v1468 v1468 := (r_plt hl h_v1467 h_v95 (of_decide_eq_true rfl))
  have e_v1468 : (v1468 = 1 ↔ sv v1467 < sv v95) := e_plt h_v1467 h_v95 (of_decide_eq_true rfl)
  have h_v1469 : R 1 0 4611686018158952386 4611686018695823360 v1469 v1469 := (r_psel hl h_v1468 h_v95 h_v1467 (of_decide_eq_true rfl))
  have e_v1469 : v1469 = if v1468 = 1 then v95 else v1467 := e_psel h_v1468 h_v95 h_v1467 (of_decide_eq_true rfl)
  have h_v1470 : R 1 0 4611686018427387904 4683743620518379745 v1470 v1470 := (r_smx_sq hl 29 h_v1282 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1470 : sv v1470 = sv v1282 * sv v1282 := e_smx_sq 29 h_v1282 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1471 : R 1 0 4611686018427387904 4611686018695823390 v1471 v1471 := (r_srdF hl h_v1470 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1471 : sv v1471 = sv v1470 / 2 ^ 28 := e_srdF h_v1470 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1472 : R 1 0 4611686018427387904 4611686018964258876 v1472 v1472 := (r_sub hl (r_add hl h_v1471 h_v1471 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1472 : sv v1472 = sv v1471 + sv v1471 := e_add h_v1471 h_v1471 (of_decide_eq_true rfl)
  have h_v1473 : R 1 0 4611686018158952388 4611686018695823360 v1473 v1473 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1472 (of_decide_eq_true rfl))
  have e_v1473 : sv v1473 = sv v33 - sv v1472 := e_sub h_v33 h_v1472 (of_decide_eq_true rfl)
  have h_v1474 : R 1 0 0 1 v1474 v1474 := (r_plt hl h_v1459 h_v61 (of_decide_eq_true rfl))
  have e_v1474 : (v1474 = 1 ↔ sv v1459 < sv v61) := e_plt h_v1459 h_v61 (of_decide_eq_true rfl)
  have h_v1476 : R 1 0 0 1 v1476 v1476 := (r_plt hl h_v61 h_v1463 (of_decide_eq_true rfl))
  have e_v1476 : (v1476 = 1 ↔ sv v61 < sv v1463) := e_plt h_v61 h_v1463 (of_decide_eq_true rfl)
  have h_v1477 : R 1 0 0 1 v1477 v1477 := (r_sub hl (r_O hl) h_v1476 (of_decide_eq_true rfl))
  have e_v1477 : (v1477 = 1 ↔ ¬v1476 = 1) := e_not h_v1476 (of_decide_eq_true rfl)
  have h_v1478 : R 1 0 0 1 v1478 v1478 := (r_land hl h_v1474 h_v1477 (of_decide_eq_true rfl))
  have e_v1478 : (v1478 = 1 ↔ v1474 = 1 ∧ v1477 = 1) := e_land h_v1474 h_v1477 (of_decide_eq_true rfl)
  have h_v1479 : R 1 0 0 1 v1479 v1479 := (r_land hl h_v1474 h_v1476 (of_decide_eq_true rfl))
  have e_v1479 : (v1479 = 1 ↔ v1474 = 1 ∧ v1476 = 1) := e_land h_v1474 h_v1476 (of_decide_eq_true rfl)
  clear h_v1465 h_v1466 h_v1467 h_v1468 h_v1471 h_v1472 h_v1474 h_v1476 h_v1477
  have h_v1480 : R 1 0 0 1 v1480 v1480 := (r_plt hl h_v1469 h_v61 (of_decide_eq_true rfl))
  have e_v1480 : (v1480 = 1 ↔ sv v1469 < sv v61) := e_plt h_v1469 h_v61 (of_decide_eq_true rfl)
  have h_v1482 : R 1 0 0 1 v1482 v1482 := (r_plt hl h_v61 h_v1473 (of_decide_eq_true rfl))
  have e_v1482 : (v1482 = 1 ↔ sv v61 < sv v1473) := e_plt h_v61 h_v1473 (of_decide_eq_true rfl)
  have h_v1483 : R 1 0 0 1 v1483 v1483 := (r_sub hl (r_O hl) h_v1482 (of_decide_eq_true rfl))
  have e_v1483 : (v1483 = 1 ↔ ¬v1482 = 1) := e_not h_v1482 (of_decide_eq_true rfl)
  have h_v1484 : R 1 0 0 1 v1484 v1484 := (r_land hl h_v1480 h_v1483 (of_decide_eq_true rfl))
  have e_v1484 : (v1484 = 1 ↔ v1480 = 1 ∧ v1483 = 1) := e_land h_v1480 h_v1483 (of_decide_eq_true rfl)
  have h_v1485 : R 1 0 0 1 v1485 v1485 := (r_land hl h_v1480 h_v1482 (of_decide_eq_true rfl))
  have e_v1485 : (v1485 = 1 ↔ v1480 = 1 ∧ v1482 = 1) := e_land h_v1480 h_v1482 (of_decide_eq_true rfl)
  have h_v1486 : R 1 0 0 1 v1486 v1486 := (r_land hl h_v1479 h_v1485 (of_decide_eq_true rfl))
  have e_v1486 : (v1486 = 1 ↔ v1479 = 1 ∧ v1485 = 1) := e_land h_v1479 h_v1485 (of_decide_eq_true rfl)
  have h_v1487 : R 1 0 0 1 v1487 v1487 := (r_sub hl (r_O hl) h_v1486 (of_decide_eq_true rfl))
  have e_v1487 : (v1487 = 1 ↔ ¬v1486 = 1) := e_not h_v1486 (of_decide_eq_true rfl)
  have h_v1488 : R 1 0 0 1 v1488 v1488 := (r_lor hl h_v823 h_v1487 (of_decide_eq_true rfl))
  have e_v1488 : (v1488 = 1 ↔ v823 = 1 ∨ v1487 = 1) := e_lor h_v823 h_v1487 (of_decide_eq_true rfl)
  have h_v1495 : R 1 0 0 1 v1495 v1495 := (r_land hl h_v1478 h_v1485 (of_decide_eq_true rfl))
  have e_v1495 : (v1495 = 1 ↔ v1478 = 1 ∧ v1485 = 1) := e_land h_v1478 h_v1485 (of_decide_eq_true rfl)
  have h_v1496 : R 1 0 0 1 v1496 v1496 := (r_lor hl h_v1484 h_v1495 (of_decide_eq_true rfl))
  have e_v1496 : (v1496 = 1 ↔ v1484 = 1 ∨ v1495 = 1) := e_lor h_v1484 h_v1495 (of_decide_eq_true rfl)
  have h_v1497 : R 1 0 4611686018158952386 4611686018695823360 v1497 v1497 := (r_psel hl h_v1496 h_v1459 h_v1463 (of_decide_eq_true rfl))
  have e_v1497 : v1497 = if v1496 = 1 then v1459 else v1463 := e_psel h_v1496 h_v1459 h_v1463 (of_decide_eq_true rfl)
  have h_v1498 : R 1 0 0 1 v1498 v1498 := (r_land hl h_v1479 h_v1484 (of_decide_eq_true rfl))
  have e_v1498 : (v1498 = 1 ↔ v1479 = 1 ∧ v1484 = 1) := e_land h_v1479 h_v1484 (of_decide_eq_true rfl)
  have h_v1499 : R 1 0 0 1 v1499 v1499 := (r_lor hl h_v1478 h_v1498 (of_decide_eq_true rfl))
  clear h_v1459 h_v1463 h_v1479 h_v1480 h_v1482 h_v1483 h_v1484 h_v1485 h_v1486 h_v1487 h_v1495 h_v1496
  have e_v1499 : (v1499 = 1 ↔ v1478 = 1 ∨ v1498 = 1) := e_lor h_v1478 h_v1498 (of_decide_eq_true rfl)
  have h_v1500 : R 1 0 4611686018158952386 4611686018695823360 v1500 v1500 := (r_psel hl h_v1499 h_v1469 h_v1473 (of_decide_eq_true rfl))
  have e_v1500 : v1500 = if v1499 = 1 then v1469 else v1473 := e_psel h_v1499 h_v1469 h_v1473 (of_decide_eq_true rfl)
  have h_v1503 : R 1 0 4539628407746461696 4683743645751316228 v1503 v1503 := (r_smx hl 30 h_v1500 h_v1497 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1503 : sv v1503 = sv v1500 * sv v1497 := e_smx 30 h_v1500 h_v1497 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1504 : R 1 0 4611686018158952386 4611686018695823485 v1504 v1504 := (r_srdC hl h_v1503 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v1504 : sv v1504 = -((-sv v1503) / 2 ^ 28) := e_srdC h_v1503 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v1505 : R 1 0 4611686017890516805 4611686018964258878 v1505 v1505 := (r_sub hl (r_add hl h_v804 h_OFFr (of_decide_eq_true rfl)) h_v1504 (of_decide_eq_true rfl))
  have e_v1505 : sv v1505 = sv v804 - sv v1504 := e_sub h_v804 h_v1504 (of_decide_eq_true rfl)
  have h_v1507 : R 1 0 4611686010374323999 4683743612465315840 v1507 v1507 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1460 (of_decide_eq_true rfl))
  have e_v1507 : sv v1507 = sv v940 - sv v1460 := e_sub h_v940 h_v1460 (of_decide_eq_true rfl)
  have h_v1508 : R 1 0 4611686018427387904 4611686018695823360 v1508 v1508 := (r_psqrt hl h_v1507 (of_decide_eq_true rfl))
  have e_v1508 : sv v1508 = ((Nat.sqrt (v1507 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1507 (of_decide_eq_true rfl)
  have h_v1509 : R 1 0 4611686018427387905 4611686018695823361 v1509 v1509 := (r_sub hl (r_add hl h_v105 h_v1508 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1509 : sv v1509 = sv v105 + sv v1508 := e_add h_v105 h_v1508 (of_decide_eq_true rfl)
  have pb_v1508_v1278 : PB 1 v1508 v1278 36028797018963968 := pb_sqrt hl h_v1278 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1510 : R 1 0 4611686017085210624 4647714815446351872 v1510 v1510 := (r_smx_pb hl 29 h_v1508 h_v1278 pb_v1508_v1278 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1510 : sv v1510 = sv v1508 * sv v1278 := e_smx_pb 29 h_v1508 h_v1278 pb_v1508_v1278 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1511 : R 1 0 4611686018427387899 4611686018561605632 v1511 v1511 := (r_srdF hl h_v1510 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1511 : sv v1511 = sv v1510 / 2 ^ 28 := e_srdF h_v1510 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1512 : R 1 0 4611686018427387894 4611686018695823360 v1512 v1512 := (r_sub hl (r_add hl h_v1511 h_v1511 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1512 : sv v1512 = sv v1511 + sv v1511 := e_add h_v1511 h_v1511 (of_decide_eq_true rfl)
  have pb_v1509_v1278 : PB 1 v1509 v1278 36028797287399439 := pb_sqrt1 hl h_v1278 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1513 : R 1 0 4611686017085210619 4647714815714787343 v1513 v1513 := (r_smx_pb hl 29 h_v1509 h_v1278 pb_v1509_v1278 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1513 : sv v1513 = sv v1509 * sv v1278 := e_smx_pb 29 h_v1509 h_v1278 pb_v1509_v1278 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  clear h_v1278 h_v1469 h_v1473 h_v1478 h_v1497 h_v1498 h_v1499 h_v1500 h_v1503 h_v1504 h_v1507 h_v1508 h_v1509 pb_v1508_v1278 h_v1510 h_v1511 pb_v1509_v1278
  have h_v1514 : R 1 0 4611686018427387899 4611686018561605634 v1514 v1514 := (r_srdC hl h_v1513 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1514 : sv v1514 = -((-sv v1513) / 2 ^ 28) := e_srdC h_v1513 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1515 : R 1 0 4611686018427387894 4611686018695823364 v1515 v1515 := (r_sub hl (r_add hl h_v1514 h_v1514 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1515 : sv v1515 = sv v1514 + sv v1514 := e_add h_v1514 h_v1514 (of_decide_eq_true rfl)
  have h_v1516 : R 1 0 0 1 v1516 v1516 := (r_plt hl h_v1515 h_v33 (of_decide_eq_true rfl))
  have e_v1516 : (v1516 = 1 ↔ sv v1515 < sv v33) := e_plt h_v1515 h_v33 (of_decide_eq_true rfl)
  have h_v1517 : R 1 0 4611686018427387894 4611686018695823364 v1517 v1517 := (r_psel hl h_v1516 h_v1515 h_v33 (of_decide_eq_true rfl))
  have e_v1517 : v1517 = if v1516 = 1 then v1515 else v33 := e_psel h_v1516 h_v1515 h_v33 (of_decide_eq_true rfl)
  have h_v1518 : R 1 0 4611686010374323999 4683743612465315840 v1518 v1518 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1454 (of_decide_eq_true rfl))
  have e_v1518 : sv v1518 = sv v940 - sv v1454 := e_sub h_v940 h_v1454 (of_decide_eq_true rfl)
  have h_v1519 : R 1 0 4611686018427387904 4611686018695823360 v1519 v1519 := (r_psqrt hl h_v1518 (of_decide_eq_true rfl))
  have e_v1519 : sv v1519 = ((Nat.sqrt (v1518 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1518 (of_decide_eq_true rfl)
  have h_v1520 : R 1 0 4611686018427387905 4611686018695823361 v1520 v1520 := (r_sub hl (r_add hl h_v105 h_v1519 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1520 : sv v1520 = sv v105 + sv v1519 := e_add h_v105 h_v1519 (of_decide_eq_true rfl)
  have pb_v1519_v1279 : PB 1 v1519 v1279 36028797018963968 := pb_sqrt hl h_v1279 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1521 : R 1 0 4611686017085210624 4647714815446351872 v1521 v1521 := (r_smx_pb hl 29 h_v1519 h_v1279 pb_v1519_v1279 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1521 : sv v1521 = sv v1519 * sv v1279 := e_smx_pb 29 h_v1519 h_v1279 pb_v1519_v1279 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1522 : R 1 0 4611686018427387899 4611686018561605632 v1522 v1522 := (r_srdF hl h_v1521 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1522 : sv v1522 = sv v1521 / 2 ^ 28 := e_srdF h_v1521 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1523 : R 1 0 4611686018427387894 4611686018695823360 v1523 v1523 := (r_sub hl (r_add hl h_v1522 h_v1522 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1523 : sv v1523 = sv v1522 + sv v1522 := e_add h_v1522 h_v1522 (of_decide_eq_true rfl)
  have pb_v1520_v1279 : PB 1 v1520 v1279 36028797287399439 := pb_sqrt1 hl h_v1279 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1524 : R 1 0 4611686017085210619 4647714815714787343 v1524 v1524 := (r_smx_pb hl 29 h_v1520 h_v1279 pb_v1520_v1279 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1524 : sv v1524 = sv v1520 * sv v1279 := e_smx_pb 29 h_v1520 h_v1279 pb_v1520_v1279 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1525 : R 1 0 4611686018427387899 4611686018561605634 v1525 v1525 := (r_srdC hl h_v1524 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  clear h_v1279 h_v1513 h_v1514 h_v1515 h_v1516 h_v1518 h_v1519 h_v1520 pb_v1519_v1279 h_v1521 h_v1522 pb_v1520_v1279
  have e_v1525 : sv v1525 = -((-sv v1524) / 2 ^ 28) := e_srdC h_v1524 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1526 : R 1 0 4611686018427387894 4611686018695823364 v1526 v1526 := (r_sub hl (r_add hl h_v1525 h_v1525 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1526 : sv v1526 = sv v1525 + sv v1525 := e_add h_v1525 h_v1525 (of_decide_eq_true rfl)
  have h_v1527 : R 1 0 0 1 v1527 v1527 := (r_plt hl h_v1526 h_v33 (of_decide_eq_true rfl))
  have e_v1527 : (v1527 = 1 ↔ sv v1526 < sv v33) := e_plt h_v1526 h_v33 (of_decide_eq_true rfl)
  have h_v1528 : R 1 0 4611686018427387894 4611686018695823364 v1528 v1528 := (r_psel hl h_v1527 h_v1526 h_v33 (of_decide_eq_true rfl))
  have e_v1528 : v1528 = if v1527 = 1 then v1526 else v33 := e_psel h_v1527 h_v1526 h_v33 (of_decide_eq_true rfl)
  have h_v1529 : R 1 0 0 1 v1529 v1529 := (r_plt hl h_v1512 h_v1523 (of_decide_eq_true rfl))
  have e_v1529 : (v1529 = 1 ↔ sv v1512 < sv v1523) := e_plt h_v1512 h_v1523 (of_decide_eq_true rfl)
  have h_v1530 : R 1 0 4611686018427387894 4611686018695823360 v1530 v1530 := (r_psel hl h_v1529 h_v1512 h_v1523 (of_decide_eq_true rfl))
  have e_v1530 : v1530 = if v1529 = 1 then v1512 else v1523 := e_psel h_v1529 h_v1512 h_v1523 (of_decide_eq_true rfl)
  have h_v1531 : R 1 0 0 1 v1531 v1531 := (r_plt hl h_v1517 h_v1528 (of_decide_eq_true rfl))
  have e_v1531 : (v1531 = 1 ↔ sv v1517 < sv v1528) := e_plt h_v1517 h_v1528 (of_decide_eq_true rfl)
  have h_v1532 : R 1 0 4611686018427387894 4611686018695823364 v1532 v1532 := (r_psel hl h_v1531 h_v1528 h_v1517 (of_decide_eq_true rfl))
  have e_v1532 : v1532 = if v1531 = 1 then v1528 else v1517 := e_psel h_v1531 h_v1528 h_v1517 (of_decide_eq_true rfl)
  have h_v1533 : R 1 0 0 1 v1533 v1533 := (r_plt hl h_v967 h_v1460 (of_decide_eq_true rfl))
  have e_v1533 : (v1533 = 1 ↔ sv v967 < sv v1460) := e_plt h_v967 h_v1460 (of_decide_eq_true rfl)
  have h_v1534 : R 1 0 0 1 v1534 v1534 := (r_sub hl (r_O hl) h_v1533 (of_decide_eq_true rfl))
  have e_v1534 : (v1534 = 1 ↔ ¬v1533 = 1) := e_not h_v1533 (of_decide_eq_true rfl)
  have h_v1535 : R 1 0 0 1 v1535 v1535 := (r_plt hl h_v1454 h_v967 (of_decide_eq_true rfl))
  have e_v1535 : (v1535 = 1 ↔ sv v1454 < sv v967) := e_plt h_v1454 h_v967 (of_decide_eq_true rfl)
  have h_v1536 : R 1 0 0 1 v1536 v1536 := (r_sub hl (r_O hl) h_v1535 (of_decide_eq_true rfl))
  have e_v1536 : (v1536 = 1 ↔ ¬v1535 = 1) := e_not h_v1535 (of_decide_eq_true rfl)
  have h_v1537 : R 1 0 0 1 v1537 v1537 := (r_land hl h_v1534 h_v1536 (of_decide_eq_true rfl))
  have e_v1537 : (v1537 = 1 ↔ v1534 = 1 ∧ v1536 = 1) := e_land h_v1534 h_v1536 (of_decide_eq_true rfl)
  clear h_v1454 h_v1460 h_v1512 h_v1517 h_v1523 h_v1524 h_v1525 h_v1526 h_v1527 h_v1528 h_v1529 h_v1531 h_v1533 h_v1534 h_v1535 h_v1536
  have h_v1538 : R 1 0 4611686018427387894 4611686018695823364 v1538 v1538 := (r_psel hl h_v1537 h_v33 h_v1532 (of_decide_eq_true rfl))
  have e_v1538 : v1538 = if v1537 = 1 then v33 else v1532 := e_psel h_v1537 h_v33 h_v1532 (of_decide_eq_true rfl)
  have h_v1539 : R 1 0 4611686010374323999 4683743612465315840 v1539 v1539 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1470 (of_decide_eq_true rfl))
  have e_v1539 : sv v1539 = sv v940 - sv v1470 := e_sub h_v940 h_v1470 (of_decide_eq_true rfl)
  have h_v1540 : R 1 0 4611686018427387904 4611686018695823360 v1540 v1540 := (r_psqrt hl h_v1539 (of_decide_eq_true rfl))
  have e_v1540 : sv v1540 = ((Nat.sqrt (v1539 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1539 (of_decide_eq_true rfl)
  have h_v1541 : R 1 0 4611686018427387905 4611686018695823361 v1541 v1541 := (r_sub hl (r_add hl h_v105 h_v1540 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1541 : sv v1541 = sv v105 + sv v1540 := e_add h_v105 h_v1540 (of_decide_eq_true rfl)
  have pb_v1540_v1282 : PB 1 v1540 v1282 36028797018963968 := pb_sqrt hl h_v1282 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1542 : R 1 0 4611686017085210624 4647714815446351872 v1542 v1542 := (r_smx_pb hl 29 h_v1540 h_v1282 pb_v1540_v1282 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1542 : sv v1542 = sv v1540 * sv v1282 := e_smx_pb 29 h_v1540 h_v1282 pb_v1540_v1282 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1543 : R 1 0 4611686018427387899 4611686018561605632 v1543 v1543 := (r_srdF hl h_v1542 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1543 : sv v1543 = sv v1542 / 2 ^ 28 := e_srdF h_v1542 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1544 : R 1 0 4611686018427387894 4611686018695823360 v1544 v1544 := (r_sub hl (r_add hl h_v1543 h_v1543 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1544 : sv v1544 = sv v1543 + sv v1543 := e_add h_v1543 h_v1543 (of_decide_eq_true rfl)
  have pb_v1541_v1282 : PB 1 v1541 v1282 36028797287399439 := pb_sqrt1 hl h_v1282 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1545 : R 1 0 4611686017085210619 4647714815714787343 v1545 v1545 := (r_smx_pb hl 29 h_v1541 h_v1282 pb_v1541_v1282 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1545 : sv v1545 = sv v1541 * sv v1282 := e_smx_pb 29 h_v1541 h_v1282 pb_v1541_v1282 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1546 : R 1 0 4611686018427387899 4611686018561605634 v1546 v1546 := (r_srdC hl h_v1545 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1546 : sv v1546 = -((-sv v1545) / 2 ^ 28) := e_srdC h_v1545 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1547 : R 1 0 4611686018427387894 4611686018695823364 v1547 v1547 := (r_sub hl (r_add hl h_v1546 h_v1546 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1547 : sv v1547 = sv v1546 + sv v1546 := e_add h_v1546 h_v1546 (of_decide_eq_true rfl)
  have h_v1548 : R 1 0 0 1 v1548 v1548 := (r_plt hl h_v1547 h_v33 (of_decide_eq_true rfl))
  have e_v1548 : (v1548 = 1 ↔ sv v1547 < sv v33) := e_plt h_v1547 h_v33 (of_decide_eq_true rfl)
  have h_v1549 : R 1 0 4611686018427387894 4611686018695823364 v1549 v1549 := (r_psel hl h_v1548 h_v1547 h_v33 (of_decide_eq_true rfl))
  clear h_v1282 h_v1532 h_v1537 h_v1539 h_v1540 h_v1541 pb_v1540_v1282 h_v1542 h_v1543 pb_v1541_v1282 h_v1545 h_v1546
  have e_v1549 : v1549 = if v1548 = 1 then v1547 else v33 := e_psel h_v1548 h_v1547 h_v33 (of_decide_eq_true rfl)
  have h_v1550 : R 1 0 4611686010374323999 4683743612465315840 v1550 v1550 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1464 (of_decide_eq_true rfl))
  have e_v1550 : sv v1550 = sv v940 - sv v1464 := e_sub h_v940 h_v1464 (of_decide_eq_true rfl)
  have h_v1551 : R 1 0 4611686018427387904 4611686018695823360 v1551 v1551 := (r_psqrt hl h_v1550 (of_decide_eq_true rfl))
  have e_v1551 : sv v1551 = ((Nat.sqrt (v1550 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1550 (of_decide_eq_true rfl)
  have h_v1552 : R 1 0 4611686018427387905 4611686018695823361 v1552 v1552 := (r_sub hl (r_add hl h_v105 h_v1551 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1552 : sv v1552 = sv v105 + sv v1551 := e_add h_v105 h_v1551 (of_decide_eq_true rfl)
  have pb_v1551_v1283 : PB 1 v1551 v1283 36028797018963968 := pb_sqrt hl h_v1283 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1553 : R 1 0 4611686017085210624 4647714815446351872 v1553 v1553 := (r_smx_pb hl 29 h_v1551 h_v1283 pb_v1551_v1283 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1553 : sv v1553 = sv v1551 * sv v1283 := e_smx_pb 29 h_v1551 h_v1283 pb_v1551_v1283 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1554 : R 1 0 4611686018427387899 4611686018561605632 v1554 v1554 := (r_srdF hl h_v1553 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1554 : sv v1554 = sv v1553 / 2 ^ 28 := e_srdF h_v1553 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1555 : R 1 0 4611686018427387894 4611686018695823360 v1555 v1555 := (r_sub hl (r_add hl h_v1554 h_v1554 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1555 : sv v1555 = sv v1554 + sv v1554 := e_add h_v1554 h_v1554 (of_decide_eq_true rfl)
  have pb_v1552_v1283 : PB 1 v1552 v1283 36028797287399439 := pb_sqrt1 hl h_v1283 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1556 : R 1 0 4611686017085210619 4647714815714787343 v1556 v1556 := (r_smx_pb hl 29 h_v1552 h_v1283 pb_v1552_v1283 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1556 : sv v1556 = sv v1552 * sv v1283 := e_smx_pb 29 h_v1552 h_v1283 pb_v1552_v1283 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1557 : R 1 0 4611686018427387899 4611686018561605634 v1557 v1557 := (r_srdC hl h_v1556 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1557 : sv v1557 = -((-sv v1556) / 2 ^ 28) := e_srdC h_v1556 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1558 : R 1 0 4611686018427387894 4611686018695823364 v1558 v1558 := (r_sub hl (r_add hl h_v1557 h_v1557 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1558 : sv v1558 = sv v1557 + sv v1557 := e_add h_v1557 h_v1557 (of_decide_eq_true rfl)
  have h_v1559 : R 1 0 0 1 v1559 v1559 := (r_plt hl h_v1558 h_v33 (of_decide_eq_true rfl))
  have e_v1559 : (v1559 = 1 ↔ sv v1558 < sv v33) := e_plt h_v1558 h_v33 (of_decide_eq_true rfl)
  have h_v1560 : R 1 0 4611686018427387894 4611686018695823364 v1560 v1560 := (r_psel hl h_v1559 h_v1558 h_v33 (of_decide_eq_true rfl))
  have e_v1560 : v1560 = if v1559 = 1 then v1558 else v33 := e_psel h_v1559 h_v1558 h_v33 (of_decide_eq_true rfl)
  clear h_v940 h_v1283 h_v1547 h_v1548 h_v1550 h_v1551 h_v1552 pb_v1551_v1283 h_v1553 h_v1554 pb_v1552_v1283 h_v1556 h_v1557 h_v1558 h_v1559
  have h_v1561 : R 1 0 0 1 v1561 v1561 := (r_plt hl h_v1544 h_v1555 (of_decide_eq_true rfl))
  have e_v1561 : (v1561 = 1 ↔ sv v1544 < sv v1555) := e_plt h_v1544 h_v1555 (of_decide_eq_true rfl)
  have h_v1562 : R 1 0 4611686018427387894 4611686018695823360 v1562 v1562 := (r_psel hl h_v1561 h_v1544 h_v1555 (of_decide_eq_true rfl))
  have e_v1562 : v1562 = if v1561 = 1 then v1544 else v1555 := e_psel h_v1561 h_v1544 h_v1555 (of_decide_eq_true rfl)
  have h_v1563 : R 1 0 0 1 v1563 v1563 := (r_plt hl h_v1549 h_v1560 (of_decide_eq_true rfl))
  have e_v1563 : (v1563 = 1 ↔ sv v1549 < sv v1560) := e_plt h_v1549 h_v1560 (of_decide_eq_true rfl)
  have h_v1564 : R 1 0 4611686018427387894 4611686018695823364 v1564 v1564 := (r_psel hl h_v1563 h_v1560 h_v1549 (of_decide_eq_true rfl))
  have e_v1564 : v1564 = if v1563 = 1 then v1560 else v1549 := e_psel h_v1563 h_v1560 h_v1549 (of_decide_eq_true rfl)
  have h_v1565 : R 1 0 0 1 v1565 v1565 := (r_plt hl h_v967 h_v1470 (of_decide_eq_true rfl))
  have e_v1565 : (v1565 = 1 ↔ sv v967 < sv v1470) := e_plt h_v967 h_v1470 (of_decide_eq_true rfl)
  have h_v1566 : R 1 0 0 1 v1566 v1566 := (r_sub hl (r_O hl) h_v1565 (of_decide_eq_true rfl))
  have e_v1566 : (v1566 = 1 ↔ ¬v1565 = 1) := e_not h_v1565 (of_decide_eq_true rfl)
  have h_v1567 : R 1 0 0 1 v1567 v1567 := (r_plt hl h_v1464 h_v967 (of_decide_eq_true rfl))
  have e_v1567 : (v1567 = 1 ↔ sv v1464 < sv v967) := e_plt h_v1464 h_v967 (of_decide_eq_true rfl)
  have h_v1568 : R 1 0 0 1 v1568 v1568 := (r_sub hl (r_O hl) h_v1567 (of_decide_eq_true rfl))
  have e_v1568 : (v1568 = 1 ↔ ¬v1567 = 1) := e_not h_v1567 (of_decide_eq_true rfl)
  have h_v1569 : R 1 0 0 1 v1569 v1569 := (r_land hl h_v1566 h_v1568 (of_decide_eq_true rfl))
  have e_v1569 : (v1569 = 1 ↔ v1566 = 1 ∧ v1568 = 1) := e_land h_v1566 h_v1568 (of_decide_eq_true rfl)
  have h_v1570 : R 1 0 4611686018427387894 4611686018695823364 v1570 v1570 := (r_psel hl h_v1569 h_v33 h_v1564 (of_decide_eq_true rfl))
  have e_v1570 : v1570 = if v1569 = 1 then v33 else v1564 := e_psel h_v1569 h_v33 h_v1564 (of_decide_eq_true rfl)
  have h_v1571 : R 1 0 0 1 v1571 v1571 := (r_plt hl h_v1530 h_v61 (of_decide_eq_true rfl))
  have e_v1571 : (v1571 = 1 ↔ sv v1530 < sv v61) := e_plt h_v1530 h_v61 (of_decide_eq_true rfl)
  have h_v1572 : R 1 0 0 1 v1572 v1572 := (r_sub hl (r_O hl) h_v1571 (of_decide_eq_true rfl))
  have e_v1572 : (v1572 = 1 ↔ ¬v1571 = 1) := e_not h_v1571 (of_decide_eq_true rfl)
  have h_v1573 : R 1 0 0 1 v1573 v1573 := (r_plt hl h_v61 h_v1538 (of_decide_eq_true rfl))
  clear h_v967 h_v1464 h_v1470 h_v1544 h_v1549 h_v1555 h_v1560 h_v1561 h_v1563 h_v1564 h_v1565 h_v1566 h_v1567 h_v1568 h_v1569
  have e_v1573 : (v1573 = 1 ↔ sv v61 < sv v1538) := e_plt h_v61 h_v1538 (of_decide_eq_true rfl)
  have h_v1574 : R 1 0 0 1 v1574 v1574 := (r_sub hl (r_O hl) h_v1573 (of_decide_eq_true rfl))
  have e_v1574 : (v1574 = 1 ↔ ¬v1573 = 1) := e_not h_v1573 (of_decide_eq_true rfl)
  have h_v1575 : R 1 0 0 1 v1575 v1575 := (r_land hl h_v1571 h_v1574 (of_decide_eq_true rfl))
  have e_v1575 : (v1575 = 1 ↔ v1571 = 1 ∧ v1574 = 1) := e_land h_v1571 h_v1574 (of_decide_eq_true rfl)
  have h_v1576 : R 1 0 0 1 v1576 v1576 := (r_land hl h_v1571 h_v1573 (of_decide_eq_true rfl))
  have e_v1576 : (v1576 = 1 ↔ v1571 = 1 ∧ v1573 = 1) := e_land h_v1571 h_v1573 (of_decide_eq_true rfl)
  have h_v1577 : R 1 0 0 1 v1577 v1577 := (r_plt hl h_v1562 h_v61 (of_decide_eq_true rfl))
  have e_v1577 : (v1577 = 1 ↔ sv v1562 < sv v61) := e_plt h_v1562 h_v61 (of_decide_eq_true rfl)
  have h_v1578 : R 1 0 0 1 v1578 v1578 := (r_sub hl (r_O hl) h_v1577 (of_decide_eq_true rfl))
  have e_v1578 : (v1578 = 1 ↔ ¬v1577 = 1) := e_not h_v1577 (of_decide_eq_true rfl)
  have h_v1579 : R 1 0 0 1 v1579 v1579 := (r_plt hl h_v61 h_v1570 (of_decide_eq_true rfl))
  have e_v1579 : (v1579 = 1 ↔ sv v61 < sv v1570) := e_plt h_v61 h_v1570 (of_decide_eq_true rfl)
  have h_v1580 : R 1 0 0 1 v1580 v1580 := (r_sub hl (r_O hl) h_v1579 (of_decide_eq_true rfl))
  have e_v1580 : (v1580 = 1 ↔ ¬v1579 = 1) := e_not h_v1579 (of_decide_eq_true rfl)
  have h_v1581 : R 1 0 0 1 v1581 v1581 := (r_land hl h_v1577 h_v1580 (of_decide_eq_true rfl))
  have e_v1581 : (v1581 = 1 ↔ v1577 = 1 ∧ v1580 = 1) := e_land h_v1577 h_v1580 (of_decide_eq_true rfl)
  have h_v1582 : R 1 0 0 1 v1582 v1582 := (r_land hl h_v1577 h_v1579 (of_decide_eq_true rfl))
  have e_v1582 : (v1582 = 1 ↔ v1577 = 1 ∧ v1579 = 1) := e_land h_v1577 h_v1579 (of_decide_eq_true rfl)
  have h_v1583 : R 1 0 0 1 v1583 v1583 := (r_land hl h_v1576 h_v1582 (of_decide_eq_true rfl))
  have e_v1583 : (v1583 = 1 ↔ v1576 = 1 ∧ v1582 = 1) := e_land h_v1576 h_v1582 (of_decide_eq_true rfl)
  have h_v1584 : R 1 0 0 1 v1584 v1584 := (r_sub hl (r_O hl) h_v1583 (of_decide_eq_true rfl))
  have e_v1584 : (v1584 = 1 ↔ ¬v1583 = 1) := e_not h_v1583 (of_decide_eq_true rfl)
  have h_v1585 : R 1 0 0 1 v1585 v1585 := (r_lor hl h_v823 h_v1584 (of_decide_eq_true rfl))
  have e_v1585 : (v1585 = 1 ↔ v823 = 1 ∨ v1584 = 1) := e_lor h_v823 h_v1584 (of_decide_eq_true rfl)
  clear h_v1571 h_v1573 h_v1574 h_v1577 h_v1579 h_v1580 h_v1583 h_v1584
  have h_v1586 : R 1 0 0 1 v1586 v1586 := (r_land hl h_v1572 h_v1582 (of_decide_eq_true rfl))
  have e_v1586 : (v1586 = 1 ↔ v1572 = 1 ∧ v1582 = 1) := e_land h_v1572 h_v1582 (of_decide_eq_true rfl)
  have h_v1587 : R 1 0 0 1 v1587 v1587 := (r_lor hl h_v1581 h_v1586 (of_decide_eq_true rfl))
  have e_v1587 : (v1587 = 1 ↔ v1581 = 1 ∨ v1586 = 1) := e_lor h_v1581 h_v1586 (of_decide_eq_true rfl)
  have h_v1588 : R 1 0 4611686018427387894 4611686018695823364 v1588 v1588 := (r_psel hl h_v1587 h_v1538 h_v1530 (of_decide_eq_true rfl))
  have e_v1588 : v1588 = if v1587 = 1 then v1538 else v1530 := e_psel h_v1587 h_v1538 h_v1530 (of_decide_eq_true rfl)
  have h_v1589 : R 1 0 0 1 v1589 v1589 := (r_land hl h_v1576 h_v1578 (of_decide_eq_true rfl))
  have e_v1589 : (v1589 = 1 ↔ v1576 = 1 ∧ v1578 = 1) := e_land h_v1576 h_v1578 (of_decide_eq_true rfl)
  have h_v1590 : R 1 0 0 1 v1590 v1590 := (r_lor hl h_v1575 h_v1589 (of_decide_eq_true rfl))
  have e_v1590 : (v1590 = 1 ↔ v1575 = 1 ∨ v1589 = 1) := e_lor h_v1575 h_v1589 (of_decide_eq_true rfl)
  have h_v1591 : R 1 0 4611686018427387894 4611686018695823364 v1591 v1591 := (r_psel hl h_v1590 h_v1570 h_v1562 (of_decide_eq_true rfl))
  have e_v1591 : v1591 = if v1590 = 1 then v1570 else v1562 := e_psel h_v1590 h_v1570 h_v1562 (of_decide_eq_true rfl)
  have h_v1592 : R 1 0 0 1 v1592 v1592 := (r_land hl h_v1575 h_v1582 (of_decide_eq_true rfl))
  have e_v1592 : (v1592 = 1 ↔ v1575 = 1 ∧ v1582 = 1) := e_land h_v1575 h_v1582 (of_decide_eq_true rfl)
  have h_v1593 : R 1 0 0 1 v1593 v1593 := (r_lor hl h_v1581 h_v1592 (of_decide_eq_true rfl))
  have e_v1593 : (v1593 = 1 ↔ v1581 = 1 ∨ v1592 = 1) := e_lor h_v1581 h_v1592 (of_decide_eq_true rfl)
  have h_v1594 : R 1 0 4611686018427387894 4611686018695823364 v1594 v1594 := (r_psel hl h_v1593 h_v1530 h_v1538 (of_decide_eq_true rfl))
  have e_v1594 : v1594 = if v1593 = 1 then v1530 else v1538 := e_psel h_v1593 h_v1530 h_v1538 (of_decide_eq_true rfl)
  have h_v1595 : R 1 0 0 1 v1595 v1595 := (r_land hl h_v1576 h_v1581 (of_decide_eq_true rfl))
  have e_v1595 : (v1595 = 1 ↔ v1576 = 1 ∧ v1581 = 1) := e_land h_v1576 h_v1581 (of_decide_eq_true rfl)
  have h_v1596 : R 1 0 0 1 v1596 v1596 := (r_lor hl h_v1575 h_v1595 (of_decide_eq_true rfl))
  have e_v1596 : (v1596 = 1 ↔ v1575 = 1 ∨ v1595 = 1) := e_lor h_v1575 h_v1595 (of_decide_eq_true rfl)
  have h_v1597 : R 1 0 4611686018427387894 4611686018695823364 v1597 v1597 := (r_psel hl h_v1596 h_v1562 h_v1570 (of_decide_eq_true rfl))
  have e_v1597 : v1597 = if v1596 = 1 then v1562 else v1570 := e_psel h_v1596 h_v1562 h_v1570 (of_decide_eq_true rfl)
  have h_v1598 : R 1 0 4611686015743033304 4683743614612799504 v1598 v1598 := (r_smx hl 29 h_v1591 h_v1588 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  clear h_v1530 h_v1538 h_v1562 h_v1570 h_v1572 h_v1575 h_v1576 h_v1578 h_v1581 h_v1582 h_v1586 h_v1587 h_v1589 h_v1590 h_v1592 h_v1593 h_v1595 h_v1596
  have e_v1598 : sv v1598 = sv v1591 * sv v1588 := e_smx 29 h_v1591 h_v1588 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1599 : R 1 0 4611686018427387893 4611686018695823368 v1599 v1599 := (r_srdF hl h_v1598 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v1599 : sv v1599 = sv v1598 / 2 ^ 28 := e_srdF h_v1598 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1600 : R 1 0 4611686015743033304 4683743614612799504 v1600 v1600 := (r_smx hl 29 h_v1597 h_v1594 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1600 : sv v1600 = sv v1597 * sv v1594 := e_smx 29 h_v1597 h_v1594 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1601 : R 1 0 4611686018427387894 4611686018695823369 v1601 v1601 := (r_srdC hl h_v1600 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1601 : sv v1601 = -((-sv v1600) / 2 ^ 28) := e_srdC h_v1600 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1602 : R 1 0 0 1 v1602 v1602 := (r_plt hl h_v61 h_v1599 (of_decide_eq_true rfl))
  have e_v1602 : (v1602 = 1 ↔ sv v61 < sv v1599) := e_plt h_v61 h_v1599 (of_decide_eq_true rfl)
  have h_v1603 : R 1 0 0 1 v1603 v1603 := (r_sub hl (r_O hl) h_v1602 (of_decide_eq_true rfl))
  have e_v1603 : (v1603 = 1 ↔ ¬v1602 = 1) := e_not h_v1602 (of_decide_eq_true rfl)
  have h_v1604 : R 1 0 0 1 v1604 v1604 := (r_plt hl h_v1505 h_v61 (of_decide_eq_true rfl))
  have e_v1604 : (v1604 = 1 ↔ sv v1505 < sv v61) := e_plt h_v1505 h_v61 (of_decide_eq_true rfl)
  have h_v1605 : R 1 0 4611686018427387893 4611686018695823369 v1605 v1605 := (r_psel hl h_v1604 h_v1599 h_v1601 (of_decide_eq_true rfl))
  have e_v1605 : v1605 = if v1604 = 1 then v1599 else v1601 := e_psel h_v1604 h_v1599 h_v1601 (of_decide_eq_true rfl)
  have h_v1608 : R 1 0 0 1 v1608 v1608 := (r_plt hl h_v1605 h_v1505 (of_decide_eq_true rfl))
  have e_v1608 : (v1608 = 1 ↔ sv v1605 < sv v1505) := e_plt h_v1605 h_v1505 (of_decide_eq_true rfl)
  have h_v1609 : R 1 0 0 1 v1609 v1609 := (r_land hl h_v1602 h_v1608 (of_decide_eq_true rfl))
  have e_v1609 : (v1609 = 1 ↔ v1602 = 1 ∧ v1608 = 1) := e_land h_v1602 h_v1608 (of_decide_eq_true rfl)
  have h_v1610 : R 1 0 4611686018158952439 4611686018427387915 v1610 v1610 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v1605 (of_decide_eq_true rfl))
  have e_v1610 : sv v1610 = sv v61 - sv v1605 := e_sub h_v61 h_v1605 (of_decide_eq_true rfl)
  have h_v1611 : R 1 0 0 1 v1611 v1611 := (r_plt hl h_v1610 h_v1505 (of_decide_eq_true rfl))
  have e_v1611 : (v1611 = 1 ↔ sv v1610 < sv v1505) := e_plt h_v1610 h_v1505 (of_decide_eq_true rfl)
  have h_v1612 : R 1 0 0 1 v1612 v1612 := (r_sub hl (r_O hl) h_v1611 (of_decide_eq_true rfl))
  have e_v1612 : (v1612 = 1 ↔ ¬v1611 = 1) := e_not h_v1611 (of_decide_eq_true rfl)
  clear h_v1588 h_v1591 h_v1594 h_v1597 h_v1598 h_v1599 h_v1600 h_v1601 h_v1602 h_v1604 h_v1608 h_v1610 h_v1611
  have h_v1613 : R 1 0 0 1 v1613 v1613 := (r_lor hl h_v1603 h_v1612 (of_decide_eq_true rfl))
  have e_v1613 : (v1613 = 1 ↔ v1603 = 1 ∨ v1612 = 1) := e_lor h_v1603 h_v1612 (of_decide_eq_true rfl)
  have h_v1614 : R 1 0 4611686017890516805 4611686018964258878 v1614 v1614 := (r_psel hl h_v1613 h_v95 h_v1505 (of_decide_eq_true rfl))
  have e_v1614 : v1614 = if v1613 = 1 then v95 else v1505 := e_psel h_v1613 h_v95 h_v1505 (of_decide_eq_true rfl)
  have h_v1615 : R 1 0 4611686018427387893 4611686018695823369 v1615 v1615 := (r_psel hl h_v1613 h_v33 h_v1605 (of_decide_eq_true rfl))
  have e_v1615 : v1615 = if v1613 = 1 then v33 else v1605 := e_psel h_v1613 h_v33 h_v1605 (of_decide_eq_true rfl)
  have h_v1616 : R 1 0 0 1 v1616 v1616 := (r_lor hl h_v1445 h_v1609 (of_decide_eq_true rfl))
  have e_v1616 : (v1616 = 1 ↔ v1445 = 1 ∨ v1609 = 1) := e_lor h_v1445 h_v1609 (of_decide_eq_true rfl)
  have h_v1618 : R 1 0 4611686018427387904 4611686019501129727 v1618 v1618 := (r1_hxa hb_H3 0 (of_decide_eq_true rfl))
  have e_v1618 : sv v1618 = ((H3 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H3 0 (of_decide_eq_true rfl)
  have h_v1619 : R 1 0 0 1 v1619 v1619 := (r_plt hl h_v61 h_v1618 (of_decide_eq_true rfl))
  have e_v1619 : (v1619 = 1 ↔ sv v61 < sv v1618) := e_plt h_v61 h_v1618 (of_decide_eq_true rfl)
  have h_v1620 : R 1 0 0 1 v1620 v1620 := (r_sub hl (r_O hl) h_v1619 (of_decide_eq_true rfl))
  have e_v1620 : (v1620 = 1 ↔ ¬v1619 = 1) := e_not h_v1619 (of_decide_eq_true rfl)
  have h_t1618_1 : R 1 0 4611686018427387904 4611686018695823363 t1618.1 t1618.1 := r_sc1 hl h_v1618 (of_decide_eq_true rfl)
  have h_t1618_2 : R 1 0 4611686018158952445 4611686018695823363 t1618.2 t1618.2 := r_sc2 hl h_v1618 (of_decide_eq_true rfl)
  have e_t1618_1 : sv t1618.1 = (sc28pS (scArg v1618)).1 := e_sc1 h_v1618 (of_decide_eq_true rfl)
  have e_t1618_2 : sv t1618.2 = (sc28pS (scArg v1618)).2 := e_sc2 h_v1618 (of_decide_eq_true rfl)
  have h_v1622 : R 1 0 4611686018158952441 4611686018695823359 v1622 v1622 := (r_sub hl (r_add hl h_v28 h_t1618_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1622 : sv v1622 = sv v28 + sv t1618.2 := e_add h_v28 h_t1618_2 (of_decide_eq_true rfl)
  have h_v1623 : R 1 0 0 1 v1623 v1623 := (r_plt hl h_v1622 h_v95 (of_decide_eq_true rfl))
  have e_v1623 : (v1623 = 1 ↔ sv v1622 < sv v95) := e_plt h_v1622 h_v95 (of_decide_eq_true rfl)
  have h_v1624 : R 1 0 4611686018158952441 4611686018695823359 v1624 v1624 := (r_psel hl h_v1623 h_v95 h_v1622 (of_decide_eq_true rfl))
  have e_v1624 : v1624 = if v1623 = 1 then v95 else v1622 := e_psel h_v1623 h_v95 h_v1622 (of_decide_eq_true rfl)
  have h_v1625 : R 1 0 4467570782033149952 4755801223146242048 v1625 v1625 := (r_sshl hl h_v1449 4467570782033149952 4755801223146242048 (of_decide_eq_true rfl))
  clear h_v1445 h_v1505 h_v1603 h_v1605 h_v1609 h_v1612 h_v1613 h_v1619 h_v1622 h_v1623
  have e_v1625 : sv v1625 = sv v1449 * 2 ^ 28 := e_sshl h_v1449 4467570782033149952 4755801223146242048 (of_decide_eq_true rfl)
  have h_v1626 : R 1 0 4539628420094492609 4683743614612799479 v1626 v1626 := (r_smx hl 29 h_v1624 h_v1450 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl))
  have e_v1626 : sv v1626 = sv v1624 * sv v1450 := e_smx 29 h_v1624 h_v1450 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl)
  have h_v1627 : R 1 0 0 1 v1627 v1627 := (r_plt hl h_v1626 h_v1625 (of_decide_eq_true rfl))
  have e_v1627 : (v1627 = 1 ↔ sv v1626 < sv v1625) := e_plt h_v1626 h_v1625 (of_decide_eq_true rfl)
  have h_v1628 : R 1 0 0 1 v1628 v1628 := (r_sub hl (r_O hl) h_v1627 (of_decide_eq_true rfl))
  have e_v1628 : (v1628 = 1 ↔ ¬v1627 = 1) := e_not h_v1627 (of_decide_eq_true rfl)
  have h_v1629 : R 1 0 0 1 v1629 v1629 := (r_plt hl h_v15 h_v1618 (of_decide_eq_true rfl))
  have e_v1629 : (v1629 = 1 ↔ sv v15 < sv v1618) := e_plt h_v15 h_v1618 (of_decide_eq_true rfl)
  have h_v1630 : R 1 0 0 1 v1630 v1630 := (r_sub hl (r_O hl) h_v1629 (of_decide_eq_true rfl))
  have e_v1630 : (v1630 = 1 ↔ ¬v1629 = 1) := e_not h_v1629 (of_decide_eq_true rfl)
  have h_v1631 : R 1 0 0 1 v1631 v1631 := (r_land hl h_v1628 h_v1630 (of_decide_eq_true rfl))
  have e_v1631 : (v1631 = 1 ↔ v1628 = 1 ∧ v1630 = 1) := e_land h_v1628 h_v1630 (of_decide_eq_true rfl)
  have h_v1632 : R 1 0 0 1 v1632 v1632 := (r_lor hl h_v1620 h_v1631 (of_decide_eq_true rfl))
  have e_v1632 : (v1632 = 1 ↔ v1620 = 1 ∨ v1631 = 1) := e_lor h_v1620 h_v1631 (of_decide_eq_true rfl)
  have h_v1633 : R 1 0 4611686018427387904 4611686019501129727 v1633 v1633 := (r_psel hl h_v1632 h_v1618 h_v61 (of_decide_eq_true rfl))
  have e_v1633 : v1633 = if v1632 = 1 then v1618 else v61 := e_psel h_v1632 h_v1618 h_v61 (of_decide_eq_true rfl)
  have h_v1634 : R 1 0 4611686018427387904 4611686019501129727 v1634 v1634 := (r1_hxa hb_H3 32 (of_decide_eq_true rfl))
  have e_v1634 : sv v1634 = ((H3 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H3 32 (of_decide_eq_true rfl)
  have h_v1635 : R 1 0 0 1 v1635 v1635 := (r_plt hl h_v1634 h_v9 (of_decide_eq_true rfl))
  have e_v1635 : (v1635 = 1 ↔ sv v1634 < sv v9) := e_plt h_v1634 h_v9 (of_decide_eq_true rfl)
  have h_v1636 : R 1 0 0 1 v1636 v1636 := (r_sub hl (r_O hl) h_v1635 (of_decide_eq_true rfl))
  have e_v1636 : (v1636 = 1 ↔ ¬v1635 = 1) := e_not h_v1635 (of_decide_eq_true rfl)
  have h_t1634_1 : R 1 0 4611686018427387904 4611686018695823363 t1634.1 t1634.1 := r_sc1 hl h_v1634 (of_decide_eq_true rfl)
  have h_t1634_2 : R 1 0 4611686018158952445 4611686018695823363 t1634.2 t1634.2 := r_sc2 hl h_v1634 (of_decide_eq_true rfl)
  clear h_v15 h_v1449 h_v1450 h_v1618 h_v1620 h_v1624 h_v1625 h_v1626 h_v1627 h_v1628 h_v1629 h_v1630 h_v1631 h_v1635
  have e_t1634_1 : sv t1634.1 = (sc28pS (scArg v1634)).1 := e_sc1 h_v1634 (of_decide_eq_true rfl)
  have e_t1634_2 : sv t1634.2 = (sc28pS (scArg v1634)).2 := e_sc2 h_v1634 (of_decide_eq_true rfl)
  have h_v1638 : R 1 0 4611686018158952449 4611686018695823367 v1638 v1638 := (r_sub hl (r_add hl h_v31 h_t1634_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1638 : sv v1638 = sv v31 + sv t1634.2 := e_add h_v31 h_t1634_2 (of_decide_eq_true rfl)
  have h_v1639 : R 1 0 0 1 v1639 v1639 := (r_plt hl h_v1638 h_v33 (of_decide_eq_true rfl))
  have e_v1639 : (v1639 = 1 ↔ sv v1638 < sv v33) := e_plt h_v1638 h_v33 (of_decide_eq_true rfl)
  have h_v1640 : R 1 0 4611686018158952449 4611686018695823367 v1640 v1640 := (r_psel hl h_v1639 h_v1638 h_v33 (of_decide_eq_true rfl))
  have e_v1640 : v1640 = if v1639 = 1 then v1638 else v33 := e_psel h_v1639 h_v1638 h_v33 (of_decide_eq_true rfl)
  have h_v1641 : R 1 0 4467570780154101760 4755801223146242048 v1641 v1641 := (r_sshl hl h_v1614 4467570780154101760 4755801223146242048 (of_decide_eq_true rfl))
  have e_v1641 : sv v1641 = sv v1614 * 2 ^ 28 := e_sshl h_v1614 4467570780154101760 4755801223146242048 (of_decide_eq_true rfl)
  have h_v1642 : R 1 0 4539628422241976329 4683743616760283199 v1642 v1642 := (r_smx hl 29 h_v1640 h_v1615 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl))
  have e_v1642 : sv v1642 = sv v1640 * sv v1615 := e_smx 29 h_v1640 h_v1615 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl)
  have h_v1643 : R 1 0 0 1 v1643 v1643 := (r_plt hl h_v1641 h_v1642 (of_decide_eq_true rfl))
  have e_v1643 : (v1643 = 1 ↔ sv v1641 < sv v1642) := e_plt h_v1641 h_v1642 (of_decide_eq_true rfl)
  have h_v1644 : R 1 0 0 1 v1644 v1644 := (r_sub hl (r_O hl) h_v1643 (of_decide_eq_true rfl))
  have e_v1644 : (v1644 = 1 ↔ ¬v1643 = 1) := e_not h_v1643 (of_decide_eq_true rfl)
  have h_v1645 : R 1 0 0 1 v1645 v1645 := (r_lor hl h_v1636 h_v1644 (of_decide_eq_true rfl))
  have e_v1645 : (v1645 = 1 ↔ v1636 = 1 ∨ v1644 = 1) := e_lor h_v1636 h_v1644 (of_decide_eq_true rfl)
  have h_v1646 : R 1 0 4611686018427387904 4611686019501129727 v1646 v1646 := (r_psel hl h_v1645 h_v1634 h_v9 (of_decide_eq_true rfl))
  have e_v1646 : v1646 = if v1645 = 1 then v1634 else v9 := e_psel h_v1645 h_v1634 h_v9 (of_decide_eq_true rfl)
  have h_v1647 : R 1 0 4611686018427387904 4611686019501129727 v1647 v1647 := (r_psel hl h_v778 h_v1633 h_v61 (of_decide_eq_true rfl))
  have e_v1647 : v1647 = if v778 = 1 then v1633 else v61 := e_psel h_v778 h_v1633 h_v61 (of_decide_eq_true rfl)
  have h_v1648 : R 1 0 4611686018427387904 4611686019501129727 v1648 v1648 := (r_psel hl h_v778 h_v1646 h_v9 (of_decide_eq_true rfl))
  have e_v1648 : v1648 = if v778 = 1 then v1646 else v9 := e_psel h_v778 h_v1646 h_v9 (of_decide_eq_true rfl)
  have h_v1649 : R 1 0 0 1 v1649 v1649 := (r_land hl h_v778 h_v1616 (of_decide_eq_true rfl))
  clear h_v1614 h_v1615 h_v1633 h_v1634 h_v1636 h_v1638 h_v1639 h_v1640 h_v1641 h_v1642 h_v1643 h_v1644 h_v1646
  have e_v1649 : (v1649 = 1 ↔ v778 = 1 ∧ v1616 = 1) := e_land h_v778 h_v1616 (of_decide_eq_true rfl)
  have h_v1652 : R 1 0 0 1 v1652 v1652 := (r_sub hl (r_O hl) h_v1649 (of_decide_eq_true rfl))
  have e_v1652 : (v1652 = 1 ↔ ¬v1649 = 1) := e_not h_v1649 (of_decide_eq_true rfl)
  have h_v1654 : R 1 0 4611686017353646081 4611686020574871550 v1654 v1654 := (r_sub hl (r_add hl h_v397 h_v1248 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1654 : sv v1654 = sv v397 + sv v1248 := e_add h_v397 h_v1248 (of_decide_eq_true rfl)
  have h_v1656 : R 1 0 4611686017353646081 4611686020574871550 v1656 v1656 := (r_sub hl (r_add hl h_v722 h_v1648 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1656 : sv v1656 = sv v722 + sv v1648 := e_add h_v722 h_v1648 (of_decide_eq_true rfl)
  have h_v1657 : R 1 0 0 1 v1657 v1657 := (r_plt hl h_v3 h_v9 (of_decide_eq_true rfl))
  have e_v1657 : (v1657 = 1 ↔ sv v3 < sv v9) := e_plt h_v3 h_v9 (of_decide_eq_true rfl)
  have h_v1658 : R 1 0 0 1 v1658 v1658 := (r_plt hl h_v1654 h_v9 (of_decide_eq_true rfl))
  have e_v1658 : (v1658 = 1 ↔ sv v1654 < sv v9) := e_plt h_v1654 h_v9 (of_decide_eq_true rfl)
  have h_v1659 : R 1 0 0 1 v1659 v1659 := (r_land hl h_v1657 h_v1658 (of_decide_eq_true rfl))
  have e_v1659 : (v1659 = 1 ↔ v1657 = 1 ∧ v1658 = 1) := e_land h_v1657 h_v1658 (of_decide_eq_true rfl)
  have h_v1661 : R 1 0 0 1 v1661 v1661 := (r_lor hl h_v23 h_v1659 (of_decide_eq_true rfl))
  have e_v1661 : (v1661 = 1 ↔ v23 = 1 ∨ v1659 = 1) := e_lor h_v23 h_v1659 (of_decide_eq_true rfl)
  have h_v1662 : R 1 0 0 1 v1662 v1662 := (r_lor hl h_v47 h_v1659 (of_decide_eq_true rfl))
  have e_v1662 : (v1662 = 1 ↔ v47 = 1 ∨ v1659 = 1) := e_lor h_v47 h_v1659 (of_decide_eq_true rfl)
  have h_v1663 : R 1 0 0 1 v1663 v1663 := (r_land hl h_v73 h_v139 (of_decide_eq_true rfl))
  have e_v1663 : (v1663 = 1 ↔ v73 = 1 ∧ v139 = 1) := e_land h_v73 h_v139 (of_decide_eq_true rfl)
  have h_v1664 : R 1 0 0 1 v1664 v1664 := (r_sub hl (r_O hl) h_v1663 (of_decide_eq_true rfl))
  have e_v1664 : (v1664 = 1 ↔ ¬v1663 = 1) := e_not h_v1663 (of_decide_eq_true rfl)
  have h_v1665 : R 1 0 0 1 v1665 v1665 := (r_lor hl h_v1659 h_v1664 (of_decide_eq_true rfl))
  have e_v1665 : (v1665 = 1 ↔ v1659 = 1 ∨ v1664 = 1) := e_lor h_v1659 h_v1664 (of_decide_eq_true rfl)
  have h_v1666 : R 1 0 0 1 v1666 v1666 := (r_land hl h_v73 h_v135 (of_decide_eq_true rfl))
  have e_v1666 : (v1666 = 1 ↔ v73 = 1 ∧ v135 = 1) := e_land h_v73 h_v135 (of_decide_eq_true rfl)
  clear h_v3 h_v1616 h_v1649 h_v1654 h_v1657 h_v1658 h_v1663 h_v1664
  have h_v1667 : R 1 0 0 1 v1667 v1667 := (r_lor hl h_v72 h_v1666 (of_decide_eq_true rfl))
  have e_v1667 : (v1667 = 1 ↔ v72 = 1 ∨ v1666 = 1) := e_lor h_v72 h_v1666 (of_decide_eq_true rfl)
  have h_v1668 : R 1 0 4611686018158952441 4611686018695823367 v1668 v1668 := (r_psel hl h_v1667 h_v107 h_v100 (of_decide_eq_true rfl))
  have e_v1668 : v1668 = if v1667 = 1 then v107 else v100 := e_psel h_v1667 h_v107 h_v100 (of_decide_eq_true rfl)
  have h_v1669 : R 1 0 0 1 v1669 v1669 := (r_land hl h_v69 h_v139 (of_decide_eq_true rfl))
  have e_v1669 : (v1669 = 1 ↔ v69 = 1 ∧ v139 = 1) := e_land h_v69 h_v139 (of_decide_eq_true rfl)
  have h_v1670 : R 1 0 0 1 v1670 v1670 := (r_lor hl h_v138 h_v1669 (of_decide_eq_true rfl))
  have e_v1670 : (v1670 = 1 ↔ v138 = 1 ∨ v1669 = 1) := e_lor h_v138 h_v1669 (of_decide_eq_true rfl)
  have h_v1671 : R 1 0 4611686018427387900 4611686018695823367 v1671 v1671 := (r_psel hl h_v1670 h_v60 h_v52 (of_decide_eq_true rfl))
  have e_v1671 : v1671 = if v1670 = 1 then v60 else v52 := e_psel h_v1670 h_v60 h_v52 (of_decide_eq_true rfl)
  have h_v1678 : R 1 0 4539628420631363535 4683743616223412273 v1678 v1678 := (r_smx hl 29 h_v1671 h_v1668 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v1678 : sv v1678 = sv v1671 * sv v1668 := e_smx 29 h_v1671 h_v1668 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v1679 : R 1 0 4611686018158952433 4611686018695823374 v1679 v1679 := (r_srdF hl h_v1678 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v1679 : sv v1679 = sv v1678 / 2 ^ 28 := e_srdF h_v1678 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v1682 : R 1 0 0 1 v1682 v1682 := (r_plt hl h_v19 h_v1247 (of_decide_eq_true rfl))
  have e_v1682 : (v1682 = 1 ↔ sv v19 < sv v1247) := e_plt h_v19 h_v1247 (of_decide_eq_true rfl)
  have h_v1683 : R 1 0 0 1 v1683 v1683 := (r_plt hl h_v9 h_v1248 (of_decide_eq_true rfl))
  have e_v1683 : (v1683 = 1 ↔ sv v9 < sv v1248) := e_plt h_v9 h_v1248 (of_decide_eq_true rfl)
  have h_v1684 : R 1 0 0 1 v1684 v1684 := (r_sub hl (r_O hl) h_v1683 (of_decide_eq_true rfl))
  have e_v1684 : (v1684 = 1 ↔ ¬v1683 = 1) := e_not h_v1683 (of_decide_eq_true rfl)
  have h_v1685 : R 1 0 0 1 v1685 v1685 := (r_land hl h_v1682 h_v1684 (of_decide_eq_true rfl))
  have e_v1685 : (v1685 = 1 ↔ v1682 = 1 ∧ v1684 = 1) := e_land h_v1682 h_v1684 (of_decide_eq_true rfl)
  have h_v1686 : R 1 0 0 1 v1686 v1686 := (r_lor hl h_v1659 h_v1685 (of_decide_eq_true rfl))
  have e_v1686 : (v1686 = 1 ↔ v1659 = 1 ∨ v1685 = 1) := e_lor h_v1659 h_v1685 (of_decide_eq_true rfl)
  have h_v1687 : R 1 0 4611686018158952445 4611686018695823363 v1687 v1687 := (r_psel hl h_v1245 h_t1234_2 h_v95 (of_decide_eq_true rfl))
  clear h_v1666 h_v1667 h_v1668 h_v1669 h_v1670 h_v1671 h_v1678 h_v1682 h_v1683 h_v1684 h_v1685
  have e_v1687 : v1687 = if v1245 = 1 then t1234.2 else v95 := e_psel h_v1245 h_t1234_2 h_v95 (of_decide_eq_true rfl)
  have h_v1688 : R 1 0 4611686018158952445 4611686018695823363 v1688 v1688 := (r_psel hl h_v778 h_v1687 h_v95 (of_decide_eq_true rfl))
  have e_v1688 : v1688 = if v778 = 1 then v1687 else v95 := e_psel h_v778 h_v1687 h_v95 (of_decide_eq_true rfl)
  have h_v1689 : R 1 0 4611686018158952441 4611686018695823359 v1689 v1689 := (r_sub hl (r_add hl h_v28 h_v1688 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1689 : sv v1689 = sv v28 + sv v1688 := e_add h_v28 h_v1688 (of_decide_eq_true rfl)
  have h_v1690 : R 1 0 0 1 v1690 v1690 := (r_plt hl h_v1689 h_v95 (of_decide_eq_true rfl))
  have e_v1690 : (v1690 = 1 ↔ sv v1689 < sv v95) := e_plt h_v1689 h_v95 (of_decide_eq_true rfl)
  have h_v1691 : R 1 0 4611686018158952441 4611686018695823359 v1691 v1691 := (r_psel hl h_v1690 h_v95 h_v1689 (of_decide_eq_true rfl))
  have e_v1691 : v1691 = if v1690 = 1 then v95 else v1689 := e_psel h_v1690 h_v95 h_v1689 (of_decide_eq_true rfl)
  have h_v1692 : R 1 0 0 1 v1692 v1692 := (r_plt hl h_v98 h_v1248 (of_decide_eq_true rfl))
  have e_v1692 : (v1692 = 1 ↔ sv v98 < sv v1248) := e_plt h_v98 h_v1248 (of_decide_eq_true rfl)
  have h_v1693 : R 1 0 4611686018158952441 4611686018695823359 v1693 v1693 := (r_psel hl h_v1692 h_v95 h_v1691 (of_decide_eq_true rfl))
  have e_v1693 : v1693 = if v1692 = 1 then v95 else v1691 := e_psel h_v1692 h_v95 h_v1691 (of_decide_eq_true rfl)
  have h_v1694 : R 1 0 4611686018158952445 4611686018695823363 v1694 v1694 := (r_psel hl h_v1232 h_t1218_2 h_v33 (of_decide_eq_true rfl))
  have e_v1694 : v1694 = if v1232 = 1 then t1218.2 else v33 := e_psel h_v1232 h_t1218_2 h_v33 (of_decide_eq_true rfl)
  have h_v1695 : R 1 0 4611686018158952445 4611686018695823363 v1695 v1695 := (r_psel hl h_v778 h_v1694 h_v33 (of_decide_eq_true rfl))
  have e_v1695 : v1695 = if v778 = 1 then v1694 else v33 := e_psel h_v778 h_v1694 h_v33 (of_decide_eq_true rfl)
  have h_v1696 : R 1 0 4611686018158952449 4611686018695823367 v1696 v1696 := (r_sub hl (r_add hl h_v31 h_v1695 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1696 : sv v1696 = sv v31 + sv v1695 := e_add h_v31 h_v1695 (of_decide_eq_true rfl)
  have h_v1697 : R 1 0 0 1 v1697 v1697 := (r_plt hl h_v1696 h_v33 (of_decide_eq_true rfl))
  have e_v1697 : (v1697 = 1 ↔ sv v1696 < sv v33) := e_plt h_v1696 h_v33 (of_decide_eq_true rfl)
  have h_v1698 : R 1 0 4611686018158952449 4611686018695823367 v1698 v1698 := (r_psel hl h_v1697 h_v1696 h_v33 (of_decide_eq_true rfl))
  have e_v1698 : v1698 = if v1697 = 1 then v1696 else v33 := e_psel h_v1697 h_v1696 h_v33 (of_decide_eq_true rfl)
  have h_v1699 : R 1 0 0 1 v1699 v1699 := (r_plt hl h_v1247 h_v105 (of_decide_eq_true rfl))
  have e_v1699 : (v1699 = 1 ↔ sv v1247 < sv v105) := e_plt h_v1247 h_v105 (of_decide_eq_true rfl)
  clear h_v1687 h_v1688 h_v1689 h_v1690 h_v1691 h_v1692 h_v1694 h_v1695 h_v1696 h_v1697
  have h_v1700 : R 1 0 4611686018158952449 4611686018695823367 v1700 v1700 := (r_psel hl h_v1699 h_v33 h_v1698 (of_decide_eq_true rfl))
  have e_v1700 : v1700 = if v1699 = 1 then v33 else v1698 := e_psel h_v1699 h_v33 h_v1698 (of_decide_eq_true rfl)
  have h_v1702 : R 1 0 4611686018427387904 4611686018695823363 v1702 v1702 := (r_psel hl h_v1232 h_t1218_1 h_v61 (of_decide_eq_true rfl))
  have e_v1702 : v1702 = if v1232 = 1 then t1218.1 else v61 := e_psel h_v1232 h_t1218_1 h_v61 (of_decide_eq_true rfl)
  have h_v1703 : R 1 0 4611686018427387904 4611686018695823363 v1703 v1703 := (r_psel hl h_v778 h_v1702 h_v61 (of_decide_eq_true rfl))
  have e_v1703 : v1703 = if v778 = 1 then v1702 else v61 := e_psel h_v778 h_v1702 h_v61 (of_decide_eq_true rfl)
  have h_v1705 : R 1 0 4611686018427387904 4611686018695823363 v1705 v1705 := (r_psel hl h_v1245 h_t1234_1 h_v61 (of_decide_eq_true rfl))
  have e_v1705 : v1705 = if v1245 = 1 then t1234.1 else v61 := e_psel h_v1245 h_t1234_1 h_v61 (of_decide_eq_true rfl)
  have h_v1706 : R 1 0 4611686018427387904 4611686018695823363 v1706 v1706 := (r_psel hl h_v778 h_v1705 h_v61 (of_decide_eq_true rfl))
  have e_v1706 : v1706 = if v778 = 1 then v1705 else v61 := e_psel h_v778 h_v1705 h_v61 (of_decide_eq_true rfl)
  have h_v1707 : R 1 0 0 1 v1707 v1707 := (r_plt hl h_v1703 h_v1706 (of_decide_eq_true rfl))
  have e_v1707 : (v1707 = 1 ↔ sv v1703 < sv v1706) := e_plt h_v1703 h_v1706 (of_decide_eq_true rfl)
  have h_v1708 : R 1 0 4611686018427387904 4611686018695823363 v1708 v1708 := (r_psel hl h_v1707 h_v1703 h_v1706 (of_decide_eq_true rfl))
  have e_v1708 : v1708 = if v1707 = 1 then v1703 else v1706 := e_psel h_v1707 h_v1703 h_v1706 (of_decide_eq_true rfl)
  have h_v1709 : R 1 0 4611686018427387900 4611686018695823359 v1709 v1709 := (r_sub hl (r_add hl h_v28 h_v1708 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1709 : sv v1709 = sv v28 + sv v1708 := e_add h_v28 h_v1708 (of_decide_eq_true rfl)
  have h_v1710 : R 1 0 4611686018427387904 4611686018695823363 v1710 v1710 := (r_psel hl h_v1707 h_v1706 h_v1703 (of_decide_eq_true rfl))
  have e_v1710 : v1710 = if v1707 = 1 then v1706 else v1703 := e_psel h_v1707 h_v1706 h_v1703 (of_decide_eq_true rfl)
  have h_v1711 : R 1 0 4611686018427387908 4611686018695823367 v1711 v1711 := (r_sub hl (r_add hl h_v31 h_v1710 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1711 : sv v1711 = sv v31 + sv v1710 := e_add h_v31 h_v1710 (of_decide_eq_true rfl)
  have h_v1712 : R 1 0 0 1 v1712 v1712 := (r_plt hl h_v1711 h_v33 (of_decide_eq_true rfl))
  have e_v1712 : (v1712 = 1 ↔ sv v1711 < sv v33) := e_plt h_v1711 h_v33 (of_decide_eq_true rfl)
  have h_v1713 : R 1 0 4611686018427387908 4611686018695823367 v1713 v1713 := (r_psel hl h_v1712 h_v1711 h_v33 (of_decide_eq_true rfl))
  have e_v1713 : v1713 = if v1712 = 1 then v1711 else v33 := e_psel h_v1712 h_v1711 h_v33 (of_decide_eq_true rfl)
  have h_v1714 : R 1 0 0 1 v1714 v1714 := (r_plt hl h_v1247 h_v36 (of_decide_eq_true rfl))
  clear h_v1698 h_v1699 h_v1702 h_v1703 h_v1705 h_v1706 h_v1707 h_v1708 h_v1710 h_v1711 h_v1712
  have e_v1714 : (v1714 = 1 ↔ sv v1247 < sv v36) := e_plt h_v1247 h_v36 (of_decide_eq_true rfl)
  have h_v1715 : R 1 0 0 1 v1715 v1715 := (r_plt hl h_v38 h_v1248 (of_decide_eq_true rfl))
  have e_v1715 : (v1715 = 1 ↔ sv v38 < sv v1248) := e_plt h_v38 h_v1248 (of_decide_eq_true rfl)
  have h_v1716 : R 1 0 0 1 v1716 v1716 := (r_land hl h_v1714 h_v1715 (of_decide_eq_true rfl))
  have e_v1716 : (v1716 = 1 ↔ v1714 = 1 ∧ v1715 = 1) := e_land h_v1714 h_v1715 (of_decide_eq_true rfl)
  have h_v1717 : R 1 0 4611686018427387908 4611686018695823367 v1717 v1717 := (r_psel hl h_v1716 h_v33 h_v1713 (of_decide_eq_true rfl))
  have e_v1717 : v1717 = if v1716 = 1 then v33 else v1713 := e_psel h_v1716 h_v33 h_v1713 (of_decide_eq_true rfl)
  have h_v1718 : R 1 0 0 1 v1718 v1718 := (r_plt hl h_v61 h_v1709 (of_decide_eq_true rfl))
  have e_v1718 : (v1718 = 1 ↔ sv v61 < sv v1709) := e_plt h_v61 h_v1709 (of_decide_eq_true rfl)
  have h_v1719 : R 1 0 0 1 v1719 v1719 := (r_sub hl (r_O hl) h_v1718 (of_decide_eq_true rfl))
  have e_v1719 : (v1719 = 1 ↔ ¬v1718 = 1) := e_not h_v1718 (of_decide_eq_true rfl)
  have h_v1720 : R 1 0 0 1 v1720 v1720 := (r_plt hl h_v1693 h_v61 (of_decide_eq_true rfl))
  have e_v1720 : (v1720 = 1 ↔ sv v1693 < sv v61) := e_plt h_v1693 h_v61 (of_decide_eq_true rfl)
  have h_v1721 : R 1 0 4611686018427387900 4611686018695823367 v1721 v1721 := (r_psel hl h_v1720 h_v1709 h_v1717 (of_decide_eq_true rfl))
  have e_v1721 : v1721 = if v1720 = 1 then v1709 else v1717 := e_psel h_v1720 h_v1709 h_v1717 (of_decide_eq_true rfl)
  have h_v1722 : R 1 0 0 1 v1722 v1722 := (r_plt hl h_v1700 h_v61 (of_decide_eq_true rfl))
  have e_v1722 : (v1722 = 1 ↔ sv v1700 < sv v61) := e_plt h_v1700 h_v61 (of_decide_eq_true rfl)
  have h_v1723 : R 1 0 4611686018427387900 4611686018695823367 v1723 v1723 := (r_psel hl h_v1722 h_v1717 h_v1709 (of_decide_eq_true rfl))
  have e_v1723 : v1723 = if v1722 = 1 then v1717 else v1709 := e_psel h_v1722 h_v1717 h_v1709 (of_decide_eq_true rfl)
  have h_v1724 : R 1 0 0 1 v1724 v1724 := (r_lor hl h_v47 h_v1719 (of_decide_eq_true rfl))
  have e_v1724 : (v1724 = 1 ↔ v47 = 1 ∨ v1719 = 1) := e_lor h_v47 h_v1719 (of_decide_eq_true rfl)
  have h_v1725 : R 1 0 0 1 v1725 v1725 := (r_lor hl h_v1659 h_v1724 (of_decide_eq_true rfl))
  have e_v1725 : (v1725 = 1 ↔ v1659 = 1 ∨ v1724 = 1) := e_lor h_v1659 h_v1724 (of_decide_eq_true rfl)
  have h_v1726 : R 1 0 0 1 v1726 v1726 := (r_sub hl (r_O hl) h_v1720 (of_decide_eq_true rfl))
  have e_v1726 : (v1726 = 1 ↔ ¬v1720 = 1) := e_not h_v1720 (of_decide_eq_true rfl)
  clear h_v36 h_v38 h_v1247 h_v1248 h_v1709 h_v1713 h_v1714 h_v1715 h_v1716 h_v1717 h_v1722 h_v1724
  have h_v1727 : R 1 0 0 1 v1727 v1727 := (r_plt hl h_v61 h_v1700 (of_decide_eq_true rfl))
  have e_v1727 : (v1727 = 1 ↔ sv v61 < sv v1700) := e_plt h_v61 h_v1700 (of_decide_eq_true rfl)
  have h_v1728 : R 1 0 0 1 v1728 v1728 := (r_sub hl (r_O hl) h_v1727 (of_decide_eq_true rfl))
  have e_v1728 : (v1728 = 1 ↔ ¬v1727 = 1) := e_not h_v1727 (of_decide_eq_true rfl)
  have h_v1729 : R 1 0 0 1 v1729 v1729 := (r_land hl h_v1720 h_v1728 (of_decide_eq_true rfl))
  have e_v1729 : (v1729 = 1 ↔ v1720 = 1 ∧ v1728 = 1) := e_land h_v1720 h_v1728 (of_decide_eq_true rfl)
  have h_v1730 : R 1 0 0 1 v1730 v1730 := (r_land hl h_v1720 h_v1727 (of_decide_eq_true rfl))
  have e_v1730 : (v1730 = 1 ↔ v1720 = 1 ∧ v1727 = 1) := e_land h_v1720 h_v1727 (of_decide_eq_true rfl)
  have h_v1731 : R 1 0 0 1 v1731 v1731 := (r_plt hl h_v61 h_v272 (of_decide_eq_true rfl))
  have e_v1731 : (v1731 = 1 ↔ sv v61 < sv v272) := e_plt h_v61 h_v272 (of_decide_eq_true rfl)
  have h_v1732 : R 1 0 0 1 v1732 v1732 := (r_sub hl (r_O hl) h_v1731 (of_decide_eq_true rfl))
  have e_v1732 : (v1732 = 1 ↔ ¬v1731 = 1) := e_not h_v1731 (of_decide_eq_true rfl)
  have h_v1733 : R 1 0 0 1 v1733 v1733 := (r_land hl h_v166 h_v1732 (of_decide_eq_true rfl))
  have e_v1733 : (v1733 = 1 ↔ v166 = 1 ∧ v1732 = 1) := e_land h_v166 h_v1732 (of_decide_eq_true rfl)
  have h_v1734 : R 1 0 0 1 v1734 v1734 := (r_land hl h_v166 h_v1731 (of_decide_eq_true rfl))
  have e_v1734 : (v1734 = 1 ↔ v166 = 1 ∧ v1731 = 1) := e_land h_v166 h_v1731 (of_decide_eq_true rfl)
  have h_v1735 : R 1 0 0 1 v1735 v1735 := (r_land hl h_v1730 h_v1734 (of_decide_eq_true rfl))
  have e_v1735 : (v1735 = 1 ↔ v1730 = 1 ∧ v1734 = 1) := e_land h_v1730 h_v1734 (of_decide_eq_true rfl)
  have h_v1736 : R 1 0 0 1 v1736 v1736 := (r_sub hl (r_O hl) h_v1735 (of_decide_eq_true rfl))
  have e_v1736 : (v1736 = 1 ↔ ¬v1735 = 1) := e_not h_v1735 (of_decide_eq_true rfl)
  have h_v1737 : R 1 0 0 1 v1737 v1737 := (r_lor hl h_v1719 h_v1736 (of_decide_eq_true rfl))
  have e_v1737 : (v1737 = 1 ↔ v1719 = 1 ∨ v1736 = 1) := e_lor h_v1719 h_v1736 (of_decide_eq_true rfl)
  have h_v1738 : R 1 0 0 1 v1738 v1738 := (r_lor hl h_v1659 h_v1737 (of_decide_eq_true rfl))
  have e_v1738 : (v1738 = 1 ↔ v1659 = 1 ∨ v1737 = 1) := e_lor h_v1659 h_v1737 (of_decide_eq_true rfl)
  have h_v1739 : R 1 0 0 1 v1739 v1739 := (r_land hl h_v1726 h_v1734 (of_decide_eq_true rfl))
  clear h_v1719 h_v1720 h_v1727 h_v1728 h_v1731 h_v1732 h_v1735 h_v1736 h_v1737
  have e_v1739 : (v1739 = 1 ↔ v1726 = 1 ∧ v1734 = 1) := e_land h_v1726 h_v1734 (of_decide_eq_true rfl)
  have h_v1740 : R 1 0 0 1 v1740 v1740 := (r_lor hl h_v1733 h_v1739 (of_decide_eq_true rfl))
  have e_v1740 : (v1740 = 1 ↔ v1733 = 1 ∨ v1739 = 1) := e_lor h_v1733 h_v1739 (of_decide_eq_true rfl)
  have h_v1741 : R 1 0 4611686018158952441 4611686018695823367 v1741 v1741 := (r_psel hl h_v1740 h_v1700 h_v1693 (of_decide_eq_true rfl))
  have e_v1741 : v1741 = if v1740 = 1 then v1700 else v1693 := e_psel h_v1740 h_v1700 h_v1693 (of_decide_eq_true rfl)
  have h_v1742 : R 1 0 4611686018427387900 4611686018695823367 v1742 v1742 := (r_psel hl h_v1740 h_v1723 h_v1721 (of_decide_eq_true rfl))
  have e_v1742 : v1742 = if v1740 = 1 then v1723 else v1721 := e_psel h_v1740 h_v1723 h_v1721 (of_decide_eq_true rfl)
  have h_v1743 : R 1 0 0 1 v1743 v1743 := (r_land hl h_v173 h_v1730 (of_decide_eq_true rfl))
  have e_v1743 : (v1743 = 1 ↔ v173 = 1 ∧ v1730 = 1) := e_land h_v173 h_v1730 (of_decide_eq_true rfl)
  have h_v1744 : R 1 0 0 1 v1744 v1744 := (r_lor hl h_v1729 h_v1743 (of_decide_eq_true rfl))
  have e_v1744 : (v1744 = 1 ↔ v1729 = 1 ∨ v1743 = 1) := e_lor h_v1729 h_v1743 (of_decide_eq_true rfl)
  have h_v1745 : R 1 0 4611686018158952441 4611686018695823367 v1745 v1745 := (r_psel hl h_v1744 h_v272 h_v116 (of_decide_eq_true rfl))
  have e_v1745 : v1745 = if v1744 = 1 then v272 else v116 := e_psel h_v1744 h_v272 h_v116 (of_decide_eq_true rfl)
  have h_v1746 : R 1 0 4611686018158952434 4611686018695823375 v1746 v1746 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v1679 (of_decide_eq_true rfl))
  have e_v1746 : sv v1746 = sv v61 - sv v1679 := e_sub h_v61 h_v1679 (of_decide_eq_true rfl)
  have h_v1747 : R 1 0 4539628418752315294 4683743618370895977 v1747 v1747 := (r_smx hl 29 h_v1746 h_v1742 4539628418752315294 4683743618370895977 (of_decide_eq_true rfl))
  have e_v1747 : sv v1747 = sv v1746 * sv v1742 := e_smx 29 h_v1746 h_v1742 4539628418752315294 4683743618370895977 (of_decide_eq_true rfl)
  have h_v1748 : R 1 0 4539628420631363535 4683743616223412273 v1748 v1748 := (r_smx hl 29 h_v1745 h_v1741 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v1748 : sv v1748 = sv v1745 * sv v1741 := e_smx 29 h_v1745 h_v1741 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v1749 : R 1 0 0 1 v1749 v1749 := (r_plt hl h_v1747 h_v1748 (of_decide_eq_true rfl))
  have e_v1749 : (v1749 = 1 ↔ sv v1747 < sv v1748) := e_plt h_v1747 h_v1748 (of_decide_eq_true rfl)
  have h_v1750 : R 1 0 0 1 v1750 v1750 := (r_land hl h_v1718 h_v1749 (of_decide_eq_true rfl))
  have e_v1750 : (v1750 = 1 ↔ v1718 = 1 ∧ v1749 = 1) := e_land h_v1718 h_v1749 (of_decide_eq_true rfl)
  have h_v1751 : R 1 0 0 1 v1751 v1751 := (r_lor hl h_v1659 h_v1750 (of_decide_eq_true rfl))
  have e_v1751 : (v1751 = 1 ↔ v1659 = 1 ∨ v1750 = 1) := e_lor h_v1659 h_v1750 (of_decide_eq_true rfl)
  clear h_v1659 h_v1679 h_v1693 h_v1700 h_v1718 h_v1721 h_v1723 h_v1726 h_v1729 h_v1730 h_v1733 h_v1734 h_v1739 h_v1740 h_v1741 h_v1742 h_v1743 h_v1744 h_v1745 h_v1746 h_v1747 h_v1748 h_v1749 h_v1750
  have h_v1752 : R 1 0 0 1 v1752 v1752 := (r_plt hl h_v5 h_v9 (of_decide_eq_true rfl))
  have e_v1752 : (v1752 = 1 ↔ sv v5 < sv v9) := e_plt h_v5 h_v9 (of_decide_eq_true rfl)
  have h_v1753 : R 1 0 0 1 v1753 v1753 := (r_plt hl h_v1656 h_v9 (of_decide_eq_true rfl))
  have e_v1753 : (v1753 = 1 ↔ sv v1656 < sv v9) := e_plt h_v1656 h_v9 (of_decide_eq_true rfl)
  have h_v1754 : R 1 0 0 1 v1754 v1754 := (r_land hl h_v1752 h_v1753 (of_decide_eq_true rfl))
  have e_v1754 : (v1754 = 1 ↔ v1752 = 1 ∧ v1753 = 1) := e_land h_v1752 h_v1753 (of_decide_eq_true rfl)
  have h_v1756 : R 1 0 0 1 v1756 v1756 := (r_lor hl h_v23 h_v1754 (of_decide_eq_true rfl))
  have e_v1756 : (v1756 = 1 ↔ v23 = 1 ∨ v1754 = 1) := e_lor h_v23 h_v1754 (of_decide_eq_true rfl)
  have h_v1757 : R 1 0 0 1 v1757 v1757 := (r_lor hl h_v403 h_v1754 (of_decide_eq_true rfl))
  have e_v1757 : (v1757 = 1 ↔ v403 = 1 ∨ v1754 = 1) := e_lor h_v403 h_v1754 (of_decide_eq_true rfl)
  have h_v1758 : R 1 0 0 1 v1758 v1758 := (r_land hl h_v139 h_v422 (of_decide_eq_true rfl))
  have e_v1758 : (v1758 = 1 ↔ v139 = 1 ∧ v422 = 1) := e_land h_v139 h_v422 (of_decide_eq_true rfl)
  have h_v1759 : R 1 0 0 1 v1759 v1759 := (r_sub hl (r_O hl) h_v1758 (of_decide_eq_true rfl))
  have e_v1759 : (v1759 = 1 ↔ ¬v1758 = 1) := e_not h_v1758 (of_decide_eq_true rfl)
  have h_v1760 : R 1 0 0 1 v1760 v1760 := (r_lor hl h_v1754 h_v1759 (of_decide_eq_true rfl))
  have e_v1760 : (v1760 = 1 ↔ v1754 = 1 ∨ v1759 = 1) := e_lor h_v1754 h_v1759 (of_decide_eq_true rfl)
  have h_v1761 : R 1 0 0 1 v1761 v1761 := (r_land hl h_v135 h_v422 (of_decide_eq_true rfl))
  have e_v1761 : (v1761 = 1 ↔ v135 = 1 ∧ v422 = 1) := e_land h_v135 h_v422 (of_decide_eq_true rfl)
  have h_v1762 : R 1 0 0 1 v1762 v1762 := (r_lor hl h_v421 h_v1761 (of_decide_eq_true rfl))
  have e_v1762 : (v1762 = 1 ↔ v421 = 1 ∨ v1761 = 1) := e_lor h_v421 h_v1761 (of_decide_eq_true rfl)
  have h_v1763 : R 1 0 4611686018158952441 4611686018695823367 v1763 v1763 := (r_psel hl h_v1762 h_v107 h_v100 (of_decide_eq_true rfl))
  have e_v1763 : v1763 = if v1762 = 1 then v107 else v100 := e_psel h_v1762 h_v107 h_v100 (of_decide_eq_true rfl)
  have h_v1764 : R 1 0 0 1 v1764 v1764 := (r_land hl h_v139 h_v418 (of_decide_eq_true rfl))
  have e_v1764 : (v1764 = 1 ↔ v139 = 1 ∧ v418 = 1) := e_land h_v139 h_v418 (of_decide_eq_true rfl)
  have h_v1765 : R 1 0 0 1 v1765 v1765 := (r_lor hl h_v138 h_v1764 (of_decide_eq_true rfl))
  clear h_v5 h_v1656 h_v1752 h_v1753 h_v1758 h_v1759 h_v1761 h_v1762
  have e_v1765 : (v1765 = 1 ↔ v138 = 1 ∨ v1764 = 1) := e_lor h_v138 h_v1764 (of_decide_eq_true rfl)
  have h_v1766 : R 1 0 4611686018427387900 4611686018695823367 v1766 v1766 := (r_psel hl h_v1765 h_v416 h_v408 (of_decide_eq_true rfl))
  have e_v1766 : v1766 = if v1765 = 1 then v416 else v408 := e_psel h_v1765 h_v416 h_v408 (of_decide_eq_true rfl)
  have h_v1773 : R 1 0 4539628420631363535 4683743616223412273 v1773 v1773 := (r_smx hl 29 h_v1766 h_v1763 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v1773 : sv v1773 = sv v1766 * sv v1763 := e_smx 29 h_v1766 h_v1763 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v1774 : R 1 0 4611686018158952433 4611686018695823374 v1774 v1774 := (r_srdF hl h_v1773 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v1774 : sv v1774 = sv v1773 / 2 ^ 28 := e_srdF h_v1773 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v1777 : R 1 0 0 1 v1777 v1777 := (r_plt hl h_v19 h_v1647 (of_decide_eq_true rfl))
  have e_v1777 : (v1777 = 1 ↔ sv v19 < sv v1647) := e_plt h_v19 h_v1647 (of_decide_eq_true rfl)
  have h_v1778 : R 1 0 0 1 v1778 v1778 := (r_plt hl h_v9 h_v1648 (of_decide_eq_true rfl))
  have e_v1778 : (v1778 = 1 ↔ sv v9 < sv v1648) := e_plt h_v9 h_v1648 (of_decide_eq_true rfl)
  have h_v1779 : R 1 0 0 1 v1779 v1779 := (r_sub hl (r_O hl) h_v1778 (of_decide_eq_true rfl))
  have e_v1779 : (v1779 = 1 ↔ ¬v1778 = 1) := e_not h_v1778 (of_decide_eq_true rfl)
  have h_v1780 : R 1 0 0 1 v1780 v1780 := (r_land hl h_v1777 h_v1779 (of_decide_eq_true rfl))
  have e_v1780 : (v1780 = 1 ↔ v1777 = 1 ∧ v1779 = 1) := e_land h_v1777 h_v1779 (of_decide_eq_true rfl)
  have h_v1781 : R 1 0 0 1 v1781 v1781 := (r_lor hl h_v1754 h_v1780 (of_decide_eq_true rfl))
  have e_v1781 : (v1781 = 1 ↔ v1754 = 1 ∨ v1780 = 1) := e_lor h_v1754 h_v1780 (of_decide_eq_true rfl)
  have h_v1782 : R 1 0 4611686018158952445 4611686018695823363 v1782 v1782 := (r_psel hl h_v1645 h_t1634_2 h_v95 (of_decide_eq_true rfl))
  have e_v1782 : v1782 = if v1645 = 1 then t1634.2 else v95 := e_psel h_v1645 h_t1634_2 h_v95 (of_decide_eq_true rfl)
  have h_v1783 : R 1 0 4611686018158952445 4611686018695823363 v1783 v1783 := (r_psel hl h_v778 h_v1782 h_v95 (of_decide_eq_true rfl))
  have e_v1783 : v1783 = if v778 = 1 then v1782 else v95 := e_psel h_v778 h_v1782 h_v95 (of_decide_eq_true rfl)
  have h_v1784 : R 1 0 4611686018158952441 4611686018695823359 v1784 v1784 := (r_sub hl (r_add hl h_v28 h_v1783 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1784 : sv v1784 = sv v28 + sv v1783 := e_add h_v28 h_v1783 (of_decide_eq_true rfl)
  have h_v1785 : R 1 0 0 1 v1785 v1785 := (r_plt hl h_v1784 h_v95 (of_decide_eq_true rfl))
  have e_v1785 : (v1785 = 1 ↔ sv v1784 < sv v95) := e_plt h_v1784 h_v95 (of_decide_eq_true rfl)
  clear h_v9 h_v19 h_t1634_2 h_v1763 h_v1764 h_v1765 h_v1766 h_v1773 h_v1777 h_v1778 h_v1779 h_v1780 h_v1782 h_v1783
  have h_v1786 : R 1 0 4611686018158952441 4611686018695823359 v1786 v1786 := (r_psel hl h_v1785 h_v95 h_v1784 (of_decide_eq_true rfl))
  have e_v1786 : v1786 = if v1785 = 1 then v95 else v1784 := e_psel h_v1785 h_v95 h_v1784 (of_decide_eq_true rfl)
  have h_v1787 : R 1 0 0 1 v1787 v1787 := (r_plt hl h_v98 h_v1648 (of_decide_eq_true rfl))
  have e_v1787 : (v1787 = 1 ↔ sv v98 < sv v1648) := e_plt h_v98 h_v1648 (of_decide_eq_true rfl)
  have h_v1788 : R 1 0 4611686018158952441 4611686018695823359 v1788 v1788 := (r_psel hl h_v1787 h_v95 h_v1786 (of_decide_eq_true rfl))
  have e_v1788 : v1788 = if v1787 = 1 then v95 else v1786 := e_psel h_v1787 h_v95 h_v1786 (of_decide_eq_true rfl)
  have h_v1789 : R 1 0 4611686018158952445 4611686018695823363 v1789 v1789 := (r_psel hl h_v1632 h_t1618_2 h_v33 (of_decide_eq_true rfl))
  have e_v1789 : v1789 = if v1632 = 1 then t1618.2 else v33 := e_psel h_v1632 h_t1618_2 h_v33 (of_decide_eq_true rfl)
  have h_v1790 : R 1 0 4611686018158952445 4611686018695823363 v1790 v1790 := (r_psel hl h_v778 h_v1789 h_v33 (of_decide_eq_true rfl))
  have e_v1790 : v1790 = if v778 = 1 then v1789 else v33 := e_psel h_v778 h_v1789 h_v33 (of_decide_eq_true rfl)
  have h_v1791 : R 1 0 4611686018158952449 4611686018695823367 v1791 v1791 := (r_sub hl (r_add hl h_v31 h_v1790 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1791 : sv v1791 = sv v31 + sv v1790 := e_add h_v31 h_v1790 (of_decide_eq_true rfl)
  have h_v1792 : R 1 0 0 1 v1792 v1792 := (r_plt hl h_v1791 h_v33 (of_decide_eq_true rfl))
  have e_v1792 : (v1792 = 1 ↔ sv v1791 < sv v33) := e_plt h_v1791 h_v33 (of_decide_eq_true rfl)
  have h_v1793 : R 1 0 4611686018158952449 4611686018695823367 v1793 v1793 := (r_psel hl h_v1792 h_v1791 h_v33 (of_decide_eq_true rfl))
  have e_v1793 : v1793 = if v1792 = 1 then v1791 else v33 := e_psel h_v1792 h_v1791 h_v33 (of_decide_eq_true rfl)
  have h_v1794 : R 1 0 0 1 v1794 v1794 := (r_plt hl h_v1647 h_v105 (of_decide_eq_true rfl))
  have e_v1794 : (v1794 = 1 ↔ sv v1647 < sv v105) := e_plt h_v1647 h_v105 (of_decide_eq_true rfl)
  have h_v1795 : R 1 0 4611686018158952449 4611686018695823367 v1795 v1795 := (r_psel hl h_v1794 h_v33 h_v1793 (of_decide_eq_true rfl))
  have e_v1795 : v1795 = if v1794 = 1 then v33 else v1793 := e_psel h_v1794 h_v33 h_v1793 (of_decide_eq_true rfl)
  have h_v1797 : R 1 0 4611686018427387904 4611686018695823363 v1797 v1797 := (r_psel hl h_v1632 h_t1618_1 h_v61 (of_decide_eq_true rfl))
  have e_v1797 : v1797 = if v1632 = 1 then t1618.1 else v61 := e_psel h_v1632 h_t1618_1 h_v61 (of_decide_eq_true rfl)
  have h_v1798 : R 1 0 4611686018427387904 4611686018695823363 v1798 v1798 := (r_psel hl h_v778 h_v1797 h_v61 (of_decide_eq_true rfl))
  have e_v1798 : v1798 = if v778 = 1 then v1797 else v61 := e_psel h_v778 h_v1797 h_v61 (of_decide_eq_true rfl)
  have h_v1800 : R 1 0 4611686018427387904 4611686018695823363 v1800 v1800 := (r_psel hl h_v1645 h_t1634_1 h_v61 (of_decide_eq_true rfl))
  clear h_v33 h_v95 h_v98 h_v105 h_t1618_1 h_t1618_2 h_v1632 h_v1784 h_v1785 h_v1786 h_v1787 h_v1789 h_v1790 h_v1791 h_v1792 h_v1793 h_v1794 h_v1797
  have e_v1800 : v1800 = if v1645 = 1 then t1634.1 else v61 := e_psel h_v1645 h_t1634_1 h_v61 (of_decide_eq_true rfl)
  have h_v1801 : R 1 0 4611686018427387904 4611686018695823363 v1801 v1801 := (r_psel hl h_v778 h_v1800 h_v61 (of_decide_eq_true rfl))
  have e_v1801 : v1801 = if v778 = 1 then v1800 else v61 := e_psel h_v778 h_v1800 h_v61 (of_decide_eq_true rfl)
  have h_v1802 : R 1 0 0 1 v1802 v1802 := (r_plt hl h_v1798 h_v1801 (of_decide_eq_true rfl))
  have e_v1802 : (v1802 = 1 ↔ sv v1798 < sv v1801) := e_plt h_v1798 h_v1801 (of_decide_eq_true rfl)
  have h_v1803 : R 1 0 4611686018427387904 4611686018695823363 v1803 v1803 := (r_psel hl h_v1802 h_v1798 h_v1801 (of_decide_eq_true rfl))
  have e_v1803 : v1803 = if v1802 = 1 then v1798 else v1801 := e_psel h_v1802 h_v1798 h_v1801 (of_decide_eq_true rfl)
  have h_v1804 : R 1 0 4611686018427387900 4611686018695823359 v1804 v1804 := (r_sub hl (r_add hl h_v28 h_v1803 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1804 : sv v1804 = sv v28 + sv v1803 := e_add h_v28 h_v1803 (of_decide_eq_true rfl)
  have h_v1805 : R 1 0 4611686018427387904 4611686018695823363 v1805 v1805 := (r_psel hl h_v1802 h_v1801 h_v1798 (of_decide_eq_true rfl))
  have e_v1805 : v1805 = if v1802 = 1 then v1801 else v1798 := e_psel h_v1802 h_v1801 h_v1798 (of_decide_eq_true rfl)
  have h_v1806 : R 1 0 4611686018427387908 4611686018695823367 v1806 v1806 := (r_sub hl (r_add hl h_v31 h_v1805 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1806 : sv v1806 = sv v31 + sv v1805 := e_add h_v31 h_v1805 (of_decide_eq_true rfl)
  exact fun _ k => k e_v1246 e_v1247 e_v1248 e_v1249 h_v1252 e_v1252 e_v1253 e_v1254 h_v1255 e_v1255 e_v1256 e_v1257 e_v1258 e_v1259 e_v1260 e_v1261 e_v1262 e_v1263 e_v1264 e_v1265 e_v1266 e_v1267 e_v1268 e_v1269 e_v1270 e_v1271 e_v1272 e_v1273 e_v1274 e_v1275 e_v1276 e_v1277 e_v1278 e_v1279 e_v1280 e_v1281 e_v1282 e_v1283 e_v1289 e_v1290 e_v1291 e_v1292 e_v1293 e_v1294 e_v1295 e_v1296 e_v1297 e_v1298 e_v1299 e_v1300 e_v1301 e_v1302 e_v1303 e_v1304 e_v1305 e_v1306 e_v1307 e_v1308 e_v1309 e_v1310 e_v1311 e_v1312 e_v1313 e_v1314 e_v1315 e_v1316 e_v1317 e_v1318 e_v1319 e_v1320 e_v1321 e_v1322 h_v1323 e_v1323 e_v1324 e_v1325 e_v1326 e_v1327 e_v1328 e_v1329 e_v1336 e_v1337 e_v1341 e_v1342 e_v1343 e_v1344 e_v1345 e_v1346 e_v1347 e_v1348 e_v1349 e_v1350 e_v1351 e_v1352 e_v1353 e_v1354 e_v1355 e_v1356 e_v1357 e_v1358 e_v1359 e_v1360 e_v1361 e_v1362 e_v1363 e_v1364 e_v1365 e_v1366 e_v1367 e_v1368 e_v1369 e_v1370 e_v1371 e_v1372 e_v1373 e_v1374 e_v1375 e_v1376 e_v1377 e_v1378 e_v1379 e_v1380 e_v1381 e_v1382 e_v1383 e_v1384 e_v1385 e_v1386 e_v1387 e_v1388 e_v1389 e_v1390 e_v1391 e_v1392 e_v1393 e_v1394 e_v1395 e_v1396 e_v1397 e_v1398 e_v1399 e_v1400 e_v1401 e_v1402 e_v1403 e_v1404 e_v1405 e_v1406 e_v1407 e_v1408 e_v1409 e_v1410 e_v1411 e_v1412 e_v1413 e_v1414 e_v1415 e_v1416 e_v1417 e_v1418 e_v1419 h_v1420 e_v1420 e_v1421 e_v1422 e_v1423 e_v1424 e_v1425 e_v1426 e_v1427 e_v1428 e_v1429 e_v1430 e_v1431 e_v1432 e_v1433 e_v1434 e_v1435 e_v1436 e_v1437 e_v1438 e_v1441 e_v1442 e_v1443 e_v1444 e_v1445 e_v1446 e_v1447 e_v1448 e_v1449 e_v1450 e_v1454 e_v1455 e_v1456 e_v1457 e_v1458 e_v1459 e_v1460 e_v1461 e_v1462 e_v1463 e_v1464 e_v1465 e_v1466 e_v1467 e_v1468 e_v1469 e_v1470 e_v1471 e_v1472 e_v1473 e_v1474 e_v1476 e_v1477 e_v1478 e_v1479 e_v1480 e_v1482 e_v1483 e_v1484 e_v1485 e_v1486 e_v1487 h_v1488 e_v1488 e_v1495 e_v1496 e_v1497 e_v1498 e_v1499 e_v1500 e_v1503 e_v1504 e_v1505 e_v1507 e_v1508 e_v1509 e_v1510 e_v1511 e_v1512 e_v1513 e_v1514 e_v1515 e_v1516 e_v1517 e_v1518 e_v1519 e_v1520 e_v1521 e_v1522 e_v1523 e_v1524 e_v1525 e_v1526 e_v1527 e_v1528 e_v1529 e_v1530 e_v1531 e_v1532 e_v1533 e_v1534 e_v1535 e_v1536 e_v1537 e_v1538 e_v1539 e_v1540 e_v1541 e_v1542 e_v1543 e_v1544 e_v1545 e_v1546 e_v1547 e_v1548 e_v1549 e_v1550 e_v1551 e_v1552 e_v1553 e_v1554 e_v1555 e_v1556 e_v1557 e_v1558 e_v1559 e_v1560 e_v1561 e_v1562 e_v1563 e_v1564 e_v1565 e_v1566 e_v1567 e_v1568 e_v1569 e_v1570 e_v1571 e_v1572 e_v1573 e_v1574 e_v1575 e_v1576 e_v1577 e_v1578 e_v1579 e_v1580 e_v1581 e_v1582 e_v1583 e_v1584 h_v1585 e_v1585 e_v1586 e_v1587 e_v1588 e_v1589 e_v1590 e_v1591 e_v1592 e_v1593 e_v1594 e_v1595 e_v1596 e_v1597 e_v1598 e_v1599 e_v1600 e_v1601 e_v1602 e_v1603 e_v1604 e_v1605 e_v1608 e_v1609 e_v1610 e_v1611 e_v1612 e_v1613 e_v1614 e_v1615 e_v1616 e_v1618 e_v1619 e_v1620 e_t1618_1 e_t1618_2 e_v1622 e_v1623 e_v1624 e_v1625 e_v1626 e_v1627 e_v1628 e_v1629 e_v1630 e_v1631 e_v1632 e_v1633 e_v1634 e_v1635 e_v1636 e_t1634_1 e_t1634_2 e_v1638 e_v1639 e_v1640 e_v1641 e_v1642 e_v1643 e_v1644 e_v1645 e_v1646 h_v1647 e_v1647 h_v1648 e_v1648 e_v1649 h_v1652 e_v1652 e_v1654 e_v1656 e_v1657 e_v1658 e_v1659 h_v1661 e_v1661 h_v1662 e_v1662 e_v1663 e_v1664 h_v1665 e_v1665 e_v1666 e_v1667 e_v1668 e_v1669 e_v1670 e_v1671 e_v1678 e_v1679 e_v1682 e_v1683 e_v1684 e_v1685 h_v1686 e_v1686 e_v1687 e_v1688 e_v1689 e_v1690 e_v1691 e_v1692 e_v1693 e_v1694 e_v1695 e_v1696 e_v1697 e_v1698 e_v1699 e_v1700 e_v1702 e_v1703 e_v1705 e_v1706 e_v1707 e_v1708 e_v1709 e_v1710 e_v1711 e_v1712 e_v1713 e_v1714 e_v1715 e_v1716 e_v1717 e_v1718 e_v1719 e_v1720 e_v1721 e_v1722 e_v1723 e_v1724 h_v1725 e_v1725 e_v1726 e_v1727 e_v1728 e_v1729 e_v1730 e_v1731 e_v1732 e_v1733 e_v1734 e_v1735 e_v1736 e_v1737 h_v1738 e_v1738 e_v1739 e_v1740 e_v1741 e_v1742 e_v1743 e_v1744 e_v1745 e_v1746 e_v1747 e_v1748 e_v1749 e_v1750 h_v1751 e_v1751 e_v1752 e_v1753 h_v1754 e_v1754 h_v1756 e_v1756 h_v1757 e_v1757 e_v1758 e_v1759 h_v1760 e_v1760 e_v1761 e_v1762 e_v1763 e_v1764 e_v1765 e_v1766 e_v1773 h_v1774 e_v1774 e_v1777 e_v1778 e_v1779 e_v1780 h_v1781 e_v1781 e_v1782 e_v1783 e_v1784 e_v1785 e_v1786 e_v1787 h_v1788 e_v1788 e_v1789 e_v1790 e_v1791 e_v1792 e_v1793 e_v1794 h_v1795 e_v1795 e_v1797 e_v1798 e_v1800 e_v1801 e_v1802 e_v1803 h_v1804 e_v1804 e_v1805 h_v1806 e_v1806

end Tammes15.D3Trig
