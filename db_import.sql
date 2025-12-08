-- MySQL dump 10.13  Distrib 9.2.0, for macos15.2 (arm64)
--
-- Host: localhost    Database: second_chance
-- ------------------------------------------------------
-- Server version	9.2.0

/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!50503 SET NAMES utf8mb4 */;
/*!40103 SET @OLD_TIME_ZONE=@@TIME_ZONE */;
/*!40103 SET TIME_ZONE='+00:00' */;
/*!40014 SET @OLD_UNIQUE_CHECKS=@@UNIQUE_CHECKS, UNIQUE_CHECKS=0 */;
/*!40014 SET @OLD_FOREIGN_KEY_CHECKS=@@FOREIGN_KEY_CHECKS, FOREIGN_KEY_CHECKS=0 */;
/*!40101 SET @OLD_SQL_MODE=@@SQL_MODE, SQL_MODE='NO_AUTO_VALUE_ON_ZERO' */;
/*!40111 SET @OLD_SQL_NOTES=@@SQL_NOTES, SQL_NOTES=0 */;

--
-- Table structure for table `categoria`
--

CREATE DATABASE IF NOT EXISTS second_chance;
USE second_chance;

DROP TABLE IF EXISTS `categoria`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `categoria` (
  `nome` varchar(50) NOT NULL,
  PRIMARY KEY (`nome`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `categoria`
--

LOCK TABLES `categoria` WRITE;
/*!40000 ALTER TABLE `categoria` DISABLE KEYS */;
INSERT INTO `categoria` VALUES ('iPad'),('Iphone'),('Mac'),('telefono');
/*!40000 ALTER TABLE `categoria` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `composto`
--

DROP TABLE IF EXISTS `composto`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `composto` (
  `id_ordine` int NOT NULL,
  `id_prodotto` int NOT NULL,
  `quantita` int NOT NULL,
  `prezzo` double NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `composto`
--

LOCK TABLES `composto` WRITE;
/*!40000 ALTER TABLE `composto` DISABLE KEYS */;
INSERT INTO `composto` VALUES (1,2,4,10000),(2,2,2,10000),(3,4,1,579.9),(4,6,4,1950),(5,9,2,300),(5,8,1,500),(6,5,3,456),(7,13,1,359);
/*!40000 ALTER TABLE `composto` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `ordine`
--

DROP TABLE IF EXISTS `ordine`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `ordine` (
  `id_ordine` int NOT NULL AUTO_INCREMENT,
  `id_utente` int NOT NULL,
  `data` datetime NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `indirizzo` varchar(500) NOT NULL,
  `totale` double NOT NULL,
  PRIMARY KEY (`id_ordine`)
) ENGINE=InnoDB AUTO_INCREMENT=8 DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `ordine`
--

LOCK TABLES `ordine` WRITE;
/*!40000 ALTER TABLE `ordine` DISABLE KEYS */;
INSERT INTO `ordine` VALUES (1,6,'2023-07-16 17:25:09','Via roma 129',40000),(2,6,'2023-07-16 17:25:41','Via roma 129',20000),(3,4,'2023-07-16 17:54:19','Via roma 129',579.9),(4,4,'2023-07-16 19:37:00','Via Veneto 350',7800),(5,10,'2023-07-24 21:09:25','Via roma 129',1100),(6,10,'2023-07-24 22:23:56','Via roma 129',1368),(7,3,'2025-10-31 13:19:11','Via roma 129',359);
/*!40000 ALTER TABLE `ordine` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `prodotto`
--

DROP TABLE IF EXISTS `prodotto`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `prodotto` (
  `id_prodotto` int NOT NULL AUTO_INCREMENT,
  `categoria` varchar(45) NOT NULL,
  `descrizione` varchar(1500) NOT NULL,
  `dimensioni` varchar(45) NOT NULL,
  `quantita` int NOT NULL DEFAULT '0',
  `peso` float NOT NULL,
  `immagine` varchar(450) NOT NULL DEFAULT 'default_prodotto.png',
  `marca` varchar(45) NOT NULL,
  `modello` varchar(45) NOT NULL,
  `prezzo` double NOT NULL,
  `disabilitato` tinyint NOT NULL DEFAULT '0',
  PRIMARY KEY (`id_prodotto`)
) ENGINE=InnoDB AUTO_INCREMENT=14 DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `prodotto`
--

LOCK TABLES `prodotto` WRITE;
/*!40000 ALTER TABLE `prodotto` DISABLE KEYS */;
INSERT INTO `prodotto` VALUES (3,'Iphone','iPhone 13 è uscito a Novembre 2021. iPhone 13 è uno smartphone molto giovane e colorato, adatto a chi desidera il massimo dal proprio iPhone, ma con un costo contenuto in confronto alle sue performance. E’ dotato del chip A15 Bionic ed è uno degli iPhone più potenti sul mercato, perfetto per chi ama scattare foto e registrare video. iPhone 13 è disponibile nelle seguenti versioni: iPhone 13 colore Rosa, iPhone 13 colore Verde, iPhone 13 colore Rosso, iPhone 13 colore Mezzanotte, iPhone 13 colore Blu e iPhone 13 colore Galassia.','12x10x10',0,120,'iphone13.avif','Apple','iPhone 13',419.9,0),(5,'iPad','Apple iPad mini 6 è un tablet Apple ricco di funzioni e con una potenza incredibile, il tutto racchiuso in un design eccezionale e con un formato mini. Questo modello è disponibile in 4 colori: grigio siderale, rosa, viola e galassia. Per quanto riguarda la capacità, puoi trovare iPad mini 6 64GB e iPad mini 6 256GB. Disponibile in versione Wi-Fi e Wi-Fi   Cell, questo modello di iPad pesa rispettivamente 293 grammi e 297 grammi. Uno dei punti di forza della linea iPad mini è proprio la dimensione ridotta, che lo rende un modello perfetto da trasportare durante i viaggi o da utilizzare nelle occasioni più disparate, per l’esattezza 195,4 mm x 134,8 mm x 6,3 mm. ','195x134x6',0,700,'ipadmini6.avif','Apple','iPad mini 6 ',456,0),(6,'Mac','Notebook - Chip Apple M1 con CPU 8-core con 4 performance core e 4 efficiency core Neural Engine 16-core - RAM 8 Gb - HD 256 GB - GPU 7-core - Monitor LED - 13,3 pollici - Wireless 802.11 ax - Bluetooth 5.0 - Con videocamera incorporata - Sistema operativo Mac OS-X Big Sur','16cc',0,1456,'macbook-pro-2019.jpg','Apple','MacBookPro',1950,0),(8,'Iphone','Apple iPhone 13 Pro Max è uno smartphone iOS con caratteristiche all\'avanguardia che lo rendono una scelta eccellente per ogni tipo di utilizzo. Dispone di un grande display da 6.7 pollici e di una risoluzione da 2778x1284 pixel, fra le più elevate attualmente in circolazione. Le funzionalità offerte da questo Apple iPhone 13 Pro Max sono innumerevoli e al top di gamma. A cominciare dal modulo 5G che permette un trasferimento dati e una navigazione in internet eccellente, passando per la connettività Wi-fi e il GPS.Fotocamera da 12 megapixel. Lo spessore di 7.7mm è veramente contenuto e rende questo Apple iPhone 13 Pro Max ancora più spettacolare.','12x12x3',0,123,'iphone13promax.webp','Apple','iPhone13 pro max',500,0),(9,'iPad','Apple iPhone 12 è uno degli smartphone iOS più avanzati e completi che ci siano in circolazione. Dispone di un grande display da 6.1 pollici con una risoluzione di 2532x1170 pixel. Le funzionalità offerte da questo Apple iPhone 12 sono veramente tante e all\'avanguardia. A cominciare dal modulo 5G che permette un trasferimento dati e una navigazione in internet eccellente.Fotocamera da 12 megapixel ma che permette ugualmente al Apple iPhone 12 di scattare foto di buona qualità con una risoluzione di 4000x3000 pixel e di registrare video in 4K alla risoluzione di 3840x2160 pixel. Lo spessore di 7.4mm è veramente contenuto e rende questo Apple iPhone 12 ancora più spettacolare.','10x10x3',0,140,'iphone12promax.jpg','Apple','iPhone 12',400,1),(11,'Iphone','iPhone 11 è uno smartphone con sistema operativo iOS 13, che non ha molto da invidiare ai dispositivi più avanzati.La certificazione IP 68 lo rende impermeabile e per questo è adatto a tutte le situazioni.Il design convince e lo spessore di 8.3 mm regala a questo iPhone 11 un ottimo touch and feel.Dispone di un ottimo display da 6.1 pollici con una risoluzione di 828 x 1792 con tecnologia Liquid Retina. Sul versante hardware, iPhone 11 dispone di un SOC Apple A13 Bionic e ha 4GB di ram. Per quanto riguarda la batteria, è una 3046 mAH che da discrete prestazioni in termini di autonomia.Questo iPhone 11 è un prodotto che soddisfa anche per ciò che riguarda la multimedialità anche grazie alla fotocamera da 12 megapixel con apertura 1.8 che garantisce ottimi scatti, mentre la fotocamera frontale è da 12mpx.','12x12x3',0,180,'iphone11.jpg','Apple','iPhone 11',430,0),(12,'Mac','l MacBook Pro 2020 di Apple è il notebook di punta della casa produttrice. Come tutti i dispositivi Apple, la sua particolarità sta nel sistema operativo proprietario. Il MacBook Pro 2020 dispone di macOS 11 Big Sur. Questo notebook è quindi compatibile con le applicazioni dell’ecosistema Apple.Un potente processore multi-core di Intel garantisce elevate performance per qualsiasi task. L’Apple MacBook Pro 2020 completamente ricondizionato convince grazie all’elevata durata della batteria e al suo peso incredibilmente ridotto. Ciò fa del MacBook Pro 2020 di Apple una scelta adatta alla mobilità ma con tanta potenza.','16\'\'',0,700,'mackbookpro16.jpg','Apple','MacBook Pro 16\'\'',1890,0),(13,'iPad','L\'iPad di ottava generazione, anche noto come iPad 2020, è un tablet sviluppato e commercializzato da Apple Inc. È dotato di un display Retina da 10,2 pollici ed è alimentato dal processore Apple A12 Bionic. È il successore dell\'iPad di settima generazione. Il dispositivo è stato presentato il 15 settembre 2020.','9\'\'',0,400,'ipad8.jpg','Apple','iPad 8th',359,0);
/*!40000 ALTER TABLE `prodotto` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `recensione`
--

DROP TABLE IF EXISTS `recensione`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `recensione` (
  `id_recensione` int NOT NULL AUTO_INCREMENT,
  `cliente` int NOT NULL,
  `prodotto` int NOT NULL,
  `data` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `testo` varchar(500) DEFAULT NULL,
  `valutazione` int NOT NULL,
  PRIMARY KEY (`id_recensione`)
) ENGINE=InnoDB AUTO_INCREMENT=8 DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `recensione`
--

LOCK TABLES `recensione` WRITE;
/*!40000 ALTER TABLE `recensione` DISABLE KEYS */;
INSERT INTO `recensione` VALUES (1,0,2,'2023-07-16 13:18:21','è davvero bello!',5),(2,4,2,'2023-07-16 13:20:57','asdas',3),(3,0,2,'2023-07-16 13:22:29','123',3),(4,5,2,'2023-07-16 13:22:55','123412312',4),(6,10,11,'2023-07-24 20:47:33','Molto bello',5);
/*!40000 ALTER TABLE `recensione` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `specifiche`
--

DROP TABLE IF EXISTS `specifiche`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `specifiche` (
  `nome` varchar(45) NOT NULL,
  `id_prodotto` int NOT NULL,
  `valore` varchar(500) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `specifiche`
--

LOCK TABLES `specifiche` WRITE;
/*!40000 ALTER TABLE `specifiche` DISABLE KEYS */;
INSERT INTO `specifiche` VALUES ('Colore',0,'rosso'),('colore',0,'rosso'),('colore',0,'rosso'),('colore',0,'rosso'),('colore',0,'oro'),('capienza',0,'128gb'),('colore',5,'grigio'),('capacita',5,'128gb'),('colore',6,'oro'),('capacita',6,'1thera'),('Colore ',9,'viola'),('Capacita',9,'128gb'),('Colore',9,'grigio siderale'),('Capacita',9,'1tera'),('colore',8,'oro'),('capacita',8,'128gb'),('Colore',8,'viola'),('Capacita',8,'64gb'),('Colore ',8,'rosso'),('Capacita',8,'128gb '),('Colore',8,'oro'),('Colore',13,'Grigio'),('Capacita',13,'16gb'),('Colore',12,'spacegray'),('Capacita',12,'1Thera'),('Colore',11,'rosso'),('Capacita ',11,'268gb'),('Capacita',3,'512 GB'),('Colore',3,'viola'),('Fotocamera',3,'Grandangolo (1.6); Ultra-grandangolo (2.4)'),('test',3,'test');
/*!40000 ALTER TABLE `specifiche` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `utente`
--

DROP TABLE IF EXISTS `utente`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `utente` (
  `id_utente` int NOT NULL AUTO_INCREMENT,
  `nome` varchar(45) NOT NULL,
  `cognome` varchar(45) NOT NULL,
  `admin` tinyint NOT NULL DEFAULT '0',
  `email` varchar(150) NOT NULL,
  `telefono` varchar(45) DEFAULT NULL,
  `passwordhash` varchar(500) NOT NULL,
  `immagine` varchar(45) DEFAULT 'default_user.png',
  PRIMARY KEY (`id_utente`)
) ENGINE=InnoDB AUTO_INCREMENT=13 DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `utente`
--

LOCK TABLES `utente` WRITE;
/*!40000 ALTER TABLE `utente` DISABLE KEYS */;
INSERT INTO `utente` VALUES (3,'MatteoEdit','sacco',1,'matteosacco00@gmail.com','3314978343','49efef5f70d47adc2db2eb397fbef5f7bc560e29','pizza-monster_c0.png'),(4,'Daria','Gambardella',0,'dg.ambardella@icloud.it','3663320761','b2e98ad6f6eb8508dd6a14cfa704bad7f05f6fb1',''),(6,'Daria','test',0,'daria@test.it','3333333333','b2e98ad6f6eb8508dd6a14cfa704bad7f05f6fb1','rabbit_innamorato (3).png'),(7,'Daria','Gambardella',0,'d.gambardella01@gmail.com','3663320761','b2e98ad6f6eb8508dd6a14cfa704bad7f05f6fb1','samantha-fotografa.png'),(8,'Daria','Gambardella',1,'dg.ambardella2@icloud.com','3333333333','b2e98ad6f6eb8508dd6a14cfa704bad7f05f6fb1',''),(9,'Daria','Gambardella',0,'dg.ambardella234@icloud.com','3333333333','b2e98ad6f6eb8508dd6a14cfa704bad7f05f6fb1',''),(10,'Daria','Gambardella',0,'dg.ambardella3@icloud.com','3333333333','b2e98ad6f6eb8508dd6a14cfa704bad7f05f6fb1',''),(11,'Daria','Gambardella',0,'dg.ambardella56@icloud.com','3333333333','5b96672ae7709eab297550cae362d5bee468c57d',''),(12,'Daria','Gambardella',0,'dg.ambardella@icloud.com','3313131123','49efef5f70d47adc2db2eb397fbef5f7bc560e29','free-ai-online-qr-code-generator.webp');
/*!40000 ALTER TABLE `utente` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `wishlist`
--

DROP TABLE IF EXISTS `wishlist`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `wishlist` (
  `id_cliente` int NOT NULL,
  `id_prodotto` int NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `wishlist`
--

LOCK TABLES `wishlist` WRITE;
/*!40000 ALTER TABLE `wishlist` DISABLE KEYS */;
INSERT INTO `wishlist` VALUES (4,3),(4,4),(10,12),(10,13),(3,12),(12,13),(3,11);
/*!40000 ALTER TABLE `wishlist` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Dumping routines for database 'second_chance'
--
/*!40103 SET TIME_ZONE=@OLD_TIME_ZONE */;

/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40014 SET UNIQUE_CHECKS=@OLD_UNIQUE_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;

-- Dump completed on 2025-10-31 13:33:58
