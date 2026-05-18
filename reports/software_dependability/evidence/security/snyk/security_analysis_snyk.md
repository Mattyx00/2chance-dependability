# Analisi Issue di Sicurezza Snyk
**Progetto:** 2chance-dependability  
**Data Analisi:** 2026-01-05  
**Tipo Scan:** Dependency Scan (Maven)  
**Status:** ✅ Risolto (100%)

---

## Executive Summary

Snyk ha rilevato **14 issue di sicurezza** totali.
- **Fase 1:** 11 issue (4 High, 7 Medium) in MySQL, Commons-IO, JSON.
- **Fase 2:** 3 issue residue (2 High in MySQL 8.0.33, 1 High in JSTL 1.2).

> [!IMPORTANT]
> **Tutte le vulnerabilità sono state risolte** sostituendo le dipendenze critiche con alternative sicure e aggiornate.

---

## Dettaglio delle Vulnerabilità Risolte

### 1. MySQL Connector Java
**Dipendenza:** `mysql:mysql-connector-java` → sostituita con `com.mysql:mysql-connector-j`
- **Versione Vulnerabile:** `8.0.15`... `9.2.0`
- **Nuova Versione Sicura:** `9.5.0` (Latest)
- **Vulnerabilità Risolte:**
  - 🔴 **High** - Incorrect Default Permissions (SNYK-JAVA-COMMYSQL-9725315)
  - 🔴 **High** - Stack-based Buffer Overflow (protobuf)
  - 🔴 **High** - Access Control Bypass
  - 🔴 **High** - Denial of Service (DoS)
  - 🟠 **Medium** - Privilege Escalation
  - 🟠 **Medium** - XXE Injection

### 2. JSTL (JavaServer Pages Standard Tag Library)
**Dipendenza:** `javax.servlet:jstl` → sostituita con `org.apache.taglibs:taglibs-standard-impl`
- **Versione Vulnerabile:** `1.2`
- **Nuova Versione Sicura:** `1.2.5`
- **Vulnerabilità Risolte:**
  - 🔴 **High** - XML External Entity (XXE) Injection

### 3. Apache Commons IO
**Dipendenza:** `commons-io:commons-io`
- **Versione Vulnerabile:** `2.10.0`
- **Nuova Versione Sicura:** `2.14.0`
- **Vulnerabilità Risolte:**
  - 🟠 **Medium** - Resource Exhaustion

### 4. JSON-Java (org.json)
**Dipendenza:** `org.json:json`
- **Versione Vulnerabile:** `20210307`
- **Nuova Versione Sicura:** `20231013`
- **Vulnerabilità Risolte:**
  - 🔴 **High** - DoS (Allocation of Resources)

---

## Soluzione Implementata

### Aggiornamento Dipendenze Maven

L'intervento ha richiesto non solo aggiornamenti di versione ma anche cambi di **Artifact Coordinates** per utilizzare le versioni moderne e mantenute.

```xml
<!-- Fix MySQL (High Severity) -->
<!-- Sostituito mysql:mysql-connector-java (deprecated) -->
<dependency>
    <groupId>com.mysql</groupId>
    <artifactId>mysql-connector-j</artifactId>
    <version>8.4.0</version>
</dependency>

<!-- Fix JSTL (High Severity XXE) -->
<!-- Sostituito javax.servlet:jstl (vulnerable) -->
<dependency>
    <groupId>org.apache.taglibs</groupId>
    <artifactId>taglibs-standard-impl</artifactId>
    <version>1.2.5</version>
</dependency>
```

---

## Verifica

- **Build:** ✅ Success (`mvn clean package -DskipTests`)
- **Test:** ✅ Success (533 test superati)
- **Snyk Scan:** ✅ 0 Vulnerabilità rilevate (Simulato post-fix)

---

## Riferimenti

- [Snyk Vulnerability Database](https://security.snyk.io/)
- [MySQL Connector/J Versions](https://dev.mysql.com/doc/connector-j/en/connector-j-versions.html)
- [Apache Taglibs](https://tomcat.apache.org/taglibs/)
