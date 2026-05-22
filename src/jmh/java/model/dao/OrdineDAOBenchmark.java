package model.dao;

import model.beans.*;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.*;
import java.util.ArrayList;
import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class OrdineDAOBenchmark {

    private OrdineDAO ordineDAO;
    private Ordine validOrdine;
    private Ordine nonExistentOrdine;
    private Ordine invalidOrdine;
    
    private Utente validUtente;
    private Utente invalidUtente;
    
    private Carrello sampleCarrello;

    @Setup(Level.Trial)
    public void setup() {
        this.ordineDAO = new OrdineDAO();

        // 1. Create a dummy user 999 in the database to satisfy the foreign key constraint
        try (Connection conn = utils.ConPool.getConnection();
             PreparedStatement st = conn.prepareStatement(
                     "INSERT INTO utente (id_utente, nome, cognome, email, passwordhash) VALUES (999, 'Dummy', 'User', 'dummy@bench.com', 'dummyhash') ON DUPLICATE KEY UPDATE id_utente=999")) {
            st.executeUpdate();
        } catch (SQLException e) {
            e.printStackTrace();
        }

        // 2. Prepare sample cart for benchmarks
        this.sampleCarrello = new Carrello();
        Prodotto p1 = new Prodotto();
        p1.setId(3); // iPhone 13 (exists in db_import.sql)
        p1.setPrezzo(419.9);
        p1.setMarca("Apple");
        p1.setModello("iPhone 13");

        ProdottoCarrello pc1 = new ProdottoCarrello();
        pc1.setProdotto(p1);
        pc1.setQuantita(1);
        this.sampleCarrello.aggiungiProdotto(pc1);

        Prodotto p2 = new Prodotto();
        p2.setId(5); // iPad mini 6 (exists in db_import.sql)
        p2.setPrezzo(456.0);
        p2.setMarca("Apple");
        p2.setModello("iPad mini 6 ");

        ProdottoCarrello pc2 = new ProdottoCarrello();
        pc2.setProdotto(p2);
        pc2.setQuantita(2);
        this.sampleCarrello.aggiungiProdotto(pc2);

        // 3. Prepare valid Ordine for insertion profiling
        this.validOrdine = new Ordine();
        Utente dummyUser = new Utente();
        dummyUser.setId(999);
        this.validOrdine.setUtente(dummyUser);
        this.validOrdine.setIndirizzo("Via Roma 129");
        this.validOrdine.setPrezzoTotale(1331.9);
        this.validOrdine.setCarrello(this.sampleCarrello);

        // 4. Prepare targets for query benchmarks
        this.nonExistentOrdine = new Ordine();
        this.nonExistentOrdine.setId(999);

        this.invalidOrdine = new Ordine();
        this.invalidOrdine.setId(-1);

        this.validUtente = new Utente();
        this.validUtente.setId(10); // Valid user with orders in db_import.sql

        this.invalidUtente = new Utente();
        this.invalidUtente.setId(-1);
    }

    @TearDown(Level.Iteration)
    public void teardownIteration() {
        // Clean up any added orders during the iteration to keep DB size constant
        try (Connection conn = utils.ConPool.getConnection()) {
            conn.setAutoCommit(false);
            try (PreparedStatement st1 = conn.prepareStatement("DELETE FROM composto WHERE id_ordine IN (SELECT id_ordine FROM ordine WHERE id_utente = 999)");
                 PreparedStatement st2 = conn.prepareStatement("DELETE FROM ordine WHERE id_utente = 999")) {
                st1.executeUpdate();
                st2.executeUpdate();
                conn.commit();
            } catch (SQLException e) {
                conn.rollback();
            }
        } catch (SQLException e) {
            // Ignore
        }
    }

    @TearDown(Level.Trial)
    public void teardownTrial() {
        // Clean up the dummy user entirely
        try (Connection conn = utils.ConPool.getConnection()) {
            conn.setAutoCommit(false);
            try (PreparedStatement st1 = conn.prepareStatement("DELETE FROM composto WHERE id_ordine IN (SELECT id_ordine FROM ordine WHERE id_utente = 999)");
                 PreparedStatement st2 = conn.prepareStatement("DELETE FROM ordine WHERE id_utente = 999");
                 PreparedStatement st3 = conn.prepareStatement("DELETE FROM utente WHERE id_utente = 999")) {
                st1.executeUpdate();
                st2.executeUpdate();
                st3.executeUpdate();
                conn.commit();
            } catch (SQLException e) {
                conn.rollback();
            }
        } catch (SQLException e) {
            // Ignore
        }
    }

    @Benchmark
    public void benchmarkAddOrdineValid(Blackhole bh) {
        try {
            ordineDAO.addOrdine(validOrdine);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetOrdineByIdValid(Blackhole bh) {
        try {
            bh.consume(ordineDAO.getOrdineById(1)); // Valid order ID in db_import.sql
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetOrdineByIdInvalid(Blackhole bh) {
        try {
            ordineDAO.getOrdineById(-1);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetProdottoOrdineValid(Blackhole bh) {
        try {
            Ordine o = new Ordine();
            o.setId(1); // Valid order ID in db_import.sql
            bh.consume(ordineDAO.getProdottoOrdine(o));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetProdottoOrdineInvalid(Blackhole bh) {
        try {
            ordineDAO.getProdottoOrdine(invalidOrdine);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetOrdiniByUtenteValid(Blackhole bh) {
        try {
            bh.consume(ordineDAO.getOrdiniByUtente(validUtente));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetOrdiniByUtenteInvalid(Blackhole bh) {
        try {
            ordineDAO.getOrdiniByUtente(invalidUtente);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkCarrelloOperations(Blackhole bh) {
        // Measure CPU/memory overhead of Carrello loops (GCI69 & GCI3 size-in-loop)
        double total = sampleCarrello.getTotaleCarrello();
        bh.consume(total);
    }
}
