package model.dao;

import model.beans.Ordine;
import model.beans.Recensione;
import model.beans.Utente;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.Mock;
import org.mockito.MockedStatic;
import org.mockito.MockitoAnnotations;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class UtenteDAOTest {

    private UtenteDAO utenteDAO;
    private MockedStatic<ConPool> conPoolMock;

    @Mock
    private Connection connection;

    @Mock
    private PreparedStatement preparedStatement;

    @Mock
    private ResultSet resultSet;

    @Mock
    private OrdineDAO ordineDAO;

    @Mock
    private RecensioneDAO recensioneDAO;

    @BeforeEach
    void setUp() throws SQLException {
        MockitoAnnotations.openMocks(this);

        // Spy on UtenteDAO to mock protected factory methods
        utenteDAO = spy(new UtenteDAO());
        doReturn(ordineDAO).when(utenteDAO).getOrdineDAO();
        doReturn(recensioneDAO).when(utenteDAO).getRecensioneDAO();

        conPoolMock = mockStatic(ConPool.class);
        conPoolMock.when(ConPool::getConnection).thenReturn(connection);

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
    }

    @AfterEach
    void tearDown() {
        conPoolMock.close();
    }

    // =================================================================================================
    // getUtenteById Tests (F1-F6)
    // =================================================================================================

    @Test
    @DisplayName("F1: Should return user with dependencies found")
    void shouldReturnUserWithDependenciesWhenFound() throws SQLException {
        // Arrange
        int validId = 1;
        when(preparedStatement.executeQuery()).thenReturn(resultSet);

        when(resultSet.next()).thenReturn(true);
        stubValidUserRow(validId, "Mario", "Rossi", "mario@test.com");

        when(ordineDAO.getOrdiniByUtente(any())).thenReturn(createFakeOrdini());
        when(recensioneDAO.getRecensioniByUtente(any())).thenReturn(createFakeRecensioni());

        // Act
        Utente result = utenteDAO.getUtenteById(validId);

        // Assert
        assertNotNull(result);
        assertEquals(validId, result.getId());
        assertEquals("Mario", result.getNome());
        assertFalse(result.getOrdini().isEmpty());
        assertFalse(result.getRecensioni().isEmpty());
    }

    @Test
    @DisplayName("F2: Should return user with empty dependencies when none found")
    void shouldReturnUserWithEmptyDependenciesWhenNoneFound() throws SQLException {
        // Arrange
        int validId = 1;
        when(preparedStatement.executeQuery()).thenReturn(resultSet);

        when(resultSet.next()).thenReturn(true);
        stubValidUserRow(validId, "Mario", "Rossi", "mario@test.com");

        when(ordineDAO.getOrdiniByUtente(any())).thenReturn(new ArrayList<>());
        when(recensioneDAO.getRecensioniByUtente(any())).thenReturn(new ArrayList<>());

        // Act
        Utente result = utenteDAO.getUtenteById(validId);

        // Assert
        assertNotNull(result);
        assertTrue(result.getOrdini().isEmpty());
        assertTrue(result.getRecensioni().isEmpty());
    }

    @Test
    @DisplayName("F3: Should return null when user not found")
    void shouldReturnNullWhenUserNotFound() throws SQLException {
        // Arrange
        int nonExistentId = 999;
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        Utente result = utenteDAO.getUtenteById(nonExistentId);

        // Assert
        assertNull(result);
    }

    @ParameterizedTest
    @DisplayName("F4, F5: Should throw exception when User ID is invalid")
    @CsvSource({ "0", "-1", "-100" })
    void shouldThrowExceptionWhenUserIdIsInvalid(int invalidId) {
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> utenteDAO.getUtenteById(invalidId));
        assertEquals("L'ID dell'utente deve essere maggiore di zero.", exception.getMessage());
    }

    @Test
    @DisplayName("F6: Should return user with empty lists when dependent DAO fails")
    void shouldReturnUserWithEmptyListsWhenDependentDaoFails() throws SQLException {
        // Arrange
        int validId = 1;
        when(preparedStatement.executeQuery()).thenReturn(resultSet);

        when(resultSet.next()).thenReturn(true);
        stubValidUserRow(validId, "Mario", "Rossi", "mario@test.com");

        when(ordineDAO.getOrdiniByUtente(any())).thenThrow(new SQLException("DB Error"));
        when(recensioneDAO.getRecensioniByUtente(any())).thenThrow(new SQLException("DB Error"));

        // Act
        Utente result = utenteDAO.getUtenteById(validId);

        // Assert
        assertNotNull(result);
        assertNotNull(result.getOrdini());
        assertTrue(result.getOrdini().isEmpty());
        assertNotNull(result.getRecensioni());
        assertTrue(result.getRecensioni().isEmpty());
    }

    // =================================================================================================
    // addUtente Tests (F7-F11)
    // =================================================================================================

    @Test
    @DisplayName("F7: Should add user successfully when valid")
    void shouldAddUserSuccessfully() throws SQLException {
        // Arrange
        Utente validUser = createValidUtente();
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        // Act
        int result = utenteDAO.addUtente(validUser);

        // Assert
        assertEquals(1, result);
        verify(preparedStatement).setString(1, validUser.getNome());
    }

    @Test
    @DisplayName("F8: Should add user successfully without image")
    void shouldAddUserSuccessfullyWithoutImage() throws SQLException {
        // Arrange
        Utente validUser = createValidUtente();
        validUser.setImmagine(null);

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        // Act
        int result = utenteDAO.addUtente(validUser);

        // Assert
        assertEquals(1, result);
    }

    @Test
    @DisplayName("F9, F10: Should throw exception when user or mandatory field is null")
    void shouldThrowExceptionWhenUserOrFieldIsNull() {
        // F9: Null user
        assertThrows(IllegalArgumentException.class, () -> utenteDAO.addUtente(null));

        // F10: Missing mandatory field WITHOUT calling bean setter (setter would throw
        // before DAO)
        Utente mockedUser = mock(Utente.class);
        when(mockedUser.getNome()).thenReturn(null); // mandatory missing
        when(mockedUser.getCognome()).thenReturn("Cognome");
        when(mockedUser.getEmail()).thenReturn("email@test.com");
        when(mockedUser.getPassword()).thenReturn("pass");

        assertThrows(IllegalArgumentException.class, () -> utenteDAO.addUtente(mockedUser));
    }

    @Test
    @DisplayName("F11: Should throw exception on duplicate entry")
    void shouldThrowExceptionOnDuplicateEntry() throws SQLException {
        // Arrange
        Utente validUser = createValidUtente();
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenThrow(new SQLException("Duplicate entry"));

        // Act & Assert
        assertThrows(SQLException.class, () -> utenteDAO.addUtente(validUser));
    }

    // =================================================================================================
    // getUserByEmailPassword Tests (F12-F14)
    // =================================================================================================

    @Test
    @DisplayName("F12: Should return user when credentials match")
    void shouldReturnUserWhenCredentialsMatch() throws SQLException {
        // Arrange
        String email = "test@test.com";
        String pwd = "password";

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);

        when(resultSet.next()).thenReturn(true);
        stubValidUserRow(1, "Mario", "Rossi", email);

        when(ordineDAO.getOrdiniByUtente(any())).thenReturn(new ArrayList<>());
        when(recensioneDAO.getRecensioniByUtente(any())).thenReturn(new ArrayList<>());

        // Act
        Utente result = utenteDAO.getUserByEmailPassword(email, pwd);

        // Assert
        assertNotNull(result);
        assertEquals(1, result.getId());
        verify(ordineDAO).getOrdiniByUtente(any());
        verify(recensioneDAO).getRecensioniByUtente(any());
    }

    @ParameterizedTest
    @DisplayName("F14: Should throw exception for invalid credentials input")
    @CsvSource({
            ", password",
            "'', password",
            "email, ",
            "email, ''"
    })
    void shouldThrowExceptionForInvalidCredentialsInput(String email, String password) {
        assertThrows(IllegalArgumentException.class, () -> utenteDAO.getUserByEmailPassword(email, password));
    }

    // =================================================================================================
    // editProfilo Tests (F15-F17)
    // =================================================================================================

    @ParameterizedTest
    @DisplayName("F15: Should support all valid edit operations")
    @CsvSource({
            "/editNome",
            "/editCognome",
            "/editEmail",
            "/editTelefono",
            "/editImmagine"
    })
    void shouldSupportAllValidEditOperations(String operation) throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);

        // Act
        utenteDAO.editProfilo(operation, "newVal", 1);

        // Assert
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F16: Should throw exception for unsupported operation")
    void shouldThrowExceptionForUnsupportedOperation() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> utenteDAO.editProfilo("/invalidOp", "val", 1));
        assertTrue(e.getMessage().contains("Operazione non supportata"));
    }

    @ParameterizedTest
    @DisplayName("F17: Should throw exception for invalid edit inputs")
    @CsvSource({
            ", val, 1",
            "op, , 1",
            "op, val, 0",
            "op, val, -1"
    })
    void shouldThrowExceptionForInvalidEditInputs(String op, String val, int id) {
        assertThrows(IllegalArgumentException.class, () -> utenteDAO.editProfilo(op, val, id));
    }

    // =============================================================================================
    // Helpers
    // =============================================================================================

    private void stubValidUserRow(int id, String nome, String cognome, String email) throws SQLException {
        when(resultSet.getInt(1)).thenReturn(id);
        when(resultSet.getString(2)).thenReturn(nome);
        when(resultSet.getString(3)).thenReturn(cognome);
        when(resultSet.getBoolean(4)).thenReturn(false);
        when(resultSet.getString(5)).thenReturn(email);
        when(resultSet.getString(6)).thenReturn("1234567890");
        when(resultSet.getString(7)).thenReturn("pass");
        when(resultSet.getString(8)).thenReturn(null);
    }

    private ArrayList<Ordine> createFakeOrdini() {
        ArrayList<Ordine> list = new ArrayList<>();
        list.add(new Ordine());
        return list;
    }

    private ArrayList<Recensione> createFakeRecensioni() {
        ArrayList<Recensione> list = new ArrayList<>();
        list.add(new Recensione());
        return list;
    }

    private Utente createValidUtente() {
        Utente u = new Utente();
        u.setNome("Nome");
        u.setCognome("Cognome");
        u.setEmail("email@test.com");
        u.setPassword("pass");
        u.setTelefono("1234567890");
        return u;
    }
}
